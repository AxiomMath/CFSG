module

public import CFSG.Permutation.FiveTransitive.CyclicPreimageSylow
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.InvolutionSylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.FixedNormalizerCyclicPreimageSylow

open MulAction FixedNormalizerAction

variable {G X : Type*} [Group G] [MulAction G X] (Q : Subgroup G)

theorem inside_le_kernel :
    Inside Q ≤ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker := by
  intro q hq
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro y
  apply Subtype.ext
  exact mem_fixedPoints.mp y.property ⟨q, hq⟩

private theorem kernel_ambient_le_fixer :
    ((toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker).map (Normalizer Q).subtype ≤
      fixingSubgroup G (fixedPoints Q X) := by
  rintro g ⟨n, hn, rfl⟩
  rw [mem_fixingSubgroup_iff]
  intro y hy
  have hyF : y ∈ Fixed (X := X) Q := by rw [fixed_eq]; exact hy
  have he := DFunLike.congr_fun (MonoidHom.mem_ker.mp hn) (⟨y, hyF⟩ : Fixed (X := X) Q)
  exact congrArg Subtype.val he

theorem kernel_pgroup_le_inside {p : ℕ}
    (S : Sylow p (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (B : Subgroup (Normalizer Q))
    (hBker : B ≤ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker)
    (hB : IsPGroup p B) : B ≤ Inside Q := by
  let H := fixingSubgroup G (fixedPoints Q X)
  have hQH : Q ≤ H := by
    rw [← hS]
    rintro q ⟨s, hs, rfl⟩
    exact s.property
  have hQp : IsPGroup p Q := by rw [← hS]; exact S.isPGroup'.map H.subtype
  have hIp : IsPGroup p (Inside Q) := hQp.comap_subtype
  let J : Subgroup (Normalizer Q) := Inside Q ⊔ B
  have hJp : IsPGroup p J := hIp.to_sup_of_normal_left hB
  let D := J.map (Normalizer Q).subtype
  have hJH : J ≤ H.comap (Normalizer Q).subtype := by
    apply sup_le
    · intro q hq
      exact hQH hq
    · intro b hb
      exact kernel_ambient_le_fixer Q ⟨b, hBker hb, rfl⟩
  have hDH : D ≤ H := Subgroup.map_le_iff_le_comap.mpr hJH
  have hDp : IsPGroup p D := hJp.map (Normalizer Q).subtype
  have hD'p : IsPGroup p (D.subgroupOf H) := hDp.of_injective
    (Subgroup.subgroupOfEquivOfLe hDH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hDH).injective
  have hSD : (S : Subgroup H) ≤ D.subgroupOf H := by
    intro s hs
    have hsQ : (s : G) ∈ Q := hS.le ⟨s, hs, rfl⟩
    exact ⟨⟨(s : G), Q.le_normalizer hsQ⟩,
      (show Inside Q ≤ J from le_sup_left) hsQ, rfl⟩
  have he := S.is_maximal' hD'p hSD
  intro b hb
  have hbD : (b : G) ∈ D := ⟨b, (show B ≤ J from le_sup_right) hb, rfl⟩
  have hbS : (⟨(b : G), hDH hbD⟩ : H) ∈ (S : Subgroup H) := by
    rw [← he]
    exact hbD
  change (b : G) ∈ Q
  exact hS.le ⟨⟨(b : G), hDH hbD⟩, hbS, rfl⟩

private theorem exists_sylow_generated {p : ℕ}
    (S : Sylow p (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (A : Subgroup G) (hA : IsPGroup p A) (hQA : Q ≤ A)
    (x : Normalizer Q) (hxA : (x : G) ∈ A) :
    ∃ R : Sylow p ((Subgroup.zpowers (toPermHom (Normalizer Q) (Fixed (X := X) Q) x)).comap
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))),
      SylowPreimageNormalizer.ambient (toPermHom (Normalizer Q) (Fixed (X := X) Q))
        (Subgroup.zpowers (toPermHom (Normalizer Q) (Fixed (X := X) Q) x)) R =
          Inside Q ⊔ Subgroup.zpowers x := by
  exact CyclicPreimageSylow.exists_sylow_of_kernel_maximal
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (Inside Q) (inside_le_kernel Q)
    (kernel_pgroup_le_inside Q S hS) (A.subgroupOf (Normalizer Q)) hA.comap_subtype
    (fun _ hq => hQA hq) x hxA

theorem normalizer_generated_map_eq_centralizer [Finite G] [Finite X]
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hQA : Q ≤ A)
    (x : Normalizer Q) (hxA : (x : G) ∈ A)
    (himage : Image (X := X) Q = ⊤)
    (hxorder : orderOf (toPermHom (Normalizer Q) (Fixed (X := X) Q) x) = 2) :
    (Subgroup.normalizer ((Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q)) : Set (Normalizer Q))).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) =
        Subgroup.centralizer ({toPermHom (Normalizer Q) (Fixed (X := X) Q) x} :
          Set (Equiv.Perm (Fixed (X := X) Q))) := by
  obtain ⟨R, hR⟩ := exists_sylow_generated Q S hS A hA hQA x hxA
  have he := InvolutionSylowPreimageNormalizer.normalizer_map_eq_centralizer
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (MonoidHom.range_eq_top.mp himage)
    (toPermHom (Normalizer Q) (Fixed (X := X) Q) x) hxorder R
  rw [hR] at he
  exact he

end FiveTransitive.FixedNormalizerCyclicPreimageSylow

end CFSG
