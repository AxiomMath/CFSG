module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeMat
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

namespace ResU3Three

open CFSG.Assembly Matrix

theorem not_isSolvable_of_isQuasisimple {G : Type*} [Group G]
    (h : CFSG.Assembly.IsQuasisimple G) : ¬ Group.IsSolvable G := by
  intro hs
  obtain ⟨h1, h2⟩ := h
  have : Nontrivial G := by
    obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial (G := G ⧸ Subgroup.center G)).exists_pair_ne
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a', b', fun h => hab (by rw [h])⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne h1

theorem not_isComponentOf_of_isSolvable {G : Type*} [Group G] {S J : Subgroup G}
    (hS : Group.IsSolvable S) : ¬ CFSG.Assembly.IsComponentOf J S := by
  rintro ⟨hJS, -, hJq⟩
  have hJsolv : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJS)
      (Subgroup.inclusion_injective hJS)
  exact not_isSolvable_of_isQuasisimple hJq hJsolv

section Solv

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem isSolvable_ggFix_projConj {H : Subgroup (GL ι K)}
    (M : Subgroup.normalizer (H : Set (GL ι K)))
    (hM : ∀ x y : GL ι K, x ∈ H → y ∈ H → x * M = M * x → y * M = M * y → x * y = y * x) :
    Group.IsSolvable (ggFix (TableB.projConj H M)) := by
  classical
  set π := LargeEvenProjMk H with hπ
  set S : Subgroup H := (ggFix (TableB.projConj H M)).comap π with hS
  set n : H →* H := (H.normalizerMonoidHom M).toMonoidHom with hn
  have hc : ∀ s : H, s ∈ S → n s * s⁻¹ ∈ Subgroup.center H := by
    intro s hs
    have h1 : TableB.projConj H M (π s) = π s := hs
    have h2 : π (n s) = π s := by
      rw [← h1]
      rfl
    have h3 : n s * s⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
    rw [hπ, LargeEvenProjMk, QuotientGroup.ker_mk'] at h3
    have h4 : ((n s * s⁻¹ : H) : GL ι K) ∈ Subgroup.center (GL ι K) :=
      TableB.scalars_le_center (Subgroup.mem_subgroupOf.mp h3)
    rw [Subgroup.mem_center_iff] at h4 ⊢
    intro g
    exact Subtype.ext (h4 g)
  let z : S →* Subgroup.center H :=
    { toFun := fun s => ⟨n s * (s : H)⁻¹, hc s s.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => by
        apply Subtype.ext
        have hct := Subgroup.mem_center_iff.mp (hc t t.2)
        change n ((s : H) * t) * ((s : H) * t)⁻¹ = n s * (s : H)⁻¹ * (n t * (t : H)⁻¹)
        rw [map_mul, _root_.mul_inv_rev]
        calc n s * n t * ((t : H)⁻¹ * (s : H)⁻¹) = n s * ((n t * (t : H)⁻¹) * (s : H)⁻¹) := by
              group
          _ = n s * ((s : H)⁻¹ * (n t * (t : H)⁻¹)) := by rw [hct]
          _ = n s * (s : H)⁻¹ * (n t * (t : H)⁻¹) := by group }
  have hker : ∀ s : S, z s = 1 → ((s : H) : GL ι K) * M = M * ((s : H) : GL ι K) := by
    intro s hs
    have h1 : n s * (s : H)⁻¹ = 1 := congrArg Subtype.val hs
    have h2 : n s = s := by
      calc n s = n s * (s : H)⁻¹ * s := by group
        _ = s := by rw [h1, one_mul]
    have h3 : (M : GL ι K) * ((s : H) : GL ι K) * (M : GL ι K)⁻¹ = ((s : H) : GL ι K) :=
      congrArg Subtype.val h2
    calc ((s : H) : GL ι K) * M = (M : GL ι K) * ((s : H) : GL ι K) * (M : GL ι K)⁻¹ * M := by
          rw [h3]
      _ = M * ((s : H) : GL ι K) := by group
  haveI : Group.IsSolvable z.ker := isSolvable_of_comm fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hM _ _ ((a : S) : H).2 ((b : S) : H).2 (hker a a.2) (hker b b.2)
  haveI : Group.IsSolvable (Subgroup.center H) := isSolvable_of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  haveI : Group.IsSolvable S :=
    Group.isSolvable_of_ker_le_range z.ker.subtype z (by rw [Subgroup.range_subtype])
  have hmap : Group.IsSolvable (S.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective S)
  rwa [hS, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hmap

theorem isSolvable_ggFix_projConj_of_reg {H : Subgroup (GL (Fin 3) K)}
    (M : Subgroup.normalizer (H : Set (GL (Fin 3) K)))
    (hM : RegU3Three ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    Group.IsSolvable (ggFix (TableB.projConj H M)) := by
  refine isSolvable_ggFix_projConj M fun x y _ _ hx hy => Units.ext ?_
  have hx' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hx
  have hy' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hy
  simp only [Units.val_mul] at hx' hy' ⊢
  exact hM.commute hx' hy'

end Solv

end ResU3Three

end CFSG.StandardType

end
