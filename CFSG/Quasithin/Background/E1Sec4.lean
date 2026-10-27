module

public import CFSG.Quasithin.Background.E1Sec7Two
import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

section OInftyE

variable {Q : Type*} [Group Q] [Finite Q]

theorem oInftyE_eq_cCompSpan_sup (X : Type*) [Group X] [Finite X] :
    oInftyE X = cCompSpan (⊤ : Subgroup X) ⊔ CFSG.solvableRadical X := by
  show (CFSG.layer (X ⧸ CFSG.solvableRadical X)).comap
    (QuotientGroup.mk' (CFSG.solvableRadical X)) = _
  rw [← map_cCompSpan_eq_layer, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem map_subtype_solvableRadical_le (N : Subgroup Q) [N.Normal] :
    (CFSG.solvableRadical ↥N).map N.subtype ≤ CFSG.solvableRadical Q := by
  have hs : Group.IsSolvable ↥((CFSG.solvableRadical ↥N).map N.subtype) := by
    have : Group.IsSolvable ↥(CFSG.solvableRadical ↥N) := A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical ↥N).equivMapOfInjective N.subtype
        N.subtype_injective).toMonoidHom)
      ((CFSG.solvableRadical ↥N).equivMapOfInjective N.subtype N.subtype_injective).surjective
  refine A3.le_solvableRadical ⟨fun r hr q => ?_⟩ hs
  obtain ⟨x, hx, rfl⟩ := hr
  refine ⟨MulAut.conjNormal q x, ?_, by simp [MulAut.conjNormal_apply]⟩
  have := solvableRadical_map_mulEquiv (MulAut.conjNormal (H := N) q)
  rw [← this]
  exact Subgroup.mem_map_of_mem _ hx

theorem le_oInftyE_of_oInftyE_eq_top {N : Subgroup Q} [N.Normal] (h : oInftyE ↥N = ⊤) :
    N ≤ oInftyE Q := by
  have h1 : (⊤ : Subgroup ↥N) = cCompSpan (⊤ : Subgroup ↥N) ⊔ CFSG.solvableRadical ↥N := by
    rw [← oInftyE_eq_cCompSpan_sup, h]
  have h2 : N = (cCompSpan (⊤ : Subgroup ↥N)).map N.subtype ⊔
      (CFSG.solvableRadical ↥N).map N.subtype := by
    rw [← Subgroup.map_sup, ← h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hsub : IsSubnormal N ⊤ :=
    IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)
  rw [oInftyE_eq_cCompSpan_sup Q]
  conv_lhs => rw [h2]
  refine sup_le_sup ?_ (map_subtype_solvableRadical_le N)
  rw [← cCompSpan_eq_map_subtype N]
  exact sSup_le_sSup fun L hL => cComp_mem_of_subnormal hsub hL

theorem le_oInftyE_of_injective {N' : Type*} [Group N'] [Finite N'] (ι : N' →* Q)
    (hι : Function.Injective ι) [ι.range.Normal] (h : oInftyE N' = ⊤) :
    ι.range ≤ oInftyE Q := by
  let e : N' ≃* ι.range := MonoidHom.ofInjective hι
  have h' : oInftyE ↥ι.range = ⊤ := by
    have h1 := oInftyE_map_mulEquiv e
    have h2 : (⊤ : Subgroup N').map e.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
    rw [h, h2] at h1
    exact h1.symm
  exact le_oInftyE_of_oInftyE_eq_top h'

end OInftyE

section Main

variable {G : Type*} [Group G] [Finite G]

theorem ten_four {T X Y K : Subgroup G} [X.Normal] [Y.Normal] (hT : IsSylowIn 2 T ⊤)
    (hYX : Y ≤ X) (hK : K ∈ sFamily T X Y)
    (h1 : oInftyE ↥((K ⊓ X).map (QuotientGroup.mk' Y)) = ⊤)
    (h2 : IsTwoClosed (CFSG.solvableRadical ↥(K.map (QuotientGroup.mk' Y))))
    (h3 : twoResidual (⊤ : Subgroup ↥(K.map (QuotientGroup.mk' Y))) =
      perfectCore (⊤ : Subgroup ↥(K.map (QuotientGroup.mk' Y)))) :
    CFSG.Open.pCore 2 (↥K ⧸ oInftyE ↥K) = ⊤ ∧ IsTwoClosed (CFSG.solvableRadical ↥K) ∧
      twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Y with hπ
  have hK' := hK
  obtain ⟨hKle, hTK, hEq, hmin⟩ := hK
  have hnormX : ∀ g : G, g ∈ Subgroup.normalizer (X : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t _ => hnormX t
  obtain ⟨hK1, -, -⟩ := ten_one hTX hYX hK'
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := fun k _ => hnormX k
  set Kb : Subgroup (G ⧸ Y) := K.map π with hKb
  let φ : ↥K →* ↥Kb := π.subgroupMap K
  have hφ : Function.Surjective φ := π.subgroupMap_surjective K
  have hφval : ∀ k : ↥K, ((φ k : ↥Kb) : G ⧸ Y) = π (k : G) := fun k => rfl
  have hkerY : ∀ k : ↥K, φ k = 1 → (k : G) ∈ Y := fun k hk => by
    have h1 : π (k : G) = 1 := congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hZeq : (CFSG.Open.pCore 2 ↥Kb).comap φ = (preO2 K Y).subgroupOf K := by
    ext k
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    unfold preO2
    rw [Subgroup.mem_inf, Subgroup.mem_comap]
    simp only [k.2, true_and]
    unfold pCoreOf
    exact (Subgroup.mem_map_iff_mem Kb.subtype_injective).symm
  have hZ : IsTwoClosed ((CFSG.Open.pCore 2 ↥Kb).comap φ) := by
    rw [hZeq]
    exact isTwoClosed_subgroupOf (preO2_le K Y) (ten_two hT le_top hK')
  have hker := isSolvable_ker_of_isTwoClosed φ hZ
  have hSylK : IsSylowIn 2 T K := B6.isSylowTwoOf_mono hT hTK le_top
  have hSylS : IsSylowIn 2 (T.subgroupOf K) ⊤ := by
    have := (isSylowIn_subgroupOf_iff (P := T) (K := K) (H := K) hTK le_rfl).mpr hSylK
    rwa [Subgroup.subgroupOf_self] at this
  refine ⟨?_, isTwoClosed_solvableRadical φ hφ hZ h2, ?_⟩
  ·
    rw [pCore_two_quotient_eq_top_iff]
    intro x
    have hTN : T ≤ Subgroup.normalizer ((K ⊓ X : Subgroup G) : Set G) :=
      hTK.trans (le_normalizer_inf_of_le_normalizer hKX)
    have hx : (x : G) ∈ (↑((K ⊓ X) ⊔ T) : Set G) := by
      rw [← hK1]
      exact x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (K ⊓ X) T hTN] at hx
    obtain ⟨a, ha, t, ht, hat⟩ := hx
    have hKbX : (K ⊓ X).map π ≤ Kb := Subgroup.map_mono inf_le_left
    let ι : ↥((K ⊓ X).map π) →* ↥Kb := Subgroup.inclusion hKbX
    have hιnormal : ι.range.Normal := by
      refine ⟨?_⟩
      rintro _ ⟨⟨_, ⟨a', ha', rfl⟩⟩, rfl⟩ q
      obtain ⟨k, rfl⟩ := hφ q
      have hka : (k : G) * a' * (k : G)⁻¹ ∈ K ⊓ X :=
        ⟨K.mul_mem (K.mul_mem k.2 ha'.1) (K.inv_mem k.2),
          Subgroup.Normal.conj_mem inferInstance a' ha'.2 k⟩
      refine ⟨⟨π ((k : G) * a' * (k : G)⁻¹), Subgroup.mem_map_of_mem π hka⟩, ?_⟩
      apply Subtype.ext
      simp [ι, φ, map_mul, map_inv]
      rfl
    have hιO := le_oInftyE_of_injective ι (Subgroup.inclusion_injective hKbX) h1
    have hN₀O : (K ⊓ X).subgroupOf K ≤ oInftyE ↥K := by
      intro n hn
      rw [oInftyE_eq_comap φ hφ hker, Subgroup.mem_comap]
      refine hιO ⟨⟨π (n : G), Subgroup.mem_map_of_mem π hn⟩, ?_⟩
      rfl
    have hxO : x ∈ oInftyE ↥K ⊔ T.subgroupOf K := by
      have e : x = (⟨a, ha.1⟩ : ↥K) * ⟨t, hTK ht⟩ := by
        apply Subtype.ext
        exact hat.symm
      rw [e]
      exact Subgroup.mul_mem_sup (hN₀O ha) ht
    exact exists_pow_mem_of_mem_sup hSylS.isPGroup (fun s _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top s) hxO
  ·
    refine twoResidual_eq_perfectCore_of_surjective φ hφ hSylS ?_ h3
    intro M hSM hMk
    set M' : Subgroup G := M.map K.subtype with hM'
    have hM'K : M' ≤ K := Subgroup.map_subtype_le M
    have hTM' : T ≤ M' := fun t ht => ⟨⟨t, hTK ht⟩, hSM ht, rfl⟩
    have hKM : K ≤ M' ⊔ Y := by
      intro j hj
      have hjt : (⟨j, hj⟩ : ↥K) ∈ (↑(M ⊔ φ.ker) : Set ↥K) := by
        rw [hMk]
        exact Subgroup.mem_top _
      rw [Subgroup.coe_mul_of_left_le_normalizer_right M φ.ker (fun x _ => by
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact Subgroup.mem_top x)] at hjt
      obtain ⟨m, hm, k, hk, hmk⟩ := hjt
      have hjmk : j = (m : G) * (k : G) := congrArg Subtype.val hmk.symm
      rw [hjmk]
      exact Subgroup.mul_mem_sup ⟨m, hm, rfl⟩ (hkerY k hk)
    have hEqM : X ⊔ T = M' ⊔ Y := by
      refine le_antisymm ?_ ?_
      · rw [hEq]
        exact sup_le hKM le_sup_right
      · exact sup_le (hM'K.trans hKle) (hYX.trans le_sup_left)
    have hMK : M' = K := hmin M' (hM'K.trans hKle) hTM' hEqM hM'K
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : (x : G) ∈ M' := by
      rw [hMK]
      exact x.2
    obtain ⟨m, hm, hmx⟩ := hx
    have : m = x := Subtype.ext hmx
    exact this ▸ hm

end Main

end E1

end CFSG.Quasithin
