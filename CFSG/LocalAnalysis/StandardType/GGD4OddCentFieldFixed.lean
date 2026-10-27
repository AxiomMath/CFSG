module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldBridge
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldModelC

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.Bal207.D4Graph (isoAdj)

section FixedTransport

theorem gdf_fixed_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (f : MulAut X) :
    ggAutFixedSubgroup (MulAut.congr e f) = (ggAutFixedSubgroup f).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    rw [mem_ggAutFixedSubgroup] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_ggAutFixedSubgroup]
    have h := congrArg e.symm hy
    simpa [MulAut.congr_apply] using h
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ggAutFixedSubgroup] at hx ⊢
    simp [MulAut.congr_apply, hx]

theorem gdf_orderOf_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (f : MulAut X) :
    orderOf (MulAut.congr e f) = orderOf f :=
  MulEquiv.orderOf_eq (MulAut.congr e) f

end FixedTransport

section Fixed


theorem d4Recipe_fieldAut_centralizer {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {f : MulAut (D4Recipe K)} (hf : f ∈ D4FieldSet K)
    (hord : orderOf f = 3) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (n' : ℕ), Nat.card k = 2 ^ n' ∧ n = 3 * n' ∧
      Nonempty (D4Recipe k ≃* ↥(ggAutFixedSubgroup f)) ∧
      ∀ β : MulAut (D4Recipe K), (∀ x ∈ ggAutFixedSubgroup f, β x = x) →
        β ∈ Subgroup.zpowers f := by
  obtain ⟨τ, hτeq⟩ := d4Recipe_congr_isoAdj_of_mem_fieldSet (K := K) hf
  have hordτ : orderOf τ = 3 := by
    rw [← orderOf_entrywiseAdjointAut_D4 τ, ← hτeq]
    exact (gdf_orderOf_congr (isoAdj K) f).trans hord
  obtain ⟨k, hk_field, hk_finite, n', hk_card, hn, ⟨ek⟩, hstab⟩ :=
    d4C_fixed_data (K := K) hK hordτ
  letI : Field k := hk_field
  letI : Finite k := hk_finite
  have heq : ggAutFixedSubgroup (entrywiseAdjointAut Tag.D4 τ) =
      (ggAutFixedSubgroup f).map (isoAdj K).toMonoidHom := by
    rw [← hτeq]
    exact gdf_fixed_congr (isoAdj K) f
  refine ⟨k, hk_field, hk_finite, n', hk_card, hn, ?_, ?_⟩
  · exact ⟨(isoAdj k).trans (ek.trans ((MulEquiv.subgroupCongr heq).trans
      (Subgroup.equivMapOfInjective (ggAutFixedSubgroup f) (isoAdj K).toMonoidHom
        (isoAdj K).injective).symm))⟩
  · intro β hβ
    have hfix : ∀ y ∈ ggAutFixedSubgroup (entrywiseAdjointAut Tag.D4 τ),
        MulAut.congr (isoAdj K) β y = y := by
      intro y hy
      rw [heq] at hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      simp [MulAut.congr_apply, hβ x hx]
    have hmem : MulAut.congr (isoAdj K) β ∈
        Subgroup.zpowers (MulAut.congr (isoAdj K) f) := by
      rw [hτeq]
      exact hstab (MulAut.congr (isoAdj K) β) hfix
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨m, hm⟩ := hmem
    refine ⟨m, ?_⟩
    exact MulEquiv.injective (MulAut.congr (isoAdj K)) (by rw [map_zpow, hm])

end Fixed

end CFSG.StandardType
