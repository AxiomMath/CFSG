module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitGL
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16c167_seven_normalizer_trivial {Y : Type} [CommGroup Y] [Finite Y]
    (hY : Nat.card Y = 8) (hsq : ∀ y : Y, y * y = 1) {l x : MulAut Y} (hl : l ^ 7 = 1)
    (hne : l ≠ 1) (hx : x * x = 1) (hxl : ∃ a : ℕ, x * l * x⁻¹ = l ^ a) : x = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨φ⟩ := CFSG.OddStandard.ChengHeld.GL32Inv.mulAut_mulEquiv_GL3 hY hsq
  obtain ⟨a, ha⟩ := hxl
  have ho : orderOf l = 7 := orderOf_eq_prime hl hne
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hconj : ∀ g ∈ Subgroup.zpowers l, x * g * x⁻¹ ∈ Subgroup.zpowers l := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have h1 : x * l ^ k * x⁻¹ = (x * l * x⁻¹) ^ k := (conj_zpow).symm
    rw [h1, ha, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers l) _
  let P' : Subgroup (GL (Fin 3) (ZMod 2)) := (Subgroup.zpowers l).map φ.toMonoidHom
  have hP' : Nat.card P' = 7 := by
    rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, Nat.card_zpowers, ho]
  have hN := CFSG.ComponentClassification.GMS78.card_normalizer_eq_of_card_eq_seven_GL32 hP'
  have hx_norm : φ x ∈ Subgroup.normalizer (P' : Set (GL (Fin 3) (ZMod 2))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    obtain ⟨g', rfl⟩ := φ.surjective h'
    have key : φ x * φ g' * (φ x)⁻¹ = φ (x * g' * x⁻¹) := by simp [map_mul, map_inv]
    rw [key]
    change φ g' ∈ (Subgroup.zpowers l).map φ.toMonoidHom ↔
      φ (x * g' * x⁻¹) ∈ (Subgroup.zpowers l).map φ.toMonoidHom
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
    refine ⟨hconj g', fun hg => ?_⟩
    have := hconj _ hg
    rwa [hxinv, show x * (x * g' * x) * x = g' by
      calc x * (x * g' * x) * x = (x * x) * g' * (x * x) := by group
        _ = g' := by rw [hx]; group] at this
  have h21 : orderOf (⟨φ x, hx_norm⟩ : Subgroup.normalizer (P' : Set (GL (Fin 3) (ZMod 2)))) ∣ 21 :=
    hN ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h21
  have h2 : orderOf (φ x) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← map_mul, hx, map_one])
  have h1 : orderOf (φ x) = 1 := by
    have := Nat.dvd_gcd h2 h21
    exact Nat.dvd_one.1 (by simpa using this)
  exact φ.injective (by rw [orderOf_eq_one_iff.1 h1, map_one])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
