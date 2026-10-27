module

public import CFSG.Sporadic.J4.QT2LocCntProof

public section

namespace CFSG.Quasithin.J4Seven

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open scoped Classical

theorem Dlt_orbit {ℓ : ℕ} {v : Row} (hv : v ∈ Dlt ℓ) : ∃ g : J, g • w₀ = v := by
  obtain ⟨h, -, rfl⟩ := hv
  exact ⟨h * (uElt ℓ)⁻¹, by rw [mul_smul]; rfl⟩

theorem subSizes_getD_inj : ∀ m ℓ : Fin 7,
    [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336].getD m.val 0 =
      [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336].getD ℓ.val 0 → m = ℓ := by
  decide

theorem ncard_Dlt_eq_sum (_hF : J4Facts) (ℓ : Fin 7) :
    (Dlt ℓ.val).ncard =
      ∑ m ∈ Finset.univ.filter (fun m : Fin 7 => Dlt m.val = Dlt ℓ.val), subSizesF m := by
  have hS : Finset.univ.filter (fun m : Fin 7 => Dlt m.val = Dlt ℓ.val) = {ℓ} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have e := congrArg Set.ncard h
      rw [Dlt_ncard m.isLt, Dlt_ncard ℓ.isLt] at e
      exact subSizes_getD_inj m ℓ e
    · rintro rfl
      rfl
  rw [hS, Finset.sum_singleton, Dlt_ncard ℓ.isLt]
  fin_cases ℓ <;> rfl

theorem seven_dvd_sum (S : Finset (Fin 7)) (h0 : (0 : Fin 7) ∉ S) (h5 : (5 : Fin 7) ∉ S) :
    7 ∣ ∑ m ∈ S, subSizesF m := by
  apply Finset.dvd_sum
  intro m hm
  fin_cases m
  · exact absurd hm h0
  · decide
  · decide
  · decide
  · decide
  · exact absurd hm h5
  · decide

theorem Dlt_zero_subset (hM : MatFacts) : Dlt 0 ⊆ {w₀} := by
  rintro v ⟨h, hh, rfl⟩
  have : rep 0 = w₀ := by simp [rep, uElt, repPaths, pathElt]
  rw [this, smul_root_of_mem_Hj hM hh]
  exact Set.mem_singleton _

theorem fixed_seven_subset (hF : J4Facts) {y : J} (hyH : y ∈ Hj)
    (hy7 : orderOf y = 7) {p : Row} (hp : ∃ g : J, g • w₀ = p) (hfix : y • p = p) :
    p = w₀ ∨ p ∈ Dlt 5 := by
  have hM := hF.mat
  obtain ⟨g, rfl⟩ := hp
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF g
  have hpD : (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') • w₀ ∈ Dlt ℓ :=
    ⟨h, hh, by rw [mul_smul, mul_smul, smul_root_of_mem_Hj hM hh']; rfl⟩
  set p := (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') • w₀ with hpdef
  set ℓF : Fin 7 := ⟨ℓ, hℓ⟩
  have horb : MulAction.orbit ↥Hj p = Dlt ℓ := by
    obtain ⟨h1, hh1, hq⟩ := hpD
    ext v
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      refine ⟨k * h1, Hj.mul_mem hk hh1, ?_⟩
      show k • p = (k * h1) • rep ℓ
      rw [hq, mul_smul]
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k * h1⁻¹, Hj.mul_mem hk (Hj.inv_mem hh1)⟩, ?_⟩
      show (k * h1⁻¹) • p = k • rep ℓ
      rw [hq, mul_smul, inv_smul_smul]
  have hstab : 7 ∣ Nat.card ↥(MulAction.stabilizer ↥Hj p) := by
    have hy' : (⟨y, hyH⟩ : ↥Hj) ∈ MulAction.stabilizer ↥Hj p := hfix
    have : orderOf (⟨⟨y, hyH⟩, hy'⟩ : ↥(MulAction.stabilizer ↥Hj p)) = 7 := by
      rw [← hy7, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rw [← this]
    exact orderOf_dvd_natCard _
  have h49 : ¬ 49 ∣ Nat.card ↥Hj := by
    rw [card_Hj hF]
    decide
  have hnd : ¬ 7 ∣ (Dlt ℓ).ncard := by
    intro hd
    apply h49
    have hoc := Subgroup.card_mul_index (MulAction.stabilizer ↥Hj p)
    rw [MulAction.index_stabilizer, horb] at hoc
    rw [← hoc]
    exact Nat.mul_dvd_mul hstab hd
  rw [ncard_Dlt_eq_sum hF ℓF] at hnd
  by_contra! hcon
  apply hnd
  apply seven_dvd_sum
  · intro h0
    have h0' : Dlt 0 = Dlt ℓ := (Finset.mem_filter.1 h0).2
    have : p ∈ Dlt 0 := by rw [h0']; exact hpD
    exact hcon.1 (Dlt_zero_subset hM this)
  · intro h5
    have h5' : Dlt 5 = Dlt ℓ := (Finset.mem_filter.1 h5).2
    have : p ∈ Dlt 5 := by rw [h5']; exact hpD
    exact hcon.2 this

end CFSG.Quasithin.J4Seven
