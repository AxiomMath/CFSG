module

public import CFSG.Quasithin.Background.D2Basic
import CFSG.Quasithin.Background.D2Coprime
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenModA

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem omSevenB_inv_commute {g z : MulAut W} (h : g * z = z * g) :
    g⁻¹ * z = z * g⁻¹ :=
  show g⁻¹ * z = z * g⁻¹ from (show Commute g z from h).inv_left

private theorem omSevenB_map_fixV_inf_commSub {z w g h : MulAut W}
    (hwz : w * z = z * w) (hconj : w * g * w⁻¹ = h) :
    (fixV (zpowers g) ⊓ commSub ⊤ (zpowers z)).map (w : W →* W) =
      fixV (zpowers h) ⊓ commSub ⊤ (zpowers z) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_inf] at hv ⊢
    refine ⟨?_, apply_mem_commSub_of_commute hwz hv.2⟩
    rw [mem_fixV_zpowers_iff]
    calc h (w v) = (w * g * w⁻¹) (w v) := by rw [hconj]
      _ = w (g (w⁻¹ (w v))) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = w (g v) := by rw [MulAut.inv_apply_self]
      _ = w v := by rw [mem_fixV_zpowers_iff.mp hv.1]
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    rw [Subgroup.mem_map]
    refine ⟨w⁻¹ y, ?_, by
      rw [MulAut.inv_apply]
      exact MulEquiv.apply_symm_apply w y⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [mem_fixV_zpowers_iff]
      have hg_eq : g = w⁻¹ * h * w := by
        rw [← hconj]
        group
      rw [hg_eq, MulAut.mul_apply, MulAut.mul_apply]
      rw [show w (w⁻¹ y) = y by
        rw [MulAut.inv_apply]
        exact MulEquiv.apply_symm_apply w y]
      rw [mem_fixV_zpowers_iff.mp hy.1]
    · exact apply_mem_commSub_of_commute (omSevenB_inv_commute hwz) hy.2

theorem rk_commSub_le_three_mul_of_conjLift (hW : ∀ w : W, w ^ 2 = 1) {z a c u : MulAut W}
    (hz : orderOf z = 3) (ha : a ^ 3 = 1) (hza : a * z = z * a)
    (hca : c * a * c⁻¹ = a * z) (hcz : c * z = z * c)
    (huz : u * z = z * u) (hua : u * a * u⁻¹ = a⁻¹) :
    rk ↥(commSub ⊤ (zpowers z)) ≤ 3 * rk ↥(commSub (commSub ⊤ (zpowers z)) (zpowers u)) := by
  classical
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  let U : Subgroup W := commSub ⊤ (zpowers z)
  let g : ℕ → MulAut W := fun i => a * z ^ i
  let F : ℕ → Subgroup W := fun i => fixV (zpowers (g i)) ⊓ U
  let N : ℕ → W → W := fun i v => v * (g i) v * ((g i) ^ 2) v
  have hg0 : g 0 = a := by
    change a * z ^ 0 = a
    simp
  have hg1 : g 1 = a * z := by
    change a * z ^ 1 = a * z
    simp
  have hg2 : g 2 = a * z ^ 2 := rfl
  have hgz : ∀ i, g i * z = z * g i := by
    intro i
    change (a * z ^ i) * z = z * (a * z ^ i)
    calc (a * z ^ i) * z = a * (z ^ i * z) := by rw [mul_assoc]
      _ = a * z ^ (i + 1) := by rw [pow_succ]
      _ = a * (z * z ^ i) := by rw [pow_succ']
      _ = (a * z) * z ^ i := by rw [mul_assoc]
      _ = (z * a) * z ^ i := by rw [← hza]
      _ = z * (a * z ^ i) := by rw [mul_assoc]
  have hFmem : ∀ i (v : W), v ∈ F i ↔ v ∈ U ∧ (g i) v = v := by
    intro i v
    change v ∈ fixV (zpowers (g i)) ⊓ U ↔ v ∈ U ∧ (g i) v = v
    rw [Subgroup.mem_inf, mem_fixV_zpowers_iff]
    exact and_comm
  have hgU : ∀ i, ∀ w ∈ U, (g i) w ∈ U := by
    intro i w hw
    exact apply_mem_commSub_of_commute (hgz i) hw
  have hcomm_az : Commute a z := hza
  have hg3 : ∀ i, (g i) ^ 3 = 1 := by
    intro i
    calc (g i) ^ 3 = a ^ 3 * (z ^ i) ^ 3 := (hcomm_az.pow_right i).mul_pow 3
      _ = 1 := by
        rw [ha, one_mul, ← pow_mul, Nat.mul_comm, pow_mul, hz3, one_pow]
  have hzsq : (z ^ 2) ^ 2 = z := by
    rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num,
      show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hz3, one_mul, pow_one]
  have hg1sq : (a * z) ^ 2 = a ^ 2 * z ^ 2 := hcomm_az.mul_pow 2
  have hg2sq : (a * z ^ 2) ^ 2 = a ^ 2 * z := by
    rw [(hcomm_az.pow_right 2).mul_pow 2, hzsq]
  have hNmem : ∀ i v, v ∈ U → N i v ∈ U := by
    intro i v hv
    change v * (g i) v * ((g i) ^ 2) v ∈ U
    rw [pow_two, MulAut.mul_apply]
    exact U.mul_mem (U.mul_mem hv (hgU i v hv)) (hgU i ((g i) v) (hgU i v hv))
  have hNfix : ∀ i v, v ∈ U → (g i) (N i v) = N i v := by
    intro i v _
    change (g i) (v * (g i) v * ((g i) ^ 2) v) = v * (g i) v * ((g i) ^ 2) v
    rw [map_mul, map_mul]
    rw [show (g i) ((g i) v) = ((g i) ^ 2) v by
      rw [← MulAut.mul_apply, ← pow_two]]
    rw [show (g i) (((g i) ^ 2) v) = v by
      rw [← MulAut.mul_apply, ← pow_succ', hg3 i, MulAut.one_apply]]
    ac_rfl
  have hNprod : ∀ v ∈ U, N 0 v * N 1 v * N 2 v = v := by
    intro v hv
    have hv' : v ∈ commSub ⊤ (zpowers z) := hv
    have hnorm : v * z v * (z ^ 2) v = 1 :=
      norm_apply_eq_one_of_mem_commSub hz3 hv'
    change (v * (g 0) v * ((g 0) ^ 2) v) * (v * (g 1) v * ((g 1) ^ 2) v) *
        (v * (g 2) v * ((g 2) ^ 2) v) = v
    rw [hg0, hg1, hg2]
    rw [show (a * z) ^ 2 = a ^ 2 * z ^ 2 from hg1sq,
        show (a * z ^ 2) ^ 2 = a ^ 2 * z from hg2sq]
    simp only [MulAut.mul_apply]
    have hv3 : v * v * v = v := by
      rw [show v * v = 1 by rw [← pow_two]; exact hW v, one_mul]
    have keya : a v * a (z v) * a ((z ^ 2) v) = a (v * z v * (z ^ 2) v) := by
      rw [← map_mul, ← map_mul]
    have keya2 : (a ^ 2) v * (a ^ 2) ((z ^ 2) v) * (a ^ 2) (z v) =
        (a ^ 2) (v * z v * (z ^ 2) v) := by
      rw [← map_mul, ← map_mul]
      congr 1
      ac_rfl
    calc (v * a v * (a ^ 2) v) * (v * a (z v) * (a ^ 2) ((z ^ 2) v)) *
            (v * a ((z ^ 2) v) * (a ^ 2) (z v))
        = (v * v * v) * (a v * a (z v) * a ((z ^ 2) v)) *
            ((a ^ 2) v * (a ^ 2) ((z ^ 2) v) * (a ^ 2) (z v)) := by ac_rfl
      _ = v * (a v * a (z v) * a ((z ^ 2) v)) *
            ((a ^ 2) v * (a ^ 2) ((z ^ 2) v) * (a ^ 2) (z v)) := by rw [hv3]
      _ = v * a (v * z v * (z ^ 2) v) * (a ^ 2) (v * z v * (z ^ 2) v) := by
            rw [keya, keya2]
      _ = v * 1 * 1 := by rw [hnorm, map_one a, map_one (a ^ 2)]
      _ = v := by rw [mul_one, mul_one]
  have hconjc0 : c * (g 0) * c⁻¹ = g 1 := by
    rw [hg0, hg1]
    exact hca
  have hconjc1 : c * (g 1) * c⁻¹ = g 2 := by
    rw [hg1, hg2]
    calc c * (a * z) * c⁻¹ = (c * a * c⁻¹) * (c * z * c⁻¹) := by group
      _ = (a * z) * z := by
            rw [hca, show c * z * c⁻¹ = z by rw [hcz, mul_assoc, mul_inv_cancel, mul_one]]
      _ = a * z ^ 2 := by rw [pow_two, mul_assoc]
  have hconju1 : u * (g 1) * u⁻¹ = (g 2)⁻¹ := by
    rw [hg1, hg2]
    have hainv : a⁻¹ = a ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, ha]
    have hz2inv : (z ^ 2)⁻¹ = z := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ, show (2 : ℕ) + 1 = 3 by norm_num, hz3]
    have hg2inv : (a * z ^ 2)⁻¹ = a ^ 2 * z := by
      rw [mul_inv_rev, hz2inv, hainv]
      exact (hcomm_az.pow_left 2).symm
    calc u * (a * z) * u⁻¹ = (u * a * u⁻¹) * (u * z * u⁻¹) := by group
      _ = a⁻¹ * z := by
            rw [hua, show u * z * u⁻¹ = z by rw [huz, mul_assoc, mul_inv_cancel, mul_one]]
      _ = a ^ 2 * z := by rw [hainv]
      _ = (a * z ^ 2)⁻¹ := hg2inv.symm
  have hmapc0 : (F 0).map (c : W →* W) = F 1 :=
    omSevenB_map_fixV_inf_commSub hcz hconjc0
  have hmapc1 : (F 1).map (c : W →* W) = F 2 :=
    omSevenB_map_fixV_inf_commSub hcz hconjc1
  have hmapu1 : (F 1).map (u : W →* W) = F 2 := by
    have h := omSevenB_map_fixV_inf_commSub huz hconju1
    rwa [Subgroup.zpowers_inv] at h
  have hF1F2 : F 1 ⊓ F 2 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨hu1, hg1v⟩ := (hFmem 1 v).mp hv1
    obtain ⟨-, hg2v⟩ := (hFmem 2 v).mp hv2
    rw [hg1] at hg1v
    rw [hg2] at hg2v
    have hzz : z v = (z ^ 2) v := by
      apply a.injective
      calc a (z v) = (a * z) v := rfl
        _ = v := hg1v
        _ = (a * z ^ 2) v := hg2v.symm
        _ = a ((z ^ 2) v) := rfl
    have hzeq : z v = v := by
      have h2 : v = z v := by
        have h4 := congrArg z.symm hzz
        simp only [pow_two, MulAut.mul_apply, MulEquiv.symm_apply_apply] at h4
        exact h4
      exact h2.symm
    have hvbot : v ∈ fixV (zpowers z) ⊓ commSub ⊤ (zpowers z) :=
      ⟨mem_fixV_zpowers_iff.mpr hzeq, hu1⟩
    rw [fixV_inf_commSub_zpowers_eq_bot hW hz3, Subgroup.mem_bot] at hvbot
    exact hvbot
  have hker : F 1 ⊓ (commHom u).ker = ⊥ := by
    rw [ker_commHom, Subgroup.eq_bot_iff_forall]
    intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hv1, hvu⟩ := hv
    have hu : u v = v := mem_fixV_zpowers_iff.mp hvu
    have hv2 : v ∈ F 2 := by
      have hmem : u v ∈ (F 1).map (u : W →* W) :=
        Subgroup.mem_map_of_mem (u : W →* W) hv1
      rw [hmapu1] at hmem
      rwa [hu] at hmem
    have hvbot : v ∈ F 1 ⊓ F 2 := ⟨hv1, hv2⟩
    rw [hF1F2, Subgroup.mem_bot] at hvbot
    exact hvbot
  have hstep4 : rk ↥(F 1) ≤ rk ↥(commSub U (zpowers u)) := by
    have hmap_le : (F 1).map (commHom u) ≤ commSub U (zpowers u) := by
      rintro y ⟨v, hv, rfl⟩
      refine Subgroup.subset_closure ⟨u, Subgroup.mem_zpowers u, v, ?_, rfl⟩
      exact ((hFmem 1 v).mp hv).1
    have h := rk_map_add_rk_inf_ker (commHom u) (F 1)
    rw [hker, rk_bot, add_zero] at h
    rw [← h]
    exact rk_mono hmap_le
  have hcardc0 : Nat.card ↥(F 0) = Nat.card ↥(F 1) := by
    rw [← hmapc0]
    exact (Subgroup.card_map_of_injective c.injective).symm
  have hrc0 : rk ↥(F 0) = rk ↥(F 1) := by
    unfold rk
    rw [hcardc0]
  have hcardc1 : Nat.card ↥(F 1) = Nat.card ↥(F 2) := by
    rw [← hmapc1]
    exact (Subgroup.card_map_of_injective c.injective).symm
  have hrc2 : rk ↥(F 2) = rk ↥(F 1) := by
    unfold rk
    rw [hcardc1]
  have hUF : U ≤ F 0 ⊔ F 1 ⊔ F 2 := by
    intro v hv
    have hN0 : N 0 v ∈ F 0 := (hFmem 0 (N 0 v)).mpr ⟨hNmem 0 v hv, hNfix 0 v hv⟩
    have hN1 : N 1 v ∈ F 1 := (hFmem 1 (N 1 v)).mpr ⟨hNmem 1 v hv, hNfix 1 v hv⟩
    have hN2 : N 2 v ∈ F 2 := (hFmem 2 (N 2 v)).mpr ⟨hNmem 2 v hv, hNfix 2 v hv⟩
    refine Subgroup.mem_sup.mpr
      ⟨N 0 v * N 1 v, Subgroup.mul_mem_sup hN0 hN1, N 2 v, hN2, hNprod v hv⟩
  have h2 : rk ↥(F 0 ⊔ F 1 ⊔ F 2) ≤ rk ↥(F 0) + rk ↥(F 1) + rk ↥(F 2) := by
    have hA := rk_sup_add_rk_inf (F 0 ⊔ F 1) (F 2)
    have hB := rk_sup_add_rk_inf (F 0) (F 1)
    omega
  have h3 : rk ↥(F 0) + rk ↥(F 1) + rk ↥(F 2) = 3 * rk ↥(F 1) := by
    rw [hrc0, hrc2]
    ring
  calc rk ↥U ≤ rk ↥(F 0 ⊔ F 1 ⊔ F 2) := rk_mono hUF
    _ ≤ rk ↥(F 0) + rk ↥(F 1) + rk ↥(F 2) := h2
    _ = 3 * rk ↥(F 1) := h3
    _ ≤ 3 * rk ↥(commSub U (zpowers u)) := Nat.mul_le_mul_left 3 hstep4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
