module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD2

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.GH74.Uniqueness.Bender

variable {k : Type} [Field k] [CharP k 2]

theorem dihedral_or_large [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {H : Subgroup (antiSp k)} {v w : Fin 4 → k}
    (hvw : spBil v w = 1) (hHle : H ≤ fixPerp v w) (h1 : trv v 1 ∈ H) {b₀ : k} (hb₀ : b₀ ≠ 0)
    (hb₀L : trv w b₀ ∈ H) :
    4 ≤ Nat.card (Lam H v) ∨
      (∃ z : ℕ, 3 ≤ z ∧ Odd z ∧ Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      Nat.card H = 6 := by
  classical
  have hK := benderType_psl2 (k := k) hn hk
  have hρ := rhoP_injective (k := k) hvw
  set J := (H.subgroupOf (fixPerp v w)).map (rhoP hvw) with hJdef
  let eH : H ≃* J := (Subgroup.subgroupOfEquivOfLe hHle).symm.trans
    ((H.subgroupOf (fixPerp v w)).equivMapOfInjective (rhoP hvw) hρ)
  have hcard : Nat.card H = Nat.card J := Nat.card_congr eH.toEquiv
  have hg : trv v 1 * trv w b₀ ∈ H := H.mul_mem h1 hb₀L
  have htr : Matrix.trace (glMat ((trv v 1 * trv w b₀ : antiSp k) : GL (Fin 4) k)) = b₀ := by
    rw [trace_trv_mul_trv, hvw]
    ring
  have hnot2 : ∀ j : ℕ, (trv v 1 * trv w b₀) ^ 2 ^ j ≠ 1 := by
    intro j hj
    have := trace_eq_zero_of_pow_two_pow hj
    rw [htr] at this
    exact hb₀ this
  have hnotP : ¬ IsPGroup 2 H := by
    intro hP
    obtain ⟨j, hj⟩ := hP ⟨_, hg⟩
    exact hnot2 j (by simpa using congrArg Subtype.val hj)
  have hv : v ≠ 0 := ne_zero_of_bil_eq_one hvw
  have heven : Even (Nat.card H) := by
    have htv : (⟨trv v 1, h1⟩ : H) ≠ 1 := fun h =>
      (isTransvection_trv hv one_ne_zero).1 (congrArg Subtype.val h)
    have ho : orderOf (⟨trv v 1, h1⟩ : H) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simp [sq, trv_mul_self])) htv
    exact even_iff_two_dvd.mpr (ho ▸ orderOf_dvd_natCard _)
  rcases hK.linear_subgroup_cases J with hP | ⟨-, -, hodd⟩ | ⟨z, hz3, hz, hcz, ⟨φ⟩⟩ | ⟨-, Q, hJQ⟩ |
      ⟨m, hm, -, ⟨φ⟩⟩ | h6
  · exact absurd (hP.of_equiv eH.symm) hnotP
  · rw [← hcard] at hodd
    exact absurd heven (Nat.not_even_iff_odd.mpr hodd)
  · exact Or.inr (Or.inl ⟨z, hz3, hz, hcard ▸ hcz, ⟨eH.trans φ⟩⟩)
  · exfalso
    have key : ∀ x : fixPerp v w, (x : antiSp k) ∈ H → x * x = 1 →
        rhoP hvw x ∈ (Q : Subgroup _) := by
      intro x hxH hx2
      have hxJ : rhoP hvw x ∈ J :=
        Subgroup.mem_map_of_mem (rhoP hvw) (by rw [Subgroup.mem_subgroupOf]; exact hxH)
      have hzp : IsPGroup 2 (Subgroup.zpowers (rhoP hvw x)) :=
        isPGroup_two_zpowers_of_mul_self_eq_one (by rw [← map_mul, hx2, map_one])
      have hle : Subgroup.zpowers (rhoP hvw x) ≤
          borel (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) :=
        Subgroup.zpowers_le.mpr (hJQ hxJ)
      have hmax := Q.is_maximal' (hzp.to_sup_of_normal_right' Q.isPGroup' hle) le_sup_right
      exact (sup_eq_right.mp hmax) (Subgroup.mem_zpowers _)
    set xv : fixPerp v w := ⟨trv v 1, trv_mem_fixPerp_left v w 1⟩
    set xw : fixPerp v w := ⟨trv w b₀, trv_mem_fixPerp_right v w b₀⟩
    have hxv := key xv h1 (Subtype.ext (trv_mul_self v 1))
    have hxw := key xw hb₀L (Subtype.ext (trv_mul_self w b₀))
    have hprod : rhoP hvw (xv * xw) ∈ (Q : Subgroup _) := by
      rw [map_mul]
      exact (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)).mul_mem hxv hxw
    obtain ⟨j, hj⟩ := Q.isPGroup' ⟨_, hprod⟩
    have h2 : rhoP hvw ((xv * xw) ^ 2 ^ j) = rhoP hvw 1 := by
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val hj
    have h3 := congrArg Subtype.val (hρ h2)
    exact hnot2 j (by simpa [xv, xw] using h3)
  · left
    have hB : BenderType H m 1 1 := BenderType.linear m hm (eH.trans φ)
    have hX : rootGrp H v ≤ H := rootGrp_le v
    rw [card_lam_eq hvw hHle le_rfl hX one_ne_zero h1 hB]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · exact Or.inr (Or.inr (hcard ▸ h6))

theorem fixPerp_eq {v w : Fin 4 → k} (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0)
    (hvw : spBil v w = 1) : fixPerp v w = fixPerp (Pi.single 0 1 : Fin 4 → k) (Pi.single 3 1) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hvw' : v 0 * w 3 + v 3 * w 0 = 1 := by
    rw [bil_apply, hv1, hv2, hw1, hw2] at hvw
    linear_combination hvw
  have key : ∀ z : Fin 4 → k, (spBil z v = 0 ∧ spBil z w = 0) ↔
      (spBil z (Pi.single 0 1) = 0 ∧ spBil z (Pi.single 3 1) = 0) := by
    intro z
    rw [bil_single, bil_single, bil_apply, bil_apply, hv1, hv2, hw1, hw2]
    simp only [Fin.rev, Fin.isValue, mul_zero, add_zero]
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨?_, ?_⟩
      · change z 3 = 0
        linear_combination w 3 * ha - v 3 * hb - z 3 * hvw' + (z 3 * v 3 * w 0) * h2
      · change z 0 = 0
        linear_combination v 0 * hb - w 0 * ha - z 0 * hvw' + (z 0 * v 3 * w 0) * h2
    · rintro ⟨ha, hb⟩
      change z 3 = 0 at ha
      change z 0 = 0 at hb
      rw [ha, hb]
      simp
  ext g
  simp only [mem_fixPerp]
  exact ⟨fun h z h0 h3 => h z ((key z).mpr ⟨h0, h3⟩).1 ((key z).mpr ⟨h0, h3⟩).2,
    fun h z hv hw => h z ((key z).mp ⟨hv, hw⟩).1 ((key z).mp ⟨hv, hw⟩).2⟩

theorem secGrp_dihedral_or_large [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n)
    {Z : Set (Fin 4 → k)} (hZ : ∀ z ∈ Z, z 2 = 0) {z₁ z₂ : Fin 4 → k} (hz₁ : z₁ ∈ Z) (hz₂ : z₂ ∈ Z)
    (hc : spBil (proj z₁) (proj z₂) ≠ 0) :
    4 ≤ Nat.card (Lam (secGrp Z) (proj z₁)) ∨
      (∃ z : ℕ, 3 ≤ z ∧ Odd z ∧ Nat.card (secGrp Z) = 2 * z ∧
        Nonempty (secGrp Z ≃* DihedralGroup z)) ∨
      Nat.card (secGrp Z) = 6 := by
  set c := spBil (proj z₁) (proj z₂) with hcdef
  set w := c⁻¹ • proj z₂ with hwdef
  have hvw : spBil (proj z₁) w = 1 := by
    rw [hwdef, LinearMap.map_smul, smul_eq_mul, ← hcdef, inv_mul_cancel₀ hc]
  have hle : secGrp Z ≤ fixPerp (proj z₁) w := by
    rw [fixPerp_eq (by simp [proj]) (by simp [proj]) (by simp [hwdef, proj]) (by simp [hwdef, proj])
      hvw]
    exact secGrp_le_fixPerp Z
  have hw : trv w (c ^ 2) ∈ secGrp Z := by
    have h := trv_proj_mem_secGrp hZ hz₂
    rwa [show proj z₂ = c • w by rw [hwdef, smul_smul, mul_inv_cancel₀ hc, one_smul], trv_smul,
      mul_one] at h
  exact dihedral_or_large hn hk hvw hle (trv_proj_mem_secGrp hZ hz₁) (pow_ne_zero 2 hc) hw

end CFSG.Quasithin.Ch3E213M.G41.Big
