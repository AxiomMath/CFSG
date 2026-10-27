module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open Matrix CFSG.Open Subgroup
open CFSG.LieType.Universal.Unitary (SU mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.KFU (D8Mod diagU diagUHom diagU_val det_diagU diagU_pow diagU_one
  diagU_gram)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD torusD_apply longSL longSL_le_SU
  longSL_le_centralizer entry_zero_zero_of_mem_longSL iotaL coe_iotaL blkL coe_torusD)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

omit [Finite F] [CharP F 2] in
theorem diag_commute_longSL {σ : F ≃+* F} (μ : Fˣ) {x : GL (Fin 4) F}
    (hx : x ∈ longSL σ) :
    Commute (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) x := by
  obtain ⟨M, rfl⟩ := hx
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagU_val, coe_iotaL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkL, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

omit [Finite F] [CharP F 2] in
private theorem coe_torusD_one {ω : rootsOfUnity 3 F} :
    ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![((ω : Fˣ) : F), 1, 1, (((ω⁻¹ : rootsOfUnity 3 F) : Fˣ) : F)] := by
  rw [coe_torusD]
  congr 1

theorem dvd_card_longSL (hb : 0 < b) (hF : Nat.card F = (2 ^ b) ^ 2) {p : ℕ}
    (hpq : p ∣ 2 ^ b + 1) :
    p ∣ Nat.card (longSL (unitaryInvolution F 2 b)) := by
  let K := GaloisField 2 b
  obtain ⟨eL⟩ := CFSG.RankThree.PartTwo.Sec21.U4Lines.nonempty_longSL_mulEquiv
    (F := F) hb hF
  have hcardK : Nat.card K = 2 ^ b := GaloisField.card 2 b hb.ne'
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 2) K) = (2 ^ b) * ((2 ^ b) ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 2)
      (by norm_num), hcardK]
    simp [Finset.Icc_self]
  have hcard : Nat.card (longSL (unitaryInvolution F 2 b)) =
      (2 ^ b) * ((2 ^ b) ^ 2 - 1) := by
    calc Nat.card (longSL (unitaryInvolution F 2 b)) =
          Nat.card (CFSG.PGLModel.projSL 2 K) := Nat.card_congr eL.toEquiv
      _ = Nat.card (SpecialLinearGroup (Fin 2) K) :=
          Nat.card_congr (CFSG.RankThree.PartTwo.Sec21.projSLTwoEquivSL K).toEquiv
      _ = (2 ^ b) * ((2 ^ b) ^ 2 - 1) := hcardSL
  rw [hcard]
  have hsq : (2 ^ b) ^ 2 - 1 = ((2 ^ b) - 1) * (2 ^ b + 1) := by
    have h1 : (1 : ℕ) = 1 ^ 2 := by norm_num
    rw [h1, Nat.sq_sub_sq, mul_comm]
    norm_num
  rw [hsq]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hpq (2 ^ b - 1)) (2 ^ b)

omit [Finite F] [CharP F 2] in
theorem diagU_four_mem_SU {σ : F ≃+* F} {μ : Fˣ}
    (hσμ : σ ((μ : Fˣ) : F) * ((μ : Fˣ) : F) = 1) :
    (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) ∈ SU σ 4 := by
  have hσμinv : (σ ((μ : Fˣ) : F))⁻¹ * (((μ : Fˣ) : F)⁻¹) = 1 := by
    rw [← mul_inv, hσμ, inv_one]
  rw [mem_SU]
  refine ⟨?_, ?_⟩
  · rw [det_diagU, Fin.prod_univ_four]
    simp
  · refine diagU_gram σ ?_
    intro i
    fin_cases i <;> simp [hσμ, hσμinv]

omit [Finite F] [CharP F 2] in
theorem orderOf_diagU_four {μ : Fˣ} {p : ℕ} (hp : p.Prime) (hμp : μ ^ p = 1)
    (hμinvp : (μ⁻¹ : Fˣ) ^ p = 1) (hμ1 : μ ≠ 1) :
    orderOf (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) = p := by
  have hdp : (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) ^ p = 1 := by
    calc (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) ^ p =
          diagU ((![μ, μ⁻¹, μ⁻¹, μ] : Fin 4 → Fˣ) ^ p) := diagU_pow _ p
      _ = diagU 1 := by
        congr 1
        funext i
        fin_cases i <;> simp [Pi.pow_apply, hμp, hμinvp]
      _ = 1 := diagU_one
  have hd00 : ((diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 =
      (μ : F) := by
    simp [diagU_val]
  have hd_ne : (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) ≠ 1 := by
    intro h
    have h1 : ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 = 1 := rfl
    rw [h, h1] at hd00
    exact hμ1 (Units.ext hd00.symm)
  have hdvd : orderOf (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr hdp
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hd_ne
  · exact h1

omit [Finite F] [CharP F 2] in
theorem not_mem_longSL_diagU_four {σ : F ≃+* F} {μ : Fˣ} (hμ1 : μ ≠ 1) :
    (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) ∉ longSL σ := by
  have hd00 : ((diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) 0 0 = (μ : F) := by
    simp [diagU_val]
  intro hmem
  have h := entry_zero_zero_of_mem_longSL (σ := σ) hmem
  rw [hd00] at h
  exact hμ1 (Units.ext h)

omit [Finite F] [CharP F 2] in
private theorem diagU_four_mem_centralizer {ω : rootsOfUnity 3 F} (μ : Fˣ) :
    (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F) ∈
      centralizer (zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F)) := by
  have hcomm : Commute (diagU ![μ, μ⁻¹, μ⁻¹, μ] : GL (Fin 4) F)
      (torusD ((ω, 1) : D8Mod 3 F)) := by
    rw [torusD_apply]
    exact (Commute.all _ _).map diagUHom
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (hcomm.zpow_right n).symm

omit [CharP F 2] in
theorem not_mem_zpowers_of_not_mem_longSL {σ : F ≃+* F} {p : ℕ} {d s : GL (Fin 4) F}
    (hdord : orderOf d = p) (hsord : orderOf s = p) (hs_longSL : s ∈ longSL σ)
    (hd_not : d ∉ longSL σ) : s ∉ zpowers d := by
  intro hs
  have hle : zpowers s ≤ zpowers d := Subgroup.zpowers_le.mpr hs
  have hcard_s : Nat.card (zpowers s) = p := by rw [Nat.card_zpowers, hsord]
  have hcard_d : Nat.card (zpowers d) = p := by rw [Nat.card_zpowers, hdord]
  have heq : zpowers s = zpowers d := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard_s, hcard_d]
  have hd_in : d ∈ zpowers s := by
    rw [heq]
    exact Subgroup.mem_zpowers d
  exact hd_not (Subgroup.zpowers_le.mpr hs_longSL hd_in)

theorem two_le_pRank_centralizer_line (hb : 0 < b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ b + 1) :
    2 ≤ Open.pRank p (SU (unitaryInvolution F 2 b) 4 ⊓
      centralizer (zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F))) := by
  let σ : F ≃+* F := unitaryInvolution F 2 b
  let t : GL (Fin 4) F := torusD ((ω, 1) : D8Mod 3 F)
  have ht : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![((ω : Fˣ) : F), 1, 1, (((ω⁻¹ : rootsOfUnity 3 F) : Fˣ) : F)] :=
    coe_torusD_one
  have hdvd : p ∣ (2 ^ b) ^ 2 - 1 := by
    have hsq : (2 ^ b) ^ 2 - 1 = ((2 ^ b) - 1) * (2 ^ b + 1) := by
      have h1 : (1 : ℕ) = 1 ^ 2 := by norm_num
      rw [h1, Nat.sq_sub_sq, mul_comm]
      norm_num
    rw [hsq]
    exact Dvd.dvd.mul_left hpq _
  have hpF : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact hdvd
  obtain ⟨μ, hμ⟩ := @exists_prime_orderOf_dvd_card' (Fˣ) _ _ p ⟨hp⟩ hpF
  have hμpow : μ ^ (2 ^ b + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hμ]; exact hpq)
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hμ
    exact hp.one_lt.ne' hμ.symm
  have hσμ : σ ((μ : Fˣ) : F) * ((μ : Fˣ) : F) = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, ← pow_succ]
    exact congrArg (fun u : Fˣ => (u : F)) hμpow
  have hμp : μ ^ p = 1 := by
    rw [← hμ]
    exact pow_orderOf_eq_one μ
  have hμinvp : (μ⁻¹ : Fˣ) ^ p = 1 := by
    rw [inv_pow, hμp, inv_one]
  let d : GL (Fin 4) F := diagU ![μ, μ⁻¹, μ⁻¹, μ]
  have hd_SU : d ∈ SU σ 4 := diagU_four_mem_SU hσμ
  have hdord : orderOf d = p := orderOf_diagU_four hp hμp hμinvp hμ1
  have hd_not_longSL : d ∉ longSL σ := not_mem_longSL_diagU_four hμ1
  have hd_cent : d ∈ centralizer (zpowers t : Set (GL (Fin 4) F)) :=
    diagU_four_mem_centralizer μ
  have hp_longSL : p ∣ Nat.card (longSL σ) := dvd_card_longSL hb hF hpq
  obtain ⟨s, hsord'⟩ := @exists_prime_orderOf_dvd_card' (longSL σ) _ _ p ⟨hp⟩ hp_longSL
  have hs_longSL : (s : GL (Fin 4) F) ∈ longSL σ := s.2
  have hsord : orderOf (s : GL (Fin 4) F) = p := (Subgroup.orderOf_coe s).trans hsord'
  have hs_SU : (s : GL (Fin 4) F) ∈ SU σ 4 := longSL_le_SU σ hs_longSL
  have hs_cent : (s : GL (Fin 4) F) ∈ centralizer (zpowers t : Set (GL (Fin 4) F)) :=
    longSL_le_centralizer (σ := σ) ht hs_longSL
  have hds : Commute d (s : GL (Fin 4) F) := diag_commute_longSL μ hs_longSL
  have hs_not_zpowers : (s : GL (Fin 4) F) ∉ zpowers d :=
    not_mem_zpowers_of_not_mem_longSL hdord hsord hs_longSL hd_not_longSL
  exact @CFSG.GroupTheory.two_le_pRank_of_commute (GL (Fin 4) F) _ _ p ⟨hp⟩
    (SU σ 4 ⊓ centralizer (zpowers t : Set (GL (Fin 4) F))) d (s : GL (Fin 4) F)
    (Subgroup.mem_inf.mpr ⟨hd_SU, hd_cent⟩) (Subgroup.mem_inf.mpr ⟨hs_SU, hs_cent⟩)
    hdord hsord hds hs_not_zpowers

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
