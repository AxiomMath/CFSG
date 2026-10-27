module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL3
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofRankTwo
import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedProj StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped Matrix

theorem pRank_le_one_of_card_sq_le {S : Type*} [Group S]
    (hS : ∀ B : Subgroup S, CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ^ 2 ≤ 27) :
    CFSG.pRank 3 S ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  have hB' : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨hB.toIsMulCommutative, fun x hx => ?_⟩
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hx⟩
    simpa using congrArg Subtype.val h
  have h27 := hS B hB'
  rw [hr, ← pow_mul] at h27
  by_contra hr1
  have : 3 ^ 4 ≤ 3 ^ (r * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem isElemAbelian_map_subtype {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)}
    {B : Subgroup H} (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    (∀ x ∈ B.map H.subtype, ∀ y ∈ B.map H.subtype, x * y = y * x) ∧
      ∀ x ∈ B.map H.subtype, x ^ 3 = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB.2 x hx, map_one]

theorem pRank_statedSL_three_le_one {K : Type} [Field K] [Finite K] {p e : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ e) (hq : p ^ e % 3 = 2) : CFSG.pRank 3 (StatedSL 3 K) ≤ 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = p ^ e := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K p := charP_of_card_eq_prime_pow hK'
  refine pRank_le_one_of_card_sq_le fun B hB => ?_
  obtain ⟨hcomm, hexp⟩ := isElemAbelian_map_subtype hB
  have : Finite (B.map (StatedSL 3 K).subtype) := inferInstance
  have h := Sec21.Item223CensusResProof.card_sq_le_of_card_mod_two (ι := Fin 3) hK' hq
    (B.map (StatedSL 3 K).subtype) hcomm hexp
  rwa [Fintype.card_fin, Subgroup.card_map_of_injective (StatedSL 3 K).subtype_injective] at h

theorem pRank_statedSU_three_le_one {K : Type} [Field K] {p e : ℕ} (h : UnitaryFieldData p e K)
    (hq : p ^ e % 3 = 1) : CFSG.pRank 3 (StatedSU 3 (p ^ e) K) ≤ 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ^ e % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by have := h.one_le; omega))
    omega
  have h3K : (3 : K) ≠ 0 := Sec4.three_ne_zero_of_card h.prime hp3 h.card
  refine pRank_le_one_of_card_sq_le fun B hB => ?_
  obtain ⟨hcomm, hexp⟩ := isElemAbelian_map_subtype hB
  have : Finite (B.map (StatedSU 3 (p ^ e) K).subtype) := inferInstance
  have hU : ∀ x ∈ B.map (StatedSU 3 (p ^ e) K).subtype,
      ((x : Matrix (Fin 3) (Fin 3) K).map (· ^ (p ^ e)))ᵀ * (x : Matrix (Fin 3) (Fin 3) K) =
        1 := by
    rintro _ ⟨x, -, rfl⟩
    exact ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp x.2).2
  have h2 := Sec21.Item223CensusResProof.card_sq_le_of_unitary_of_mod_one (ι := Fin 3) h3K hq
    (B.map (StatedSU 3 (p ^ e) K).subtype) hcomm hexp hU
  rwa [Fintype.card_fin,
    Subgroup.card_map_of_injective (StatedSU 3 (p ^ e) K).subtype_injective] at h2

theorem statedScalars_subgroupOf_statedSU_eq_bot {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ p ^ e + 1) :
    (StatedScalars (Fin 3) (GaloisField p (2 * e))).subgroupOf
      (StatedSU 3 (p ^ e) (GaloisField p (2 * e))) = ⊥ := by
  have hU := Sec4.unitaryFieldData_galoisField p e he
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hgs
  rw [Subgroup.mem_subgroupOf] at hgs
  obtain ⟨l, hl⟩ := hgs
  have hl' : Matrix.GeneralLinearGroup.scalar (Fin 3) l ∈
      StatedSU 3 (p ^ e) (GaloisField p (2 * e)) := by
    change Matrix.GeneralLinearGroup.scalar (Fin 3) l = g at hl
    rw [hl]
    exact hg
  obtain ⟨hdet, hunit⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hU).mp hl'
  have hl3 : (l : GaloisField p (2 * e)) ^ 3 = 1 := by
    have : (Matrix.scalar (Fin 3) (l : GaloisField p (2 * e))).det = 1 := by simpa using hdet
    simpa [Matrix.det_smul] using this
  have hlq : (l : GaloisField p (2 * e)) ^ (p ^ e + 1) = 1 := by
    have h00 := congrFun (congrFun hunit 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, UnitaryFieldData.bar_apply] at h00
    rw [pow_succ]
    exact h00
  have hpow : ∀ k : ℕ, (l : GaloisField p (2 * e)) ^ k = (l : GaloisField p (2 * e)) ^ (k % 3) :=
    fun k => by
      conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hl3, one_pow, one_mul]
  have hl1 : (l : GaloisField p (2 * e)) = 1 := by
    rw [hpow] at hlq
    rcases (show (p ^ e + 1) % 3 = 1 ∨ (p ^ e + 1) % 3 = 2 by omega) with h | h
    · rw [h, pow_one] at hlq
      exact hlq
    · rw [h] at hlq
      have h32 : (l : GaloisField p (2 * e)) ^ 3 = (l : GaloisField p (2 * e)) ^ 2 * l := by ring
      rw [hl3, hlq, one_mul] at h32
      exact h32.symm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change g = 1
  have hl2 : Matrix.GeneralLinearGroup.scalar (Fin 3) l = g := hl
  rw [← hl2, show l = 1 from Units.ext hl1, map_one]

noncomputable def projSUEquivStatedSU {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ p ^ e + 1) : projSU 3 p e ≃* StatedSU 3 (p ^ e) (GaloisField p (2 * e)) :=
  (Sec4.projSUEquivStatedProj 3 p e).trans
    ((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSU_eq_bot he h3)).trans
      QuotientGroup.quotientBot)

theorem k417RankOneL3_holds : Res417Three.K417RankOneL3 := by
  intro p e _ hp3 he hq
  have hSL : ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ e →
      CFSG.pRank 3 (StatedSL 3 K) ≤ 1 := fun K _ _ hK => pRank_statedSL_three_le_one hK hq
  refine ⟨?_, hSL⟩
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have h1 : ¬ 3 ∣ p ^ e - 1 := by
    have : 2 ≤ p ^ e := by omega
    omega
  obtain ⟨e₂⟩ := Sec4.nonempty_statedSL_mulEquiv_projSL (K := GaloisField p e) he hK h1
  have : Finite (projSL 3 (GaloisField p e)) := Finite.of_equiv _ e₂.toEquiv
  exact (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num) e₂.symm.toMonoidHom
    e₂.symm.injective).trans (hSL _ hK)

theorem k417RankOneU3_holds : Res417Three.K417RankOneU3 := by
  intro p e hpf _ he hq
  have hp : p.Prime := hpf.out
  have hSU : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ e) ^ 2 →
      CFSG.pRank 3 (StatedSU 3 (p ^ e) K) ≤ 1 := fun K _ _ hK =>
    pRank_statedSU_three_le_one ⟨hp, he, by rw [hK, ← pow_mul, mul_comm]⟩ hq
  refine ⟨?_, hSU⟩
  have h1 : ¬ 3 ∣ p ^ e + 1 := by omega
  have e₂ := projSUEquivStatedSU he h1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have : Finite (projSU 3 p e) := Finite.of_equiv _ e₂.symm.toEquiv
  exact (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num) e₂.toMonoidHom
    e₂.injective).trans (hSU _ hK)

end CFSG.RankThree.PartTwo.Sec4.Res417Four
