module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofExt
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharStab
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLines

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof Subgroup

@[expose] def gT : Exp3 := ![1, 0, 0, 1]

variable {L : Type} [Field L]

theorem tup_gT_eq {ζ : Lˣ} (hζ3 : ζ ^ 3 = 1) {q : ℕ} {ε : ℤ}
    (hqε : ((ε * q : ℤ) : ZMod 3) = 1) : tup ζ gT = threeSixTuple q ε (ζ, 1) := by
  obtain ⟨t0, t1, t2, t3⟩ := threeSixTuple_values (L := L) q ε ζ 1
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  refine (fin_D4_eq_iff _ _).2 ⟨?_, ?_, ?_, ?_⟩
  · rw [t0]
    simp [tup, gT, hv1]
  · rw [t1]
    simp [tup, gT]
  · rw [t2]
    simp [tup, gT]
  · rw [t3, one_zpow, mul_one, zpow_eq_pow_val hζ3, hqε]
    simp [tup, gT, hv1]

theorem mem_threeSixTorus_tup_gT
    [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hqε : (q : ZMod 3) = ε)
    {ζ : Lˣ} (hζ3 : ζ ^ 3 = 1) :
    rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈ threeSixTorus L Fr ε := by
  have hεq : ((ε * q : ℤ) : ZMod 3) = 1 := by
    push_cast
    rw [hqε]
    rcases hε with rfl | rfl <;> decide
  have hd : (((q : ℤ) ^ 2 + ε * q + 1 : ℤ) : ZMod 3) = 0 := by
    push_cast
    rw [hqε]
    rcases hε with rfl | rfl <;> decide
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  have h0 : tup ζ gT 0 = ζ := by simp [tup, gT, hv1]
  have h1 : tup ζ gT 1 = 1 := by simp [tup, gT]
  rw [rootDiagUnit_mem_threeSixTorus_iff' Fr hFr hε, h0, h1]
  refine ⟨tup_gT_eq hζ3 hεq, ?_, one_zpow _⟩
  rw [zpow_eq_pow_val hζ3, hd, ZMod.val_zero, pow_zero]

theorem orderOf_rootDiagUnit_tup_gT
    {ζ : Lˣ} (hζ : orderOf ζ = 3) : orderOf (rootDiagUnit TwistTag.D4.tag (tup ζ gT)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  refine orderOf_eq_prime ?_ ?_
  · rw [← rootDiagUnit_pow', tup_pow_three hζ3, rootDiagUnit_one]
  · intro h
    rw [← rootDiagUnit_one] at h
    exact tup_ne_one hζ (by decide) (CFSG.LieType.Chevalley.rootDiagUnit_injective h)

abbrev rootVecT (k : Fin 24) : Fin TwistTag.D4.tag.rank → ℤ := d4RootVec k

abbrev sigma0T : List (Fin TwistTag.D4.tag.rank → ℤ) := d4Sigma0List

abbrev vT : WeylGroup Tag.D4 := (coxeterSystem Tag.D4).wordProd [0, 2, 1]

theorem survCheck_one : ∀ β ∈ sigma0T, ∃ k : Fin 24, wordVec [0, 2, 1] β = rootVecT k ∧
    ∑ j, ((rootVecT k j : ℤ) : ZMod 3) * gT j = 0 := by decide

theorem survCheck_two : ∀ k : Fin 24, ∑ j, ((rootVecT k j : ℤ) : ZMod 3) * gT j = 0 →
    ∃ β ∈ sigma0T, wordVec [0, 2, 1] β = rootVecT k := by decide

theorem survivingRoots_tup_gT {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    (fun α => vT • α) '' d4A2Sigma = survivingRoots (tup ζ gT) := by
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hsm : ∀ β : Fin Tag.D4.rank → ℤ, vT • β = wordVec [0, 2, 1] β := fun β =>
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.wordProd_smul [0, 2, 1] β
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨k, hk, hsum⟩ := survCheck_one β ((mem_d4A2Sigma_iff β).1 hβ)
    have hv : vT • β = rootVecT k := (hsm β).trans hk
    refine ⟨(congrArg (IsRoot TwistTag.D4.tag) hv).mpr (isRoot_d4RootVec k), ?_⟩
    refine (congrArg (rootChar (tup ζ gT)) hv).trans ((rootChar_tup hζ3 gT (rootVecT k)).trans ?_)
    rw [hsum, ZMod.val_zero, pow_zero]
  · rintro ⟨hα, h1⟩
    obtain ⟨k, rfl⟩ := isRoot_iff_exists_d4RootVec.1 hα
    have h0 : ∑ j, ((rootVecT k j : ℤ) : ZMod 3) * gT j = 0 := by
      apply pow_val_inj hζ (b := 0)
      rw [ZMod.val_zero, pow_zero]
      exact (rootChar_tup hζ3 gT (rootVecT k)).symm.trans h1
    obtain ⟨β, hβ, hβk⟩ := survCheck_two k h0
    exact ⟨β, (mem_d4A2Sigma_iff β).2 hβ, (hsm β).trans hβk⟩

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
