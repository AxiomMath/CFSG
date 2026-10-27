module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixTorus
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofLine
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section TupAlg

variable {L : Type} [Field L] {ζ : Lˣ}

theorem tup_zero_eq : tup ζ (0 : Exp3) = 1 := by
  funext i
  simp [tup]

theorem tup_add (hζ3 : ζ ^ 3 = 1) (β γ : Exp3) : tup ζ (β + γ) = tup ζ β * tup ζ γ := by
  funext i
  simp only [tup, Pi.mul_apply, Pi.add_apply]
  exact (pow_val_add hζ3 (β i) (γ i)).symm

theorem tup_neg (hζ3 : ζ ^ 3 = 1) (β : Exp3) : tup ζ (-β) = (tup ζ β)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← tup_add hζ3, neg_add_cancel, tup_zero_eq]

theorem tup_pow_eq (hζ3 : ζ ^ 3 = 1) (β : Exp3) (k : ℕ) : tup ζ β ^ k = tup ζ (k • β) := by
  induction k with
  | zero => rw [pow_zero, zero_smul, tup_zero_eq]
  | succ k ih => rw [pow_succ, ih, succ_nsmul, tup_add hζ3]

theorem pow_val_zpow (hζ3 : ζ ^ 3 = 1) (a : ZMod 3) (z : ℤ) :
    (ζ ^ a.val) ^ z = ζ ^ (a * (z : ZMod 3)).val := by
  rw [← zpow_natCast, ← _root_.zpow_mul, zpow_eq_pow_val hζ3]
  congr 2
  push_cast
  rw [ZMod.natCast_zmod_val]


theorem rootDiagUnit_tup_add (hζ3 : ζ ^ 3 = 1) (β γ : Exp3) :
    rootDiagUnit TwistTag.D4.tag (tup ζ (β + γ)) =
      rootDiagUnit TwistTag.D4.tag (tup ζ β) * rootDiagUnit TwistTag.D4.tag (tup ζ γ) := by
  rw [tup_add hζ3, rootDiagUnit_mul]

theorem rootDiagUnit_tup_neg (hζ3 : ζ ^ 3 = 1) (β : Exp3) :
    rootDiagUnit TwistTag.D4.tag (tup ζ (-β)) = (rootDiagUnit TwistTag.D4.tag (tup ζ β))⁻¹ := by
  rw [tup_neg hζ3]
  exact map_inv (rootDiagUnitHom TwistTag.D4.tag L) _

theorem rootDiagUnit_tup_pow (hζ3 : ζ ^ 3 = 1) (β : Exp3) (k : ℕ) :
    rootDiagUnit TwistTag.D4.tag (tup ζ β) ^ k = rootDiagUnit TwistTag.D4.tag (tup ζ (k • β)) := by
  rw [← tup_pow_eq hζ3, rootDiagUnit_pow']

end TupAlg

section Torus

variable {L : Type} [Field L]

@[expose] def vecV (i j : ZMod 3) : Exp3 := ![i, j, j, i + 2 * j]

theorem mem_threeSixTorus_tup_vec [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hqε : (q : ZMod 3) = ε)
    {ζ : Lˣ} (hζ3 : ζ ^ 3 = 1) (i j : ZMod 3) :
    rootDiagUnit TwistTag.D4.tag (tup ζ (vecV i j)) ∈ threeSixTorus L Fr ε := by
  have hεq : ((ε * q : ℤ) : ZMod 3) = 1 := by
    push_cast
    rw [hqε]
    rcases hε with rfl | rfl <;> decide
  have hd : (((q : ℤ) ^ 2 + ε * q + 1 : ℤ) : ZMod 3) = 0 := by
    push_cast
    rw [hqε]
    rcases hε with rfl | rfl <;> decide
  have h2 : (((-ε * q - 1 : ℤ)) : ZMod 3) = 1 := by
    have : (-ε * q - 1 : ℤ) = -(ε * q) - 1 := by ring
    rw [this]
    push_cast at hεq ⊢
    rw [hεq]
    decide
  have h3 : ((ε * q + 1 : ℤ) : ZMod 3) = 2 := by
    push_cast at hεq ⊢
    rw [hεq]
    decide
  have h0 : tup ζ (vecV i j) 0 = ζ ^ i.val := by simp [tup, vecV]
  have h1 : tup ζ (vecV i j) 1 = ζ ^ j.val := by simp [tup, vecV]
  obtain ⟨t0, t1, t2, t3⟩ := threeSixTuple_values (L := L) q ε (ζ ^ i.val) (ζ ^ j.val)
  rw [rootDiagUnit_mem_threeSixTorus_iff' Fr hFr hε, h0, h1]
  refine ⟨(fin_D4_eq_iff _ _).2 ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [t0, h0]
  · rw [t1, h1]
  · rw [t2, pow_val_zpow hζ3, h2, mul_one]
    simp [tup, vecV]
  · rw [t3, pow_val_zpow hζ3, pow_val_zpow hζ3, hεq, h3, mul_one, pow_val_add hζ3]
    have e : (vecV i j) 3 = i + 2 * j := rfl
    show ζ ^ ((vecV i j) 3).val = _
    rw [e]
    congr 2
    ring
  · rw [pow_val_zpow hζ3, hd, mul_zero]
    simp
  · rw [pow_val_zpow hζ3, hd, mul_zero]
    simp

end Torus

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
