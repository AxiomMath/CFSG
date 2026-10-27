module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddSz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddFamilies
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.HardMathSupport.Dickson.I271.Support.CyclicCenter
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

namespace CoreSetup

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

theorem false_of_noSzOverTwo (h : CoreSetup X K L T Y n)
    (hNo : NoSzOverTwo (↥K ⧸ center ↥K)) : False := by
  let φ : ↥L →* (↥K ⧸ center ↥K) :=
    (QuotientGroup.mk' (center ↥K)).comp (Subgroup.inclusion h.le)
  have hφ : Function.Injective φ := by
    intro a b hab
    have hmem : (Subgroup.inclusion h.le (a * b⁻¹)) ∈ Subgroup.center ↥K := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 : φ (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hab, mul_inv_cancel]
      exact h1
    have hxZ : (((a : L) * (b : L)⁻¹ : L) : X) ∈ (Subgroup.center ↥K).map K.subtype :=
      ⟨Subgroup.inclusion h.le (a * b⁻¹), hmem, rfl⟩
    have hxbot : (((a : L) * (b : L)⁻¹ : L) : X) ∈
        L ⊓ (Subgroup.center ↥K).map K.subtype :=
      ⟨Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ b.2), hxZ⟩
    rw [h.inf_center_eq_bot] at hxbot
    have h1 : a * b⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.mp hxbot)
    exact mul_inv_eq_one.mp h1
  have hLNo : NoSzOverTwo ↥L := noSzOverTwo_of_injective φ hφ hNo
  have hSz : CFSG.Blueprint.SuzukiModel (Bar2 L) 2 n :=
    CFSG.LocalAnalysis.EvenBN.GMSK.suzukiModel_of_lieModel_twistedB2 h.sz
  exact hLNo.not_suzukiModel_quotient (CFSG.pCore 2 ↥L) (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    2 n hSz

theorem pRank_centerQuotient_le_three
    (h : CoreSetup X K L T Y n) {d : TauCeti.ValidLieTypeIndex} (hd : d.1.characteristic ≠ 2)
    (e : (↥K ⧸ center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank d.1.characteristic (⊤ : Subgroup (↥K ⧸ center ↥K)) ≤ 3 := by
  set p := d.1.characteristic with hpdef
  have hp : p.Prime := TauCeti.ValidLieTypeIndex.characteristic_prime d
  have hp2 : p ≠ 2 := hd
  by_cases hpZ : p ∣ Nat.card (Subgroup.center ↥K)
  · have hGA : CFSG.Open.GriessAllModelsStatement :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    obtain ⟨hp3, hshape⟩ :=
      CFSG.HardMathSupport.Dickson.I271.center_shape hGA h.quasisimple hp hp2 d hpdef.symm e hpZ
    rw [hp3] at hpZ ⊢
    by_cases hlt : CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ center ↥K)) < 3
    · omega
    · have h3le : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ center ↥K)) := by omega
      have hExc := CFSG.HardMathSupport.Timmesfeld.LieRank.lieCoverRankHighExc3_holds hGA
      have hex : 3 = 3 ∧ ∃ (t : CFSG.Open.StatedLieTag) (n r f : ℕ),
          ((t = .PSL ∧ n = 2 ∧ r = 3 ∧ f = 2) ∨
            (t = .POmegaOdd ∧ n = 3 ∧ r = 3 ∧ f = 1) ∨
            (t = .G2 ∧ n = 0 ∧ r = 3 ∧ f = 1) ∨
            (t = .PSU ∧ n = 4 ∧ r = 3 ∧ f = 1)) ∧
          CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) t n r f := by
        rcases hshape with hPSU | hPOmega | ⟨hG2, q, d', hq, hd', ⟨e'⟩⟩
        · exact ⟨rfl, .PSU, 4, 3, 1, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)),
            Or.inl ⟨by decide, hPSU⟩⟩
        · exact ⟨rfl, .POmegaOdd, 3, 3, 1, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩),
            Or.inl ⟨by decide, hPOmega⟩⟩
        · obtain ⟨d'', hv''⟩ := d'
          have hd'' : d'' = TauCeti.LieTypeIndex.G2 q := hd'
          subst hd''
          have hqcard : q.p ^ q.exponent = 3 := by rwa [TauCeti.PrimePower.card_def] at hq
          obtain ⟨hp3q, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hqcard
          have hCh :=
            CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_three q hv'' hp3q hf1
          have hCh' := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e' hCh
          exact ⟨rfl, .G2, 0, 3, 1, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)),
            Or.inr (Or.inl ⟨rfl, by decide, hCh'⟩)⟩
      have hle := hExc (↥K) h.quasisimple ⟨d, ⟨e⟩⟩ 3 Nat.prime_three (by norm_num) hpZ h3le hex
      exact hle.trans (h.pRank_K_le Nat.prime_three (by norm_num))
  · exact (CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_not_dvd
      hp hpZ).trans (h.pRank_K_le hp hp2)

end CoreSetup

theorem coreOddSlice :
    CoreOddSlice := by
  intro X _ _ K L T Y n d h hd ⟨e⟩
  exact h.false_of_noSzOverTwo
    (noSzOverTwo_of_lie_odd hd e (h.pRank_centerQuotient_le_three hd e))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
