module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofL
public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofLeA7
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofQL
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

open Res163 in
theorem step162LPointA7_of_items
    (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (h135 : Item135) (h142 : Concl142R) :
    Step162LPointA7 := by
  intro G _ _ A c L h Y hY e Le he hLe _ h7 _ hT _
  have he' : Sec15R G A e Le := sec15R_of_point h he hLe
  have hS : Sec14Std G A c L := h.toSec14Std
  have h7all : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* alternatingGroup (Fin 7)) :=
    fun b Lb hb hLb => Step163Alt.nonempty_a7_of_point he' h7 hT hb hLb
  have hno : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro b Lb hb hLb
    obtain ⟨χ⟩ := h7all b Lb hb hLb
    exact ⟨fun ψ => KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1.false (ψ.symm.trans χ)⟩
  have hY0 : Y ∈ scriptY0 A (lB A) := hY.prop
  have hYY : Y ∈ scriptY A := hY0.1.1
  obtain ⟨hYs, hYB, B, Q, f, K, Lf, hP, hf, hLf⟩ :=
    exists_point148_of_noHJ hCore h hno (hPoint G A c L hS) hY0
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({f} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKLf : K ≤ Lf := hP.2.2.2.2.2.2.2.1
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  let := ker148_normal hYY.2
  have hkt := hKT G A c L hS Y hYY hYs hYB B Q f K Lf hP
  have hsα : IsSimpleGroup ↥(img148 A Y K) := isSimpleGroup_img148_of_kType148 hS hkt
  obtain ⟨-, ⟨ψ⟩⟩ := Main148.theta_equiv_of_img148 hKM hKp hKq hsα (MulEquiv.refl _)
  obtain ⟨χ⟩ := h7all f Lf hf hLf
  have h2520 : Nat.card (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf) = 2520 := by
    rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  have hKα : Nat.card ↥(img148 A Y K) = 2520 := by
    rcases hkt.2 with ⟨-, -, ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f', e', hp, -, -, hiso, -⟩⟩ | ⟨h3, -⟩
    · rw [Nat.card_congr φ.toEquiv, h2520]
    · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    · exact (not_isoLThreePi_of_card_eq_2520 h2520 p (f' * e') hiso).elim
    · exfalso
      obtain ⟨-, hZ, -, -, -⟩ := KFacts.KS14.a7_facts _ ⟨χ⟩
      have h3' := h3.1
      rw [hZ, Subgroup.card_bot] at h3'
      omega
  have hcard : Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) =
      Nat.card (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf) := by
    rw [Nat.card_congr ψ.toEquiv, hKα, h2520]
  have hcov := eq_sup_theta_of_card hKLf hcard
  have hf' : Sec15R G A f Lf := sec15R_of_point h hf hLf
  have hθ := Res3LeA7.theta_eq_pCore_two h135 hf' ⟨χ⟩
  by_cases hO : CFSG.Open.pCoreOf 2 Lf = ⊥
  ·
    refine ⟨f, Lf, hf, hLf, Y, hY, ?_⟩
    have hθ1 : (aschbacherSolvableCore 3 ↥Lf).map Lf.subtype = ⊥ := by
      rw [hθ, ← Res3LeA7.pCoreOf_eq_map, hO]
    rw [hcov, hθ1, sup_bot_eq]
    exact hKY
  ·
    obtain ⟨Y₀, hLY₀, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A)))
      (Res3LeA7.mem_scriptY0 h135 hf' (h142 G A c L h) ⟨χ⟩ hO)
    exact ⟨f, Lf, hf, hLf, Y₀, hY₀, hLY₀⟩

end CFSG.RankThree.PartTwo.Sec16
