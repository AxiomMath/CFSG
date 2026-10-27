module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO2Bound
import CFSG.RankThree.PartTwo.Sec18.Item186Act
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO3Act
import CFSG.RankThree.PartTwo.Sec18.SylowFusion
import CFSG.RankThree.PartTwo.Sec18.SylowInnerH3
import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTI
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec5.Items52
import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)


section Certs


theorem card_pCoreOf_inf_centralizer_le_two189 (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}
    (h : Sec18H G A M H c) (h7 : Hyp187 A M H c)
    (hO2 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G)) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := inSubgroup perfectResidual H with hLdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set Lc := lc H c with hLcdef
  set B := A ⊓ L with hBdef
  set R := CFSG.Open.pCoreOf 2 M ⊓ C with hRdef
  set E := C ⊓ Subgroup.centralizer (Lc : Set G) with hEdef
  have hAM : A ≤ M := sec18Std_le h.toSec18Std
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H h
  have hAC : A ≤ C := Sec19.le_centralizer_of_mem hA.1.1 hcA
  have hCLc : C ≤ Subgroup.normalizer (Lc : Set G) :=
    (SylowInner.centralizer_le_normalizer_zpowers c).trans
      (normalizer_zpowers_le_normalizer_lc h1842 h)
  have hLcC : Lc ≤ C := SylowFusion.lc_le_centralizer H c
  have hOLc : CFSG.Open.pCoreOf 2 Lc = ⊥ := by
    apply le_bot_iff.mp
    rw [← hO2]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Lc).trans hLcC)
      (hCLc.trans (Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf Lc))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lc)
  obtain ⟨eLc⟩ := SylowFusion.nonempty_quotient_lc h184 h
  have hLcp : ⁅Lc, Lc⁆ = Lc := commutator_inSubgroup_perfectResidual _
  have hθ : inSubgroup (aschbacherSolvableCore 3) Lc = ⊥ := by
    rw [Item189O3Proof.inSubgroup_theta_eq_pCoreOf hLcp eLc, hOLc]
  have hBLc : B ≤ Lc := (SylowFusion.isSylowOf_lc h1812 h184 h).le
  have hB9 : Nat.card B = 9 := card_inf_of_sec18H h1812 h184 h
  have hB3 : IsPGroup 3 B := hA.isPGroup.to_le inf_le_left
  have hNB : Subgroup.normalizer (B : Set G) ≤ M :=
    Sec20.normalizer_inf_le_of_hyp201One (hyp201One_of189 h h7) hB9
  have hEM : E ≤ M :=
    inf_le_right.trans ((Subgroup.centralizer_le hBLc).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNB))
  have hCE : C ≤ Subgroup.normalizer (E : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer
      (hCLc.trans (Sec5.normalizer_le_normalizer_centralizer Lc))
  have hRE : CFSG.Open.pCoreOf 2 M ⊓ E = ⊥ := by
    apply le_bot_iff.mp
    rw [← hO2]
    have h1 : CFSG.Open.pCoreOf 2 M ⊓ E ≤ CFSG.Open.pCoreOf 2 E :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (Late.le_normalizer_inf (hEM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
          Subgroup.le_normalizer)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left)
    exact h1.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 E).trans inf_le_left)
      (hCE.trans (Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf E))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 E))
  have hRD : ∀ x ∈ R, x ∈ Sec4.thetaQuotCentralizer Lc → x = 1 := by
    intro x hxR hxD
    have hxE : x ∈ E := by
      refine Subgroup.mem_inf.mpr ⟨hxR.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hxD).2 l hl
      rw [hθ, Subgroup.mem_bot, inv_mul_eq_one] at h1
      calc l * x = x * l * x⁻¹ * x := by rw [← h1]
        _ = x * l := by group
    have hx : x ∈ CFSG.Open.pCoreOf 2 M ⊓ E := ⟨hxR.1, hxE⟩
    rw [hRE] at hx
    exact hx
  have hR2 : IsPGroup 2 R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := inf_le_right.trans hCLc
  have hBR : B ≤ Subgroup.normalizer (R : Set G) :=
    Late.le_normalizer_inf
      ((inf_le_left.trans hAM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      ((inf_le_left.trans hAC).trans Subgroup.le_normalizer)
  have key : ∀ x ∈ R, ∀ y ∈ R, x ≠ 1 → y ≠ 1 → x = y := by
    intro x hx y hy hx1 hy1
    have h1 := Item186Proof.inv_mul_mem_thetaQuotCentralizer hLcp eLc hBLc hB9 hB3 hR2 hRN hBR
      hx hy (fun hD => hx1 (hRD x hx hD)) (fun hD => hy1 (hRD y hy hD))
    exact inv_mul_eq_one.mp (hRD _ (R.mul_mem (R.inv_mem hx) hy) h1)
  let f : R → Bool := fun x => decide ((x : G) = 1)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : G) = 1 <;> by_cases hy : (y : G) = 1
    · exact Subtype.ext (hx.trans hy.symm)
    · have h1 : f x = true := decide_eq_true hx
      have h2 : f y = false := decide_eq_false hy
      rw [h1, h2] at hxy
      exact absurd hxy (by decide)
    · have h1 : f x = false := decide_eq_false hx
      have h2 : f y = true := decide_eq_true hy
      rw [h1, h2] at hxy
      exact absurd hxy (by decide)
    · exact Subtype.ext (key _ x.2 _ y.2 hx hy)
  calc Nat.card R ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
    _ = 2 := by simp

theorem step189O2Bound_direct (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2) :
    Step189O2Bound := by
  intro G _ _ A M H c h h7 hO2
  exact card_pCoreOf_inf_centralizer_le_two189 h1812 h184 h1842 h h7 hO2

theorem step189O2BoundSplit_of (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2) :
    Step189O2BoundSplit := by
  intro G _ _ A M H c h h7 hO2 _ _ _ _ _ _
  exact card_pCoreOf_inf_centralizer_le_two189 h1812 h184 h1842 h h7 hO2

end Certs

end CFSG.RankThree.PartTwo.Sec18
