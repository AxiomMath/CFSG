module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4Proof
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Step158InnerSigmaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    Sec8.IsZ3PGLThreePi (lBarA c L A) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
    ∀ X ∈ scriptY4 A (lB A), X ≤ L →
    ∀ (r f e' : ℕ) [Fact r.Prime], 1 ≤ f → 1 ≤ e' →
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) r (f * e') →
      IsLThreeEpsAt (↥X ⧸ CFSG.pPrimeCore 3 ↥X) r f →
      ¬ Sec4.IsoLThreePi (↥X ⧸ CFSG.pPrimeCore 3 ↥X) r f → False

theorem step158InnerRank_of_res6 (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (hSig : Step158InnerSigmaR) : Step158InnerRank := by
  intro G _ _ A c L hR p e _ he hL3 hPGL htype X hX hXL
  have h14 := hR.toSec14Std
  have hNHJ : ¬ AllPointsHJ A :=
    Proof15Res6.not_allPointsHJ_of_isEmpty h14 (Proof15Res6.isEmpty_j2_of_isoLThreePi hL3)
  have hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥ :=
    fun B hB => lB_eq_bot_of_not_allPointsHJ' h134 h48 h14 hNHJ hB
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.2
  have hXΔ0 : X = deltaZero A (lB A) X :=
    eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
      h14 hAX hX.2.1 hX.2.2.1
  have hHJ : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        False := fun c' L' hc' hL' hJ2 =>
    hNHJ (allPointsHJ_of_j2 h134 h48 { h14 with zpowers_mem_omegaA := hc', mem_lA := hL' } hJ2)
  suffices hE : ∃ E : Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X),
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 by
    obtain ⟨E, hE, h9⟩ := hE
    exact Proof15Res6.exists_e9_of_quot hE h9
  rcases Proof1515.cases148_of_mem_scriptY4 (h148 G A c L hR) hR.isElemAbelian.1 hX hXΔ0 with
    h2 | h3 | h4 | h5
  · obtain ⟨c', hc'Ω, hdec, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨r, f, e', hr, hf, he', hiso, hε⟩ | ⟨hJ2, -⟩
    ·
      exact exists_e9_of_mulEquiv φ (ks153ThreeRank _ (h14.chosen136.2 c' hc'Ω L' hL').1)
    ·
      exact exists_e9_of_mulEquiv φ exists_e9_alternatingGroup_seven
    ·
      by_cases hpi : Sec4.IsoLThreePi (↥X ⧸ CFSG.pPrimeCore 3 ↥X) r f
      · exact exists_e9_of_isLThreePi ⟨r, f, hr, hf, hpi⟩
      · exfalso
        have hA := hR.isElemAbelian
        have hA27 := hR.card_eq
        obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'Ω
        obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp h14.zpowers_mem_omegaA
        have hc'1 : c' ≠ 1 := by
          rintro rfl
          rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc'3
          exact absurd hc'3 (by norm_num)
        have hc1 : c ≠ 1 := by
          rintro rfl
          rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
          exact absurd hc3 (by norm_num)
        have hord' : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
        have hc'T := Proof15Res6.mem_actTriv_of_eq_sup hc'A hord' hAX hdec
        have hcT : c ∈ Proof15Res6.actTriv X (pPrimeCoreOf 3 X) := by
          refine ⟨(hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)) hcA, fun x hx => ?_⟩
          have hxc : x ∈ Subgroup.centralizer ({c} : Set G) :=
            le_centralizer_of_mem_thetaComponentsAt h14.mem_lA.1 (hXL hx)
          have hcomm : x * c = c * x := (Subgroup.mem_centralizer_singleton_iff.mp hxc)
          have heq : ⁅x, c⁆ = 1 := by
            rw [commutatorElement_def, hcomm]
            group
          rw [heq]
          exact one_mem _
        have hX3 : 3 ∣ Nat.card X :=
          (Proof1515.three_dvd_card_of_mem_scriptY4 hX).trans
            (Subgroup.card_quotient_dvd_card _)
        have hN3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 X) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X)
        have hzc : Subgroup.zpowers c' = Subgroup.zpowers c :=
          Proof15Res6.zpowers_eq_of_mem_actTriv hA hA27 hLB hX.2.2.1
            (le_normalizer_pPrimeCoreOf 3 X) hN3 hX3 hcA hc'A hc1 hc'1 hcT hc'T
        have hL'c : L' ∈ lA A c := (lA_eq_of_zpowers_eq hzc) ▸ hL'
        have hL'3 : 3 ∣ Nat.card L' :=
          (Main148.three_dvd_card_of_isoLThreePi148 (Nat.mul_pos hf he') hiso).trans
            (Subgroup.card_quotient_dvd_card _)
        have hL'L : L' = L :=
          (h14.chosen136.2 c h14.zpowers_mem_omegaA L h14.mem_lA).2 L' hL'c.1 hL'3
        subst hL'L
        exact hSig G A c L' hR p e he hL3 hPGL htype X hX hXL r f e' hf he' hiso hε hpi
    ·
      exact (hHJ c' L' hc'Ω hL' hJ2).elim
  ·
    obtain ⟨c', L', hc', hL', hJ2, -⟩ := h3
    exact (hHJ c' L' hc' hL' hJ2).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact exists_e9_of_mulEquiv φ exists_e9_alternatingGroup_ten
  ·
    obtain ⟨-, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    exact exists_e9_of_isLThreePi ⟨2, 3 * n, ⟨Nat.prime_two⟩, by omega, hiso⟩

theorem item158Y0R_of_res6
    (h131 : Item131) (h138 : Item138N) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h148 : Item148R) (hSig : Step158InnerSigmaR) (hC : Step158CartanP) : Item158Y0R :=
  item158Y0R_of_res2 h131 h138 (step158InnerRank_of_res6 h134 h48 h148 hSig)
    (step158CartanCore_of hC)

end CFSG.RankThree.PartTwo.Sec15
