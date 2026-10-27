module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck156O2
public import CFSG.RankThree.PartTwo.Sec15.Liebeck156Bridge
public import CFSG.RankThree.PartTwo.Sec15.Liebeck156Type
public import CFSG.RankThree.PartTwo.Sec15.Liebeck156Four
public import CFSG.RankThree.PartTwo.Sec15.Liebeck156A5
import CFSG.RankThree.PartTwo.Sec15.Liebeck156Theta
import CFSG.RankThree.PartTwo.Sec15.Liebeck155KFacts
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

section TypeHolds

theorem typeK156_holds : TypeK156 :=
  fun _ _ _ htype _ _ hYt hPY hP2 hPn hA5 γ hγ3 hγY hγP hγc hfpf =>
    eq_bot_of_type156 htype hYt hPY hP2 hPn hA5 γ hγ3 hγY hγP hγc hfpf

end TypeHolds

variable {G : Type} [Group G] [Finite G]

section Certified

theorem step156CQA5DO2_of (h134 : Item134) (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5)
    (h44 : Sec4.Item4_4) (hK : TypeK156) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h143 : Ronan148Q.Item143Q A (lB A)) :
    Step156CQA5DO2 A (lB A) := by
  intro Y hY hY5 c₀ L₀ d X₁ D hΩ _ _ hYX hYd hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have hA : Late.IsE27 A := h₀.isE27
  have hc₀A : c₀ ∈ A := h₀.toSec13Data.mem_A
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.1.1
  have hYp : Group.IsPerfect ↥Y := isPerfect_of_mem_scriptY4 hY4
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY4.1.2
  have hP1 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.1.2.2
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  have hdS : d ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hYC : Y ≤ C := Proof155w.le_centralizer_of_pCoreOf_le_centralizer (hA.1.2 d D.mem_d)
    D.le_x hYX hdS.2 hYd
  have h3Y : 3 ∣ Nat.card Y := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y)]
    exact Dvd.dvd.mul_right (Liebeck155.three_dvd_card_quot_pCore_two hY4) _
  obtain ⟨𝒳, h𝒳, -, hYX', htypes⟩ :=
    exists_le_sSup_of_item143Q h134 h48 h45 h h143 hY4 h3Y D hΩ hYC
  have hc₀d : c₀ * d = d * c₀ :=
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨c₀, hc₀A⟩ ⟨d, D.mem_d⟩)
  have hc₀C : c₀ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hc₀d
  have hc₀3 : c₀ ^ 3 = 1 := hA.1.2 c₀ hc₀A
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d D.mem_d) D.ne_d
  have hc₀X : c₀ ∈ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) :=
    mem_normalizer_sSup_of_item45 h45 h.toTheoremFourHyp hd3 h𝒳 hc₀C (k := 1)
      (by rw [pow_one]; exact hc₀3)
  have hc₀c : ∀ y ∈ Y, c₀ * y * c₀⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
    intro y hy
    have h1 := commutator_mem_pCoreOf_of_data156 D hAY hYX y hy c₀
      (Subgroup.subset_closure (Set.mem_insert _ _))
    have e : c₀ * y * c₀⁻¹ * y⁻¹ = (y * c₀ * y⁻¹ * c₀⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hPT : CFSG.Open.pCoreOf 2 Y ≤ T :=
    (pCoreOf_le_theta_of_typeK156 hK htypes hYX' hYp hY5 hc₀X (hAY hc₀A) hc₀3 hc₀c
      hfix).trans (theta_sSup_le h𝒳)
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top h₀.isSimpleGroup h₀.nonabelian D.ne_d
  have hTC : T ≤ C := Sec17.Proof171Steps.theta_le C
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := Sec17.Proof171Steps.le_normalizer_theta C
  have hS : ∀ H : Subgroup G, H ≤ T ⊔ Y → SectionFourHyp ↥H := fun H hH =>
    h.toTheoremFourHyp.sectionFourHyp fun htop =>
      hCtop (eq_top_iff.mpr (htop ▸ hH.trans (sup_le hTC hYC)))
  have hT3 : ¬ 3 ∣ Nat.card T := by
    rw [hT, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).2.2.1
  have hT2 := pCoreOf_ne_bot_of_item44 h44 hS (Sec17.Proof171Steps.isSolvable_theta C) hT3
    (hYC.trans hCT) hYp hY5 hPT hP1 (hAY hc₀A) (hCT hc₀C) hc₀3 hfix
  have hle : CFSG.Open.pCoreOf 2 T ≤ CFSG.Open.pCoreOf 2 C :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 T).trans hTC)
      (hCT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 T))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) T)
  intro hbot
  exact hT2 (eq_bot_iff.mpr (hbot ▸ hle))

theorem step156CQA5DO2R_of (h134 : Item134) (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5)
    (h44 : Sec4.Item4_4) (hK : TypeK156) (h143 : Ronan148Q.Item143QS14) : Step156CQA5DO2R :=
  fun G _ _ A c L hR => step156CQA5DO2_of h134 h48 h45 h44 hK hR.toSec14Std
    (h143 G A c L hR.toSec14Std)

end Certified

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
