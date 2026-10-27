module

public import CFSG.RankThree.PartTwo.Sec16.Item163P6Conf
import CFSG.RankThree.PartTwo.Sec16.Item162Res7A7Setup
import CFSG.RankThree.PartTwo.Sec16.Item166ResProofVB
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open scoped commutatorElement

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y S : Subgroup G}

private theorem pCoreOf_commutator_mem_scriptQ {A Q D : Subgroup G} {c : G}
    (hA : Late.IsE27 A) (hQmem : Q ∈ scriptQ A (lB A))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hQ3 : ¬ 3 ∣ Nat.card ↥Q)
    (hcA : c ∈ A) (hc3 : Nat.card (Subgroup.zpowers c) = 3) :
    let U₀ := ⁅Q ⊓ Subgroup.centralizer (D : Set G), Subgroup.zpowers c⁆
    U₀ ∈ scriptQ A (lB A) ∧ U₀ ≤ Q ∧ U₀ ≤ Subgroup.centralizer (D : Set G) ∧
      U₀ = ⁅U₀, A⁆ ∧ A ≤ Subgroup.normalizer (U₀ : Set G) ∧ ¬ 3 ∣ Nat.card ↥U₀ := by
  set U₀ := ⁅Q ⊓ Subgroup.centralizer (D : Set G), Subgroup.zpowers c⁆ with hU₀def
  have hACD : A ≤ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) :=
    hAD.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D)
  have hWQ : Q ⊓ Subgroup.centralizer (D : Set G) ≤ Q := inf_le_left
  have hAW : A ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAQ hACD
  have hcW : Subgroup.zpowers c ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (hAW hcA)
  have hW3 : ¬ 3 ∣ Nat.card ↥(Q ⊓ Subgroup.centralizer (D : Set G)) :=
    fun hd => hQ3 (hd.trans (Subgroup.card_dvd_of_le hWQ))
  have hcP : IsPGroup 3 ↥(Subgroup.zpowers c) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [hc3]; norm_num)
  have hU₀Q : U₀ ≤ Q := by
    rw [hU₀def]
    exact (Subgroup.commutator_mono hWQ le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (Subgroup.zpowers_le.mpr (hAQ hcA)))
  have hU₀W : U₀ ≤ Q ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hU₀def]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hcW
  have hU₀3 : ¬ 3 ∣ Nat.card ↥U₀ :=
    fun hd => hQ3 (hd.trans (Subgroup.card_dvd_of_le hU₀Q))
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1).trans
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hcA))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hAU₀ : A ≤ Subgroup.normalizer (U₀ : Set G) := by
    rw [hU₀def]
    exact GorensteinWalter.le_normalizer_commutator_of_le_normalizer A
      (Q ⊓ Subgroup.centralizer (D : Set G)) (Subgroup.zpowers c) hAW hAc
  have hU₀idem : ⁅U₀, Subgroup.zpowers c⁆ = U₀ := by
    rw [hU₀def]
    exact RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
      (Subgroup.zpowers c) (Q ⊓ Subgroup.centralizer (D : Set G)) hcP hW3 hcW
  have hU₀A : U₀ = ⁅U₀, A⁆ := by
    refine le_antisymm ?_ (Subgroup.le_normalizer_iff_commutator_le_left.mp hAU₀)
    calc U₀ = ⁅U₀, Subgroup.zpowers c⁆ := hU₀idem.symm
      _ ≤ ⁅U₀, A⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)
  exact ⟨mem_scriptQ_of_le hQmem hU₀Q hAU₀, hU₀Q, hU₀W.trans inf_le_right, hU₀A, hAU₀,
    hU₀3⟩

private theorem exists_hyperplane_of_commutator {A Q D U₀ : Subgroup G}
    (hA : Late.IsE27 A) (hU₀mem : U₀ ∈ scriptQ A (lB A)) (hU₀Q : U₀ ≤ Q)
    (hU₀CD : U₀ ≤ Subgroup.centralizer (D : Set G)) (hU₀3 : ¬ 3 ∣ Nat.card ↥U₀)
    (hAU₀ : A ≤ Subgroup.normalizer (U₀ : Set G)) (hU₀A : U₀ = ⁅U₀, A⁆)
    (hU₀ne : U₀ ≠ ⊥) (hDleL : D ≤ L) (hLQ : L ⊓ Q = ⊥) :
    ∃ H U : Subgroup G, IsHyperplane A H ∧ U ∈ scriptQZero A (lB A) ∧ U ≠ ⊥ ∧
      U ≤ Q ∧ U ≤ Subgroup.centralizer (H : Set G) ∧
      U ≤ Subgroup.centralizer (D : Set G) ∧ U ⊓ D = ⊥ := by
  have hU₀le : U₀ ≤ ⨆ (B : Subgroup G) (_ : IsHyperplane A B),
      ⁅U₀ ⊓ Subgroup.centralizer (B : Set G), A⁆ :=
    le_iSup_commutator_centralizer hA hU₀3 hAU₀ hU₀A
  have hex : ∃ B : Subgroup G, IsHyperplane A B ∧
      ⁅U₀ ⊓ Subgroup.centralizer (B : Set G), A⁆ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hbot : (⨆ (B : Subgroup G) (_ : IsHyperplane A B),
        ⁅U₀ ⊓ Subgroup.centralizer (B : Set G), A⁆) = ⊥ := by
      rw [iSup_eq_bot]
      intro B
      rw [iSup_eq_bot]
      exact hno B
    exact hU₀ne (le_bot_iff.mp (hU₀le.trans (le_of_eq hbot)))
  obtain ⟨H, hH, hUne⟩ := hex
  have hUmem : ⁅U₀ ⊓ Subgroup.centralizer (H : Set G), A⁆ ∈ scriptQZero A (lB A) :=
    commutator_inf_centralizer_mem_scriptQZero hA hU₀mem hH.1
  have hUle : ⁅U₀ ⊓ Subgroup.centralizer (H : Set G), A⁆ ≤
      U₀ ⊓ Subgroup.centralizer (H : Set G) :=
    commutator_inf_centralizer_le hA.1.1 hAU₀ hH.1
  have hUleQ : ⁅U₀ ⊓ Subgroup.centralizer (H : Set G), A⁆ ≤ Q :=
    (hUle.trans inf_le_left).trans hU₀Q
  have hUleCH : ⁅U₀ ⊓ Subgroup.centralizer (H : Set G), A⁆ ≤
      Subgroup.centralizer (H : Set G) :=
    hUle.trans inf_le_right
  have hUleCD : ⁅U₀ ⊓ Subgroup.centralizer (H : Set G), A⁆ ≤
      Subgroup.centralizer (D : Set G) :=
    (hUle.trans inf_le_left).trans hU₀CD
  have hUinfD : ⁅U₀ ⊓ Subgroup.centralizer (H : Set G), A⁆ ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    calc ⁅U₀ ⊓ Subgroup.centralizer (H : Set G), A⁆ ⊓ D ≤ Q ⊓ L :=
          inf_le_inf hUleQ hDleL
      _ = L ⊓ Q := inf_comm Q L
      _ = ⊥ := hLQ
  exact ⟨H, _, hH, hUmem, hUne, hUleQ, hUleCH, hUleCD, hUinfD⟩

namespace Conf685

theorem pCoreOf_inf_centralizer_le (h : Conf685 A c L Y S)
    (hLQ : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.centralizer (L : Set G) := by
  have h3 : 3 ∣ Nat.card L :=
    three_dvd_card_of_mem_lA h.sec15R h.sec15R.zpowers_mem_omegaA h.sec15R.mem_lA
  have hC : Subgroup.centralizer (Subgroup.zpowers c : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    hC ▸ (Subgroup.centralizer_le_normalizer (Subgroup.zpowers c : Set G)).trans
      (normalizer_zpowers_le_normalizer_L h.sec15R h3)
  intro x hx
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hxNL : x ∈ Subgroup.normalizer (L : Set G) := hcN hxC
  have hcommL : ⁅x, l⁆ ∈ L := by
    have hle : ⁅Subgroup.zpowers x, L⁆ ≤ L := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (Subgroup.zpowers_le.mpr hxNL)
    exact hle (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) hl)
  have hLQY : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    (h.le_y Y h.mem_y).trans ((Subgroup.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
  have hcommQ : ⁅x, l⁆ ∈ CFSG.Open.pCoreOf 2 Y := by
    have hle : ⁅CFSG.Open.pCoreOf 2 Y, L⁆ ≤ CFSG.Open.pCoreOf 2 Y :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hLQY
    exact hle (Subgroup.commutator_mem_commutator hxQ hl)
  have hone : ⁅x, l⁆ = 1 := by
    have hmem : ⁅x, l⁆ ∈ L ⊓ CFSG.Open.pCoreOf 2 Y :=
      Subgroup.mem_inf.mpr ⟨hcommL, hcommQ⟩
    rw [hLQ] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact (commutatorElement_eq_one_iff_commute.mp hone).symm

theorem not_pCoreOf_le_centralizer (h : Conf685 A c L Y S)
    (hLQ : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    ¬ CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({c} : Set G) := by
  intro hQc
  have hQCL : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer (L : Set G) := by
    intro q hq
    exact pCoreOf_inf_centralizer_le h hLQ (Subgroup.mem_inf.mpr ⟨hq, hQc hq⟩)
  have hLCQ : L ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    Subgroup.le_centralizer_iff.mp hQCL
  have hLY : L ≤ Y := h.le_y Y h.mem_y
  have hLinf : L ≤ Y ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    le_inf hLY hLCQ
  have hLleQ : L ≤ CFSG.Open.pCoreOf 2 Y :=
    hLinf.trans (Res162Seven.inf_centralizer_pCoreOf_le h.item153 h.mem_y)
  have hLbot : L = ⊥ :=
    le_bot_iff.mp ((le_inf le_rfl hLleQ).trans (le_of_eq hLQ))
  exact h.d_ne_bot (by rw [hLbot, inf_bot_eq])

theorem commutator_ne_bot (h : Conf685 A c L Y S) (hLQ : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G),
      Subgroup.zpowers c⁆ ≠ ⊥ := by
  intro hcomm
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.sec15R.zpowers_mem_omegaA).1
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.sec15R.zpowers_mem_omegaA).2.1
  have hcP : IsPGroup 3 ↥(Subgroup.zpowers c) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [hc3]; norm_num)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := h.mem_y.prop.1.1.2
  have hAQ : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hcQ : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) := hAQ hcA
  have hLY : L ≤ Y := h.le_y Y h.mem_y
  have hLQnorm : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hLY.trans ((Subgroup.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
  have hDQ : S ⊓ L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    inf_le_right.trans hLQnorm
  have hD2 : IsPGroup 2 ↥(S ⊓ L) :=
    (isPiSubgroup_piOf_iff Nat.prime_two (S ⊓ L)).mp h.mem_d.prop.2
  have hQ2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hcOdd : Odd (orderOf c) := by
    rw [← Nat.card_zpowers, hc3]
    norm_num
  have hLCc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.sec15R.mem_lA.1
  have hcD : ∀ b ∈ S ⊓ L, c * b = b * c := by
    intro b hb
    have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := hLCc (Subgroup.mem_inf.mp hb).2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hbC).symm
  have hfix : ∀ q ∈ CFSG.Open.pCoreOf 2 Y,
      (∀ b ∈ S ⊓ L, q * b = b * q) → c * q = q * c := by
    intro q hq hqD
    have hqC : q ∈ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hqD b hb).symm
    have hqW : q ∈ CFSG.Open.pCoreOf 2 Y ⊓
        Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hq, hqC⟩
    have hle : CFSG.Open.pCoreOf 2 Y ⊓
        Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) ≤
          Subgroup.centralizer (Subgroup.zpowers c : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact Subgroup.mem_centralizer_iff.mp (hle hqW) c (Subgroup.mem_zpowers c)
  have hcentral : ∀ q ∈ CFSG.Open.pCoreOf 2 Y, c * q = q * c :=
    CFSG.RankThree.GF2n.Tim78.commute_of_thompson_A_times_B hQ2 hD2 hcQ hDQ hcOdd hcD hfix
  apply not_pCoreOf_le_centralizer h hLQ
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hcentral q hq).symm

theorem exists_hyperplane_scriptQZero (h : Conf685 A c L Y S)
    (hLQ : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)
    (hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∨ c ∈ Y) :
    ∃ H U : Subgroup G, IsHyperplane A H ∧ U ∈ scriptQZero A (lB A) ∧ U ≠ ⊥ ∧
      U ≤ CFSG.Open.pCoreOf 2 Y ∧ U ≤ Subgroup.centralizer (H : Set G) ∧
      U ≤ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) ∧ U ⊓ (S ⊓ L) = ⊥ := by
  set Q := CFSG.Open.pCoreOf 2 Y with hQdef
  set D := S ⊓ L with hDdef
  have hY4 : Y ∈ scriptY4 A (lB A) := h.mem_y.prop.1
  have hQmem : Q ∈ scriptQ A (lB A) :=
    ProofVB167.pCoreOf_mem_scriptQ_of_cover h.sec15R.toSec14Std h.item1444 h.item146 h.bot
      h.concl142 hY4 hcov
  obtain ⟨hQpi, hAQ, -⟩ := mem_scriptQ_iff.mp hQmem
  have hQ3 : ¬ 3 ∣ Nat.card ↥Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQpi
  have hA : Late.IsE27 A :=
    Late.isE27_of_mem_partTwoE h.sec15R.toSec14Std.toSec13Data.mem_partTwoE
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.sec15R.zpowers_mem_omegaA).1
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.sec15R.zpowers_mem_omegaA).2.1
  have hDmem : D ∈ scriptQ A (lB A) := h.mem_d.prop.1.1
  have hDleL : D ≤ L := h.mem_d.prop.1.2
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := (mem_scriptQ_iff.mp hDmem).2.1
  obtain ⟨hU₀mem, hU₀Q, hU₀CD, hU₀A, hAU₀, hU₀3⟩ :=
    pCoreOf_commutator_mem_scriptQ hA hQmem hAQ hAD hQ3 hcA hc3
  exact exists_hyperplane_of_commutator hA hU₀mem hU₀Q hU₀CD hU₀3 hAU₀ hU₀A
    (commutator_ne_bot h hLQ) hDleL hLQ

end Conf685

end CFSG.RankThree.PartTwo.Sec16.Proof163P6
