module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec6.Item64
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec14.Item145Bot
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

@[expose] noncomputable def Step1712Seven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
        ∃ U ∈ fourGroups A, U ≤ ⁅V, Subgroup.zpowers c⁆ ∧ U ∈ scriptQ A (lB A)

@[expose] noncomputable def Step1712Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ = ⊥ →
        (∃ R ∈ fourGroups A, R = ⁅R, Subgroup.zpowers c⁆ ∧ R ∈ scriptQ A (lB A) ∧
          R ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) ∨
        ∃ a ∈ A, a ≠ 1 ∧ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∈ scriptY3 A (lB A) ∧
          ∃ U ∈ fourGroups A, U = ⁅U, Subgroup.zpowers a⁆ ∧ U ∈ scriptQ A (lB A) ∧ U ≤ V

section Item1712

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem rank3II_17_12_of_witness (h : Sec17Std G A c L Y₀) (h1711 : Item1711 A (lB A))
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {U : Subgroup G} (hU : U ∈ fourGroups A)
    (hUa : U = ⁅U, Subgroup.zpowers a⁆) (hUQ : U ∈ scriptQ A (lB A))
    (hUM : U ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) {Y : Subgroup G}
    (hY : Y ∈ scriptY3 A (lB A))
    (hΔY : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≤ Y) : Item1712 A (lB A) := by
  obtain ⟨Y', hYY', hY'⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := (mem_fourGroups_iff.mp hU).1
  have hUA : ⁅U, A⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hAU
  have hUm : U ∈ fourGroupsMinus A :=
    ⟨hU, le_antisymm (hUa.le.trans (Subgroup.commutator_mono le_rfl
      (Subgroup.zpowers_le.mpr ha))) hUA⟩
  have hB9 := Sec6.card_inf_centralizer_of_mem_fourGroupsMinus (isE27_of_std h) hUm
  set B := A ⊓ Subgroup.centralizer (U : Set G) with hB
  refine ⟨B, ⟨inf_le_left, by rw [(isE27_of_std h).2, hB9]⟩, fun b hb hb1 => ?_,
    a, ha, fun haB => ?_, Y, hY, hΔY⟩
  · refine h1711 Y₀ h.mem_y0Star a ha ha1 Y' hY' (hΔY.trans hYY') b hb.1 hb1 U hU hUa
      ⟨hUQ, le_inf hUM fun u hu => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hb.2 u hu)
  · have hbot : ⁅U, Subgroup.zpowers a⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure]
      intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp haB.2 u hu)
    have h4 := (mem_fourGroups_iff.mp hU).2.2
    rw [hUa, hbot, Subgroup.card_bot] at h4
    omega

theorem Sec17Std.mem_scriptY3_delta_c (h : Sec17Std G A c L Y₀) {U : Subgroup G}
    (hUQ : U ∈ scriptQ A (lB A))
    (hUM : U ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) (hU1 : U ≠ ⊥) :
    ∃ Y ∈ scriptY3 A (lB A), delta A (lB A) (Subgroup.centralizer ({c} : Set G)) ≤ Y :=
  ⟨_, (delta_M_mem_scriptY3 h hUQ hUM hU1).1, delta_mono (centralizer_c_le_M h)⟩

theorem eq_commutator_of_le_commutator {V U : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    (hV : IsPGroup 2 V) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hcV : c ∈ Subgroup.normalizer (V : Set G)) (hcU : c ∈ Subgroup.normalizer (U : Set G))
    (hUV : U ≤ ⁅V, Subgroup.zpowers c⁆) : U = ⁅U, Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc3' : IsPGroup 3 (Subgroup.zpowers c) := fun g => ⟨1, Subtype.ext (by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hc3, one_zpow, Subgroup.coe_one])⟩
  have h2 : ∀ {X : Subgroup G}, IsPGroup 2 X → ¬ 3 ∣ Nat.card X := fun {X} hX h3 => by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hUV' : U ≤ V := hUV.trans (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (Subgroup.zpowers_le.mpr hcV))
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three (Subgroup.zpowers c) U hc3' (h2 (hV.to_le hUV'))
    (Subgroup.zpowers_le.mpr hcU)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card V) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hc3'
    rw [hn, hm]
    exact Nat.Coprime.pow m n (by norm_num)
  have hfit := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot hVab
    (Subgroup.zpowers_le.mpr hcV) hcop
  rw [Subgroup.commutator_comm] at hfit
  have hCU : U ⊓ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hUV).trans hfit.le)
  rw [hCU, sup_bot_eq] at hfac
  exact hfac

theorem rank3II_17_12_of (h : Sec17Std G A c L Y₀) (h1711 : Item1711 A (lB A))
    (h7 : ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
        ∃ U ∈ fourGroups A, U ≤ ⁅V, Subgroup.zpowers c⁆ ∧ U ∈ scriptQ A (lB A))
    (hmain : ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ = ⊥ →
        (∃ R ∈ fourGroups A, R = ⁅R, Subgroup.zpowers c⁆ ∧ R ∈ scriptQ A (lB A) ∧
          R ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) ∨
        ∃ a ∈ A, a ≠ 1 ∧ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∈ scriptY3 A (lB A) ∧
          ∃ U ∈ fourGroups A, U = ⁅U, Subgroup.zpowers a⁆ ∧ U ∈ scriptQ A (lB A) ∧ U ≤ V) :
    Item1712 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  have hc1 : c ≠ 1 := h.toSec13Data.ne_one
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hU4ne : ∀ {U : Subgroup G}, U ∈ fourGroups A → U ≠ ⊥ := fun {U} hU hbot => by
    have h4 := (mem_fourGroups_iff.mp hU).2.2
    rw [hbot, Subgroup.card_bot] at h4
    omega
  obtain ⟨V, -, hV⟩ := Finite.exists_le_maximal (p := fun V : Subgroup G => V ≤ M ∧
    M ≤ Subgroup.normalizer (V : Set G) ∧ CFSG.Assembly.IsElemAbelian 2 V) (a := ⊥)
    ⟨bot_le, by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top,
      ⟨⟨⟨fun a b => Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, (Subgroup.mem_bot).mp a.2,
          (Subgroup.mem_bot).mp b.2])⟩⟩,
        fun x hx => by rw [(Subgroup.mem_bot).mp hx, one_pow]⟩⟩
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.prop.2.2.2 x x.2)⟩
  have hVO : V ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.prop.1 hV.prop.2.1 hV2
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hV.prop.2.2.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcV : c ∈ Subgroup.normalizer (V : Set G) :=
    hV.prop.2.1 (h.normalizer_le (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => h.toSec13Data.commute ha hcA)))
  have hcase_c : ∀ {U : Subgroup G}, U ∈ fourGroups A → U = ⁅U, Subgroup.zpowers c⁆ →
      U ∈ scriptQ A (lB A) → U ≤ CFSG.Open.pCoreOf 2 M → Item1712 A (lB A) :=
    fun {U} hU hUc hUQ hUM => by
      obtain ⟨Y, hY, hΔY⟩ := h.mem_scriptY3_delta_c hUQ hUM (hU4ne hU)
      exact rank3II_17_12_of_witness h h1711 hcA hc1 hU hUc hUQ hUM hY hΔY
  by_cases hVc : ⁅V, Subgroup.zpowers c⁆ = ⊥
  · rcases hmain V hV hVc with ⟨R, hR, hRc, hRQ, hRM⟩ | ⟨a, ha, ha1, hΔa, U, hU, hUa, hUQ, hUV⟩
    · exact hcase_c hR hRc hRQ hRM
    · exact rank3II_17_12_of_witness h h1711 ha ha1 hU hUa hUQ (hUV.trans hVO) hΔa le_rfl
  · obtain ⟨U, hU, hUV, hUQ⟩ := h7 V hV hVc
    have hcU : c ∈ Subgroup.normalizer (U : Set G) := (mem_fourGroups_iff.mp hU).1 hcA
    have hUc := eq_commutator_of_le_commutator (pow_three_of_std h hcA) hV2 hVab hcV hcU hUV
    have hUM : U ≤ CFSG.Open.pCoreOf 2 M :=
      hUV.trans ((Subgroup.le_normalizer_iff_commutator_le_left.mp
        (Subgroup.zpowers_le.mpr hcV)).trans hVO)
    exact hcase_c hU hUc hUQ hUM

end Item1712

end CFSG.RankThree.PartTwo.Sec17
