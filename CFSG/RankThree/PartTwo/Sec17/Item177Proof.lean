module

public import CFSG.RankThree.PartTwo.Sec17.Item172Proof
public import CFSG.RankThree.PartTwo.Sec6.Item641
public import Certificates.Certificate3029
public import Certificates.Certificate3086
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Certificates.Certificate2326
public import Certificates.Certificate3139
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.RankThree.PartTwo.Sec5.Hyp
import CFSG.Sporadic.J2
import CFSG.Sporadic.Schreier.MathieuOddCoreModel
import CFSG.Sporadic.Schreier.MathieuOddCoreWords
import CFSG.Sporadic.Th.F2Spec
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] noncomputable def Step177Meet : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Y₀⁆ ≠ ⊥ → V ⊓ Y₀ ∈ scriptQ A (lB A) ∧ ⁅V ⊓ Y₀, A⁆ ≠ ⊥

namespace Proof177

variable {G : Type} [Group G] [Finite G]

theorem eq_of_card_le_two {W : Subgroup G} (hW : Nat.card W ≤ 2) {x y : G} (hx : x ∈ W)
    (hy : y ∈ W) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  set s : Finset G := {1, x, y} with hs
  have hscard : s.card = 3 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx1, Ne.symm hy1⟩
  have hsub : (s : Set G) ⊆ (W : Set G) := by
    intro z hz
    simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    exacts [one_mem W, hx, hy]
  have hle : (s : Set G).ncard ≤ (W : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hscard, ← Nat.card_coe_set_eq] at hle
  change 3 ≤ Nat.card W at hle
  omega

theorem exists_mem_fourGroupsMinus_le {A W : Subgroup G} (hA : IsE27 A)
    (hW : CFSG.Assembly.IsElemAbelian 2 W) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hWA : ⁅W, A⁆ ≠ ⊥) : ∃ U ∈ fourGroupsMinus A, U ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W₀ := ⁅W, A⁆ with hW₀def
  have hW₀W : W₀ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hAW
  have hW₀ : CFSG.Assembly.IsElemAbelian 2 W₀ := Sec5.isElemAbelian_of_le hW hW₀W
  have hAW₀ : A ≤ Subgroup.normalizer (W₀ : Set G) := by
    rw [hW₀def, Subgroup.commutator_comm]
    exact Subgroup.normalizer_commutator_ge_left A W
  have hW2 : IsPGroup 2 W := Sec5.isPGroup_of_isElemAbelian hW
  have hcop : Nat.Coprime (Nat.card A) (Nat.card W) := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hA.2, hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hfit : W₀ ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    rw [hW₀def, Subgroup.commutator_comm]
    exact CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot
      (fun x hx y hy => congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hAW hcop
  have hW₀4 : 4 ≤ Nat.card W₀ := by
    obtain ⟨k, hk⟩ := (hW2.to_le hW₀W).exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      apply hWA
      have hcard : Nat.card W₀ ≤ 2 := by
        rw [hk]
        calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      have hle : W₀ ≤ Subgroup.centralizer (A : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hax : a * x * a⁻¹ ∈ W₀ := (Subgroup.mem_normalizer_iff.mp (hAW₀ ha) x).mp hx
        by_cases hx1 : x = 1
        · rw [hx1, mul_one, one_mul]
        · have hax1 : a * x * a⁻¹ ≠ 1 := fun h1 => hx1 (by
            have := congrArg (fun y => a⁻¹ * y * a) h1
            simpa [mul_assoc] using this)
          have heq : a * x * a⁻¹ = x := eq_of_card_le_two hcard hax hx hax1 hx1
          calc a * x = a * x * a⁻¹ * a := by group
            _ = x * a := by rw [heq]
      have hbot : W₀ = ⊥ := by rw [← inf_eq_left.mpr hle, hfit]
      exact hbot
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  obtain ⟨U, hU, hUW₀⟩ := Sec6.exists_mem_fourGroups_le hA.1 hA.2 hW₀ hW₀4 hAW₀
  refine ⟨U, ⟨hU, ?_⟩, hUW₀.trans hW₀W⟩
  have hU2 : IsPGroup 2 U := Sec5.isPGroup_of_isElemAbelian hU.2.1
  have hU3 : ¬ 3 ∣ Nat.card U := by rw [hU.2.2]; norm_num
  have hdec := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three A U hA.isPGroup hU3 hU.1.2.2
  have hC : U ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right _ hUW₀
  rw [hC, sup_bot_eq] at hdec
  exact hdec

theorem le_M_of_isTwoLocal {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {K : Subgroup G} (hK : CFSG.Assembly.IsTwoLocal K)
    (hYK : Y₀ ⊔ A ≤ K) : K ≤ Subgroup.normalizer (Y₀ : Set G) := by
  obtain ⟨M', hM', hle⟩ := exists_mem_scriptM_of_isTwoLocal hK (SetLike.coe_subset_coe.mpr hYK)
  change M' ∈ CFSG.maximalTwoLocalsContaining _ at hM'
  rw [h.scriptM_eq] at hM'
  rw [← Set.mem_singleton_iff.mp hM']
  exact hle

theorem isTI_of_centralizes {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hV2 : IsPGroup 2 V) (hcen : Y₀ ⊔ A ≤ Subgroup.centralizer (V : Set G)) :
    ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V ⊓ V.map (MulAut.conj g).toMonoidHom = V := by
  intro g
  by_cases hD : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥
  · exact Or.inl hD
  refine Or.inr ?_
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  obtain ⟨w, hwV, hwv⟩ := (Subgroup.mem_inf.mp hv).2
  have hwv' : g * w * g⁻¹ = v := hwv
  have hw1 : w ≠ 1 := fun h1 => hv1' (by rw [← hwv', h1, mul_one, mul_inv_cancel])
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers w : Set G)) := by
    refine ⟨Subgroup.zpowers w, fun hbot => hw1 ?_, hV2.to_le (Subgroup.zpowers_le.mpr hwV), rfl⟩
    have : w ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers w
    exact Subgroup.mem_bot.mp this
  have hCw : ∀ x ∈ Y₀ ⊔ A, x * w = w * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hcen hx) w hwV).symm
  have hYw : Y₀ ⊔ A ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) := fun x hx =>
    Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (hCw x hx))
  have hNw : Subgroup.normalizer (Subgroup.zpowers w : Set G) ≤ M := le_M_of_isTwoLocal h hloc hYw
  have hYMg : Y₀ ⊔ A ≤ M.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    refine ⟨g⁻¹ * x * g, hNw (Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
      (Subgroup.mem_centralizer_singleton_iff.mpr ?_)), by simp [mul_assoc]⟩
    have hxv : x * v = v * x := (Subgroup.mem_centralizer_iff.mp (hcen hx) v
      (Subgroup.mem_inf.mp hv).1).symm
    rw [← hwv'] at hxv
    calc g⁻¹ * x * g * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [hxv]
      _ = w * (g⁻¹ * x * g) := by group
  have hMmax : CFSG.IsMaximalTwoLocal M := (Proof172.mem_scriptM_of_std h).1
  have hMg : M.map (MulAut.conj g).toMonoidHom = M := by
    have hmem : M.map (MulAut.conj g).toMonoidHom ∈
        CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) :=
      ⟨isMaximalTwoLocal_map hMmax (MulAut.conj g), SetLike.coe_subset_coe.mpr hYMg⟩
    rw [h.scriptM_eq] at hmem
    exact hmem
  have hgM : g ∈ M := mem_of_map_conj_eq_of_isMaximalTwoLocal hMmax hMg
  rw [Late.map_conj_eq_of_mem_normalizer (hMV hgM), inf_idem]

end Proof177

section Item177

variable {G : Type} [Group G] [Finite G]

open Proof177 in
theorem rank3II_17_7_one_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h310 : Sec6.Item3_10) {V : Subgroup G}
    (hV : Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 V) V) :
    ⁅Y₀ ⊔ A, V⁆ ≠ ⊥ := by
  intro hbot
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  obtain ⟨-, hMV, hVab⟩ := hV.prop
  exact h.not_inCatalog (h310 G h.isSimpleGroup h.nonabelian h.kProper h.charTwoType _
    (Proof172.mem_scriptM_of_std h).1 V hV
    (isTI_of_centralizes h hMV (Sec5.isPGroup_of_isElemAbelian hVab) hcen))

end Item177

end CFSG.RankThree.PartTwo.Sec17
