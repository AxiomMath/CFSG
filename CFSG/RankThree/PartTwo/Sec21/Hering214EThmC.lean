module

public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Hering214Reduce
public import CFSG.RankThree.PartTwo.Sec21.Hering214EFinal
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofList
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofU4

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem not_normalizer_le_of_mem_fourGroupsMinus
    (h211 : Item211) (h213 : Item213)
    (h215 : Item215) (h217 : Item217) (h218 : Item218) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hL3 : Item2115LThree) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hU : U ∈ fourGroupsMinus E) :
    ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
  intro hWH
  obtain ⟨a, haB, hac, X, -, haX⟩ := h215 G A E U c L hpair U hU
  have hpair' : Sec21Pair G A E U a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hU.1
      mem_pair := haX }
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hca : c ∉ Subgroup.zpowers a :=
    not_mem_zpowers_symm (hAe.2 a (hpair.mem_E.2 haB.1)) hpairs.2.1 hac
  have hcU : c ∈ Subgroup.centralizer (U : Set G) := hpairs.1.2
  exact not_isList218_of_item218 h218 hpair' (isList218_of_inf_le_normalizer h211 h213 h217 h45
    h66 hL3 hpair' hU hcA hca hcU (inf_le_right.trans hWH))

@[expose] def TripleM22E9NoInvol : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X NativeSporadic.M22 →
    ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → Nat.card F = 9 →
      ∀ t ∈ Subgroup.centralizer (F : Set (MulAut X)), t ^ 2 = 1 → t = 1

theorem mem_fourGroupsMinus_of_isTripleCover (hK : TripleM22E9NoInvol) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (h213 : Item213) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hT : Sec4.IsTripleCover (lBar L) NativeSporadic.M22) :
    U ∈ fourGroupsMinus E := by
  have hPF := Item211LieProof.pairFacts h45 h66 hpair
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := hpair.mem_E.1.1.2
  rcases Item211Res2Proof.mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hpair.mem_U with hp | hm
  · exfalso
    have hEC : E ≤ Subgroup.centralizer (U : Set G) := (mem_fourGroupsPlus_iff.mp hp).2
    obtain ⟨t, htU, ht1⟩ : ∃ t ∈ Item211Res2Proof.barImage L U, t ≠ 1 := by
      by_contra h
      push Not at h
      exact Item211LieProof.barImage_U_ne_bot hPF ((Subgroup.eq_bot_iff_forall _).mpr h)
    have ht2 : t ^ 2 = 1 := (Item211LieProof.isElemAbelian_barImage_U hPF).2 t htU
    have htC : t ∈ Subgroup.centralizer (Item211Res2Proof.barImage L E : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro σ hσ
      obtain ⟨e, he, heE, rfl⟩ := Item211Res2Proof.mem_barImage_iff.mp hσ
      obtain ⟨u, hu, huU, rfl⟩ := Item211Res2Proof.mem_barImage_iff.mp htU
      have hue : u * e = e * u := Subgroup.mem_centralizer_iff.mp (hEC heE) u huU
      have hc : (⟨e, he⟩ : Subgroup.normalizer (L : Set G)) * ⟨u, hu⟩ = ⟨u, hu⟩ * ⟨e, he⟩ :=
        Subtype.ext hue.symm
      rw [← map_mul, ← map_mul, hc]
    exact ht1 (hK (lBar L) hPF.q.1 hT (Item211Res2Proof.barImage L E)
      (Item211LieProof.isElemAbelian_barImage_E hPF) (Item211LieProof.card_barImage_E hPF)
      t htC ht2)
  · exact hm

theorem false_of_isTripleCover
    (hK : TripleM22E9NoInvol) (h211 : Item211) (h213 : Item213)
    (h215 : Item215)
    (h217 : Item217) (h218 : Item218) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hL3 : Item2115LThree) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hT : Sec4.IsTripleCover (lBar L) NativeSporadic.M22) : False :=
  not_normalizer_le_of_mem_fourGroupsMinus h211 h213 h215 h217 h218 h45 h66 hL3 hpair
    (mem_fourGroupsMinus_of_isTripleCover hK h45 h66 h213 hpair hT)
    (Item2117Proof.normalizer_le_of_isTripleCover h45 h66 hpair hT)

@[expose] def Item214Off1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ¬ Sec4.IsTripleCover (lBar L) NativeSporadic.M22 →
      ((∃ U' ∈ fourGroupsMinus E, U' ≤ L) ↔
        ¬ ∃ n : ℕ, Odd n ∧ Nonempty (L ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 n))

theorem item214_of_off1
    (hK : TripleM22E9NoInvol) (h211 : Item211) (h213 : Item213)
    (h215 : Item215)
    (h217 : Item217) (h218 : Item218) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hL3 : Item2115LThree) (hoff : Item214Off1) : Item214 := by
  intro G _ _ A E U c L hpair
  by_cases hT : Sec4.IsTripleCover (lBar L) NativeSporadic.M22
  · exact (false_of_isTripleCover hK h211 h213 h215 h217 h218 h45 h66 hL3 hpair hT).elim
  · exact hoff G A E U c L hpair hT

theorem not_isTripleCover_of_center_eq_bot {L : Subgroup G} (h : Subgroup.center (lBar L) = ⊥) :
    ¬ Sec4.IsTripleCover (lBar L) NativeSporadic.M22 := by
  rintro ⟨h3, -⟩
  rw [h, Subgroup.card_bot] at h3
  exact absurd h3 (by norm_num)

section Off1

theorem exists_pair_of_isList218_off1 (h214 : Item214Off1) (h215 : Item215)
    (hU4 : KF218NotU4) (h2114 : Item218Step214)
    {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) :
    ∃ (U₀ : Subgroup G) (b : G) (K : Subgroup G), U₀ ∈ fourGroupsMinus E ∧ U₀ ≤ L ∧
      b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G) ∧ b ∉ Subgroup.zpowers c ∧
      Sec21Pair G A E U₀ b K ∧ IsList218 K := by
  obtain ⟨U₀, hU₀, hU₀L⟩ := (h214 G A E U c L hpair (not_isTripleCover_of_center_eq_bot
    (Item2113Proof.center_lBar_eq_bot_of_isList218 hL))).mpr (hU4 G L hL)
  obtain ⟨b, hb, hbc, K, hK, hbK⟩ := h215 G A E U c L hpair U₀ hU₀
  have hpair' : Sec21Pair G A E U₀ b K :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hU₀.1
      mem_pair := hbK }
  exact ⟨U₀, b, K, hU₀, hU₀L, hb, hbc, hpair',
    h2114 G A E U c L U₀ b K hpair hL hU₀ hU₀L hb hbc hK hbK⟩

theorem item218_of_steps_off1 (h214 : Item214Off1) (h215 : Item215)
    (hU4 : KF218NotU4) (hN : Item218Normal)
    (h2114 : Item218Step214) (hF : Item218Final) : Item218 := by
  refine item218_of_not_isList218 fun G _ _ A E U c L hpair hL => ?_
  obtain ⟨U₀, b, K, hU₀, hU₀L, hb, hbc, hpair', hK⟩ :=
    exists_pair_of_isList218_off1 h214 h215 hU4 h2114 hpair hL
  exact hF G A E U c L U₀ b K hpair hL hU₀ hU₀L hpair' hK hb hbc
    (hN G A E U c L hpair hL) (hN G A E U₀ b K hpair' hK)

theorem item214Off1_of
    (h211 : Item211) (h213 : Item213)
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSpor : Hering214.Item214BarSporadic) (hLie : Hering214.Item214BarLie)
    (hL3 : Hering214.Item214BarL3) (hL45 : Hering214.Item214BarL45)
    (hA : Item214EvenThetaFacts) (hK0 : Item214EvenMultOdd) (hB : Item214EvenTypeC) :
    Item214Off1 := by
  intro G _ _ A E U c L hpair hnot
  constructor
  · intro hU' hU4
    exact item214Unitary_of_items h211 h45 h66 G A E U c L hpair hU4 hU'
  · intro hL
    have hnotU4 : ¬ ∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n) := by
      rintro ⟨n, hn, hno, ⟨e⟩⟩
      have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU le_rfl (by omega)
      have hq := h213 G A E U c L hpair
      exact hL ⟨n, hno, Item221Proof.nonempty_mulEquiv_of_center_eq_bot hq e fun e' =>
        Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hq.1 (by omega) e'⟩
    by_cases hU : U ∈ fourGroupsMinus E ∧ ∀ e ∈ E, ∃ x ∈ E ⊓ Subgroup.centralizer (U : Set G),
        ∃ y ∈ E ⊓ L, e = x * y
    · have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
      have hEA : E ≤ A := hpair.mem_E.2
      have hcA : c ∈ A := hEA hpairs.1.1
      have hc1 : c ≠ 1 := hpairs.2.1
      have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
      have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
      have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
        Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA
          hc1 L hLc
      exact ⟨U, hU.1, Item21Early3Proof.le_of_mem_fourGroupsMinus hU.1 hpairs.2.2.2.1
        (hEA.trans hAL) hU.2⟩
    · exact exists_fourGroupsMinus_of_pair h45 h66 h211 h213 hSpor hLie hL3 hL45 hpair hnotU4
        fun h81 hev => exists_fourGroupsMinus_of_even_pair h45 h66 h211 h213 hA hK0 hB hpair
          hnotU4 hU h81 hev fun _ hT _ _ _ => absurd hT hnot

end Off1

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
