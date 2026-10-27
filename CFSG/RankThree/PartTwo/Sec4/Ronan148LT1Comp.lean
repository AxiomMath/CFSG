module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LOrder3
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev)

theorem three_dvd_card_of_lie (hb : LieOrderBridge) {X : Type} [Group X] [Finite X]
    (d : TauCeti.ValidLieTypeIndex) (hsz : ∀ m, d.1 ≠ .suzuki m)
    (he : Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) : 3 ∣ Nat.card X := by
  rw [hb d X he]
  exact three_dvd_lieOrderFormula d.2 hsz

theorem three_dvd_card_of_isChevSimple (hb : LieOrderBridge) {q : ℕ} (hq2 : q ≠ 2) {X : Type}
    [Group X] [Finite X] (h : IsChevSimple q X) : 3 ∣ Nat.card X := by
  rcases h with ⟨i, hi, hf⟩ | ⟨i, hi, hf⟩
  · cases i with
    | lie d =>
      refine three_dvd_card_of_lie hb d (fun m hm => hq2 ?_) hf
      have hc : d.1.characteristic = q := hi
      rw [hm] at hc
      simpa using hc.symm
    | _ => exact False.elim hi
  · cases i with
    | lie d =>
      refine three_dvd_card_of_lie hb d (fun m hm => ?_) hf
      have hi' : ambiguousChev q (.lie d) := hi
      simp only [ambiguousChev, hm] at hi'
    | alternating n hn =>
      obtain ⟨f⟩ := hf
      rw [Nat.card_congr f.toEquiv]
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        decide
    | _ => exact False.elim hi

theorem layer_three_of_comps (hb : LieOrderBridge) {q : ℕ} (hq2 : q ≠ 2) {S : Type} [Group S]
    [Finite S] {β : MulAut S} (h : LieCompsExport q β) :
    PerfectInLayer β ∧ ∀ J : Subgroup S, CFSG.Open.IsComponentOf J (fixSubgroup β) →
      3 ∣ Nat.card J := by
  refine ⟨h.layer, fun J hJ => ?_⟩
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps J hJ
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hfk
  have h3 : 3 ∣ Nat.card (X ⧸ Subgroup.center X) :=
    three_dvd_card_of_isChevSimple hb hq2 hX.chev
  rw [Nat.card_congr e.toEquiv] at h3
  exact h3.trans (Subgroup.card_quotient_dvd_card _)

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
