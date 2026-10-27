module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Pair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3WInner
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ATwoConj
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_bb2bababba_parabolic_factors
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    (hsig : D.sig = {3}) :
    ∃ P Q : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      P ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧
      Q ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧
      Nat.card ↥P = 24 ∧ Nat.card ↥Q = 24 ∧
      (∀ p ∈ P, p ^ 12 = 1) ∧ (∀ q ∈ Q, q ^ 12 = 1) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧
      P ⊓ Q = ⊥ ∧
      barSub ⊥ V h.hyp151.isElemAbelian D.T ≤
        Subgroup.normalizer ((P ⊔ Q : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
          Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
  have hV := h.hyp151.isElemAbelian
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (barSub ⊥ V hV D.T) (Mbar D.M ⊥ V hV) := by
    have hMs : D.M ≤ stabTil ⊥ V :=
      le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
        h.hyp151.hyp125.pairFacts.le_normalizer₀
    exact s16c7_isSylowOf_barSub (p := 2) ⊥ V hV D.sylowM hMs
  have hVt : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  obtain ⟨⟨ψ, hψ, hψne⟩, hψprop⟩ :=
    c23a_two_conj (Mb := Mbar D.M ⊥ V hV) (L := lBar ⊥ V hV L) hs2
  have hconj : ∀ a ∈ Mbar D.M ⊥ V hV,
      (lBar ⊥ V hV L).map (MulAut.conj a).toMonoidHom = lBar ⊥ V hV L ∨
        (lBar ⊥ V hV L).map (MulAut.conj a).toMonoidHom =
          (lBar ⊥ V hV L).map (MulAut.conj ψ).toMonoidHom :=
    (hψprop ψ hψ hψne).1
  have hL₂ : ∃ a ∈ Mbar D.M ⊥ V hV,
      (lBar ⊥ V hV L).map (MulAut.conj a).toMonoidHom =
        (lBar ⊥ V hV L).map (MulAut.conj ψ).toMonoidHom :=
    ⟨ψ, hψ, rfl⟩
  have hcomm : ∀ x ∈ lBar ⊥ V hV L,
      ∀ y ∈ (lBar ⊥ V hV L).map (MulAut.conj ψ).toMonoidHom, x * y = y * x := by
    have han : ψ ∉ normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
      intro hmem
      exact hψne (Subgroup.mem_normalizer_iff_map_conj_eq.1 hmem)
    have hbot := (hW.2.1 ψ hψ han).1
    intro x hx y hy
    have hx' : x ∈ Subgroup.centralizer
        ((lBar ⊥ V hV L).map (MulAut.conj ψ).toMonoidHom : Set
          (MulAut (Vtil ⊥ V hV))) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot) hx
    exact (Subgroup.mem_centralizer_iff.1 hx' y hy).symm
  exact s16h_e3_l3_two_parabolics_of_inner hT hL3.1 hcomp.1 hconj hL₂ hψne hcomm
    (fun τ _ hτ => s16h_e3_l3_normalizer_inner hVt hL3 hτ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
