module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.RankThree.SteinbergR3ELargeEvenLinearTwoCover
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.OddTranspositions.PartFour

private noncomputable def psl2ModelEquivSL2OfCard {f : ℕ} (hf : 0 < f) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ f) :
    CFSG.Theory.Comparator.PSL2Model f ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  (CFSG.RankThree.projectiveSpecialLinearTwoEquivSLOfCharTwo (GaloisField 2 f)).trans
    (CFSG.ClassicalModels.specialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 f hf hF).symm (Fin 2))

private noncomputable def l2WreathEquivWreathSymOfCard {f : ℕ} (hf : 0 < f) (m : ℕ) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ f) :
    CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f m ≃*
      CFSG.LocalAnalysis.WeakClosure81.WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m :=
  SemidirectProduct.congr (MulEquiv.piCongrRight fun _ => psl2ModelEquivSL2OfCard hf hF)
    (MulEquiv.refl _) (fun σ => by ext h i; rfl)

theorem nonempty_mulEquiv_psl2Model_of_isSymplecticTransvection_two {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {f : ℕ} (hf : 2 ≤ f) {s : X}
    (h : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsSymplecticTransvection X 2 f s) :
    Nonempty (X ≃* CFSG.Theory.Comparator.PSL2Model f) := by
  obtain ⟨k, hk, F, hF, hFin, hcard, e, -⟩ := h
  obtain rfl : k = 1 := by omega
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (e.trans ((CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F).symm.trans
      (psl2ModelEquivSL2OfCard (by omega) hcard).symm))⟩

theorem isBenderGroup_of_isSymplecticTransvection_two {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {f : ℕ} (hf : 2 ≤ f) {s : X}
    (h : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsSymplecticTransvection X 2 f s) :
    CFSG.BenderSuzuki.IsBenderGroup X :=
  let ⟨e⟩ := nonempty_mulEquiv_psl2Model_of_isSymplecticTransvection_two hZ hf h
  .isPSL2 f hf e

theorem nonempty_mulEquiv_l2Wreath_of_isWreathTransposition {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {f m : ℕ} {s : X}
    (h : CFSG.LocalAnalysis.WeakClosure81.IsWreathTransposition X f m s) :
    Nonempty (X ≃* CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f m) := by
  obtain ⟨hf, F, hF, hFin, hcard, e, -⟩ := h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (e.trans (l2WreathEquivWreathSymOfCard (by omega) m hcard).symm)⟩

end CFSG.OddTranspositions.PartFour
