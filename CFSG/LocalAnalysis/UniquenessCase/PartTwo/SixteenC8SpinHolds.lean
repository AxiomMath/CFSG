module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinAt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinForm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinG2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinStabS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinUniq
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinPtCent
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.G10Four
public import CFSG.Quasithin.Background.G10Three
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.A38c8Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S143EB
public import CFSG.Quasithin.EmptyFaithful.S143VG94
public import CFSG.Quasithin.EmptyFaithful.S143VQG
public import CFSG.Quasithin.EmptyFaithful.S143VTwo
public import CFSG.Quasithin.EmptyFaithful.S143VZU
public import CFSG.Quasithin.EmptyFaithful.S143WAL
public import CFSG.Quasithin.EmptyFaithful.S143WCl
public import CFSG.Quasithin.EmptyFaithful.S143WE
public import CFSG.Quasithin.EmptyFaithful.S143WT
public import CFSG.Quasithin.EmptyFaithful.S151WE
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151ZF
public import CFSG.Quasithin.EmptyFaithful.S151ZH
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.EmptyFaithful.S153DInputs
public import CFSG.Quasithin.EmptyFaithful.S153Five
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.SzN28Solv
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Quasithin.Recognition.RuTypeDefs
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabInputs
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LieType.SpinGeom CFSG.LieType.D4Small
open CFSG.StandardType CFSG.StandardType.Triality
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem spinW_exp_rk : (∀ w : SpinW, w ^ 2 = 1) ∧ rk ↥(⊤ : Subgroup SpinW) = 8 := by
  constructor
  · intro w
    apply Multiplicative.ext
    rw [toAdd_pow, toAdd_one]
    exact CharTwo.two_nsmul _
  · rw [rk_top]
    unfold rk
    have h : Nat.card SpinW = 2 ^ 8 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rw [h]
    exact padicValNat.prime_pow 8

theorem spinCentAt_spinH : SpinCentAt SpinW spinH := spinCent

theorem spinFormAt_spinH : SpinFormAt SpinW spinH := exists_plusQuad_spinH

theorem spinStabAt_spinH :
    SpinStabAt SpinW spinH := by
  intro Q hQ hinv
  obtain rfl : Q = spinQ :=
    quad_unique_of_cent_irr spinH spinCent spinH_irr hQ.1 spinQ_isPlus.1 hinv spinQ_invariant
  constructor
  · intro w hw hQw
    have hw' : Multiplicative.toAdd w ≠ 0 := by
      intro h
      exact hw (by rw [← ofAdd_toAdd w, h, ofAdd_zero]; rfl)
    have hQ' : coordinateQuadPlus 4 (ZMod 2) (Multiplicative.toAdd w) = 0 := hQw
    obtain ⟨h, hh, hact⟩ :=
      spinSeven_transitive (ZMod 2) (Multiplicative.toAdd w) hw' hQ'
    have hg : spinHom h ∈ spinH := (mem_spinH_iff _).2 ⟨h, hh, rfl⟩
    have hgw : spinHom h (Multiplicative.ofAdd (frameE (ZMod 2) 0)) = w := by
      rw [spinHom_apply]
      simp only [toAdd_ofAdd]
      rw [hact, ofAdd_toAdd]
    obtain ⟨e⟩ := nonempty_ptCent_mulEquiv_of_orbit (H := spinH)
      (w := Multiplicative.ofAdd (frameE (ZMod 2) 0)) (w' := w) ⟨spinHom h, hg, hgw⟩
    exact isE64L3_of_equiv e.symm isE64L3_ptCent_E0
  · intro w hw
    obtain ⟨e⟩ := nonempty_spinSeven_mulEquiv (ZMod 2)
    let ι : ↥(ptCent spinH w) →* ↥(StatedSp 3 (ZMod 2)) :=
      e.toMonoidHom.comp (spinHEquiv.symm.toMonoidHom.comp
        (Subgroup.inclusion (show ptCent spinH w ≤ spinH from inf_le_left)))
    have hι : Function.Injective ι := by
      change Function.Injective (⇑e ∘ ⇑spinHEquiv.symm ∘ ⇑(Subgroup.inclusion
        (show ptCent spinH w ≤ spinH from inf_le_left)))
      exact e.injective.comp (spinHEquiv.symm.injective.comp
        (Subgroup.inclusion_injective
          (show ptCent spinH w ≤ spinH from inf_le_left)))
    exact isG2Two_of_card_sp6 ι hι (card_ptCent_nonsing hw)

theorem rSp6SpinCent_holds (hU : RSp6SpinUnique) : RSp6SpinCent := by
  intro W _ _ hW H hH hrk hirr
  obtain ⟨α, φ, hφ⟩ := hU W SpinW hW spinW_exp_rk.1 H spinH hH isSpn_spinH hrk spinW_exp_rk.2
    hirr spinH_irr
  exact spinCentAt_of_equivariant (α := α) (φ := φ) hφ spinCentAt_spinH

theorem rSp6SpinForm_holds (hU : RSp6SpinUnique) : RSp6SpinForm := by
  intro W _ _ hW H hH hrk hirr
  obtain ⟨α, φ, hφ⟩ := hU W SpinW hW spinW_exp_rk.1 H spinH hH isSpn_spinH hrk spinW_exp_rk.2
    hirr spinH_irr
  exact spinFormAt_of_equivariant (α := α) (φ := φ) hφ spinFormAt_spinH

theorem rSp6SpinStab_holds
    (hU : RSp6SpinUnique) : RSp6SpinStab := by
  intro W _ _ hW H hH hrk hirr
  obtain ⟨α, φ, hφ⟩ := hU W SpinW hW spinW_exp_rk.1 H spinH hH isSpn_spinH hrk spinW_exp_rk.2
    hirr spinH_irr
  exact spinStabAt_of_equivariant (α := α) (φ := φ) hφ spinStabAt_spinH

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
