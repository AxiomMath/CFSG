module

public import CFSG.Monster.Existence.TwoPoint.HN
public import CFSG.Monster.Existence.TwoPoint.HNTwoBConj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Spin CFSG.Monster.Visible

theorem wordLin_hnXWord : wordLin hnXWord = xmat := by
  have h : Rep4371.pauliQ (true, 0, 0) = zQ := by
    unfold Rep4371.pauliQ zQ
    congr 1
    simp [Rep4371.toSC, SpinCoord.z, Rep4371.boolZ, Rep4371.toC_zero, Rep4371.toD_zero]
  show wordLin [Native.Gen.rho (true, 0, 0)] = xmat
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho, h, rhoEquiv_zQ, xmat_eq_xB]

theorem hnMkW_hnXWord : hnMkW hnXWord = xGriess := Subtype.ext wordLin_hnXWord

@[expose] noncomputable def hnW : MGriess := hnE 3 * hnE 0

theorem hnW_eq : hnW = hnMkW hnWW := by
  rw [hnW, hnWW]
  have e : hnMkW (hnWU[0]! ++ hnWU[3]!) = hnMkW hnWU[3]! * hnMkW hnWU[0]! :=
    hnMkW_append _ _
  rw [e]
  rfl

theorem hnW_mem_cent2 :
    hnW ∈ cent2 hnAlpha hnBeta :=
  Subgroup.mul_mem _ (hnE_mem_cent2 (by norm_num)) (hnE_mem_cent2 (by norm_num))

theorem isConj_xGriess_hnW :
    IsConj xGriess hnW := by
  have h := hn_wordLin_twoB hnTwoBCheck_ok
  have h' : hnMkW hnCW * xGriess = hnW * hnMkW hnCW := by
    rw [← hnMkW_hnXWord, hnW_eq]
    exact Subtype.ext h
  exact isConj_iff.2 ⟨hnMkW hnCW, by rw [h', mul_inv_cancel_right]⟩

theorem exists_hn_two_point' :
    ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧
    orderOf (α * β) = 5 ∧ IsConj xGriess w ∧ w ∈ cent2 α β ∧
      ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
        Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.HN) := by
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have hP : TauCeti.SporadicName.HN.presentation = TauCeti.Sporadic.hnPresentation := rfl
  have hrel : TauCeti.SporadicName.HN.presentation.relatorLetters =
      CFSG.Sporadic.Bridge.SurjD.Native.hnRels := by
    rw [hP]
    exact CFSG.Sporadic.Bridge.HN.relatorLetters_eq
  have hgen : TauCeti.SporadicName.HN.presentation.generatorCount = 5 := by
    rw [hP]
    simp [TauCeti.GroupPresentation.generatorCount]
  have : IsSimpleGroup TauCeti.SporadicName.HN.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HN.isSimpleGroup_HN ψ.symm
  exact ⟨hnAlpha, hnBeta, hnW, isConj_alpha, isConj_beta, orderOf_alpha_mul_beta,
    isConj_xGriess_hnW, hnW_mem_cent2, (hnHom _ hrel).range, range_hnHom_le _ hrel hgen,
    ⟨(MonoidHom.ofInjective (hnHom_injective _ hrel hgen)).symm.trans ψ.symm⟩⟩

end CFSG.Monster.Existence
