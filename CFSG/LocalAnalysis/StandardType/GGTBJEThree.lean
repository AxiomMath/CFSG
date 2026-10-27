module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTBJEThree_n_eq {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (h1 : ¬ (lab.tag = .twD ∧ lab.rank = 2)) (h2 : ¬ (lab.tag = .A ∧ lab.rank = 1)) :
    lab'.n = lab.n := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  unfold GGLabelIso at h
  simp only at h1 h2 ⊢
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggTBJLeftOn_eThree (hRig : GGLabelRigidInput) : GGTBJLeftOn ggTBJEThreeLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX
  exfalso
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨lab₁, hΛ₁, hhas₁, R₁, _, I₁, F₁, θ₁, hP₁⟩ := largeEvenMarking_exists_hasLabel hst.1
  have hiso : GGLabelIso lab lab₁ := hRig lab lab₁ _ hΛ hΛ₁ hhas hhas₁
  have hn : lab₁.n = lab.n := ggTBJEThree_n_eq hiso hP.1.2.2.1 hP.1.2.2.2
  have h2 : p ∣ 4 ^ lab₁.n - 1 := ggLabPhiOneTwo_of_largeEvenSplit hP₁.1
  rw [hn] at h2
  exact hP.1.1 h2

theorem ggTBJNbrOn_eThree (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) : GGTBJNbrOn ggTBJEThreeLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hK hX
  exfalso
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hHS := ggNbr_halfSplit_of_hyp hraw hiso hH.1 hnb hInnK
  obtain ⟨lab', hΛ', hhas', R', _, I', F', θ', hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have hisoL : GGLabelIso lab lab' := hRig lab lab' _ hΛ hΛ' hhas hhas'
  rcases largeEvenHalfSplit_dvd hΛ' hHSlab with hdvd | ⟨hp7, hex⟩
  · have hn : lab'.n = lab.n := ggTBJEThree_n_eq hisoL hP.1.2.2.1 hP.1.2.2.2
    have h4 : (2 ^ lab'.n) ^ 2 = 4 ^ lab'.n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4, hn] at hdvd
    exact hP.1.1 hdvd
  · have heq : lab = lab' := eq_of_ggLabelIso_of_exc hex hisoL
    exact hP.1.2.1 ⟨hp7, heq ▸ hex⟩

@[expose] def GGTBJOrderRestSplitAUnitSpPlusEThreeInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab

theorem ggTBJOrderRestSplitAUnitSpPlus_of_restEThree (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (h : GGTBJOrderRestSplitAUnitSpPlusEThreeInput) : GGTBJOrderRestSplitAUnitSpPlusInput :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_eThree hRig) (ggTBJNbrOn_eThree hRig hraw hiso) h

end CFSG.StandardType

end
