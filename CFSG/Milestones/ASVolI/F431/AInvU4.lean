module

public import CFSG.Milestones.ASVolI.F431.AInv
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieStdTwo
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF
  CFSG.LieType.Universal.Unitary

section U4Lie

theorem burnsideF4m_map_equiv_symm_of_eq {X D : Type} [Group X] [Group D] (e : X ≃* D)
    {M : Subgroup X} {Q : Subgroup D} (h : Q = M.map e.toMonoidHom) :
    Q.map e.symm.toMonoidHom = M := by
  rw [h, Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem burnsideF4m_invCent_U4 {f : ℕ} (hf : 1 ≤ f) {D : Type} [Group D] [Finite D]
    (hD : CFSG.Blueprint.LieModel D .PSU 4 2 f) (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (Lift.iK A hgen).range.index) : burnsideF4m_InvCent A := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := Un.un_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  haveI := Un.isSimpleGroup_unSU hF
  haveI := Finite.of_equiv D e.symm.toEquiv
  have S1 := Un.stdTwo_datum hF ζ hf
  obtain ⟨e', hTD, hP⟩ := BN.exists_iso_of_yam (Un.unSystem hF ζ) (Un.isSylowTwoOf_unU hF) e A
  have hU : A.TD.map e'.symm.toMonoidHom = Un.unU hF 4 :=
    burnsideF4m_map_equiv_symm_of_eq e' hTD
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF4m_invCent_of_twoClassD A hgen hcen hodd
      (Lift.twoClassD_of_std A e'.symm S1 (Or.inr ⟨rfl, rfl⟩)
        (burnsideF4m_map_equiv_symm_of_eq e' h2) (burnsideF4m_map_equiv_symm_of_eq e' h1) hU)
  · exact burnsideF4m_invCent_of_twoClassD A hgen hcen hodd
      (Lift.twoClassD_of_std A e'.symm S1 (Or.inl ⟨rfl, rfl⟩)
        (burnsideF4m_map_equiv_symm_of_eq e' h1) (burnsideF4m_map_equiv_symm_of_eq e' h2) hU)

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_centInput_U4 (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hodd : Odd Gp.index)
    {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU4 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U4 hyp.model
  have hf : 1 ≤ f := hyp.model.2.1
  exact burnsideF4m_centInput_of hyp.toHypF_4_4g hTD hodd
    (fun hgen hcen hodd' => burnsideF4m_invCent_U4 hf hmodel _ hgen hcen hodd') hx1 hx2

end U4Lie

end CFSG.ASVolI
