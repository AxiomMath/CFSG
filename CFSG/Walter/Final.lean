module

public import CFSG.Walter.Bender1970
public import CFSG.Walter.W67.Corollary
public import CFSG.Walter.Models
public import CFSG.Walter.ReeOrder.JTFinal
public import CFSG.Walter.Statement
public import CFSG.Walter.J1Recog.Main

public section

namespace CFSG.Walter

open scoped MatrixGroups

@[expose] def ReeIdentHyp : Prop := ∀ (G : Type) [Group G] [Finite G], Ward.ReeTypeHyp G →
  ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Models.LieModel G .twistedG2 0 3 f

theorem walter_structure
    (hJ : JRStrongHyp) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) (hP : IsMulCommutative (P : Subgroup G)) :
    IsTypeL2 G ∨ Nonempty (Ward.ReeTypeHyp G) ∨ Nonempty (G ≃* CFSG.Open.walterJ1) := by
  have hab : HasAbelianSylowTwo G := hasAbelianSylowTwo_of_sylow P hP
  have hSC := simpleCaseHyp_of_benderHyp benderHyp
  rcases hSC G inferInstance hnonab hab
      (fun H _ => isAStar_of_hasAbelianSylowTwo hSC (hab.subgroup H)) with hL2 | hJR
  · exact Or.inl hL2
  · exact Or.inr (hJ G hJR hnonab)

theorem j1RecogHyp : J1RecogHyp := fun _ _ _ h => J1Recog.nonempty_mulEquiv_walterJ1 h

theorem jrStrongHyp_of_open
    (hT : W67.Theorem) (hJ1 : J1RecogHyp) (hJT : JTThreeHyp) :
    JRStrongHyp :=
  jrStrongHyp_of (W67.walter67Hyp_of_theorem hT) hJ1 hJT

theorem walter_order_form_of
    (hT : W67.Theorem) (hJ1 : J1RecogHyp) (hJT : JTThreeHyp) :
    WalterOrderForm :=
  walter_order_form benderHyp (jrHyp_of_jrStrongHyp (jrStrongHyp_of_open hT hJ1 hJT))

theorem walter_models_form_of
    (hT : W67.Theorem) (hJ1 : J1RecogHyp) (hJT : JTThreeHyp)
    (hR : ReeIdentHyp) :
    WalterModelsTauCeti := by
  intro G _ _ _ hnonab P hP
  rcases walter_structure (jrStrongHyp_of_open hT hJ1 hJT) G hnonab P hP with hL2 | hR' | hJ
  · rcases hL2 with ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩
    · have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      exact Or.inl ⟨f, hf, lieModel_psl_two_of_mulEquiv 2 f h4 e⟩
    · refine Or.inr (Or.inl ⟨p, f, hp.out, ?_, hf, h5, h8,
        lieModel_psl_two_of_mulEquiv p f (by omega) e⟩)
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  · obtain ⟨hR'⟩ := hR'
    obtain ⟨f, hfo, hf3, hm⟩ := hR G hR'
    exact Or.inr (Or.inr (Or.inl ⟨f, hfo, hf3, hm⟩))
  · obtain ⟨e⟩ := hJ
    exact Or.inr (Or.inr (Or.inr (isSporadic_J1_of_mulEquiv e)))

theorem walter_order_form_of'
    (hT : W67.Theorem) (hJT : JTThreeHyp) :
    WalterOrderForm :=
  walter_order_form_of hT j1RecogHyp hJT

theorem walter_models_form_of'
    (hT : W67.Theorem) (hJT : JTThreeHyp) (hR : ReeIdentHyp) :
    WalterModelsTauCeti :=
  walter_models_form_of hT j1RecogHyp hJT hR

theorem walter_order_form_of_W67
    (hT : W67.Theorem) :
    WalterOrderForm :=
  walter_order_form_of' hT jtThreeHyp

theorem walter_models_form_of_W67
    (hT : W67.Theorem) (hR : ReeIdentHyp) :
    WalterModelsTauCeti :=
  walter_models_form_of' hT jtThreeHyp hR

end CFSG.Walter
