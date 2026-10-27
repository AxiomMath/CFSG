module

public import CFSG.Quasithin.EmptyFaithful.SBc14Call

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem jFacts (h5 : Stage1461Five) (h38 : A38ForSQTK) (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hctx : Ctx15 T M H p H₁) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hG₂ : ¬ g2_14615 K₂ ≤ mcOf T) {J : Subgroup G} (hJc : J ∈ cComp (g2_14615 K₂))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hJle : ¬ J ≤ g12_14615 T K₂) :
    K₁ ≤ Subgroup.normalizer (J : Set G) ∧ K₂ ≤ Subgroup.normalizer (J : Set G) ∧
      ⁅J, K₂⁆ ≤ pCoreOf 2 J ∧ pCoreOf 2 J ≤ mcOf T ∧ ∃ k ∈ K₂, orderOf k = 5 := by
  obtain ⟨hHyp, -, hPcore⟩ := SBc14.callSite_facts h5 S hred hmax hdec hctx hset hG₂
  have hp5 : p = 5 := hctx.1
  have hp : p.Prime := hred.prime
  have hX : SQTKGroup ↥(g2_14615 K₂) := hHyp.sqtk
  have hK₂G₁ : K₂ ≤ mcOf T := hset.le_mcOf S hred
  have hK₂X : K₂ ≤ g2_14615 K₂ := Subgroup.le_normalizer
  have hK₂₁₂ : K₂ ≤ g12_14615 T K₂ := le_inf hK₂G₁ hK₂X
  have hJK₂ : ¬ J ≤ K₂ := fun h => hJle (h.trans hK₂₁₂)
  have hK₂N : K₂ ≤ Subgroup.normalizer (J : Set G) :=
    SBc13.normalizer_le_of_normal_of_not_le hK₂X le_rfl hJc hJK₂
  have hK₂c : ⁅J, K₂⁆ ≤ pCoreOf 2 J :=
    SBc13.commutator_le_pCore_of_normal hK₂X le_rfl hJc hJq hJK₂
  have hKz5 : K₁ ⊔ K₂ ≤ Subgroup.closure {x | x ∈ K₁ ⊔ K₂ ∧ orderOf x = 5} := by
    have := kz_le_closure_five_14615 S hdec hp5 hset
    rwa [hset.kz] at this
  have hKodd : K₁ ⊔ K₂ ≤ oTwoUpper (K₁ ⊔ K₂) :=
    hKz5.trans ((Subgroup.closure_le _).mpr fun x hx =>
      Subgroup.subset_closure ⟨hx.1, by rw [hx.2]; decide⟩)
  have hKzG₂ : K₁ ⊔ K₂ ≤ g2_14615 K₂ := by
    rw [← hset.kz]
    exact kz_le_g2_14615 hdec hset
  have hKzN : K₁ ⊔ K₂ ≤ Subgroup.normalizer (J : Set G) :=
    SBc13.le_normalizer_of_odd_gen h38 hX hJc hKzG₂ hKodd
  refine ⟨le_sup_left.trans hKzN, hK₂N, hK₂c,
    (SBc13.pCoreOf_le_pCoreOf_of_subnormal hJc).trans (hPcore.trans inf_le_left), ?_⟩
  obtain ⟨k, hkK, hk5'⟩ := hdec.swap.exists_order_p_P14 hp hred.odd
  exact ⟨k, hset.oTwo₂ hkK, by rw [hk5', hp5]⟩

end SBc17

end CFSG.Quasithin
