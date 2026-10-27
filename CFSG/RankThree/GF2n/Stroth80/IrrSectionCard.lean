module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv15

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

theorem exists_irr_section_card {G : Type} [Group G] (hG : Group.IsPerfect G) :
    ∀ (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : G →* GLV M), Module.finrank (ZMod 2) M = N → (∃ g, ρ g ≠ 1) →
      ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module (ZMod 2) Y) (_ : Finite Y)
        (σ : G →* GLV Y), Module.finrank (ZMod 2) Y ≤ N ∧ (∃ g, σ g ≠ 1) ∧
          IsIrr σ.range ⊤ ∧ (Module.finrank (ZMod 2) Y = N → IsIrr ρ.range ⊤) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro M _ _ _ ρ hN hρ
    by_cases hirr : IsIrr ρ.range ⊤
    · exact ⟨M, inferInstance, inferInstance, inferInstance, ρ, hN.le, hρ, hirr,
        fun _ => hirr⟩
    · have hMnt : Nontrivial M := by
        obtain ⟨g, hg⟩ := hρ
        by_contra hM
        rw [not_nontrivial_iff_subsingleton] at hM
        exact hg (LinearEquiv.ext fun x => Subsingleton.elim _ _)
      have hbt : (⊥ : Submodule (ZMod 2) M) < ⊤ := by
        have := (Submodule.nontrivial_iff (ZMod 2)).2 hMnt
        exact bot_lt_top
      have hinvtop : Invariant ρ.range (⊤ : Submodule (ZMod 2) M) :=
        fun _ _ _ _ => Submodule.mem_top
      obtain ⟨J, hJinv, hJ⟩ : ∃ J : Submodule (ZMod 2) M, Invariant ρ.range J ∧ J ≠ ⊥ ∧ J ≠ ⊤ := by
        by_contra hcon
        push Not at hcon
        refine hirr ⟨hinvtop, hbt, fun J hJ _ _ => ?_⟩
        by_cases hJb : J = ⊥
        · exact Or.inl hJb
        · exact Or.inr (hcon J hJ hJb)
      have hJle : Module.finrank (ZMod 2) J < N := by
        rw [← hN]; exact Submodule.finrank_lt hJ.2
      have hsum := Submodule.finrank_quotient_add_finrank J
      have : Finite (M ⧸ J) := Quotient.finite _
      have hJpos : 0 < Module.finrank (ZMod 2) J := by
        have : Module.Finite (ZMod 2) J := Module.Finite.of_finite
        have : Nontrivial J := Submodule.nontrivial_iff_ne_bot.2 hJ.1
        exact Module.finrank_pos
      have hQlt : Module.finrank (ZMod 2) (M ⧸ J) < N := by omega
      let σ₁ : G →* GLV J :=
        (CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.restrictHom
          ρ.range J hJinv).comp ρ.rangeRestrict
      let σ₂ : G →* GLV (M ⧸ J) :=
        (CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.quotientHom
          ρ.range J hJinv).comp ρ.rangeRestrict
      have hσ₁ : ∀ g (j : J), ((σ₁ g j : J) : M) = ρ g j := fun g j => by
        simp [σ₁, CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.restrictHom_apply]
      have hσ₂ : ∀ g (x : M), σ₂ g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
        fun g x => by
          simp [σ₂, CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.quotientHom_apply]
      by_cases h1 : ∃ g, σ₁ g ≠ 1
      · obtain ⟨Y, i1, i2, i3, σ, h1', h2', h3', -⟩ := ih _ hJle J σ₁ rfl h1
        exact ⟨Y, i1, i2, i3, σ, h1'.trans hJle.le, h2', h3', fun h => absurd h (by omega)⟩
      by_cases h2 : ∃ g, σ₂ g ≠ 1
      · obtain ⟨Y, i1, i2, i3, σ, h1', h2', h3', -⟩ := ih _ hQlt (M ⧸ J) σ₂ rfl h2
        exact ⟨Y, i1, i2, i3, σ, h1'.trans hQlt.le, h2', h3', fun h => absurd h (by omega)⟩
      exfalso
      push Not at h1 h2
      have hfix : ∀ g, ∀ j ∈ J, ρ g j = j := fun g j hj => by
        have := congrArg (fun f : GLV J => ((f ⟨j, hj⟩ : J) : M)) (h1 g)
        simpa [hσ₁] using this
      have hdiff : ∀ g x, ρ g x - x ∈ J := fun g x => by
        have := congrArg (fun f : GLV (M ⧸ J) => f (Submodule.Quotient.mk x)) (h2 g)
        simp only [hσ₂, LinearEquiv.coe_one, id_eq] at this
        exact (Submodule.Quotient.eq J).1 this
      have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := fun a b => by
        ext x
        simp only [LinearEquiv.mul_apply]
        obtain ⟨u, hu, huJ⟩ : ∃ u, ρ b x = x + u ∧ u ∈ J := ⟨ρ b x - x, by abel, hdiff b x⟩
        obtain ⟨v, hv, hvJ⟩ : ∃ v, ρ a x = x + v ∧ v ∈ J := ⟨ρ a x - x, by abel, hdiff a x⟩
        rw [hu, hv, map_add, map_add, hfix a u huJ, hfix b v hvJ, hu, hv]
        abel
      obtain ⟨g, hg⟩ := hρ
      exact hg (forall_eq_one_of_comm hG ρ hcomm g)

end CFSG.RankThree.GF2n.Stroth80
