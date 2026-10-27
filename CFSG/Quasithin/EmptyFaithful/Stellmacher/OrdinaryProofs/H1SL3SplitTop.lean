module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitCompl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitSetup

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {G : Type} [Group G]

theorem exists_complement_gen {F : Type} [Field F] [Fintype F] [CharP F 2] {k : ℕ}
    (S : AbelSub G) (W Z A : Subgroup G) {α : ↥A →* ↥(StatedSL 3 F)}
    (ρ0 : Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End (Fin 3 → F))
    (hA : A ≤ Subgroup.normalizer (S.carrier : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hWZ : W ≤ Z) (hZS : Z ≤ S.carrier)
    (hZW : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ W)
    (hker : ∀ a : ↥A, α a = 1 → ∀ v : S.carrier, (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ W)
    (β : ↥S.carrier →* Multiplicative (Fin k → Fin 3 → F))
    (hβker : β.ker = Z.subgroupOf S.carrier)
    (hβeq : ∀ (a : ↥A) (u v : S.carrier), (v : G) = (a : G) * (u : G) * (a : G)⁻¹ →
      ∀ i : Fin k, Multiplicative.toAdd (β v) i =
        ρ0 ((statedSLEquiv 3).symm (α a)) (Multiplicative.toAdd (β u) i))
    (hβs : Function.Surjective β) (hα : Function.Surjective α)
    (hXr : ∃ t ∈ diagSL (F := F), (∀ a : F, t * unitriMk a 0 0 = unitriMk a 0 0 * t) ∧
      ∀ v : Fin 3 → F, ρ0 t v = v → v = 0)
    (hYr : ∃ t ∈ diagSL (F := F), (∀ b : F, t * unitriMk 0 b 0 = unitriMk 0 b 0 * t) ∧
      ∀ v : Fin 3 → F, ρ0 t v = v → v = 0)
    (hZr : ∃ t ∈ diagSL (F := F), (∀ c : F, t * unitriMk 0 0 c = unitriMk 0 0 c * t) ∧
      ∀ v : Fin 3 → F, ρ0 t v = v → v = 0)
    [Module (ZMod 2) (S.quot W)] [Module (ZMod 2) (Fin k → Fin 3 → F)] :
    ∃ X : Subgroup G, W ≤ X ∧ X ≤ S.carrier ∧ A ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ Z = W ∧ X ⊔ Z = S.carrier := by
  have hψ : Function.Surjective (splitSetupOf S W Z A ρ0 hA hAW hWZ hZW hker β hβker hβeq).ψ := by
    intro g
    obtain ⟨a, ha⟩ := hα ((statedSLEquiv 3) g)
    refine ⟨a, ?_⟩
    show (statedSLEquiv 3).symm (α a) = g
    rw [ha, MulEquiv.symm_apply_apply]
  have hπ : Function.Surjective (splitSetupOf S W Z A ρ0 hA hAW hWZ hZW hker β hβker hβeq).π :=
    piL_surjective S W β (fun x hx => beta_one_of_mem S W Z β hβker hWZ x hx) hβs
  have hprin : ∀ f : Matrix.SpecialLinearGroup (Fin 3) F →
      ((Fin k → Fin 3 → F) →+
        LinearMap.ker (splitSetupOf S W Z A ρ0 hA hAW hWZ hZW hker β hβker hβeq).π),
      (∀ g h, f (g * h) = f g + homAct (splitSetupOf S W Z A ρ0 hA hAW hWZ hZW hker β hβker hβeq).ρN g
        (f h)) →
      ∃ w : (Fin k → Fin 3 → F) →+
        LinearMap.ker (splitSetupOf S W Z A ρ0 hA hAW hWZ hZW hker β hβker hβeq).π,
        ∀ g, f g = w - homAct (splitSetupOf S W Z A ρ0 hA hAW hWZ hZW hker β hβker hβeq).ρN g w := by
    intro f hf
    obtain ⟨tX, htX, hcX, hfX⟩ := hXr
    obtain ⟨tY, htY, hcY, hfY⟩ := hYr
    obtain ⟨tZ, htZ, hcZ, hfZ⟩ := hZr
    exact crossedHom_principal_coef (piAct (ι := Fin k) ρ0)
      ⟨tX, htX, hcX, fun x hx => piAct_fixed_free ρ0 tX hfX x hx⟩
      ⟨tY, htY, hcY, fun x hx => piAct_fixed_free ρ0 tY hfY x hx⟩
      ⟨tZ, htZ, hcZ, fun x hx => piAct_fixed_free ρ0 tZ hfZ x hx⟩ f hf
  obtain ⟨X₀, hinv, hX0, hcov⟩ :=
    exists_complement_core (splitSetupOf S W Z A ρ0 hA hAW hWZ hZW hker β hβker hβeq) hψ hπ hprin
  exact exists_subgroup_of_complement S hA hAW hWZ hZS β hβker
    (fun x hx => beta_one_of_mem S W Z β hβker hWZ x hx) X₀ hinv hX0 hcov

theorem exists_complement_of_isSum {G : Type} [Group G] {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hF : 4 ≤ Fintype.card F) {A V Z W : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) {dual : Bool} {k : ℕ}
    (hV : IsSumOfNaturalModulesVia A V Z α dual k)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1)
    (hWZ : W ≤ Z) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hZW : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ W)
    (hker : ∀ a : ↥A, α a = 1 → ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ W) :
    ∃ X : Subgroup G, W ≤ X ∧ X ≤ V ∧ A ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ Z = W ∧ X ⊔ Z = V := by
  obtain ⟨S, rfl⟩ : ∃ S : AbelSub G, S.carrier = V := ⟨⟨V, hVab⟩, rfl⟩
  obtain ⟨hA, hZV, β, hβs, hβker, hβeqV⟩ := hV
  have hS2 : ∀ x ∈ S.carrier, x * x = 1 := hV2
  letI : Module (ZMod 2) (S.quot W) := AbelSub.quotZMod S W hS2
  letI : Module (ZMod 2) (Fin k → Fin 3 → F) := zmodCoords k
  obtain ⟨τ, h0, h1⟩ := exists_tau hF
  have hker' : ∀ a : ↥A, α a = 1 → ∀ v : S.carrier, (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ W :=
    fun a ha v => hker a ha v v.2
  cases dual
  · exact exists_complement_gen (F := F) S W Z A natAct hA hAW hWZ hZV hZW hker' β hβker
      (fun a u v h i => by rw [natAct_statedSL]; exact hβeqV a u v h i) hβs hα
      (torusX_natural h0 h1) (torusY_natural h0 h1) (torusZ_natural h0 h1)
  · exact exists_complement_gen (F := F) S W Z A dualAct hA hAW hWZ hZV hZW hker' β hβker
      (fun a u v h i => by rw [dualAct_statedSL]; exact hβeqV a u v h i) hβs hα
      (torusX_dual h0 h1) (torusY_dual h0 h1) (torusZ_dual h0 h1)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
