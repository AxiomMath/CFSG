module

public import CFSG.Quasithin.Recognition.G112A2ModNineLin

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin
open scoped TensorProduct

theorem nine_perm3_inv : ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
    ∃ p q r : Fin 3, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ σ = Equiv.swap p q := by
  decide

theorem nine_perm3_sq : ∀ σ : Equiv.Perm (Fin 3),
    (∀ a : Fin 3 → ZMod 2, (∑ i, a i = 0) → permAct σ (permAct σ a) = a) → σ * σ = 1 := by
  decide

theorem nine_swap_coords : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r →
    ∀ a : Fin 3 → ZMod 2, (∑ i, a i = 0) →
      a = a q • (Pi.single p (1 : ZMod 2) + Pi.single q 1) +
        a r • (Pi.single p (1 : ZMod 2) + Pi.single r 1) := by
  decide

theorem nine_swap_act : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r →
    ∀ a : Fin 3 → ZMod 2, (∑ i, a i = 0) →
      permAct (Equiv.swap p q) a r = a r ∧ permAct (Equiv.swap p q) a q = a q + a r := by
  decide

theorem nine_pair_sum : ∀ p q : Fin 3, p ≠ q →
    ∑ i, (Pi.single p (1 : ZMod 2) + Pi.single q 1 : Fin 3 → ZMod 2) i = 0 := by
  decide

theorem nine_cyc_relations : ∀ a : Fin 3 → ZMod 2, (∑ i, a i = 0) →
    permAct (finRotate 3) a 2 = a 1 ∧ permAct (finRotate 3) a 1 = a 1 + a 2 := by
  decide

@[expose] def nineCoordP {n : ℕ} (i : Fin n) : permCore n →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj i).comp (permCore n).subtype

theorem nineCoordP_apply {n : ℕ} (i : Fin n) (a : permCore n) : nineCoordP i a = a.1 i := rfl

theorem nine_dec3 {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (a : permCore 3) :
    a = nineCoordP q a • (⟨Pi.single p 1 + Pi.single q 1, nine_pair_sum p q hpq⟩ : permCore 3) +
      nineCoordP r a • (⟨Pi.single p 1 + Pi.single r 1, nine_pair_sum p r hpr⟩ : permCore 3) := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_mk, nineCoordP_apply]
  exact nine_swap_coords p q r hpq hpr hqr a.1 a.2

theorem coe_nineAct_nine (σ : Equiv.Perm (Fin 3)) (a : permCore 3) :
    (nineAct 3 σ a).1 = permAct σ a.1 := rfl

theorem nineAct_one_eq (n : ℕ) : nineAct n 1 = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext i
  simp [coe_nineAct, permAct]

theorem nine_clause_of_model {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Q : Type} [AddCommMonoid Q] [Module (ZMod 2) Q] [Module.Finite (ZMod 2) Q]
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (ψ : V ≃ₗ[ZMod 2] (permCore 3 ⊗[ZMod 2] Q))
    (hV : Module.finrank (ZMod 2) V = 8) (hQ : Module.finrank (ZMod 2) Q ≤ 4)
    (hsurj : ∀ σ' : Equiv.Perm (Fin 3), ∃ γ ∈ Γ, ∀ (a : permCore 3) (b : Q),
      ψ (γ (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ' a ⊗ₜ[ZMod 2] b)
    {t : V ≃ₗ[ZMod 2] V} (ht2 : t * t = 1)
    (hT : ∃ (σ : Equiv.Perm (Fin 3)) (τ : Q →ₗ[ZMod 2] Q), ∀ (a : permCore 3) (b : Q),
      ψ (t (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ a ⊗ₜ[ZMod 2] τ b)
    {v₁ : V} (hv₁ : v₁ ≠ 0)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
      γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  classical
  obtain ⟨σ, τ, hστ⟩ := hT
  have hψt : ∀ x : V, ψ (t x) = TensorProduct.map (nineAct 3 σ) τ (ψ x) := by
    have key : ∀ z : permCore 3 ⊗[ZMod 2] Q,
        ψ (t (ψ.symm z)) = TensorProduct.map (nineAct 3 σ) τ z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rw [hστ a b, TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    intro x
    simpa using key (ψ x)
  have hTT' : ∀ z : permCore 3 ⊗[ZMod 2] Q,
      TensorProduct.map (nineAct 3 σ) τ (TensorProduct.map (nineAct 3 σ) τ z) = z := by
    intro z
    obtain ⟨x, rfl⟩ := ψ.surjective z
    have h3 : t (t x) = x := by
      have := congrArg (fun g : V ≃ₗ[ZMod 2] V => g x) ht2
      simpa using this
    rw [← hψt x, ← hψt (t x), h3]
  have hTT : ∀ (a : permCore 3) (b : Q),
      TensorProduct.map (nineAct 3 σ) τ (TensorProduct.map (nineAct 3 σ) τ (a ⊗ₜ[ZMod 2] b)) =
        a ⊗ₜ[ZMod 2] b :=
    fun a b => hTT' _
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Q, b₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ z : permCore 3 ⊗[ZMod 2] Q, z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b => rw [hcon b, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    have hVsub : Subsingleton V := ⟨fun x y => ψ.injective ((hz _).trans (hz _).symm)⟩
    have h0 := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := V)
    omega
  have hdec01 := nine_dec3 (p := 0) (q := 1) (r := 2) (by decide) (by decide) (by decide)
  have hSS : ∀ a : permCore 3, nineAct 3 σ (nineAct 3 σ a) = a :=
    fun a => nine_sq_eq_one hdec01 (by decide) (by decide) (by decide) (by decide) hTT hb₀ a
  have hσσ : σ * σ = 1 := by
    apply nine_perm3_sq σ
    intro a ha
    have h := congrArg Subtype.val (hSS ⟨a, ha⟩)
    simpa [coe_nineAct] using h
  by_cases hσ1 : σ = 1
  ·
    subst hσ1
    rw [nineAct_one_eq] at hψt
    obtain ⟨γ, hγΓ, hγ⟩ := hsurj (finRotate 3)
    have hγV : ∀ x : V,
        ψ (γ x) = TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id (ψ x) := by
      have key : ∀ z : permCore 3 ⊗[ZMod 2] Q,
          ψ (γ (ψ.symm z)) = TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id z := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => rw [hγ a b, TensorProduct.map_tmul, LinearMap.id_apply]
        | add x y hx hy => simp only [map_add, hx, hy]
      intro x
      simpa using key (ψ x)
    have hcomm' : ∀ z : permCore 3 ⊗[ZMod 2] Q,
        TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id
          (TensorProduct.map LinearMap.id τ z) =
        TensorProduct.map LinearMap.id τ
          (TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hcomm : ∀ x : V, γ (t x) = t (γ x) := by
      intro x
      apply ψ.injective
      calc ψ (γ (t x)) = TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id (ψ (t x)) :=
            hγV (t x)
        _ = TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id
              (TensorProduct.map LinearMap.id τ (ψ x)) := by rw [hψt x]
        _ = TensorProduct.map LinearMap.id τ
              (TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id (ψ x)) := hcomm' _
        _ = TensorProduct.map LinearMap.id τ (ψ (γ x)) := by rw [hγV x]
        _ = ψ (t (γ x)) := (hψt (γ x)).symm
    have hS0c : ∀ a : permCore 3,
        nineCoordP 2 (nineAct 3 (finRotate 3) a) = nineCoordP 1 a := by
      intro a
      simp only [nineCoordP_apply, coe_nineAct_nine]
      exact (nine_cyc_relations a.1 a.2).1
    have hS1c : ∀ a : permCore 3,
        nineCoordP 1 (nineAct 3 (finRotate 3) a) = nineCoordP 1 a + nineCoordP 2 a := by
      intro a
      simp only [nineCoordP_apply, coe_nineAct_nine]
      exact (nine_cyc_relations a.1 a.2).2
    refine ⟨γ, hγΓ, ?_, ?_⟩
    · rintro w ⟨x, rfl⟩
      refine LinearMap.mem_range.2 ⟨γ x, ?_⟩
      simp only [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, map_sub,
        hcomm]
    · intro hfix
      have hz : ψ v₁ ≠ 0 := fun h => hv₁ (ψ.map_eq_zero_iff.1 h)
      have h1 : TensorProduct.map (nineAct 3 (finRotate 3)) LinearMap.id (ψ v₁) = ψ v₁ := by
        rw [← hγV v₁, hfix]
      exact hz (nine_fix_eq_zero_cycle hdec01 hS0c hS1c h1)
  ·
    exfalso
    obtain ⟨p, q, r, hpq, hpr, hqr, hσe⟩ := nine_perm3_inv σ hσσ hσ1
    subst hσe
    have hS0 : ∀ a : permCore 3,
        nineCoordP r (nineAct 3 (Equiv.swap p q) a) = nineCoordP r a := by
      intro a
      simp only [nineCoordP_apply, coe_nineAct_nine]
      exact (nine_swap_act p q r hpq hpr hqr a.1 a.2).1
    have hS1 : ∀ a : permCore 3,
        nineCoordP q (nineAct 3 (Equiv.swap p q) a) = nineCoordP q a + nineCoordP r a := by
      intro a
      simp only [nineCoordP_apply, coe_nineAct_nine]
      exact (nine_swap_act p q r hpq hpr hqr a.1 a.2).2
    have hker : Module.finrank (ZMod 2) (LinearMap.ker (t.toLinearMap - LinearMap.id)) ≤
        Module.finrank (ZMod 2) Q := by
      apply nine_finrank_ker_le_of_inj (X := V) t.toLinearMap
        ((nineCoeff (nineCoordP q)).comp ψ.toLinearMap)
      intro x hx hD
      have hx' : t x = x := hx
      have hD' : nineCoeff (nineCoordP q) (ψ x) = 0 := hD
      have hy : TensorProduct.map (nineAct 3 (Equiv.swap p q)) τ (ψ x) = ψ x := by
        rw [← hψt x, hx']
      have hz := nine_fix_eq_zero_of_coeff (nine_dec3 hpq hpr hqr) hS0 hS1 hy hD'
      exact ψ.map_eq_zero_iff.1 hz
    have hrk := LinearMap.finrank_range_add_finrank_ker (t.toLinearMap - LinearMap.id)
    rw [hV] at hrk
    omega

end CFSG.Quasithin.G112A2
