module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6

namespace GE23

section Odd

variable {V : Type} [CommGroup V] [Finite V]

theorem split_of_odd_index (hV : ∀ v : V, v ^ 2 = 1) {S A : Subgroup (MulAut V)}
    (hodd : ¬ 2 ∣ (A.subgroupOf S).index) {U W : Subgroup V}
    (hUinv : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U) (htriv : ∀ s ∈ S, ∀ u ∈ U, s u * u⁻¹ ∈ W)
    (hsplit : ∀ u ∈ U, ∃ w ∈ W, ∃ c ∈ U, (∀ a ∈ A, a c = c) ∧ u = w * c) :
    ∀ u ∈ U, ∃ w ∈ W, ∃ c ∈ U, (∀ s ∈ S, s c = c) ∧ u = w * c := by
  classical
  intro u hu
  obtain ⟨w, hw, c, hcU, hcA, rfl⟩ := hsplit u hu
  let Q := ↥S ⧸ A.subgroupOf S
  have hSfin : Finite ↥S := inferInstance
  let _ : Fintype Q := Fintype.ofFinite Q
  let f : Q → V := Quotient.lift (fun g : ↥S => (g : MulAut V) c) (by
    intro g₁ g₂ hg
    have hg' : g₁⁻¹ * g₂ ∈ A.subgroupOf S := QuotientGroup.leftRel_apply.1 hg
    have hga : ((g₁⁻¹ * g₂ : ↥S) : MulAut V) ∈ A := Subgroup.mem_subgroupOf.1 hg'
    have h1 : (g₂ : MulAut V) c = (g₁ : MulAut V) (((g₁⁻¹ * g₂ : ↥S) : MulAut V) c) := by
      rw [show ((g₁⁻¹ * g₂ : ↥S) : MulAut V) = (g₁ : MulAut V)⁻¹ * (g₂ : MulAut V) from rfl]
      simp
    show (g₁ : MulAut V) c = (g₂ : MulAut V) c
    rw [h1, hcA _ hga])
  have hf : ∀ g : ↥S, f (QuotientGroup.mk g) = (g : MulAut V) c := fun g => rfl
  set c' : V := ∏ q : Q, f q with hc'
  have hfU : ∀ q : Q, f q ∈ U := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => rw [hf]; exact hUinv _ g.2 c hcU
  have hc'U : c' ∈ U := Subgroup.prod_mem _ fun q _ => hfU q
  have hc'fix : ∀ s ∈ S, s c' = c' := by
    intro s hs
    have hsf : ∀ q : Q, s (f q) = f ((⟨s, hs⟩ : ↥S) • q) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hf, MulAction.Quotient.smul_mk, hf]
        rfl
    rw [hc', map_prod]
    simp_rw [hsf]
    exact Fintype.prod_equiv (MulAction.toPerm (⟨s, hs⟩ : ↥S)) _ _ (fun q => rfl)
  have hfW : ∀ q : Q, f q * c⁻¹ ∈ W := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => rw [hf]; exact htriv _ g.2 c hcU
  have hn : Odd (Fintype.card Q) := by
    have : Fintype.card Q = (A.subgroupOf S).index := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    rw [this]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
  have hpow : c ^ Fintype.card Q = c := by
    obtain ⟨m, hm⟩ := hn
    rw [hm, pow_succ, pow_mul, hV c, one_pow, one_mul]
  set w' : V := ∏ q : Q, f q * c⁻¹ with hw'
  have hw'W : w' ∈ W := Subgroup.prod_mem _ fun q _ => hfW q
  have hc'eq : c' = w' * c := by
    have : c' = ∏ q : Q, ((f q * c⁻¹) * c) := by
      refine Finset.prod_congr rfl fun q _ => ?_
      group
    rw [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hpow]
  refine ⟨w * w'⁻¹, W.mul_mem hw (W.inv_mem hw'W), c', hc'U, hc'fix, ?_⟩
  rw [hc'eq]
  group

end Odd

section Sym

theorem swap_diff_eq {n : ℕ} (x y : Fin n → ZMod 2) (a b : Fin n)
    (h : x a + x b = y a + y b) (j : Fin n) :
    x (Equiv.swap a b j) + x j = y (Equiv.swap a b j) + y j := by
  by_cases hja : j = a
  · subst hja
    rw [Equiv.swap_apply_left, add_comm (x b), add_comm (y b)]
    exact h
  · by_cases hjb : j = b
    · subst hjb
      rw [Equiv.swap_apply_right]
      exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, CharTwo.add_self_eq_zero,
        CharTwo.add_self_eq_zero]

theorem exists_even_solution (ε : Fin 4 → ZMod 2) :
    ∃ x : Fin 5 → ZMod 2, (∑ j, x j = 0) ∧ ∀ i : Fin 4, x i.castSucc + x i.succ = ε i := by
  revert ε
  decide

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem split_sym {S : Subgroup (MulAut V)} {π : Equiv.Perm (Fin 5) →* ↥S}
    (hπs : Function.Surjective π) {β₀ : ↥(coreMod 5) →* V}
    (hequiv : ∀ (σ : Equiv.Perm (Fin 5)) (y : ↥(coreMod 5)),
      β₀ (coreAct 5 σ y) = ((π σ : ↥S) : MulAut V) (β₀ y))
    {U W : Subgroup V} (hW : W = β₀.range) (hWU : W ≤ U)
    (hsplit : ∀ i : Fin 4, ∀ u ∈ U, ∃ w ∈ W, ∃ c ∈ U,
      ((π (Equiv.swap i.castSucc i.succ) : ↥S) : MulAut V) c = c ∧ u = w * c) :
    ∀ u ∈ U, ∃ w ∈ W, ∃ c ∈ U, (∀ s ∈ S, s c = c) ∧ u = w * c := by
  classical
  intro u hu
  choose w hwW c hcU hcfix hweq using fun i => hsplit i u hu
  have hy : ∀ i : Fin 4, ∃ y : ↥(coreMod 5), β₀ y = w i := fun i => by
    have := hwW i
    rw [hW] at this
    exact this
  choose y hy using hy
  obtain ⟨x, hxsum, hx⟩ := exists_even_solution fun i =>
    Multiplicative.toAdd (y i : PermMod 5) i.castSucc +
      Multiplicative.toAdd (y i : PermMod 5) i.succ
  let x' : ↥(coreMod 5) := ⟨Multiplicative.ofAdd x, mem_coreMod.2 hxsum⟩
  let w₀ : V := β₀ x'
  have hw₀W : w₀ ∈ W := by
    rw [hW]
    exact ⟨x', rfl⟩
  have hadj : ∀ i : Fin 4, ((π (Equiv.swap i.castSucc i.succ) : ↥S) : MulAut V) (u * w₀⁻¹) =
      u * w₀⁻¹ := by
    intro i
    set τ : MulAut V := ((π (Equiv.swap i.castSucc i.succ) : ↥S) : MulAut V) with hτ
    set σ : Equiv.Perm (Fin 5) := Equiv.swap i.castSucc i.succ with hσ
    have hcoord : coreAct 5 σ x' * x'⁻¹ = coreAct 5 σ (y i) * (y i)⁻¹ := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext j
      have hsw : σ⁻¹ = σ := by rw [hσ, Equiv.swap_inv]
      have h1 := swap_diff_eq x (Multiplicative.toAdd (y i : PermMod 5)) i.castSucc i.succ
        (hx i) j
      simp only [coreAct_coe, Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv,
        Pi.add_apply, CharTwo.neg_eq]
      rw [permAct_apply, permAct_apply, hsw]
      exact h1
    have key : τ w₀ * w₀⁻¹ = τ (w i) * (w i)⁻¹ := by
      have e1 : τ w₀ * w₀⁻¹ = β₀ (coreAct 5 σ x' * x'⁻¹) := by
        rw [map_mul, map_inv, hequiv]
      have e2 : τ (w i) * (w i)⁻¹ = β₀ (coreAct 5 σ (y i) * (y i)⁻¹) := by
        rw [map_mul, map_inv, hequiv, hy i]
      rw [e1, e2, hcoord]
    have key' : τ w₀ * w i = τ (w i) * w₀ := by
      rw [← div_eq_div_iff_mul_eq_mul, div_eq_mul_inv, div_eq_mul_inv]
      exact key
    have hk2 : τ (w i) * (τ w₀)⁻¹ = w i * w₀⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, mul_comm (w i)]
      exact key'.symm
    have hτu : τ u = τ (w i) * c i := by
      conv_lhs => rw [hweq i]
      rw [map_mul, hcfix i]
    rw [map_mul, map_inv, hτu]
    calc τ (w i) * c i * (τ w₀)⁻¹ = (τ (w i) * (τ w₀)⁻¹) * c i := by rw [mul_right_comm]
      _ = (w i * w₀⁻¹) * c i := by rw [hk2]
      _ = (w i * c i) * w₀⁻¹ := by rw [mul_right_comm]
      _ = u * w₀⁻¹ := by rw [← hweq i]
  have hallS : ∀ s ∈ S, s (u * w₀⁻¹) = u * w₀⁻¹ := by
    let Φ : Subgroup (Equiv.Perm (Fin 5)) :=
      (MulAction.stabilizer (MulAut V) (u * w₀⁻¹)).comap (S.subtype.comp π)
    have hΦ : (⊤ : Submonoid (Equiv.Perm (Fin 5))) ≤ Φ.toSubmonoid := by
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ 4]
      refine Submonoid.closure_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact hadj i
    intro s hs
    obtain ⟨σ, hσ⟩ := hπs ⟨s, hs⟩
    have hσΦ : σ ∈ Φ := hΦ (Submonoid.mem_top σ)
    have : (S.subtype.comp π) σ • (u * w₀⁻¹) = u * w₀⁻¹ := hσΦ
    have hs' : (S.subtype.comp π) σ = s := by
      show ((π σ : ↥S) : MulAut V) = s
      rw [hσ]
    rw [hs'] at this
    exact this
  refine ⟨w₀, hw₀W, u * w₀⁻¹, U.mul_mem hu (U.inv_mem (hWU hw₀W)), hallS, ?_⟩
  rw [mul_left_comm, mul_inv_cancel, mul_one]

end Sym

end GE23

end CFSG.Quasithin
