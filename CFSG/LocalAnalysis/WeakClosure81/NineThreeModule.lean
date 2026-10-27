module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {Γ Ω : Type*} [Group Γ] [Finite Γ] [Fintype Ω]

@[expose] def nineThreeEven (Ω : Type*) [Fintype Ω] : Submodule (ZMod 2) (Ω → ZMod 2) where
  carrier := {f | ∑ ω, f ω = 0}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib] at hf hg ⊢
    rw [hf, hg, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hf ⊢
    rw [hf, mul_zero]

@[expose] def nineThreeConst (Ω : Type*) : Submodule (ZMod 2) (Ω → ZMod 2) :=
  Submodule.span (ZMod 2) {fun _ => 1}

theorem nineThree_even_le_of_mem [DecidableEq Ω] (N : Submodule (ZMod 2) (Ω → ZMod 2))
    (h : ∀ ω : Ω, (fun _ => (1 : ZMod 2)) + Pi.single ω 1 ∈ N) : nineThreeEven Ω ≤ N := by
  intro f hf
  have hsum : ∑ ω, f ω = 0 := hf
  have hf' : f = ∑ ω, f ω • ((fun _ => (1 : ZMod 2)) + Pi.single ω 1) := by
    ext ω'
    simp [Finset.sum_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib, hsum]
  rw [hf']
  exact N.sum_mem fun ω _ => N.smul_mem _ (h ω)

theorem nineThree_even_const_off [DecidableEq Ω] (hodd : Odd (Fintype.card Ω)) (v : Ω)
    {f : Ω → ZMod 2} (hf : f ∈ nineThreeEven Ω) (hc : ∀ a b, a ≠ v → b ≠ v → f a = f b) :
    f = 0 ∨ f = (fun _ => 1) + Pi.single v 1 := by
  have hsum : ∑ ω, f ω = 0 := hf
  by_cases hΩ : ∃ a, a ≠ v
  · obtain ⟨a, ha⟩ := hΩ
    have hfc : ∀ ω, ω ≠ v → f ω = f a := fun ω hω => hc ω a hω ha
    have hs : ∑ ω, f ω = f v + ((Fintype.card Ω - 1 : ℕ) : ZMod 2) * f a := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
      congr 1
      rw [Finset.sum_congr rfl (fun ω hω => hfc ω (Finset.ne_of_mem_erase hω)),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        nsmul_eq_mul]
    obtain ⟨k, hk⟩ := hodd
    have h2 : ((Fintype.card Ω - 1 : ℕ) : ZMod 2) = 0 := by
      rw [hk, Nat.add_sub_cancel]
      have : ((2 * k : ℕ) : ZMod 2) = 0 := by
        push_cast
        have : (2 : ZMod 2) = 0 := by decide
        rw [this, zero_mul]
      exact this
    rw [h2, zero_mul, add_zero] at hs
    have hfv : f v = 0 := by rw [← hs]; exact hsum
    have hbin : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hbin (f a) with h0 | h1
    · left
      ext ω
      by_cases hω : ω = v
      · subst hω; simpa using hfv
      · simpa using (hfc ω hω).trans h0
    · right
      ext ω
      by_cases hω : ω = v
      · subst hω
        simp only [hfv, Pi.add_apply, Pi.single_eq_same]
        decide
      · simp [Pi.single_apply, hω, hfc ω hω, h1]
  · have hΩ : ∀ a, a = v := fun a => not_not.mp (not_exists.mp hΩ a)
    left
    ext ω
    have : ω = v := hΩ ω
    subst this
    have h1 : ∑ ω', f ω' = f ω :=
      Finset.sum_eq_single ω (fun b _ hb => absurd (hΩ b) hb)
        (fun h => absurd (Finset.mem_univ ω) h)
    rw [← h1]
    exact hsum

theorem nineThree_exists_fixed (σ : Γ →* Equiv.Perm Ω) (Q : Subgroup Γ) (hQ : IsPGroup 2 Q)
    (N : Submodule (ZMod 2) (Ω → ZMod 2))
    (hN : ∀ γ : Γ, ∀ f ∈ N, (fun ω => f ((σ γ).symm ω)) ∈ N) (hN0 : N ≠ ⊥) :
    ∃ f ∈ N, f ≠ 0 ∧ ∀ q ∈ Q, ∀ ω, f (σ q ω) = f ω := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
  let smulQ : SMul Q N := ⟨fun q f => ⟨fun ω => f.1 ((σ q.1).symm ω), hN q.1 f.1 f.2⟩⟩
  letI : MulAction Q N :=
    { smul := smulQ.smul
      one_smul := fun f => by
        apply Subtype.ext
        funext ω
        show f.1 ((σ (1 : Q).1).symm ω) = f.1 ω
        rw [Subgroup.coe_one, map_one]
        rfl
      mul_smul := fun q r f => by
        apply Subtype.ext
        funext ω
        show f.1 ((σ (q * r).1).symm ω) = f.1 ((σ r.1).symm ((σ q.1).symm ω))
        simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply] }
  have hcard : 2 ∣ Nat.card N := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  have h0 : (0 : N) ∈ MulAction.fixedPoints Q N := fun q => by
    apply Subtype.ext
    funext ω
    rfl
  obtain ⟨f, hf, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hcard h0
  refine ⟨f.1, f.2, fun h => hne (Subtype.ext h.symm), fun q hq ω => ?_⟩
  have h1 : f.1 ((σ q).symm (σ q ω)) = f.1 (σ q ω) :=
    congrArg (fun g : N => g.1 (σ q ω)) (hf ⟨q, hq⟩)
  rw [Equiv.symm_apply_apply] at h1
  exact h1.symm

theorem nineThree_even_irred [DecidableEq Ω] (σ : Γ →* Equiv.Perm Ω)
    (hodd : Odd (Fintype.card Ω)) (htrans : ∀ a b : Ω, ∃ γ : Γ, σ γ a = b) (v : Ω)
    (Q : Subgroup Γ) (hQ : IsPGroup 2 Q) (hQt : ∀ a b : Ω, a ≠ v → b ≠ v → ∃ q ∈ Q, σ q a = b)
    (N : Submodule (ZMod 2) (Ω → ZMod 2))
    (hN : ∀ γ : Γ, ∀ f ∈ N, (fun ω => f ((σ γ).symm ω)) ∈ N)
    (hle : N ≤ nineThreeEven Ω) (h0 : N ≠ ⊥) : N = nineThreeEven Ω := by
  obtain ⟨f, hfN, hf0, hfQ⟩ := nineThree_exists_fixed σ Q hQ N hN h0
  have hc : ∀ a b, a ≠ v → b ≠ v → f a = f b := by
    intro a b ha hb
    obtain ⟨q, hq, hqab⟩ := hQt a b ha hb
    rw [← hqab]
    exact (hfQ q hq a).symm
  have hf : f = (fun _ => 1) + Pi.single v 1 :=
    (nineThree_even_const_off hodd v (hle hfN) hc).resolve_left hf0
  refine le_antisymm hle (nineThree_even_le_of_mem N fun ω => ?_)
  obtain ⟨γ, hγ⟩ := htrans v ω
  have h1 := hN γ f hfN
  convert h1 using 1
  rw [hf]
  funext ω'
  have h2 : (σ γ).symm ω' = v ↔ ω' = ω := by
    rw [Equiv.symm_apply_eq, hγ]
  simp only [Pi.add_apply, Pi.single_apply, h2]

theorem nineThree_perm_trichotomy (σ : Γ →* Equiv.Perm Ω) (hodd : Odd (Fintype.card Ω))
    (htrans : ∀ a b : Ω, ∃ γ : Γ, σ γ a = b) (v : Ω) (Q : Subgroup Γ) (hQ : IsPGroup 2 Q)
    (hQt : ∀ a b : Ω, a ≠ v → b ≠ v → ∃ q ∈ Q, σ q a = b)
    (N : Submodule (ZMod 2) (Ω → ZMod 2))
    (hN : ∀ γ : Γ, ∀ f ∈ N, (fun ω => f ((σ γ).symm ω)) ∈ N) :
    N = ⊥ ∨ N = nineThreeConst Ω ∨ N = nineThreeEven Ω ∨ N = ⊤ := by
  classical
  have hinv : ∀ γ : Γ, ∀ f ∈ N ⊓ nineThreeEven Ω,
      (fun ω => f ((σ γ).symm ω)) ∈ N ⊓ nineThreeEven Ω := by
    intro γ f hf
    refine ⟨hN γ f hf.1, ?_⟩
    show ∑ ω, f ((σ γ).symm ω) = 0
    rw [Equiv.sum_comp (σ γ).symm f]
    exact hf.2
  by_cases hbot : N ⊓ nineThreeEven Ω = ⊥
  ·
    have hfix : ∀ f ∈ N, ∀ γ : Γ, ∀ ω, f ((σ γ).symm ω) = f ω := by
      intro f hf γ
      have hmem : (fun ω => f ((σ γ).symm ω)) - f ∈ N ⊓ nineThreeEven Ω := by
        refine ⟨N.sub_mem (hN γ f hf) hf, ?_⟩
        show ∑ ω, ((fun ω => f ((σ γ).symm ω)) - f) ω = 0
        simp only [Pi.sub_apply, Finset.sum_sub_distrib]
        rw [Equiv.sum_comp (σ γ).symm f, sub_self]
      rw [hbot, Submodule.mem_bot] at hmem
      intro ω
      have := congrFun hmem ω
      simpa [sub_eq_zero] using this
    have hconst : ∀ f ∈ N, ∀ a b : Ω, f a = f b := by
      intro f hf a b
      obtain ⟨γ, hγ⟩ := htrans b a
      have := hfix f hf γ (σ γ b)
      rw [Equiv.symm_apply_apply, hγ] at this
      exact this.symm
    have hle : N ≤ nineThreeConst Ω := by
      intro f hf
      exact Submodule.mem_span_singleton.2 ⟨f v, funext fun ω => by simp [hconst f hf ω v]⟩
    by_cases hN0 : N = ⊥
    · exact Or.inl hN0
    · right; left
      refine le_antisymm hle ?_
      obtain ⟨f, hfN, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
      have hbin : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      have hfv : f v = 1 := by
        rcases hbin (f v) with h0 | h1
        · exact absurd (funext fun ω => (hconst f hfN ω v).trans h0) hf0
        · exact h1
      have h1N : (fun _ => (1 : ZMod 2)) ∈ N := by
        convert hfN using 1
        funext ω
        rw [hconst f hfN ω v, hfv]
      exact Submodule.span_le.2 (by simpa using h1N)
  · have hP : N ⊓ nineThreeEven Ω = nineThreeEven Ω :=
      nineThree_even_irred σ hodd htrans v Q hQ hQt _ hinv inf_le_right hbot
    have hPN : nineThreeEven Ω ≤ N := hP ▸ inf_le_left
    by_cases hNP : N ≤ nineThreeEven Ω
    · right; right; left
      exact le_antisymm hNP hPN
    · right; right; right
      obtain ⟨n, hnN, hnP⟩ := Set.not_subset.1 hNP
      have hbin : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      have hn1 : ∑ ω, n ω = 1 := (hbin _).resolve_left hnP
      refine eq_top_iff.2 fun f _ => ?_
      by_cases hfP : f ∈ nineThreeEven Ω
      · exact hPN hfP
      · have hf1 : ∑ ω, f ω = 1 := (hbin _).resolve_left hfP
        have hfn : f + n ∈ nineThreeEven Ω := by
          show ∑ ω, (f + n) ω = 0
          simp only [Pi.add_apply, Finset.sum_add_distrib, hf1, hn1]
          decide
        have := N.sub_mem (hPN hfn) hnN
        simpa using this

end CFSG.LocalAnalysis.WeakClosure81
