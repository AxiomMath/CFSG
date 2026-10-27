module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P Equiv

namespace S126L23c

theorem pv_self : ∀ a : Fin 8, B5FinS8.pv a a = 0 := by
  decide +kernel

theorem pv_add_pv : ∀ a b c : Fin 8, B5FinS8.pv a b + B5FinS8.pv b c = B5FinS8.pv a c := by
  decide +kernel

theorem pv_eq_pv : ∀ a b c d : Fin 8, a ≠ b → B5FinS8.pv c d = B5FinS8.pv a b →
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  decide +kernel

theorem pe_self (a : Fin 8) : pe a a = 1 :=
  Subtype.ext (congrArg Multiplicative.ofAdd (pv_self a))

theorem pe_mul_pe (a b c : Fin 8) : pe a b * pe b c = pe a c :=
  Subtype.ext (congrArg Multiplicative.ofAdd (pv_add_pv a b c))

theorem eq_of_pe_eq {a b c d : Fin 8} (hab : a ≠ b) (h : pe c d = pe a b) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) :=
  pv_eq_pv a b c d hab (congrArg (fun m : ↥(coreMod 8) => Multiplicative.toAdd (m : PermMod 8)) h)

theorem exists_two_ne : ∀ x y : Fin 8, ∃ w w' : Fin 8, w ≠ w' ∧ w ≠ x ∧ w ≠ y ∧ w' ≠ x ∧
    w' ≠ y := by
  decide

theorem exists_two_ne3 : ∀ x y u : Fin 8, ∃ v v' : Fin 8, v ≠ v' ∧ v ≠ x ∧ v ≠ y ∧ v ≠ u ∧
    v' ≠ x ∧ v' ≠ y ∧ v' ≠ u := by
  decide

theorem exists_ne4 : ∀ a b c d : Fin 8, ∃ e : Fin 8, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by
  decide

section Pairs

variable {R : Fin 8 → Fin 8 → Prop} (hs : ∀ a b, R a b → R b a)
  (ht : ∀ a b c, R a b → R b c → R a c) (h2 : ∀ a b c, R a b ∨ R b c ∨ R a c)

include hs h2 in
theorem swap_of_pairs {σ : Perm (Fin 8)}
    (hσ : ∀ a b, a ≠ b → R a b → (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a)) (h1 : σ ≠ 1) :
    ∃ x y, x ≠ y ∧ R x y ∧ σ = swap x y ∧ ∀ c, R x c → c = x ∨ c = y := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  have hcls : ∀ c, c ≠ x → R x c → c = σ x ∧ σ c = x := fun c hc hR => by
    rcases hσ x c (Ne.symm hc) hR with h | h
    · exact absurd h.1 hx
    · exact ⟨h.1.symm, h.2⟩
  have hex : ∃ c, c ≠ x ∧ R x c := by
    by_contra hcon
    push Not at hcon
    have hrel : ∀ c d, c ≠ x → d ≠ x → R c d := fun c d hc hd => by
      rcases h2 c x d with h | h | h
      · exact absurd (hs c x h) (hcon c hc)
      · exact absurd h (hcon d hd)
      · exact h
    obtain ⟨w, w', hww, hw1, hw2, hw1', hw2'⟩ := exists_two_ne x (σ x)
    have hy : σ x ≠ x := hx
    rcases hσ (σ x) w (Ne.symm hw2) (hrel _ _ hy hw1) with h | h
    · exact hx (σ.injective h.1)
    rcases hσ (σ x) w' (Ne.symm hw2') (hrel _ _ hy hw1') with h' | h'
    · exact hx (σ.injective h'.1)
    exact hww (h.1.symm.trans h'.1)
  obtain ⟨c, hc, hRc⟩ := hex
  obtain ⟨hcy, hσc⟩ := hcls c hc hRc
  subst hcy
  refine ⟨x, σ x, Ne.symm hx, hRc, ?_, fun d hd => ?_⟩
  ·
    have hfix : ∀ u, u ≠ x → u ≠ σ x → σ u = u := by
      intro u hu1 hu2
      have hnot : ¬ R x u := fun h => hu2 (hcls u hu1 h).1
      have hrel : ∀ v, v ≠ x → v ≠ σ x → R u v := fun v hv1 hv2 => by
        rcases h2 u x v with h | h | h
        · exact absurd (hs u x h) hnot
        · exact absurd (hcls v hv1 h).1 hv2
        · exact h
      obtain ⟨v, v', hvv, hv1, hv2, hv3, hv1', hv2', hv3'⟩ := exists_two_ne3 x (σ x) u
      by_contra hne
      rcases hσ u v (Ne.symm hv3) (hrel v hv1 hv2) with h | h
      · exact hne h.1
      rcases hσ u v' (Ne.symm hv3') (hrel v' hv1' hv2') with h' | h'
      · exact hne h'.1
      exact hvv (h.1.symm.trans h'.1)
    ext i
    by_cases hi1 : i = x
    · subst hi1
      rw [swap_apply_left]
    · by_cases hi2 : i = σ x
      · rw [hi2, swap_apply_right, hσc]
      · rw [swap_apply_of_ne_of_ne hi1 hi2, hfix i hi1 hi2]
  · by_cases hdx : d = x
    · exact Or.inl hdx
    · exact Or.inr (hcls d hdx hd).1

include ht h2 in
theorem swap_unique {x y x' y' : Fin 8} (hxy : x ≠ y) (hx'y' : x' ≠ y') (hR : R x y)
    (hR' : R x' y') (hc : ∀ c, R x c → c = x ∨ c = y) (hc' : ∀ c, R x' c → c = x' ∨ c = y') :
    swap x y = swap x' y' := by
  by_cases h1 : x' = x
  · subst h1
    rcases hc y' hR' with h | h
    · exact absurd h.symm hx'y'
    · rw [h]
  by_cases h2' : x' = y
  · subst h2'
    rcases hc y' (ht _ _ _ hR hR') with h | h
    · rw [h, swap_comm]
    · exact absurd h.symm hx'y'
  · exfalso
    have hnot : ¬ R x x' := fun h => (hc x' h).elim h1 h2'
    obtain ⟨e, he1, he2, he3, he4⟩ := exists_ne4 x y x' y'
    rcases h2 x x' e with h | h | h
    · exact hnot h
    · exact (hc' e h).elim he3 he4
    · exact (hc e h).elim he1 he2

end Pairs

theorem eq_of_fix_index_two {H₀ : Subgroup ↥(coreMod 8)} (h2 : H₀.index = 2) {σ τ : Perm (Fin 8)}
    (hσ : ∀ m ∈ H₀, coreAct 8 σ m = m) (hτ : ∀ m ∈ H₀, coreAct 8 τ m = m) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) : σ = τ := by
  let R : Fin 8 → Fin 8 → Prop := fun a b => pe a b ∈ H₀
  have hs : ∀ a b, R a b → R b a := fun a b h => by
    change pe b a ∈ H₀
    rwa [S126L20a.pe_comm]
  have ht : ∀ a b c, R a b → R b c → R a c := fun a b c h h' => by
    change pe a c ∈ H₀
    rw [← pe_mul_pe a b c]
    exact H₀.mul_mem h h'
  have h3 : ∀ a b c, R a b ∨ R b c ∨ R a c := fun a b c => by
    by_contra hcon
    push Not at hcon
    apply hcon.2.2
    change pe a c ∈ H₀
    rw [← pe_mul_pe a b c, Subgroup.mul_mem_iff_of_index_two h2]
    exact iff_of_false hcon.1 hcon.2.1
  have hpair : ∀ ρ : Perm (Fin 8), (∀ m ∈ H₀, coreAct 8 ρ m = m) → ∀ a b, a ≠ b → R a b →
      (ρ a = a ∧ ρ b = b) ∨ (ρ a = b ∧ ρ b = a) := fun ρ hρ a b hab h => by
    have e := hρ _ h
    rw [S126L20a.coreAct_pe] at e
    exact eq_of_pe_eq hab e
  obtain ⟨x, y, hxy, hR, rfl, hc⟩ := swap_of_pairs hs h3 (hpair σ hσ) hσ1
  obtain ⟨x', y', hx'y', hR', rfl, hc'⟩ := swap_of_pairs hs h3 (hpair τ hτ) hτ1
  exact swap_unique ht h3 hxy hx'y' hR hR' hc hc'

theorem card_le_two_mul {Γ : Type*} [Group Γ] [Finite Γ] {X C : Subgroup Γ} (hCX : C ≤ X)
    (h : ∀ x ∈ X, ∀ y ∈ X, x ∉ C → y ∉ C → x * y ∈ C) : Nat.card X ≤ 2 * Nat.card C := by
  classical
  by_cases hXC : X ≤ C
  · have := le_antisymm hXC hCX
    subst this
    omega
  obtain ⟨x₀, hx₀X, hx₀C⟩ := Set.not_subset.1 hXC
  have hinv : x₀⁻¹ ∉ C := fun h' => hx₀C (by simpa using C.inv_mem h')
  let f : ↥C ⊕ ↥C → ↥X := fun s => Sum.elim (fun c : ↥C => (⟨c, hCX c.2⟩ : ↥X))
    (fun c : ↥C => (⟨x₀ * c, X.mul_mem hx₀X (hCX c.2)⟩ : ↥X)) s
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    by_cases hyC : y ∈ C
    · exact ⟨Sum.inl ⟨y, hyC⟩, rfl⟩
    · refine ⟨Sum.inr ⟨x₀⁻¹ * y, h _ (X.inv_mem hx₀X) y hy hinv hyC⟩, ?_⟩
      simp [f]
  have h1 := Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_sum] at h1
  omega

end S126L23c

end CFSG.Quasithin.H13
