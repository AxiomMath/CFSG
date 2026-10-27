module

public import CFSG.Quasithin.Recognition.CertOvergroup

public section

namespace CFSG.Quasithin.F134

theorem closure_subset_of_left_closed {G : Type*} [Group G] {S P : Set G}
    (hord : ∀ s ∈ S, ∃ n : ℕ, 0 < n ∧ s ^ n = 1) (h1 : (1 : G) ∈ P)
    (hmul : ∀ p ∈ P, ∀ s ∈ S, s * p ∈ P) : ↑(Subgroup.closure S) ⊆ P := by
  have hinv : ↑(Subgroup.closure S) ⊆ {g : G | g⁻¹ ∈ P} := by
    refine CFSG.Quasithin.closure_subset_of_right_closed (S := S) hord (by simpa using h1) ?_
    intro p hp s hs
    change p⁻¹ ∈ P at hp
    change (p * s)⁻¹ ∈ P
    rw [mul_inv_rev]
    obtain ⟨n, hn, hsn⟩ := hord s hs
    have hsinv : s⁻¹ = s ^ (n - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hn, hsn]
    have key : ∀ k : ℕ, s ^ k * p⁻¹ ∈ P := by
      intro k
      induction k with
      | zero => simpa using hp
      | succ k ih =>
        rw [pow_succ', mul_assoc]
        exact hmul _ ih s hs
    rw [hsinv]
    exact key _
  intro g hg
  have := hinv ((Subgroup.closure S).inv_mem hg)
  simpa using this

@[expose] def pcSub {G : Type*} [Group G] (n : ℕ) (x : ℕ → G) (k : ℕ) : Subgroup G :=
  Subgroup.closure {y | ∃ l, k ≤ l ∧ l < n ∧ x l = y}

theorem mem_pcSub {G : Type*} [Group G] {n : ℕ} {x : ℕ → G} {k l : ℕ} (hk : k ≤ l) (hl : l < n) :
    x l ∈ pcSub n x k :=
  Subgroup.subset_closure ⟨l, hk, hl, rfl⟩

theorem isPGroup_two_of_pc {G : Type*} [Group G] [Finite G] (n : ℕ) (x : ℕ → G)
    (hsq : ∀ i < n, x i ^ 2 ∈ pcSub n x (i + 1))
    (hcj : ∀ i < n, ∀ j < n, i < j → (x i)⁻¹ * x j * x i ∈ pcSub n x (i + 1)) :
    IsPGroup 2 (pcSub n x 0) := by
  have hord : ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1 :=
    fun g => ⟨orderOf g, orderOf_pos g, pow_orderOf_eq_one g⟩
  have key : ∀ d k, n - k = d → ∀ g ∈ pcSub n x k, ∃ m : ℕ, g ^ 2 ^ m = 1 := by
    intro d
    induction d with
    | zero =>
      intro k hk g hg
      have hbot : pcSub n x k = ⊥ := by
        unfold pcSub
        rw [Subgroup.closure_eq_bot_iff]
        rintro y ⟨l, hl, hln, -⟩
        omega
      rw [hbot, Subgroup.mem_bot] at hg
      exact ⟨0, by rw [hg, one_pow]⟩
    | succ d ih =>
      intro k hk g hg
      have hkn : k < n := by omega
      set S' := pcSub n x (k + 1) with hS'
      have hconj : ∀ u ∈ S', (x k)⁻¹ * u * x k ∈ S' := by
        have hle : S' ≤ S'.comap (MulAut.conj (x k)⁻¹).toMonoidHom := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro _ ⟨l, hl, hln, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            inv_inv]
          exact hcj k hkn l hln (by omega)
        intro u hu
        have := hle hu
        simpa [MulAut.conj_apply] using this
      have hW : ↑(pcSub n x k) ⊆ {g : G | g ∈ S' ∨ (x k)⁻¹ * g ∈ S'} := by
        unfold pcSub
        refine CFSG.Quasithin.closure_subset_of_right_closed
          (S := {y | ∃ l, k ≤ l ∧ l < n ∧ x l = y}) (P := {g : G | g ∈ S' ∨ (x k)⁻¹ * g ∈ S'})
          (fun s _ => hord s) (Or.inl S'.one_mem) ?_
        rintro p hp s ⟨l, hl, hln, rfl⟩
        rcases Nat.lt_or_ge k l with hkl | hkl
        · have hs : x l ∈ S' := mem_pcSub (by omega) hln
          rcases hp with hp | hp
          · exact Or.inl (S'.mul_mem hp hs)
          · exact Or.inr (by rw [← mul_assoc]; exact S'.mul_mem hp hs)
        · have hlk : l = k := by omega
          subst hlk
          rcases hp with hp | hp
          · exact Or.inr (by rw [← mul_assoc]; exact hconj p hp)
          · left
            have e : p * x l = x l ^ 2 * ((x l)⁻¹ * ((x l)⁻¹ * p) * x l) := by
              rw [sq]
              group
            rw [e]
            exact S'.mul_mem (hsq l hkn) (hconj _ hp)
      have hsq' : g ^ 2 ∈ S' := by
        rcases hW hg with h | h
        · exact S'.pow_mem h 2
        · have e : g ^ 2 = x k ^ 2 * ((x k)⁻¹ * ((x k)⁻¹ * g) * x k) * ((x k)⁻¹ * g) := by
            rw [sq, sq]
            group
          rw [e]
          exact S'.mul_mem (S'.mul_mem (hsq k hkn) (hconj _ h)) h
      obtain ⟨m, hm⟩ := ih (k + 1) (by omega) _ hsq'
      exact ⟨m + 1, by rw [pow_succ', pow_mul, hm]⟩
  intro g
  obtain ⟨m, hm⟩ := key (n - 0) 0 rfl g g.2
  exact ⟨m, Subtype.ext (by simpa using hm)⟩

end CFSG.Quasithin.F134
