module

public import CFSG.RankThree.PartOne.S12.ReflectionFacts

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

structure Model {G : Type} [Group G] [Finite G] (p : ℕ) (E : Subgroup G) (c : E) where
  prime : p.Prime
  five_le : 5 ≤ p
  elem : IsElementaryAbelian p E
  card : Nat.card E = p ^ 4
  hc1 : c ≠ 1
  ψ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 5)
  k : Fin 5
  Λ : Subgroup (MulAut E)
  Λ_k : ∀ x ∈ Λ, ∃ h : x ∈ reflectionGroup p E, ψ ⟨x, h⟩ k = k
  Λ_stab : ∀ σ : Equiv.Perm (Fin 5), σ k = k →
    ((ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E) ∈ Λ
  Λ_c : ∀ x ∈ Λ, x c = c
  key : ∀ e : E, (∀ x ∈ reflectionGroup p E, x e = e) → e = 1
  D_ne : (reflectionSet p E).Nonempty
  span : ∀ N : Subgroup E, (∀ x ∈ reflectionGroup p E, ∀ m ∈ N, x m ∈ N) → c ∈ N →
    N = ⊤ ∨ N ≤ Subgroup.zpowers c

namespace Model

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} {c : E} (M : Model p E c)

theorem fixc (σ : Equiv.Perm (Fin 5)) (hσ : σ M.k = M.k) :
    ((M.ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E) c = c :=
  M.Λ_c _ (M.Λ_stab σ hσ)

noncomputable def T (a b : Fin 5) : MulAut E :=
  ((M.ψ.symm (Equiv.swap a b) : ↥(reflectionGroup p E)) : MulAut E)

theorem T_mul_self (a b : Fin 5) : M.T a b * M.T a b = 1 := by
  unfold T
  rw [← Subgroup.coe_mul, ← map_mul, Equiv.swap_mul_self, map_one, Subgroup.coe_one]

theorem T_fix {a b : Fin 5} (ha : a ≠ M.k) (hb : b ≠ M.k) : M.T a b c = c :=
  M.fixc _ (Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb))

theorem T_comm (a b : Fin 5) : M.T a b = M.T b a := by
  unfold T
  rw [Equiv.swap_comm]

theorem T_self (a : Fin 5) : M.T a a = 1 := by
  unfold T
  rw [Equiv.swap_self, ← Equiv.Perm.one_def, map_one, Subgroup.coe_one]

theorem swap_braid₁ : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
    Equiv.swap a c * Equiv.swap b c * Equiv.swap a c = Equiv.swap a b := by
  decide

theorem swap_braid₂ : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
    Equiv.swap b c * Equiv.swap a b * Equiv.swap b c = Equiv.swap a c := by
  decide

theorem T_braid₁ {a b : Fin 5} (hab : a ≠ b) (ha : a ≠ M.k) (hb : b ≠ M.k) :
    M.T a b = M.T a M.k * M.T b M.k * M.T a M.k := by
  unfold T
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
    swap_braid₁ a b M.k hab ha hb]

theorem T_braid₂ {a b : Fin 5} (hab : a ≠ b) (ha : a ≠ M.k) (hb : b ≠ M.k) :
    M.T a M.k = M.T b M.k * M.T a b * M.T b M.k := by
  unfold T
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
    swap_braid₂ a b M.k hab ha hb]

noncomputable def v (i : Fin 5) : E := M.T i M.k c

theorem v_k : M.v M.k = c := by
  unfold v
  rw [M.T_self]
  rfl

theorem equivariant (w : ↥(reflectionGroup p E)) (i : Fin 5) :
    (w : MulAut E) (M.v i) = M.v (M.ψ w i) := by
  set σ := M.ψ w with hσ
  set a : ↥(reflectionGroup p E) := M.ψ.symm (Equiv.swap i M.k) with ha
  set b : ↥(reflectionGroup p E) := M.ψ.symm (Equiv.swap (σ i) M.k) with hb
  set u : ↥(reflectionGroup p E) := b⁻¹ * w * a with hu
  have hψu : M.ψ u = (Equiv.swap (σ i) M.k)⁻¹ * σ * Equiv.swap i M.k := by
    simp [hu, ha, hb, hσ]
  have hk : M.ψ u M.k = M.k := by
    rw [hψu, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_inv, Equiv.swap_apply_left]
  have huc : (u : MulAut E) c = c := by
    have := M.fixc _ hk
    rwa [MulEquiv.symm_apply_apply] at this
  have hwa : w * a = b * u := by rw [hu]; group
  have h1 : (w : MulAut E) (M.v i) = ((w * a : ↥(reflectionGroup p E)) : MulAut E) c := rfl
  rw [h1, hwa, Subgroup.coe_mul, MulAut.mul_apply, huc]
  rfl

include M in
theorem orderOf_c : orderOf c = p := by
  have : Fact p.Prime := ⟨M.prime⟩
  have hd := RefFacts.ElemData.of_isElementaryAbelian (E := E) M.prime
    (by have := M.five_le; omega) M.elem
  exact orderOf_eq_prime (hd.pow c) M.hc1

include M in
theorem c_ne_inv : c ≠ c⁻¹ := by
  intro h
  have h2 : c ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 1 [h]; exact inv_mul_cancel c
  have := orderOf_dvd_of_pow_eq_one h2
  rw [M.orderOf_c] at this
  have := Nat.le_of_dvd (by norm_num) this
  have := M.five_le
  omega

theorem v_eq_or_inv {i : Fin 5} (h : M.v i ∈ Subgroup.zpowers c) :
    M.v i = c ∨ M.v i = c⁻¹ := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h
  have h1 : M.T i M.k c = c ^ m := hm.symm
  have hTT : M.T i M.k (M.T i M.k c) = c := by
    rw [← MulAut.mul_apply, M.T_mul_self]
    rfl
  have h2 : c ^ (m * m) = c := by
    have h3 : M.T i M.k (M.T i M.k c) = (c ^ m) ^ m := by
      rw [h1, map_zpow, h1]
    rw [hTT] at h3
    rw [zpow_mul]
    exact h3.symm
  have h4 : c ^ (m * m - 1) = 1 := by
    rw [zpow_sub_one, h2, mul_inv_cancel]
  have h5 : (p : ℤ) ∣ (m - 1) * (m + 1) := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h4
    rw [M.orderOf_c] at this
    have e : m * m - 1 = (m - 1) * (m + 1) := by ring
    rwa [e] at this
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 M.prime
  have hm' : M.v i = c ^ m := hm.symm
  rcases hpr.dvd_or_dvd h5 with h6 | h6
  · left
    have h7 : c ^ (m - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, M.orderOf_c]; exact h6
    rw [hm']
    calc c ^ m = c ^ ((m - 1) + 1) := by congr 1; ring
      _ = c ^ (m - 1) * c := zpow_add_one _ _
      _ = c := by rw [h7, one_mul]
  · right
    have h7 : c ^ (m + 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, M.orderOf_c]; exact h6
    rw [hm']
    calc c ^ m = c ^ ((m + 1) - 1) := by congr 1; ring
      _ = c ^ (m + 1) * c⁻¹ := zpow_sub_one _ _
      _ = c⁻¹ := by rw [h7, one_mul]

theorem inv_apply_of_apply_eq {H : Type*} [Group H] (g : MulAut H) {x : H} (h : g x = x) :
    g⁻¹ x = x := by
  calc g⁻¹ x = g⁻¹ (g x) := by rw [h]
    _ = x := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl

theorem span_eq_top : Subgroup.closure (Set.range M.v) = ⊤ := by
  set N : Subgroup E := Subgroup.closure (Set.range M.v) with hN
  have hstable : ∀ x ∈ reflectionGroup p E, ∀ m ∈ N, x m ∈ N := by
    intro x hx m hm
    induction hm using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have := M.equivariant ⟨x, hx⟩ i
      exact this ▸ Subgroup.subset_closure ⟨_, rfl⟩
    | one => simp
    | mul y z _ _ hy hz => rw [map_mul]; exact N.mul_mem hy hz
    | inv y _ hy => rw [map_inv]; exact N.inv_mem hy
  have hc : c ∈ N := by
    have := Subgroup.subset_closure (Set.mem_range_self (f := M.v) M.k)
    rwa [M.v_k] at this
  rcases M.span N hstable hc with h | h
  · exact h
  · exfalso
    have hv : ∀ i, M.v i ∈ Subgroup.zpowers c := fun i => h (Subgroup.subset_closure ⟨i, rfl⟩)
    have hcinv := M.c_ne_inv
    by_cases hall : ∀ i, M.v i = c
    · have hT : ∀ a b : Fin 5, M.T a b c = c := by
        intro a b
        by_cases ha : a = M.k <;> by_cases hb : b = M.k
        · subst ha; subst hb; rw [M.T_self]; rfl
        · subst ha; rw [M.T_comm]; exact hall b
        · subst hb; exact hall a
        · exact M.T_fix ha hb
      have key : ∀ σ ∈ Subgroup.closure {σ : Equiv.Perm (Fin 5) | σ.IsSwap},
          ((M.ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E) c = c := by
        intro σ hσ
        induction hσ using Subgroup.closure_induction with
        | mem σ hσ => obtain ⟨a, b, -, rfl⟩ := hσ; exact hT a b
        | one => simp
        | mul σ τ _ _ h1 h2 =>
          rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply, h2, h1]
        | inv σ _ h1 =>
          rw [map_inv, Subgroup.coe_inv]
          exact inv_apply_of_apply_eq _ h1
      refine M.hc1 (M.key c fun x hx => ?_)
      have := key (M.ψ ⟨x, hx⟩) (by rw [Equiv.Perm.closure_isSwap]; trivial)
      simpa using this
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hvi : M.v i = c⁻¹ := (M.v_eq_or_inv (hv i)).resolve_left hi
      have hik : i ≠ M.k := fun h' => hi (h' ▸ M.v_k)
      obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 5, j ≠ i ∧ j ≠ M.k := by
        have : ∀ i k : Fin 5, ∃ j : Fin 5, j ≠ i ∧ j ≠ k := by decide
        exact this i M.k
      have hvj := M.v_eq_or_inv (hv j)
      have e1 : M.T i M.k c = c⁻¹ := hvi
      have hTij : M.T i j c = c := M.T_fix hik hjk
      have hb1 : M.T i j c = M.T i M.k (M.T j M.k (M.T i M.k c)) := by
        rw [M.T_braid₁ (Ne.symm hji) hik hjk]
        simp [MulAut.mul_apply]
      have hvjc : M.v j = c := by
        rcases hvj with h' | h'
        · exact h'
        · exfalso
          have e2 : M.T j M.k c = c⁻¹ := h'
          rw [hb1, e1, map_inv, e2, inv_inv, e1] at hTij
          exact hcinv hTij.symm
      have e3 : M.T j M.k c = c := hvjc
      have hb2 : M.T i M.k c = M.T j M.k (M.T i j (M.T j M.k c)) := by
        rw [M.T_braid₂ (Ne.symm hji) hik hjk]
        simp [MulAut.mul_apply]
      rw [e3, hTij, e3] at hb2
      rw [hb2] at e1
      exact hcinv e1

end Model

end CFSG.RankThree.PartOne.U5K.Pkg
