module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPiece

public section

namespace CFSG.StandardType

namespace SUTB

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups

theorem card_le_of_forall_eq_mul {G : Type*} [Group G] {A : Subgroup G} {p : ℕ} [NeZero p]
    {y₁ y₂ y₃ : G} (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A) (hy₃ : y₃ ∈ A) (h₁ : y₁ ^ p = 1)
    (h₂ : y₂ ^ p = 1) (h₃ : y₃ ^ p = 1)
    (hA : ∀ c ∈ A, ∃ a b e : ℕ, c = y₁ ^ a * y₂ ^ b * y₃ ^ e) : Nat.card A ≤ p ^ 3 := by
  let F : Fin p × Fin p × Fin p → A := fun t =>
    ⟨y₁ ^ (t.1 : ℕ) * y₂ ^ (t.2.1 : ℕ) * y₃ ^ (t.2.2 : ℕ),
      A.mul_mem (A.mul_mem (A.pow_mem hy₁ _) (A.pow_mem hy₂ _)) (A.pow_mem hy₃ _)⟩
  have hmod : ∀ {y : G}, y ^ p = 1 → ∀ k : ℕ, y ^ k = y ^ (k % p) := by
    intro y hy k
    conv_lhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hy, one_pow, mul_one]
  have hF : Function.Surjective F := by
    rintro ⟨c, hc⟩
    obtain ⟨a, b, e, rfl⟩ := hA c hc
    refine ⟨(⟨a % p, Nat.mod_lt _ (NeZero.pos p)⟩, ⟨b % p, Nat.mod_lt _ (NeZero.pos p)⟩,
      ⟨e % p, Nat.mod_lt _ (NeZero.pos p)⟩), Subtype.ext ?_⟩
    change y₁ ^ (a % p) * y₂ ^ (b % p) * y₃ ^ (e % p) = _
    rw [← hmod h₁, ← hmod h₂, ← hmod h₃]
  calc Nat.card A ≤ Nat.card (Fin p × Fin p × Fin p) := Nat.card_le_card_of_surjective F hF
    _ = p ^ 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
      ring

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

theorem nondegOn_bot (h : UnitaryFieldData 2 f K) :
    NondegOn (stdHermForm h n) (⊥ : Submodule K (Fin n → K)) :=
  fun _ hm _ => (Submodule.mem_bot K).mp hm

theorem eq_one_of_triv {W : Submodule K (Fin n → K)} (hW : NondegOn (stdHermForm h n) W)
    {c : ↥(unitarySU 2 f K n)} (hcW : ∀ v ∈ W, lin c v = v)
    (hcW' : ∀ v ∈ W.orthogonalBilin (stdHermForm h n), lin c v = v) : c = 1 := by
  refine eq_of_lin_apply fun v => ?_
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hW v
  rw [map_add, hcW m hm, hcW' z hz, lin_one]
  rfl

theorem triv_orth_rng (hA : MaxElemAb p A) {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A) :
    ∀ v ∈ (rng y).orthogonalBilin (stdHermForm h n), lin y v = v := by
  intro v hv
  rw [rng_orth_eq_ker hA hy] at hv
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp hv)

theorem orth_anti {W W' : Submodule K (Fin n → K)} (hWW' : W ≤ W') :
    W'.orthogonalBilin (stdHermForm h n) ≤ W.orthogonalBilin (stdHermForm h n) :=
  fun _ hv => Submodule.mem_orthogonalBilin.mpr fun m hm =>
    (Submodule.mem_orthogonalBilin.mp hv) m (hWW' hm)

theorem exists_two_pieces (hA : MaxElemAb p A) (hcard : p ^ 4 ≤ Nat.card A) :
    ∃ y₁ y₂, IsPiece h p A ⊥ y₁ ∧ IsPiece h p A (rng y₁) y₂ ∧
      4 * finrank K (rng y₁) ≤ n ∧
      ∀ c ∈ A, (∀ v ∈ (rng y₁ ⊔ rng y₂).orthogonalBilin (stdHermForm h n), lin c v = v) →
        ∃ i j : ℕ, c = y₁ ^ i * y₂ ^ j := by
  classical
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  have hp1 := hA.prime.one_lt
  have hlt : ∀ k < 4, p ^ k < Nat.card A := fun k hk =>
    (Nat.pow_lt_pow_right hp1 hk).trans_le hcard
  have h1A : (1 : ↥(unitarySU 2 f K n)) ∈ A := A.one_mem
  have hp1' : (1 : ↥(unitarySU 2 f K n)) ^ p = 1 := one_pow p
  have hone : ∀ {X : Submodule K (Fin n → K)},
      ¬ (∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ X, lin c v = v) → ∀ c ∈ A, (∀ v ∈ X, lin c v = v) → c = 1 :=
    fun hcon c hc ht => by
      by_contra h1
      exact hcon ⟨c, hc, h1, ht⟩
  have hne₁ : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ (⊥ : Submodule K (Fin n → K)), lin c v = v := by
    by_contra hcon
    have hle := card_le_of_forall_eq_mul h1A h1A h1A hp1' hp1' hp1' fun c hc =>
      ⟨0, 0, 0, by
        rw [hone hcon c hc fun v hv => by rw [(Submodule.mem_bot K).mp hv, map_zero]]; simp⟩
    exact absurd hle (not_le.mpr (hlt 3 (by norm_num)))
  obtain ⟨y₁, hy₁⟩ := exists_isPiece (h := h) hA hne₁
  have hX₁ : NondegOn (stdHermForm h n) (⊥ ⊔ rng y₁) := hy₁.nondegOn_sup hA (nondegOn_bot h)
  rw [bot_sup_eq] at hX₁
  have hd₁ : ∀ c ∈ A, ∃ a : ℕ, ∃ c₁ ∈ A, c = y₁ ^ a * c₁ ∧ ∀ v ∈ rng y₁, lin c₁ v = v := by
    intro c hc
    obtain ⟨a, c₁, hc₁, rfl, hc₁t⟩ := hy₁.decomp hc fun v hv => by
      rw [(Submodule.mem_bot K).mp hv, map_zero]
    exact ⟨a, c₁, hc₁, rfl, fun v hv => hc₁t v (Submodule.mem_sup_right hv)⟩
  have hne₂ : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ rng y₁, lin c v = v := by
    by_contra hcon
    have hle := card_le_of_forall_eq_mul hy₁.mem h1A h1A (hA.pow y₁ hy₁.mem) hp1' hp1'
      fun c hc => by
        obtain ⟨a, c₁, hc₁, rfl, hc₁t⟩ := hd₁ c hc
        exact ⟨a, 0, 0, by rw [hone hcon c₁ hc₁ hc₁t]; simp⟩
    exact absurd hle (not_le.mpr (hlt 3 (by norm_num)))
  obtain ⟨y₂, hy₂⟩ := exists_isPiece (h := h) hA hne₂
  have hX₂ : NondegOn (stdHermForm h n) (rng y₁ ⊔ rng y₂) := hy₂.nondegOn_sup hA hX₁
  have hd₂ : ∀ c ∈ A, ∃ a b : ℕ, ∃ c₂ ∈ A, c = y₁ ^ a * y₂ ^ b * c₂ ∧
      ∀ v ∈ rng y₁ ⊔ rng y₂, lin c₂ v = v := by
    intro c hc
    obtain ⟨a, c₁, hc₁, rfl, hc₁t⟩ := hd₁ c hc
    obtain ⟨b, c₂, hc₂, rfl, hc₂t⟩ := hy₂.decomp hc₁ hc₁t
    exact ⟨a, b, c₂, hc₂, by group, hc₂t⟩
  have hne₃ : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ rng y₁ ⊔ rng y₂, lin c v = v := by
    by_contra hcon
    have hle := card_le_of_forall_eq_mul hy₁.mem hy₂.mem h1A (hA.pow y₁ hy₁.mem)
      (hA.pow y₂ hy₂.mem) hp1' fun c hc => by
        obtain ⟨a, b, c₂, hc₂, rfl, hc₂t⟩ := hd₂ c hc
        exact ⟨a, b, 0, by rw [hone hcon c₂ hc₂ hc₂t]; simp⟩
    exact absurd hle (not_le.mpr (hlt 3 (by norm_num)))
  obtain ⟨y₃, hy₃⟩ := exists_isPiece (h := h) hA hne₃
  have hX₃ : NondegOn (stdHermForm h n) (rng y₁ ⊔ rng y₂ ⊔ rng y₃) := hy₃.nondegOn_sup hA hX₂
  have hne₄ : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ rng y₁ ⊔ rng y₂ ⊔ rng y₃, lin c v = v := by
    by_contra hcon
    have hle := card_le_of_forall_eq_mul hy₁.mem hy₂.mem hy₃.mem (hA.pow y₁ hy₁.mem)
      (hA.pow y₂ hy₂.mem) (hA.pow y₃ hy₃.mem) fun c hc => by
        obtain ⟨a, b, c₂, hc₂, rfl, hc₂t⟩ := hd₂ c hc
        obtain ⟨e, c₃, hc₃, rfl, hc₃t⟩ := hy₃.decomp hc₂ hc₂t
        exact ⟨a, b, e, by rw [hone hcon c₃ hc₃ hc₃t, mul_one, mul_assoc]⟩
    exact absurd hle (not_le.mpr (hlt 3 (by norm_num)))
  obtain ⟨y₄, hy₄A, hy₄1, hy₄t⟩ := hne₄
  have hrk : ∀ c ∈ A, c ≠ 1 → finrank K (rng y₁) ≤ finrank K (rng c) := fun c hc hc1 =>
    hy₁.rk_le c hc hc1 fun v hv => by rw [(Submodule.mem_bot K).mp hv, map_zero]
  have hdim₂ := hy₂.finrank_sup hX₁
  have hdim₃ := hy₃.finrank_sup hX₂
  have hdim₄ : finrank K ↥(rng y₁ ⊔ rng y₂ ⊔ rng y₃ ⊔ rng y₄) =
      finrank K ↥(rng y₁ ⊔ rng y₂ ⊔ rng y₃) + finrank K (rng y₄) := by
    have hinf : (rng y₁ ⊔ rng y₂ ⊔ rng y₃) ⊓ rng y₄ = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => hX₃ v hv.1 fun m hm => ?_
      exact (rng_orth_of_triv (h := h) hy₄t v hv.2 m hm).2
    have := Submodule.finrank_sup_add_finrank_inf_eq (rng y₁ ⊔ rng y₂ ⊔ rng y₃) (rng y₄)
    rw [hinf, finrank_bot, add_zero] at this
    exact this
  have hle := Submodule.finrank_le (rng y₁ ⊔ rng y₂ ⊔ rng y₃ ⊔ rng y₄)
  rw [Module.finrank_fin_fun] at hle
  have r₂ := hrk y₂ hy₂.mem hy₂.ne_one
  have r₃ := hrk y₃ hy₃.mem hy₃.ne_one
  have r₄ := hrk y₄ hy₄A hy₄1
  refine ⟨y₁, y₂, hy₁, hy₂, by omega, fun c hc hco => ?_⟩
  obtain ⟨a, b, c₂, hc₂, rfl, hc₂t⟩ := hd₂ c hc
  refine ⟨a, b, ?_⟩
  have ht : ∀ {y : ↥(unitarySU 2 f K n)}, y ∈ A → rng y ≤ rng y₁ ⊔ rng y₂ → ∀ k : ℕ,
      ∀ v ∈ (rng y₁ ⊔ rng y₂).orthogonalBilin (stdHermForm h n), lin (y ^ k) v = v := by
    intro y hy hyle k v hv
    have hv' := triv_orth_rng hA hy v (orth_anti hyle hv)
    rw [SUTB.lin_pow]
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hv', ih]
  have hc₂1 : c₂ = 1 := by
    refine eq_one_of_triv hX₂ hc₂t fun v hv => ?_
    have h1 := hco v hv
    rw [SUTB.lin_mul, SUTB.lin_mul, Module.End.mul_apply, Module.End.mul_apply] at h1
    have e₂ := ht hy₂.mem le_sup_right b
    have e₁ := ht hy₁.mem le_sup_left a
    have hinj : ∀ (y : ↥(unitarySU 2 f K n)) {w w' : Fin n → K}, lin y w = lin y w' → w = w' := by
      intro y w w' hw
      have := congrArg (lin y⁻¹) hw
      rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← SUTB.lin_mul, inv_mul_cancel,
        SUTB.lin_one] at this
    refine hinj (y₁ ^ a * y₂ ^ b) ?_
    rw [SUTB.lin_mul, Module.End.mul_apply, Module.End.mul_apply, h1, e₂ v hv, e₁ v hv]
  rw [hc₂1, mul_one]

end SUTB

end CFSG.StandardType
