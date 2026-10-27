module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockFrame

public section

namespace CFSG.StandardType

namespace RootPlaneSU

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB

section Pieces

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

theorem exists_two_pieces_room (hA : MaxElemAb p A) (hcard : p ^ 4 ≤ Nat.card A) :
    ∃ y₁ y₂, IsPiece h p A ⊥ y₁ ∧ IsPiece h p A (rng y₁) y₂ ∧
      finrank K (rng y₁) + finrank K (rng y₂) + 2 * finrank K (rng y₁) ≤ n ∧
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

end Pieces

section Frame

variable {K : Type} [Field K] {σ : K →+* K} {V : Type} {n d₁ d₂ d₃ : ℕ}

@[expose] noncomputable def frameVec3 (hn : n = d₁ + d₂ + d₃) (e₁ : Fin d₁ → V) (e₂ : Fin d₂ → V)
    (m : Fin d₃ → V) (c : Fin n) : V :=
  if h₁ : (c : ℕ) < d₁ then e₁ ⟨c, h₁⟩
  else if h₂ : (c : ℕ) < d₁ + d₂ then e₂ ⟨c - d₁, by omega⟩
  else m ⟨c - d₁ - d₂, by have := c.isLt; omega⟩

variable (hn : n = d₁ + d₂ + d₃) (e₁ : Fin d₁ → V) (e₂ : Fin d₂ → V) (m : Fin d₃ → V)

theorem frameVec3_of_lt {c : Fin n} (hc : (c : ℕ) < d₁) :
    frameVec3 hn e₁ e₂ m c = e₁ ⟨c, hc⟩ := by
  rw [frameVec3, dite_eq_left hc]

theorem frameVec3_of_mid {c : Fin n} (hc₁ : d₁ ≤ (c : ℕ)) (hc₂ : (c : ℕ) < d₁ + d₂) :
    frameVec3 hn e₁ e₂ m c = e₂ ⟨c - d₁, by omega⟩ := by
  rw [frameVec3, dite_eq_right (by omega), dite_eq_left hc₂]

theorem frameVec3_of_ge {c : Fin n} (hc : d₁ + d₂ ≤ (c : ℕ)) :
    frameVec3 hn e₁ e₂ m c = m ⟨c - d₁ - d₂, by have := c.isLt; omega⟩ := by
  rw [frameVec3, dite_eq_right (by omega), dite_eq_right (by omega)]

variable [AddCommGroup V] [Module K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {U₁ U₂ M : Submodule K V}

theorem frameVec3_orthonormal (he₁ : ∀ i, e₁ i ∈ U₁) (he₂ : ∀ i, e₂ i ∈ U₂) (hm : ∀ i, m i ∈ M)
    (ho₁ : ∀ i j, B (e₁ i) (e₁ j) = if i = j then 1 else 0)
    (ho₂ : ∀ i j, B (e₂ i) (e₂ j) = if i = j then 1 else 0)
    (hoM : ∀ i j, B (m i) (m j) = if i = j then 1 else 0)
    (h12 : ∀ u ∈ U₁, ∀ w ∈ U₂, B u w = 0 ∧ B w u = 0)
    (h1M : ∀ u ∈ U₁, ∀ z ∈ M, B u z = 0 ∧ B z u = 0)
    (h2M : ∀ u ∈ U₂, ∀ z ∈ M, B u z = 0 ∧ B z u = 0) (i j : Fin n) :
    B (frameVec3 hn e₁ e₂ m i) (frameVec3 hn e₁ e₂ m j) = if i = j then 1 else 0 := by
  have hcase : ∀ c : Fin n, (c : ℕ) < d₁ ∨ (d₁ ≤ (c : ℕ) ∧ (c : ℕ) < d₁ + d₂) ∨
      d₁ + d₂ ≤ (c : ℕ) := by
    intro c
    omega
  have hne : ∀ {a b : Fin n}, (a : ℕ) ≠ b → a ≠ b := fun h hab => h (congrArg Fin.val hab)
  rcases hcase i with hi | ⟨hi, hi'⟩ | hi <;> rcases hcase j with hj | ⟨hj, hj'⟩ | hj
  · rw [frameVec3_of_lt hn e₁ e₂ m hi, frameVec3_of_lt hn e₁ e₂ m hj, ho₁]
    simp only [Fin.ext_iff]
  · rw [frameVec3_of_lt hn e₁ e₂ m hi, frameVec3_of_mid hn e₁ e₂ m hj hj',
      (h12 _ (he₁ _) _ (he₂ _)).1, ite_eq_right (hne (by omega))]
  · rw [frameVec3_of_lt hn e₁ e₂ m hi, frameVec3_of_ge hn e₁ e₂ m hj,
      (h1M _ (he₁ _) _ (hm _)).1, ite_eq_right (hne (by omega))]
  · rw [frameVec3_of_mid hn e₁ e₂ m hi hi', frameVec3_of_lt hn e₁ e₂ m hj,
      (h12 _ (he₁ _) _ (he₂ _)).2, ite_eq_right (hne (by omega))]
  · rw [frameVec3_of_mid hn e₁ e₂ m hi hi', frameVec3_of_mid hn e₁ e₂ m hj hj', ho₂]
    simp only [Fin.ext_iff]
    by_cases hij : (i : ℕ) = j
    · rw [ite_eq_left (by omega), ite_eq_left hij]
    · rw [ite_eq_right (by omega), ite_eq_right hij]
  · rw [frameVec3_of_mid hn e₁ e₂ m hi hi', frameVec3_of_ge hn e₁ e₂ m hj,
      (h2M _ (he₂ _) _ (hm _)).1, ite_eq_right (hne (by omega))]
  · rw [frameVec3_of_ge hn e₁ e₂ m hi, frameVec3_of_lt hn e₁ e₂ m hj,
      (h1M _ (he₁ _) _ (hm _)).2, ite_eq_right (hne (by omega))]
  · rw [frameVec3_of_ge hn e₁ e₂ m hi, frameVec3_of_mid hn e₁ e₂ m hj hj',
      (h2M _ (he₂ _) _ (hm _)).2, ite_eq_right (hne (by omega))]
  · rw [frameVec3_of_ge hn e₁ e₂ m hi, frameVec3_of_ge hn e₁ e₂ m hj, hoM]
    simp only [Fin.ext_iff]
    by_cases hij : (i : ℕ) = j
    · rw [ite_eq_left (by omega), ite_eq_left hij]
    · rw [ite_eq_right (by omega), ite_eq_right hij]

end Frame

theorem card_filter_le_val (n k : ℕ) :
    (Finset.univ.filter fun c : Fin n => k ≤ (c : ℕ)).card = n - k := by
  have h : (Finset.univ.filter fun c : Fin n => k ≤ (c : ℕ)).map Fin.valEmbedding =
      Finset.Ico k n := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Nat.card_Ico]

section Core

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

theorem exists_plane_frame (hA : MaxElemAb p A) (hcard : p ^ 4 ≤ Nat.card A) :
    ∃ (Q : GL (Fin n) K) (S₁ S₂ : Finset (Fin n)) (a₁ a₂ : ↥(unitarySU 2 f K n)),
      ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (Q : Matrix (Fin n) (Fin n) K) = 1 ∧
      a₁ ∈ A ∧ a₂ ∈ A ∧ Disjoint S₁ S₂ ∧ S₁.Nonempty ∧ S₂.Nonempty ∧ 4 ≤ (S₁ ∪ S₂)ᶜ.card ∧
      TableBUE.IsBlockOn S₁
        ((Q⁻¹ * (a₁ : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (∀ v : Fin n → K, ((Q⁻¹ * (a₁ : GL (Fin n) K) * Q : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ v = v → ∀ k ∈ S₁, v k = 0) ∧
      TableBUE.IsBlockOn S₂
        ((Q⁻¹ * (a₂ : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (∀ v : Fin n → K, ((Q⁻¹ * (a₂ : GL (Fin n) K) * Q : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ v = v → ∀ k ∈ S₂, v k = 0) ∧
      ∀ c ∈ A, TableBUE.IsBlockOn (S₁ ∪ S₂)
          ((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
        ∃ i j : ℕ, c = a₁ ^ i * a₂ ^ j := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  set B := stdHermForm h n with hBdef
  have hBs : B.IsSymm := stdHermForm_isSymm h n
  obtain ⟨y₁, y₂, hy₁, hy₂, hroom, hgen⟩ := exists_two_pieces_room (h := h) hA hcard
  set U₁ := rng y₁ with hU₁
  set U₂ := rng y₂ with hU₂
  have hnd₁ : NondegOn B U₁ := hy₁.nondegOn hA
  have hnd₂ : NondegOn B U₂ := hy₂.nondegOn hA
  have h12 : ∀ u ∈ U₁, ∀ w ∈ U₂, B u w = 0 ∧ B w u = 0 := fun u hu w hw =>
    ⟨(hy₂.orth w hw u hu).2, (hy₂.orth w hw u hu).1⟩
  have hsep : ∀ {U : Submodule K (Fin n → K)}, NondegOn B U →
      (B.domRestrict₁₂ U U).SeparatingLeft := by
    intro U hU u hu
    refine Subtype.ext (hU u u.2 fun w hw => ?_)
    rw [← hBs.eq (u : Fin n → K) w]
    rw [show B u w = 0 from hu ⟨w, hw⟩, map_zero]
  set d₁ := finrank K U₁ with hd₁
  set d₂ := finrank K U₂ with hd₂
  obtain ⟨e₁, he₁⟩ := h.exists_orthonormal_basis (hBs.domRestrict U₁) (hsep hnd₁)
  have he₁' : ∀ i j, B (e₁ i : Fin n → K) (e₁ j) = if i = j then 1 else 0 := fun i j => he₁ i j
  obtain ⟨e₂, he₂⟩ := h.exists_orthonormal_basis (hBs.domRestrict U₂) (hsep hnd₂)
  have he₂' : ∀ i j, B (e₂ i : Fin n → K) (e₂ j) = if i = j then 1 else 0 := fun i j => he₂ i j
  have h21 : ∀ u ∈ U₂, ∀ v ∈ U₁, B u v = 0 ∧ B v u = 0 := fun u hu v hv =>
    ⟨(h12 v hv u hu).2, (h12 v hv u hu).1⟩
  have hW : NondegOn B (U₁ ⊔ U₂) := nondegOn_sup hnd₁ hnd₂ h21
  set M := (U₁ ⊔ U₂).orthogonalBilin B with hM
  have hcompl : IsCompl (U₁ ⊔ U₂) M :=
    CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hW
  have hMnd : NondegOn B M := by
    intro z hz hn
    refine stdHermForm_separatingLeft h n z fun v => ?_
    obtain ⟨w, hw, z', hz', rfl⟩ := exists_add_orth hW v
    rw [map_add, ← hBs.eq w z, ← hBs.eq z' z, (Submodule.mem_orthogonalBilin.mp hz) w hw,
      hn z' hz', map_zero, add_zero]
  obtain ⟨m₀, hm₀⟩ := h.exists_orthonormal_basis (hBs.domRestrict M) (hsep hMnd)
  have hdimW : finrank K ↥(U₁ ⊔ U₂) = d₁ + d₂ := hy₂.finrank_sup hnd₁
  have hdimM : finrank K M = n - (d₁ + d₂) := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fin_fun, hdimW] at this
    omega
  have hd₁2 : 2 ≤ d₁ := two_le_finrank_rng h hA hy₁.mem hy₁.ne_one
  have hd₂2 : 2 ≤ d₂ := two_le_finrank_rng h hA hy₂.mem hy₂.ne_one
  have hn : n = d₁ + d₂ + (n - (d₁ + d₂)) := by omega
  set e₁' : Fin d₁ → (Fin n → K) := fun i => (e₁ i : Fin n → K) with he₁'def
  set e₂' : Fin d₂ → (Fin n → K) := fun i => (e₂ i : Fin n → K) with he₂'def
  set m' : Fin (n - (d₁ + d₂)) → (Fin n → K) := fun i => (m₀ (Fin.cast hdimM.symm i) : Fin n → K)
    with hm'def
  set b := frameVec3 hn e₁' e₂' m' with hb
  have h1M : ∀ u ∈ U₁, ∀ z ∈ M, B u z = 0 ∧ B z u = 0 := fun u hu z hz =>
    ⟨(Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_left hu), by
      rw [← hBs.eq, (Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_left hu),
        map_zero]⟩
  have h2M : ∀ u ∈ U₂, ∀ z ∈ M, B u z = 0 ∧ B z u = 0 := fun u hu z hz =>
    ⟨(Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_right hu), by
      rw [← hBs.eq, (Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_right hu),
        map_zero]⟩
  have hbo : ∀ i j, B (b i) (b j) = if i = j then 1 else 0 :=
    frameVec3_orthonormal hn e₁' e₂' m' (fun i => (e₁ i).2) (fun i => (e₂ i).2)
      (fun i => (m₀ _).2) he₁' he₂' (fun i j => by
        have := hm₀ (Fin.cast hdimM.symm i) (Fin.cast hdimM.symm j)
        simp only [LinearMap.domRestrict₁₂_apply, Fin.cast_inj] at this
        exact this) h12 h1M h2M
  have hbU₁ : ∀ c : Fin n, (c : ℕ) < d₁ → b c ∈ U₁ := fun c hc => by
    rw [hb, frameVec3_of_lt hn e₁' e₂' m' hc]
    exact (e₁ _).2
  have hbU₂ : ∀ c : Fin n, d₁ ≤ (c : ℕ) → (c : ℕ) < d₁ + d₂ → b c ∈ U₂ := fun c hc hc' => by
    rw [hb, frameVec3_of_mid hn e₁' e₂' m' hc hc']
    exact (e₂ _).2
  have hbM : ∀ c : Fin n, d₁ + d₂ ≤ (c : ℕ) → b c ∈ M := fun c hc => by
    rw [hb, frameVec3_of_ge hn e₁' e₂' m' hc]
    exact (m₀ _).2
  set S₁ : Finset (Fin n) := Finset.univ.filter fun c => (c : ℕ) < d₁ with hS₁
  set S₂ : Finset (Fin n) := Finset.univ.filter fun c => d₁ ≤ (c : ℕ) ∧ (c : ℕ) < d₁ + d₂
    with hS₂
  have hmem₁ : ∀ c : Fin n, c ∈ S₁ ↔ (c : ℕ) < d₁ := fun c => by simp [hS₁]
  have hmem₂ : ∀ c : Fin n, c ∈ S₂ ↔ d₁ ≤ (c : ℕ) ∧ (c : ℕ) < d₁ + d₂ := fun c => by simp [hS₂]
  have hmem₁₂ : ∀ c : Fin n, c ∈ S₁ ∪ S₂ ↔ (c : ℕ) < d₁ + d₂ := fun c => by
    rw [Finset.mem_union, hmem₁, hmem₂]
    omega
  have hS₃ : (S₁ ∪ S₂)ᶜ = Finset.univ.filter fun c : Fin n => d₁ + d₂ ≤ (c : ℕ) := by
    ext c
    rw [Finset.mem_compl, hmem₁₂, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    omega
  have hy₁t : ∀ c : Fin n, c ∉ S₁ → lin y₁ (b c) = b c := by
    intro c hc
    rw [hmem₁] at hc
    refine triv_orth_rng (h := h) hA hy₁.mem _ (Submodule.mem_orthogonalBilin.mpr fun u hu => ?_)
    rcases Nat.lt_or_ge (c : ℕ) (d₁ + d₂) with h2 | h2
    · exact (h12 u hu _ (hbU₂ c (by omega) h2)).1
    · exact (h1M u hu _ (hbM c h2)).1
  have hy₂t : ∀ c : Fin n, c ∉ S₂ → lin y₂ (b c) = b c := by
    intro c hc
    rw [hmem₂] at hc
    refine triv_orth_rng (h := h) hA hy₂.mem _ (Submodule.mem_orthogonalBilin.mpr fun u hu => ?_)
    rcases Nat.lt_or_ge (c : ℕ) d₁ with h1 | h1
    · exact (h12 _ (hbU₁ c h1) u hu).2
    · exact (h2M u hu _ (hbM c (by omega))).1
  set Qm := colMat b with hQm
  have hQQ : (Qm.map h.bar)ᵀ * Qm = 1 := conjTr_colMat_mul_self h hbo
  set Q : GL (Fin n) K := ⟨Qm, (Qm.map h.bar)ᵀ, mul_eq_one_comm.mp hQQ, hQQ⟩ with hQdef
  have hQiv : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (Qm.map h.bar)ᵀ := rfl
  have hN : ∀ (c : ↥(unitarySU 2 f K n)) (i j : Fin n),
      ((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        B (b i) (lin c (b j)) := by
    intro c i j
    rw [Units.val_mul, Units.val_mul, hQiv, lin_apply]
    exact conjTr_colMat_mul_apply h b _ i j
  have hcQ : ∀ (c : ↥(unitarySU 2 f K n)) (v : Fin n → K), mx c *ᵥ (Qm *ᵥ v) =
      Qm *ᵥ (((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    intro c v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, hQiv]
    change _ = (Qm * ((Qm.map h.bar)ᵀ * mx c * Qm)) *ᵥ v
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hQQ, Matrix.one_mul]
  have hcoord : ∀ (v : Fin n → K) (k : Fin n), B (b k) (Qm *ᵥ v) = v k := by
    intro v k
    rw [colMat_mulVec, map_sum]
    simp only [map_smul, hbo, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hexp : ∀ v : Fin n → K, Qm *ᵥ (fun k => B (b k) v) = v := by
    intro v
    have h1 : (fun k => B (b k) v) = (Qm.map h.bar)ᵀ *ᵥ v := by
      funext k
      rw [stdHermForm_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hQm, colMat,
        Matrix.of_apply]
    rw [h1, Matrix.mulVec_mulVec, mul_eq_one_comm.mp hQQ, Matrix.one_mulVec]
  have hQQ' : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (Q : Matrix (Fin n) (Fin n) K) = 1 :=
    hQQ
  have hblock : ∀ (y : ↥(unitarySU 2 f K n)) (S : Finset (Fin n)),
      (∀ c, c ∉ S → lin y (b c) = b c) → TableBUE.IsBlockOn S
        ((Q⁻¹ * (y : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro y S hyS i j hij
    rw [hN, Matrix.one_apply, ← hbo]
    rcases hij with hi | hj
    · rw [← isometry_lin h y (b i) (b j), hyS i hi]
    · rw [hyS j hj]
  have hfix : ∀ y ∈ A, ∀ S : Finset (Fin n), (∀ c ∈ S, b c ∈ rng y) →
      ∀ v : Fin n → K, ((Q⁻¹ * (y : GL (Fin n) K) * Q : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v = v → ∀ k ∈ S, v k = 0 := by
    intro y hyA S hS v hv k hk
    have hxv : lin y (Qm *ᵥ v) = Qm *ᵥ v := by rw [lin_apply, hcQ, hv]
    have hker : Qm *ᵥ v ∈ (rng y).orthogonalBilin B := by
      rw [rng_orth_eq_ker (h := h) hA hyA, LinearMap.mem_ker, LinearMap.sub_apply,
        Module.End.one_apply, hxv, sub_self]
    rw [← hcoord v k]
    exact (Submodule.mem_orthogonalBilin.mp hker) _ (hS k hk)
  refine ⟨Q, S₁, S₂, y₁, y₂, hQQ', hy₁.mem, hy₂.mem, ?_, ⟨⟨0, by omega⟩, (hmem₁ _).mpr
    (by simp only; omega)⟩, ⟨⟨d₁, by omega⟩, (hmem₂ _).mpr (by simp only; omega)⟩, ?_,
    hblock y₁ S₁ hy₁t, hfix y₁ hy₁.mem S₁ fun c hc => hbU₁ c ((hmem₁ c).mp hc),
    hblock y₂ S₂ hy₂t, hfix y₂ hy₂.mem S₂ fun c hc => hbU₂ c ((hmem₂ c).mp hc).1
      ((hmem₂ c).mp hc).2, ?_⟩
  · rw [Finset.disjoint_left]
    intro c h1 h2
    rw [hmem₁] at h1
    rw [hmem₂] at h2
    omega
  · rw [hS₃, card_filter_le_val]
    omega
  ·
    intro c hc hcb
    refine hgen c hc fun v hv => ?_
    set u : Fin n → K := fun k => B (b k) v with hu
    have hu0 : ∀ k ∈ S₁ ∪ S₂, u k = 0 := by
      intro k hk
      rw [hmem₁₂] at hk
      rcases Nat.lt_or_ge (k : ℕ) d₁ with h1 | h1
      · exact (h1M _ (hbU₁ k h1) _ hv).1
      · exact (h2M _ (hbU₂ k h1 hk) _ hv).1
    have hNu : ((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u =
        u := by
      funext i
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · by_cases hi : i ∈ S₁ ∪ S₂
        · rw [hu0 i hi, mul_zero]
        · rw [hcb i i (Or.inl hi), Matrix.one_apply_eq, one_mul]
      · intro k _ hki
        by_cases hk : k ∈ S₁ ∪ S₂
        · rw [hu0 k hk, mul_zero]
        · rw [hcb i k (Or.inr hk), Matrix.one_apply_ne (Ne.symm hki), zero_mul]
      · simp
    rw [← hexp v, lin_apply, hcQ, hNu]

end Core

section Block

variable {n : ℕ} {F : Type} [Field F]

theorem isBlockOn_mono {S T : Finset (Fin n)} {N : Matrix (Fin n) (Fin n) F}
    (hN : TableBUE.IsBlockOn S N) (hST : S ⊆ T) : TableBUE.IsBlockOn T N :=
  fun i j hij => hN i j (hij.imp (fun hi hiS => hi (hST hiS)) (fun hj hjS => hj (hST hjS)))

theorem mulVec_apply_of_not_mem {S : Finset (Fin n)} {N : Matrix (Fin n) (Fin n) F}
    (hN : TableBUE.IsBlockOn S N) (v : Fin n → F) {k : Fin n} (hk : k ∉ S) :
    (N *ᵥ v) k = v k := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single k]
  · rw [hN k k (Or.inl hk), Matrix.one_apply_eq, one_mul]
  · intro l _ hlk
    rw [hN k l (Or.inl hk), Matrix.one_apply_ne (Ne.symm hlk), zero_mul]
  · simp

theorem fix_mul_of_block {S₁ S₂ : Finset (Fin n)} {N₁ N₂ : Matrix (Fin n) (Fin n) F}
    (h₁ : TableBUE.IsBlockOn S₁ N₁) (h₂ : TableBUE.IsBlockOn S₂ N₂) (hd : Disjoint S₁ S₂)
    (hf₁ : ∀ v : Fin n → F, N₁ *ᵥ v = v → ∀ k ∈ S₁, v k = 0)
    (hf₂ : ∀ v : Fin n → F, N₂ *ᵥ v = v → ∀ k ∈ S₂, v k = 0)
    (v : Fin n → F) (hv : (N₁ * N₂) *ᵥ v = v) : ∀ k ∈ S₁ ∪ S₂, v k = 0 := by
  have hw : N₁ *ᵥ (N₂ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hv]
  have h2v : N₂ *ᵥ v = v := by
    funext k
    by_cases hk : k ∈ S₂
    · have hk1 : k ∉ S₁ := Finset.disjoint_right.mp hd hk
      have := congrFun hw k
      rw [mulVec_apply_of_not_mem h₁ _ hk1] at this
      exact this
    · exact mulVec_apply_of_not_mem h₂ v hk
  have h1v : N₁ *ᵥ v = v := by
    rw [h2v] at hw
    exact hw
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact hf₁ v h1v k hk
  · exact hf₂ v h2v k hk

theorem fix_of_pow_fix {N : Matrix (Fin n) (Fin n) F} {p : ℕ} (hp : p.Prime) (hNp : N ^ p = 1)
    {i : ℕ} (hi : ¬ p ∣ i) {v : Fin n → F} (hv : (N ^ i) *ᵥ v = v) : N *ᵥ v = v := by
  obtain ⟨i', -, hii'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi).symm hp.one_lt
  have hpow : ∀ k : ℕ, ((N ^ i) ^ k) *ᵥ v = v := by
    intro k
    induction k with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hN : (N ^ i) ^ i' = N := by
    rw [← pow_mul, ← Nat.mod_add_div (i * i') p, hii', pow_add, pow_mul, hNp, one_pow, mul_one,
      pow_one]
  rw [← hN]
  exact hpow i'

end Block

section Unitary

variable {f n : ℕ} {K : Type} [Field K]

theorem fixRow_of_fix (h : UnitaryFieldData 2 f K) (a : ↥(unitarySU 2 f K n)) {T : Finset (Fin n)}
    (hfix : ∀ v : Fin n → K, mx a *ᵥ v = v → ∀ k ∈ T, v k = 0) :
    ∀ v : Fin n → K, v ᵥ* mx a = v → ∀ k ∈ T, v k = 0 := by
  intro v hv k hk
  obtain ⟨-, hNN⟩ := (mem_unitarySU_iff h).mp a.2
  set N := mx a with hNdef
  have hNN' : N * (N.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hNN
  set w : Fin n → K := fun k => h.bar (v k) with hw
  have hw1 : (N.map h.bar)ᵀ *ᵥ w = w := by
    funext j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hw]
    rw [← this, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
  have hw2 : N *ᵥ w = w := by
    rw [← hw1, Matrix.mulVec_mulVec, hNN', Matrix.one_mulVec, hw1]
  have := hfix w hw2 k hk
  exact (h.bar_eq_zero_iff).mp this

end Unitary

end RootPlaneSU

end CFSG.StandardType
