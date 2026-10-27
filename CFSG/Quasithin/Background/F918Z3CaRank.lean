module

public import CFSG.Quasithin.Background.F918Z3Ca
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.Quasithin

open scoped Matrix
open Module LinearMap

namespace InvolMat

section Intertwiners

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem card_intertwiners_le (n k : V →ₗ[K] V) (hk : k ∘ₗ k = 0) :
    Nat.card {m : V →ₗ[K] V // n ∘ₗ m = m ∘ₗ k} ≤
      Nat.card K ^ (finrank K (range k) * finrank K V +
        (finrank K V - 2 * finrank K (range k)) * (finrank K V - finrank K (range n))) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (ker k)
  obtain ⟨T₀, hT₀⟩ := Submodule.exists_isCompl (range k)
  have hrk : range k ≤ ker k := by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun hk y
  set T : Submodule K V := T₀ ⊓ ker k with hT
  have hTk : T ≤ ker k := inf_le_right
  have hTr : T ⊓ range k = ⊥ := by
    rw [hT, inf_assoc, inf_eq_right.2 hrk]
    exact hT₀.symm.inf_eq_bot
  have hTs : T ⊔ range k = ker k := by
    rw [hT, sup_comm, ← sup_inf_assoc_of_le T₀ hrk, hT₀.sup_eq_top, top_inf_eq]
  have hdec : ∀ u : V, ∃ c ∈ C, ∃ t ∈ T, ∃ c' ∈ C, u = c + t + k c' := by
    intro u
    have hu : u ∈ ker k ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hu
    have hwT : w ∈ T ⊔ range k := by rw [hTs]; exact hw
    obtain ⟨t, ht, r, hr, rfl⟩ := Submodule.mem_sup.1 hwT
    obtain ⟨y, rfl⟩ := hr
    have hy : y ∈ ker k ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨w', hw', c', hc', rfl⟩ := Submodule.mem_sup.1 hy
    refine ⟨c, hc, t, ht, c', hc', ?_⟩
    rw [map_add, show k w' = 0 from hw', zero_add]
    abel
  have hmemT : ∀ m : V →ₗ[K] V, n ∘ₗ m = m ∘ₗ k → ∀ t ∈ T, m t ∈ ker n := by
    intro m hm t ht
    have : n (m t) = m (k t) := LinearMap.congr_fun hm t
    rw [LinearMap.mem_ker, this, show k t = 0 from hTk ht, map_zero]
  let Θ : {m : V →ₗ[K] V // n ∘ₗ m = m ∘ₗ k} → (C →ₗ[K] V) × (T →ₗ[K] ker n) := fun m =>
    (m.1 ∘ₗ C.subtype, (m.1 ∘ₗ T.subtype).codRestrict (ker n) (fun t => hmemT m.1 m.2 t t.2))
  have hΘ : Function.Injective Θ := by
    rintro ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ h
    have hC' : ∀ c ∈ C, m₁ c = m₂ c := fun c hc =>
      LinearMap.congr_fun (congrArg Prod.fst h) ⟨c, hc⟩
    have hT' : ∀ t ∈ T, m₁ t = m₂ t := fun t ht => by
      have := LinearMap.congr_fun (congrArg Prod.snd h) ⟨t, ht⟩
      exact congrArg Subtype.val this
    apply Subtype.ext
    refine LinearMap.ext fun u => ?_
    obtain ⟨c, hc, t, ht, c', hc', rfl⟩ := hdec u
    have e1 : m₁ (k c') = n (m₁ c') := (LinearMap.congr_fun h₁ c').symm
    have e2 : m₂ (k c') = n (m₂ c') := (LinearMap.congr_fun h₂ c').symm
    simp only [map_add]
    rw [e1, e2, hC' c hc, hC' c' hc', hT' t ht]
  have : Finite (C →ₗ[K] V) := Module.finite_of_finite K
  have : Finite (T →ₗ[K] ker n) := Module.finite_of_finite K
  have hrank_k := LinearMap.finrank_range_add_finrank_ker k
  have hrank_n := LinearMap.finrank_range_add_finrank_ker n
  have hC_fin : finrank K (ker k) + finrank K C = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hC
  have hT_fin := Submodule.finrank_sup_add_finrank_inf_eq T (range k)
  rw [hTs, hTr, finrank_bot] at hT_fin
  calc Nat.card {m : V →ₗ[K] V // n ∘ₗ m = m ∘ₗ k}
      ≤ Nat.card ((C →ₗ[K] V) × (T →ₗ[K] ker n)) := Nat.card_le_card_of_injective _ hΘ
    _ = Nat.card (C →ₗ[K] V) * Nat.card (T →ₗ[K] ker n) := Nat.card_prod _ _
    _ = _ := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := C →ₗ[K] V),
        Module.natCard_eq_pow_finrank (K := K) (V := T →ₗ[K] ker n), ← pow_add,
        Module.finrank_linearMap K K C V, Module.finrank_linearMap K K T (ker n)]
      congr 2
      · congr 1; omega
      · congr 1 <;> omega

end Intertwiners

section Matrices

variable {F : Type} [Field F] {d : ℕ}

theorem one_add_mul_self [CharP F 2] {P : Matrix (Fin d) (Fin d) F} (hP : P * P = 1) :
    (1 + P) * (1 + P) = 0 := by
  have e1 : (1 : Matrix (Fin d) (Fin d) F) + 1 = 0 := add_self_eq_zero F _
  have e2 : P + P = 0 := add_self_eq_zero F _
  have : (1 + P) * (1 + P) = ((1 : Matrix (Fin d) (Fin d) F) + 1) + (P + P) := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hP]
    abel
  rw [this, e1, e2, add_zero]

theorem two_mul_rank_le {A : Matrix (Fin d) (Fin d) F} (hA : A * A = 0) :
    2 * A.rank ≤ d := by
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hA, Matrix.zero_mulVec]
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at h2
  have h3 : A.rank = Module.finrank F (LinearMap.range A.mulVecLin) := rfl
  omega

theorem eq_zero_of_rank_eq_zero {A : Matrix (Fin d) (Fin d) F} (h : A.rank = 0) : A = 0 := by
  have h0 : Module.finrank F (LinearMap.range A.mulVecLin) = 0 := h
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have h1 : A.mulVecLin = 0 := h0
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', h1, map_zero]

theorem fixed_iff_intertwiner {P Q M : Matrix (Fin d) (Fin d) F} (hQ : Q * Q = 1) :
    P * M * Qᵀ = M ↔ (1 + P) * M = M * (1 + Qᵀ) := by
  have hQt : Qᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]
  rw [add_mul, mul_add, one_mul, mul_one, add_right_inj]
  constructor
  · exact mul_eq_mul_transpose_of_fixed hQ
  · intro h
    rw [h, mul_assoc, hQt, mul_one]

theorem card_fixed_le [Finite F] [CharP F 2] {P Q : Matrix (Fin d) (Fin d) F}
    (hQ : Q * Q = 1) :
    Nat.card {M : Matrix (Fin d) (Fin d) F // P * M * Qᵀ = M} ≤
      Nat.card F ^ ((1 + Q).rank * d + (d - 2 * (1 + Q).rank) * (d - (1 + P).rank)) := by
  have hQt : Qᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]
  have hK : (1 + Qᵀ) * (1 + Qᵀ) = 0 := one_add_mul_self hQt
  have hKrank : (1 + Qᵀ).rank = (1 + Q).rank := by
    rw [show (1 : Matrix (Fin d) (Fin d) F) + Qᵀ = (1 + Q)ᵀ by simp, Matrix.rank_transpose]
  have key := card_intertwiners_le (K := F) (V := Fin d → F) (Matrix.toLin' (1 + P))
    (Matrix.toLin' (1 + Qᵀ)) (by rw [← Matrix.toLin'_mul, hK, map_zero])
  have hr1 : finrank F (range (Matrix.toLin' (1 + P))) = (1 + P).rank := by
    rw [Matrix.toLin'_apply']; rfl
  have hr2 : finrank F (range (Matrix.toLin' (1 + Qᵀ))) = (1 + Q).rank := by
    rw [Matrix.toLin'_apply', ← hKrank]; rfl
  rw [hr1, hr2, Module.finrank_fin_fun] at key
  refine le_trans (le_of_eq ?_) key
  refine Nat.card_congr (Matrix.toLin'.toEquiv.subtypeEquiv fun M => ?_)
  rw [fixed_iff_intertwiner hQ]
  change _ ↔ Matrix.toLin' (1 + P) ∘ₗ Matrix.toLin' M = Matrix.toLin' M ∘ₗ Matrix.toLin' (1 + Qᵀ)
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  exact Matrix.toLin'.injective.eq_iff.symm

theorem one_le_rank_one_add [CharP F 2] {P : Matrix (Fin d) (Fin d) F} (hP : P ≠ 1) :
    1 ≤ (1 + P).rank := by
  by_contra h
  have h0 : (1 + P).rank = 0 := by omega
  have h1 := eq_zero_of_rank_eq_zero h0
  apply hP
  rw [eq_neg_of_add_eq_zero_right h1, neg_eq_self F]

end Matrices

theorem exponent_ge_two_mul_sub_two {a b d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h1 : 2 * a ≤ d)
    (h2 : 2 * b ≤ d) : 2 * d - 2 ≤ a * d + b * d - 2 * a * b := by
  apply Nat.le_sub_of_add_le
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  have e1 : 2 * (d' + 2) - 2 = 2 * d' + 2 := by omega
  rw [e1]
  nlinarith [Nat.mul_le_mul_left a' (show 2 * b' ≤ d' from by omega),
    Nat.mul_le_mul_left b' (show 0 ≤ d' from Nat.zero_le _)]

theorem le_exponent_of_one_le {a b d : ℕ} (h : 1 ≤ a ∨ 1 ≤ b) (h1 : 2 * a ≤ d)
    (h2 : 2 * b ≤ d) : d ≤ a * d + b * d - 2 * a * b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rcases h with ha | hb
    · simpa using Nat.mul_le_mul_right d ha
    · omega
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Nat.mul_le_mul_right d hb
  have := exponent_ge_two_mul_sub_two ha hb h1 h2
  omega

end InvolMat

open InvolMat

theorem card_range_ge {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) F} (hP : P * P = 1) (hQ : Q * Q = 1) :
    Nat.card F ^ (Matrix.rank (1 + P) * d + Matrix.rank (1 + Q) * d -
        2 * Matrix.rank (1 + P) * Matrix.rank (1 + Q)) ≤
      Nat.card (Set.range fun M : Matrix (Fin d) (Fin d) F => M + P * M * Qᵀ) := by
  have h1 : 2 * (1 + P).rank ≤ d := two_mul_rank_le (one_add_mul_self hP)
  have h2 : 2 * (1 + Q).rank ≤ d := two_mul_rank_le (one_add_mul_self hQ)
  have hker := card_fixed_le (P := P) hQ
  have hprod := AddSubgroup.card_ker_mul_card_range (sumHom P Q)
  rw [card_matrix F d] at hprod
  have hkerc : Nat.card (sumHom P Q).ker =
      Nat.card {M : Matrix (Fin d) (Fin d) F // P * M * Qᵀ = M} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M => mem_ker_sumHom M)
  have hrange : Nat.card (Set.range fun M : Matrix (Fin d) (Fin d) F => M + P * M * Qᵀ) =
      Nat.card (sumHom P Q).range := rfl
  rw [hrange]
  generalize (1 + P).rank = a at *
  generalize (1 + Q).rank = b at *
  have h1' : a ≤ d := by omega
  have h3 : 2 * a * b ≤ a * d + b * d := by
    have : 2 * a * b ≤ a * d := by
      calc 2 * a * b = a * (2 * b) := by ring
        _ ≤ a * d := Nat.mul_le_mul_left a h2
    omega
  have hexp : (b * d + (d - 2 * b) * (d - a)) + (a * d + b * d - 2 * a * b) = d * d := by
    zify [h1', h2, h3]
    ring
  have hpos : 0 < Nat.card F ^ (b * d + (d - 2 * b) * (d - a)) :=
    pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card F ^ (b * d + (d - 2 * b) * (d - a)) *
        Nat.card F ^ (a * d + b * d - 2 * a * b)
      = Nat.card F ^ (d * d) := by rw [← pow_add, hexp]
    _ = Nat.card (sumHom P Q).ker * Nat.card (sumHom P Q).range := hprod.symm
    _ ≤ Nat.card F ^ (b * d + (d - 2 * b) * (d - a)) * Nat.card (sumHom P Q).range := by
        rw [hkerc]
        exact Nat.mul_le_mul_right _ hker

theorem card_range_ge_of_ne_one {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) F} (hP : P * P = 1) (hQ : Q * Q = 1) (h : P ≠ 1 ∨ Q ≠ 1) :
    Nat.card F ^ d ≤ Nat.card (Set.range fun M : Matrix (Fin d) (Fin d) F => M + P * M * Qᵀ) := by
  refine le_trans (Nat.pow_le_pow_right Nat.card_pos ?_) (card_range_ge hP hQ)
  exact le_exponent_of_one_le (h.imp one_le_rank_one_add one_le_rank_one_add)
    (two_mul_rank_le (one_add_mul_self hP)) (two_mul_rank_le (one_add_mul_self hQ))

theorem card_range_ge_of_ne_one_both {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) F} (hP : P * P = 1) (hQ : Q * Q = 1) (hP1 : P ≠ 1)
    (hQ1 : Q ≠ 1) :
    Nat.card F ^ (2 * d - 2) ≤
      Nat.card (Set.range fun M : Matrix (Fin d) (Fin d) F => M + P * M * Qᵀ) := by
  refine le_trans (Nat.pow_le_pow_right Nat.card_pos ?_) (card_range_ge hP hQ)
  exact exponent_ge_two_mul_sub_two (one_le_rank_one_add hP1) (one_le_rank_one_add hQ1)
    (two_mul_rank_le (one_add_mul_self hP)) (two_mul_rank_le (one_add_mul_self hQ))

end CFSG.Quasithin
