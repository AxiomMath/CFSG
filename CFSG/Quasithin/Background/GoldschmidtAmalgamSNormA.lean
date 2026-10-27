module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSVertex
public import CFSG.Quasithin.Background.F6GoldschmidtList

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv

theorem mem_V4_iff (σ : Perm (Fin 4)) : σ ∈ V4 ↔ σ ∈ V4Fin := Iff.rfl

theorem V4_conj (g σ : Perm (Fin 4)) (h : σ ∈ V4) : g * σ * g⁻¹ ∈ V4 := by
  rw [mem_V4_iff] at h ⊢
  revert g σ
  decide

@[expose] def zc : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def Pstd : Subgroup (Perm (Fin 4)) where
  carrier := {s | s * zc = zc * s}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show a * b * zc = zc * (a * b)
    have ha' : a * zc = zc * a := ha
    have hb' : b * zc = zc * b := hb
    rw [mul_assoc, hb', ← mul_assoc, ha', mul_assoc]
  inv_mem' := fun {a} ha => by
    show a⁻¹ * zc = zc * a⁻¹
    have ha' : a * zc = zc * a := ha
    calc a⁻¹ * zc = a⁻¹ * (zc * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * zc) * a⁻¹ := by rw [ha']
      _ = zc * a⁻¹ := by group

theorem mem_Pstd_iff (s : Perm (Fin 4)) : s ∈ Pstd ↔ s * zc = zc * s := Iff.rfl

instance : DecidablePred (· ∈ Pstd) := fun s => decidable_of_iff _ (mem_Pstd_iff s).symm

theorem card_Pstd : Nat.card Pstd = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def a₀ : Perm (Fin 4) := List.formPerm [0, 1, 2, 3]

@[expose] def b₀ : Perm (Fin 4) := swap 0 2

@[expose] def u₀ : Perm (Fin 4) := a₀

@[expose] def v₀ : Perm (Fin 4) := a₀ * b₀

theorem a₀_mem : a₀ ∈ Pstd := by rw [mem_Pstd_iff]; decide

theorem b₀_mem : b₀ ∈ Pstd := by rw [mem_Pstd_iff]; decide

theorem Pstd_word : ∀ s ∈ Pstd, ∃ i < 4, ∃ j < 2, s = a₀ ^ i * b₀ ^ j := by
  intro s hs
  rw [mem_Pstd_iff] at hs
  revert s
  decide

theorem exists_conj_Pstd (P : Subgroup (Perm (Fin 4))) (hP : Nat.card P = 8) :
    ∃ g : Perm (Fin 4), ∀ s, s ∈ P ↔ g * s * g⁻¹ ∈ Pstd := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h24 : Nat.card (Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have hfac : (Nat.card (Perm (Fin 4))).factorization 2 = 3 := by
    rw [h24]
    have h := Nat.factorization_mul (show (8 : ℕ) ≠ 0 by norm_num) (show (3 : ℕ) ≠ 0 by norm_num)
    rw [show (24 : ℕ) = 8 * 3 by norm_num, h, Finsupp.add_apply,
      show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let S₁ : Sylow 2 (Perm (Fin 4)) := Sylow.ofCard P (by rw [hP, hfac]; norm_num)
  let S₂ : Sylow 2 (Perm (Fin 4)) := Sylow.ofCard Pstd (by rw [card_Pstd, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 4)) S₁ S₂
  refine ⟨g, fun s => ?_⟩
  have h1 : ((g • S₁ : Sylow 2 (Perm (Fin 4))) : Subgroup (Perm (Fin 4))) = Pstd := by
    rw [hg]; rfl
  have key : ∀ t, t ∈ ((g • S₁ : Sylow 2 (Perm (Fin 4))) : Subgroup (Perm (Fin 4))) ↔
      g⁻¹ * t * g ∈ P := by
    intro t
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
    rfl
  rw [← h1, key]
  simp [mul_assoc]


set_option synthInstance.maxSize 1000 in
theorem word_inj : ∀ i < 4, ∀ j < 2, ∀ i' < 4, ∀ j' < 2,
    a₀ ^ i * b₀ ^ j = a₀ ^ i' * b₀ ^ j' → i = i' ∧ j = j' := by
  decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
theorem conj_std : ∀ u v : Perm (Fin 4), u ^ 4 = 1 → u ^ 2 ≠ 1 → v ^ 2 = 1 →
    v * u * v⁻¹ = u⁻¹ →
    (∀ i < 4, ∀ j < 2, ∀ i' < 4, ∀ j' < 2, u ^ i * v ^ j = u ^ i' * v ^ j' → i = i' ∧ j = j') →
    (∃ i < 4, ∃ j < 2, a₀ ^ i * b₀ ^ j ∈ V4Fin ∧ u ^ i * v ^ j ∉ V4Fin) →
    ∃ g : Perm (Fin 4), g * u * g⁻¹ = u₀ ∧ g * v * g⁻¹ = v₀ := by
  decide +kernel

theorem a₀_pow_four : a₀ ^ 4 = 1 := by decide
theorem a₀_sq_ne : a₀ ^ 2 ≠ 1 := by decide
theorem b₀_sq : b₀ ^ 2 = 1 := by decide
theorem b₀_a₀ : b₀ * a₀ * b₀⁻¹ = a₀⁻¹ := by decide

section Iso

variable {E : Type*} [Group E]

structure NormA (A₁ A₂ : Subgroup E) where
  a : E
  b : E
  ha₁ : a ∈ A₁
  ha₂ : a ∈ A₂
  hb₁ : b ∈ A₁
  hb₂ : b ∈ A₂
  ψ₁ : ↥A₁ ≃* Perm (Fin 4)
  ψ₂ : ↥A₂ ≃* Perm (Fin 4)
  h₁a : ψ₁ ⟨a, ha₁⟩ = a₀
  h₁b : ψ₁ ⟨b, hb₁⟩ = b₀
  h₂a : ψ₂ ⟨a, ha₂⟩ = u₀
  h₂b : ψ₂ ⟨b, hb₂⟩ = v₀
  words : ∀ x ∈ A₁ ⊓ A₂, ∃ i j : ℕ, x = a ^ i * b ^ j

end Iso

section Normalize

variable {E : Type*} [Group E]

theorem normalize_A (A₁ A₂ : Subgroup E) (hT : Nat.card ↥(A₁ ⊓ A₂) = 8)
    (ψ₁ : ↥A₁ ≃* Perm (Fin 4)) (ψ₂ : ↥A₂ ≃* Perm (Fin 4))
    (hout : ∃ (y : E) (h₁ : y ∈ A₁) (h₂ : y ∈ A₂), ψ₁ ⟨y, h₁⟩ ∈ V4 ∧ ψ₂ ⟨y, h₂⟩ ∉ V4) :
    Nonempty (NormA A₁ A₂) := by
  classical
  have hTA₁ : A₁ ⊓ A₂ ≤ A₁ := inf_le_left
  have hTA₂ : A₁ ⊓ A₂ ≤ A₂ := inf_le_right
  let P₁ : Subgroup (Perm (Fin 4)) := ((A₁ ⊓ A₂).subgroupOf A₁).map ψ₁.toMonoidHom
  have hP₁ : Nat.card P₁ = 8 := by
    rw [Subgroup.card_map_of_injective ψ₁.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA₁).toEquiv, hT]
  obtain ⟨g₁, hg₁⟩ := exists_conj_Pstd P₁ hP₁
  let ψ₁' : ↥A₁ ≃* Perm (Fin 4) := ψ₁.trans (MulAut.conj g₁)
  have hψ₁' : ∀ x, ψ₁' x = g₁ * ψ₁ x * g₁⁻¹ := fun x => rfl
  have hmem : ∀ (x : E) (hx : x ∈ A₁), x ∈ A₁ ⊓ A₂ ↔ ψ₁' ⟨x, hx⟩ ∈ Pstd := by
    intro x hx
    rw [hψ₁', ← hg₁, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact (Subgroup.mem_subgroupOf (H := A₁ ⊓ A₂) (K := A₁) (h := ⟨x, hx⟩)).symm
  have hex : ∀ s ∈ Pstd, ∃ (x : ↥A₁), (x : E) ∈ A₁ ⊓ A₂ ∧ ψ₁' x = s := by
    intro s hs
    refine ⟨ψ₁'.symm s, (hmem _ (ψ₁'.symm s).2).2 ?_, MulEquiv.apply_symm_apply _ _⟩
    simpa using hs
  obtain ⟨a₁, ha₁T, ha₁⟩ := hex a₀ a₀_mem
  obtain ⟨b₁, hb₁T, hb₁⟩ := hex b₀ b₀_mem
  have ha₂ : (a₁ : E) ∈ A₂ := hTA₂ ha₁T
  have hb₂ : (b₁ : E) ∈ A₂ := hTA₂ hb₁T
  let a₂ : ↥A₂ := ⟨a₁, ha₂⟩
  let b₂ : ↥A₂ := ⟨b₁, hb₂⟩
  have hrel₁ : ∀ i j : ℕ, ψ₁' (a₁ ^ i * b₁ ^ j) = a₀ ^ i * b₀ ^ j := by
    intro i j; rw [map_mul, map_pow, map_pow, ha₁, hb₁]
  have hrel₂ : ∀ i j : ℕ, ((a₂ ^ i * b₂ ^ j : ↥A₂) : E) = ((a₁ ^ i * b₁ ^ j : ↥A₁) : E) := by
    intro i j; simp [a₂, b₂]
  have hE4 : a₁ ^ 4 = 1 := ψ₁'.injective (by rw [map_pow, ha₁, map_one]; exact a₀_pow_four)
  have hE2 : b₁ ^ 2 = 1 := ψ₁'.injective (by rw [map_pow, hb₁, map_one]; exact b₀_sq)
  have hEc : b₁ * a₁ * b₁⁻¹ = a₁⁻¹ :=
    ψ₁'.injective (by rw [map_mul, map_mul, map_inv, map_inv, ha₁, hb₁]; exact b₀_a₀)
  have hEne : a₁ ^ 2 ≠ 1 := fun h => a₀_sq_ne (by
    have := congrArg ψ₁' h
    rwa [map_pow, ha₁, map_one] at this)
  have hEinj : ∀ i < 4, ∀ j < 2, ∀ i' < 4, ∀ j' < 2,
      a₁ ^ i * b₁ ^ j = a₁ ^ i' * b₁ ^ j' → i = i' ∧ j = j' := by
    intro i hi j hj i' hi' j' hj' h
    apply word_inj i hi j hj i' hi' j' hj'
    have := congrArg ψ₁' h
    rwa [hrel₁, hrel₁] at this
  let u : Perm (Fin 4) := ψ₂ a₂
  let v : Perm (Fin 4) := ψ₂ b₂
  have hA₂ : ∀ i j : ℕ, ψ₂ (a₂ ^ i * b₂ ^ j) = u ^ i * v ^ j := by
    intro i j; rw [map_mul, map_pow, map_pow]
  have hcoe₂ : ∀ w w' : ↥A₂, ((w : ↥A₂) : E) = (w' : E) → w = w' := fun w w' h => Subtype.ext h
  have hu4 : u ^ 4 = 1 := by
    rw [← map_pow]
    have : a₂ ^ 4 = 1 := Subtype.ext (by simpa [a₂] using congrArg Subtype.val hE4)
    rw [this, map_one]
  have hv2 : v ^ 2 = 1 := by
    rw [← map_pow]
    have : b₂ ^ 2 = 1 := Subtype.ext (by simpa [b₂] using congrArg Subtype.val hE2)
    rw [this, map_one]
  have huv : v * u * v⁻¹ = u⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa [a₂, b₂] using congrArg Subtype.val hEc)
  have hu2 : u ^ 2 ≠ 1 := fun h => hEne (Subtype.ext (by
    have h' : a₂ ^ 2 = 1 := ψ₂.injective (by rw [map_pow, map_one]; exact h)
    simpa [a₂] using congrArg Subtype.val h'))
  have hdist : ∀ i < 4, ∀ j < 2, ∀ i' < 4, ∀ j' < 2,
      u ^ i * v ^ j = u ^ i' * v ^ j' → i = i' ∧ j = j' := by
    intro i hi j hj i' hi' j' hj' h
    apply hEinj i hi j hj i' hi' j' hj'
    have h1 : a₂ ^ i * b₂ ^ j = a₂ ^ i' * b₂ ^ j' :=
      ψ₂.injective (by rw [hA₂, hA₂]; exact h)
    apply Subtype.ext
    rw [← hrel₂, ← hrel₂, h1]
  have hword : ∀ (x : E) (hx₁ : x ∈ A₁), x ∈ A₁ ⊓ A₂ →
      ∃ i < 4, ∃ j < 2, (⟨x, hx₁⟩ : ↥A₁) = a₁ ^ i * b₁ ^ j := by
    intro x hx₁ hxT
    obtain ⟨i, hi, j, hj, hij⟩ := Pstd_word _ ((hmem x hx₁).1 hxT)
    exact ⟨i, hi, j, hj, ψ₁'.injective (by rw [hij, hrel₁])⟩
  have hH : ∃ i < 4, ∃ j < 2, a₀ ^ i * b₀ ^ j ∈ V4Fin ∧ u ^ i * v ^ j ∉ V4Fin := by
    obtain ⟨y, h₁, h₂, hV1, hV2⟩ := hout
    obtain ⟨i, hi, j, hj, hyij⟩ := hword y h₁ ⟨h₁, h₂⟩
    refine ⟨i, hi, j, hj, ?_, ?_⟩
    · have h3 : ψ₁' ⟨y, h₁⟩ ∈ V4 := by rw [hψ₁']; exact V4_conj _ _ hV1
      rw [hyij, hrel₁] at h3
      exact h3
    · have h4 : (⟨y, h₂⟩ : ↥A₂) = a₂ ^ i * b₂ ^ j := by
        apply Subtype.ext
        rw [hrel₂]
        exact congrArg Subtype.val hyij
      rw [h4, hA₂] at hV2
      exact hV2
  obtain ⟨g₂, hg₂a, hg₂b⟩ := conj_std u v hu4 hu2 hv2 huv hdist hH
  refine ⟨⟨a₁, b₁, a₁.2, ha₂, b₁.2, hb₂, ψ₁', ψ₂.trans (MulAut.conj g₂), ha₁, hb₁, hg₂a, hg₂b,
    ?_⟩⟩
  intro x hx
  obtain ⟨i, hi, j, hj, hij⟩ := hword x (hTA₁ hx) hx
  refine ⟨i, j, ?_⟩
  have := congrArg Subtype.val hij
  simpa using this

end Normalize

section Iso2

variable {E : Type*} [Group E]

theorem NormA.words_mem {A₁ A₂ : Subgroup E} (N : NormA A₁ A₂) (i j : ℕ) :
    N.a ^ i * N.b ^ j ∈ A₁ ⊓ A₂ :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_inf.2 ⟨N.ha₁, N.ha₂⟩) i)
    (Subgroup.pow_mem _ (Subgroup.mem_inf.2 ⟨N.hb₁, N.hb₂⟩) j)

theorem NormA.ψ₁_word {A₁ A₂ : Subgroup E} (N : NormA A₁ A₂) (i j : ℕ)
    (h : N.a ^ i * N.b ^ j ∈ A₁) : N.ψ₁ ⟨N.a ^ i * N.b ^ j, h⟩ = a₀ ^ i * b₀ ^ j := by
  have : (⟨N.a ^ i * N.b ^ j, h⟩ : ↥A₁) = ⟨N.a, N.ha₁⟩ ^ i * ⟨N.b, N.hb₁⟩ ^ j :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_pow, map_pow, N.h₁a, N.h₁b]

theorem NormA.ψ₂_word {A₁ A₂ : Subgroup E} (N : NormA A₁ A₂) (i j : ℕ)
    (h : N.a ^ i * N.b ^ j ∈ A₂) : N.ψ₂ ⟨N.a ^ i * N.b ^ j, h⟩ = u₀ ^ i * v₀ ^ j := by
  have : (⟨N.a ^ i * N.b ^ j, h⟩ : ↥A₂) = ⟨N.a, N.ha₂⟩ ^ i * ⟨N.b, N.hb₂⟩ ^ j :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_pow, map_pow, N.h₂a, N.h₂b]

theorem NormA.ψ₁_symm_word {A₁ A₂ : Subgroup E} (N : NormA A₁ A₂) (i j : ℕ) :
    ((N.ψ₁.symm (a₀ ^ i * b₀ ^ j) : ↥A₁) : E) = N.a ^ i * N.b ^ j := by
  have h1 : N.a ^ i * N.b ^ j ∈ A₁ := (N.words_mem i j).1
  have : N.ψ₁.symm (a₀ ^ i * b₀ ^ j) = ⟨N.a ^ i * N.b ^ j, h1⟩ := by
    rw [MulEquiv.symm_apply_eq, N.ψ₁_word]
  rw [this]

theorem NormA.ψ₂_symm_word {A₁ A₂ : Subgroup E} (N : NormA A₁ A₂) (i j : ℕ) :
    ((N.ψ₂.symm (u₀ ^ i * v₀ ^ j) : ↥A₂) : E) = N.a ^ i * N.b ^ j := by
  have h2 : N.a ^ i * N.b ^ j ∈ A₂ := (N.words_mem i j).2
  have : N.ψ₂.symm (u₀ ^ i * v₀ ^ j) = ⟨N.a ^ i * N.b ^ j, h2⟩ := by
    rw [MulEquiv.symm_apply_eq, N.ψ₂_word]
  rw [this]

theorem NormA.isAmalgamIso {E' : Type*} [Group E'] {A₁ A₂ : Subgroup E} {B₁ B₂ : Subgroup E'}
    (N : NormA A₁ A₂) (N' : NormA B₁ B₂) : CFSG.Quasithin.F6.IsAmalgamIso A₁ A₂ B₁ B₂ := by
  refine ⟨N.ψ₁.trans N'.ψ₁.symm, N.ψ₂.trans N'.ψ₂.symm, ?_, ?_⟩
  · intro x hx₁ hx₂
    obtain ⟨i, j, rfl⟩ := N.words x (Subgroup.mem_inf.2 ⟨hx₁, hx₂⟩)
    show ((N'.ψ₁.symm (N.ψ₁ ⟨N.a ^ i * N.b ^ j, hx₁⟩) : ↥B₁) : E') =
      ((N'.ψ₂.symm (N.ψ₂ ⟨N.a ^ i * N.b ^ j, hx₂⟩) : ↥B₂) : E')
    rw [N.ψ₁_word, N.ψ₂_word, N'.ψ₁_symm_word, N'.ψ₂_symm_word]
  · intro y hy₁ hy₂
    obtain ⟨i, j, rfl⟩ := N'.words y (Subgroup.mem_inf.2 ⟨hy₁, hy₂⟩)
    show ((N.ψ₁.symm (N'.ψ₁ ⟨N'.a ^ i * N'.b ^ j, hy₁⟩) : ↥A₁) : E) =
      ((N.ψ₂.symm (N'.ψ₂ ⟨N'.a ^ i * N'.b ^ j, hy₂⟩) : ↥A₂) : E)
    rw [N'.ψ₁_word, N'.ψ₂_word, N.ψ₁_symm_word, N.ψ₂_symm_word]

end Iso2

end CFSG.Quasithin.F6.GoldAmS
