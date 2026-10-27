module

public import CFSG.RankThree.CentralCover.FourGroupWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.Permutation.Embedding

public noncomputable section

namespace CFSG.RankThree.CentralCover

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

export CFSG.Permutation (viaEmbeddingHom_swap)

theorem swap_mul_swap_mem_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    {x y z w : α} (hxy : x ≠ y) (hzw : z ≠ w) : swap x y * swap z w ∈ alternatingGroup α := by
  rw [mem_alternatingGroup, sign_mul, sign_swap hxy, sign_swap hzw]
  rfl

variable {n : ℕ}

@[expose] def altPt (hn : 5 ≤ n) (k : Fin 5) : Fin n :=
  Fin.castLEEmb hn k

theorem altPt_ne (hn : 5 ≤ n) {k l : Fin 5} (hkl : k ≠ l) : altPt hn k ≠ altPt hn l :=
  (Fin.castLEEmb hn).injective.ne hkl

theorem val_altPt (hn : 5 ≤ n) (k : Fin 5) : (altPt hn k : ℕ) = k :=
  rfl

@[expose] def altA (hn : 5 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap (altPt hn 0) (altPt hn 2) * swap (altPt hn 0) (altPt hn 1),
    swap_mul_swap_mem_alternatingGroup (altPt_ne hn (by decide)) (altPt_ne hn (by decide))⟩

@[expose] def altB (hn : 5 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap (altPt hn 0) (altPt hn 1) * swap (altPt hn 3) (altPt hn 4),
    swap_mul_swap_mem_alternatingGroup (altPt_ne hn (by decide)) (altPt_ne hn (by decide))⟩

@[expose] def altV₁ (hn : 5 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap (altPt hn 0) (altPt hn 1) * swap (altPt hn 2) (altPt hn 3),
    swap_mul_swap_mem_alternatingGroup (altPt_ne hn (by decide)) (altPt_ne hn (by decide))⟩

@[expose] def altV₂ (hn : 5 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap (altPt hn 0) (altPt hn 2) * swap (altPt hn 1) (altPt hn 3),
    swap_mul_swap_mem_alternatingGroup (altPt_ne hn (by decide)) (altPt_ne hn (by decide))⟩

@[expose] def altV₃ (hn : 5 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap (altPt hn 0) (altPt hn 3) * swap (altPt hn 1) (altPt hn 2),
    swap_mul_swap_mem_alternatingGroup (altPt_ne hn (by decide)) (altPt_ne hn (by decide))⟩

@[expose] def altV (hn : 5 ≤ n) : Subgroup (alternatingGroup (Fin n)) :=
  closure {altV₁ hn, altV₂ hn, altV₃ hn}

@[expose] def altQ (hn : 5 ≤ n) : Subgroup (alternatingGroup (Fin n)) :=
  altV hn ⊔ zpowers (altA hn)

section Transport

variable (hn : 5 ≤ n)

@[expose] def altLift : Perm (Fin 5) →* Perm (Fin n) :=
  viaEmbeddingHom (Fin.castLEEmb hn)

theorem altLift_injective : Function.Injective (altLift hn) :=
  viaEmbeddingHom_injective _

theorem altLift_swap (i j : Fin 5) : altLift hn (swap i j) = swap (altPt hn i) (altPt hn j) :=
  viaEmbeddingHom_swap _ i j

theorem coe_altA : (altA hn : Perm (Fin n)) = altLift hn (swap 0 2 * swap 0 1) := by
  rw [map_mul, altLift_swap, altLift_swap]
  rfl

theorem coe_altB : (altB hn : Perm (Fin n)) = altLift hn (swap 0 1 * swap 3 4) := by
  rw [map_mul, altLift_swap, altLift_swap]
  rfl

theorem coe_altV₁ : (altV₁ hn : Perm (Fin n)) = altLift hn (swap 0 1 * swap 2 3) := by
  rw [map_mul, altLift_swap, altLift_swap]
  rfl

theorem coe_altV₂ : (altV₂ hn : Perm (Fin n)) = altLift hn (swap 0 2 * swap 1 3) := by
  rw [map_mul, altLift_swap, altLift_swap]
  rfl

theorem coe_altV₃ : (altV₃ hn : Perm (Fin n)) = altLift hn (swap 0 3 * swap 1 2) := by
  rw [map_mul, altLift_swap, altLift_swap]
  rfl

theorem altCycled : CycledFourGroup (altV₁ hn) (altV₃ hn) (altV₂ hn) (altA hn) where
  ne_one h1 := by
    have h := congrArg (fun g : alternatingGroup (Fin n) => (g : Perm (Fin n))) h1
    simp only [coe_altV₁, OneMemClass.coe_one] at h
    rw [← map_one (altLift hn)] at h
    exact absurd (altLift_injective hn h) (by decide)
  sq_eq_one := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, coe_altV₁, OneMemClass.coe_one, ← map_pow, ← map_one (altLift hn)]
    exact congrArg _ (by decide)
  mul_eq := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_altV₁, coe_altV₃, coe_altV₂, ← map_mul]
    exact congrArg _ (by decide)
  conj_one := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_altA, coe_altV₁, coe_altV₃,
      ← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (by decide)
  conj_two := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_altA, coe_altV₃, coe_altV₂,
      ← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (by decide)
  cube := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, coe_altA, OneMemClass.coe_one, ← map_pow, ← map_one (altLift hn)]
    exact congrArg _ (by decide)

theorem altB_conj : (altB hn)⁻¹ * altA hn * altB hn = (altA hn)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_altA, coe_altB,
    ← map_inv, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (by decide)

theorem coe_altV : (altV hn : Set (alternatingGroup (Fin n))) =
    {1, altV₁ hn, altV₂ hn, altV₃ hn} := by
  have h := (altCycled hn).coe_closure
  rw [Set.pair_comm (altV₃ hn) (altV₂ hn)] at h
  exact h

theorem coe_altV' : (altV hn : Set (alternatingGroup (Fin n))) =
    {1, altV₁ hn, altV₃ hn, altV₂ hn} := by
  rw [coe_altV, Set.pair_comm (altV₂ hn) (altV₃ hn)]

end Transport

section Fixing

@[expose] def altExt (n : ℕ) :
    alternatingGroup {i : Fin n // (i : ℕ) < 4} →* alternatingGroup (Fin n) :=
  ((ofSubtype : Perm {i : Fin n // (i : ℕ) < 4} →* Perm (Fin n)).comp
    (alternatingGroup _).subtype).codRestrict (alternatingGroup (Fin n)) fun τ => by
      rw [mem_alternatingGroup, MonoidHom.comp_apply, sign_ofSubtype]
      exact τ.2

theorem altExt_injective (n : ℕ) : Function.Injective (altExt n) := by
  intro τ τ' h
  have h' := congrArg (fun g : alternatingGroup (Fin n) => (g : Perm (Fin n))) h
  exact Subtype.ext (ofSubtype_injective h')

theorem mem_range_altExt (σ : alternatingGroup (Fin n)) :
    σ ∈ (altExt n).range ↔ ∀ i : Fin n, 4 ≤ (i : ℕ) → (σ : Perm (Fin n)) i = i := by
  constructor
  · rintro ⟨τ, rfl⟩ i hi
    exact ofSubtype_apply_of_not_mem _ (by omega)
  · intro hfix
    have h₁ : ∀ x, ((σ : Perm (Fin n)) x : ℕ) < 4 ↔ (x : ℕ) < 4 := by
      intro x
      by_cases hx : (x : ℕ) < 4
      · refine ⟨fun _ => hx, fun _ => ?_⟩
        by_contra hσx
        have hfx := hfix _ (not_lt.1 hσx)
        rw [(σ : Perm (Fin n)).injective hfx] at hσx
        exact hσx hx
      · rw [hfix x (not_lt.1 hx)]
    have h₂ : ∀ x, (σ : Perm (Fin n)) x ≠ x → (x : ℕ) < 4 := fun x hx => by
      by_contra hx'
      exact hx (hfix x (not_lt.1 hx'))
    have hsub := ofSubtype_subtypePerm h₁ h₂
    refine ⟨⟨(σ : Perm (Fin n)).subtypePerm h₁, ?_⟩, Subtype.ext hsub⟩
    rw [mem_alternatingGroup, ← sign_ofSubtype, hsub]
    exact σ.2

@[expose] def lowPoints (hn : 4 ≤ n) : {i : Fin n // (i : ℕ) < 4} ≃ Fin 4 where
  toFun i := ⟨i.1, i.2⟩
  invFun j := ⟨⟨j, by omega⟩, j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_alternatingGroup_fin_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  have h := two_mul_card_alternatingGroup (α := Fin 4)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  have h24 : Nat.factorial 4 = 24 := rfl
  omega

theorem card_range_altExt (hn : 4 ≤ n) : Nat.card (altExt n).range = 12 := by
  rw [← card_alternatingGroup_fin_four,
    ← Nat.card_congr (MonoidHom.ofInjective (altExt_injective n)).toEquiv]
  exact Nat.card_congr (Equiv.altCongrHom (lowPoints hn)).toEquiv

end Fixing

section Main

variable (hn : 5 ≤ n)

theorem altQ_le_range : altQ hn ≤ (altExt n).range := by
  have hfix : ∀ {k l k' l' : Fin 5}, (k : ℕ) < 4 → (l : ℕ) < 4 → (k' : ℕ) < 4 → (l' : ℕ) < 4 →
      ∀ i : Fin n, 4 ≤ (i : ℕ) →
        (swap (altPt hn k) (altPt hn l) * swap (altPt hn k') (altPt hn l')) i = i := by
    intro k l k' l' hk hl hk' hl' i hi
    have hne : ∀ m : Fin 5, (m : ℕ) < 4 → i ≠ altPt hn m := fun m hm h => by
      rw [h, val_altPt] at hi
      omega
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne k' hk') (hne l' hl'),
      swap_apply_of_ne_of_ne (hne k hk) (hne l hl)]
  have hV : altV hn ≤ (altExt n).range := by
    intro σ hσ
    rw [← SetLike.mem_coe, coe_altV] at hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rw [mem_range_altExt]
    rcases hσ with rfl | rfl | rfl | rfl
    · intro i _
      rfl
    · exact hfix (by decide) (by decide) (by decide) (by decide)
    · exact hfix (by decide) (by decide) (by decide) (by decide)
    · exact hfix (by decide) (by decide) (by decide) (by decide)
  have ha : altA hn ∈ (altExt n).range := by
    rw [mem_range_altExt]
    exact hfix (by decide) (by decide) (by decide) (by decide)
  exact sup_le hV (zpowers_le.2 ha)

theorem altQ_eq_range : altQ hn = (altExt n).range := by
  refine eq_of_le_of_card_ge (altQ_le_range hn) ?_
  rw [card_range_altExt (by omega)]
  exact ((altCycled hn).quotient_facts (coe_altV' hn)).2.2.2.2.2.ge

theorem alternating_central_three_cover_split_four_group_witness_quotient :
    (altV hn : Set (alternatingGroup (Fin n))) = {1, altV₁ hn, altV₂ hn, altV₃ hn} ∧
    IsKleinFour (altV hn) ∧
    (∀ σ : alternatingGroup (Fin n),
      σ ∈ altQ hn ↔ ∀ i : Fin n, 4 ≤ (i : ℕ) → (σ : Perm (Fin n)) i = i) ∧
    Nonempty (altQ hn ≃* alternatingGroup (Fin 4)) ∧
    (altB hn)⁻¹ * altA hn * altB hn = (altA hn)⁻¹ := by
  refine ⟨coe_altV hn, ((altCycled hn).quotient_facts (coe_altV' hn)).1, fun σ => ?_, ⟨?_⟩,
    altB_conj hn⟩
  · rw [altQ_eq_range, mem_range_altExt]
  · exact (MulEquiv.subgroupCongr (altQ_eq_range hn)).trans
      ((MonoidHom.ofInjective (altExt_injective n)).symm.trans
        (Equiv.altCongrHom (lowPoints (by omega))))

theorem alternating_central_three_cover_split_four_group_witness_cover {K : Type*} [Group K]
    [Finite K] (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center K) (hZ3 : IsPGroup 3 π.ker) :
    (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = altV hn ∧ Set.InjOn π U) ∧
    ∀ U : Subgroup K, IsPGroup 2 U → U.map π = altV hn → Set.InjOn π U →
      π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = (altV hn).comap π ∧
      ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = altA hn ∧
        (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
          u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
          x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
        x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
        (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
        (U ⊔ zpowers x).map π = altQ hn ∧ Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
        π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧ π.ker ⊔ (U ⊔ zpowers x) = (altQ hn).comap π :=
  (altCycled hn).cover (altB_conj hn) (coe_altV' hn) π hπ hZ hZ3

end Main

end CFSG.RankThree.CentralCover
