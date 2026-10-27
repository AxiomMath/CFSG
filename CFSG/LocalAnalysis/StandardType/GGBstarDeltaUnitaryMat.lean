module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi

public section

namespace CFSG.StandardType

namespace TableBUM

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv diagHom_commute)

variable {K : Type} [Field K] {d : ℕ}

theorem card_le_of_restrict {p : ℕ} [NeZero p] (W : Subgroup (Fin d → Kˣ))
    (hW : ∀ σ ∈ W, ∀ k, σ k ^ p = 1) (S : Finset (Fin d))
    (hinj : ∀ σ ∈ W, ∀ τ ∈ W, (∀ k ∈ S, σ k = τ k) → σ = τ) :
    Nat.card W ≤ p ^ S.card := by
  classical
  let F : W → (S → rootsOfUnity p K) := fun σ k =>
    ⟨(σ : Fin d → Kˣ) k, (mem_rootsOfUnity p _).mpr (hW σ σ.2 k)⟩
  have hF : Function.Injective F := by
    intro σ τ hστ
    apply Subtype.ext
    refine hinj σ σ.2 τ τ.2 fun k hk => ?_
    have := congrFun hστ ⟨k, hk⟩
    exact congrArg Subtype.val this
  calc Nat.card W ≤ Nat.card (S → rootsOfUnity p K) := Nat.card_le_card_of_injective F hF
    _ = Nat.card (rootsOfUnity p K) ^ Nat.card S := Nat.card_fun
    _ ≤ p ^ S.card := by
        rw [Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
        exact Nat.pow_le_pow_left (card_rootsOfUnity K p) _

theorem card_le_pow_sub_one {p : ℕ} [NeZero p] (hd : 1 ≤ d) (W : Subgroup (Fin d → Kˣ))
    (hW : ∀ σ ∈ W, ∀ k, σ k ^ p = 1) (hprod : ∀ σ ∈ W, ∏ k, σ k = 1) :
    Nat.card W ≤ p ^ (d - 1) := by
  classical
  set m : Fin d := ⟨0, by omega⟩
  have hcard : (Finset.univ.erase m).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine card_le_of_restrict W hW _ fun σ hσ τ hτ hστ => ?_
  have hS : ∏ k ∈ Finset.univ.erase m, σ k = ∏ k ∈ Finset.univ.erase m, τ k :=
    Finset.prod_congr rfl hστ
  have h1 := Finset.mul_prod_erase Finset.univ σ (Finset.mem_univ m)
  have h2 := Finset.mul_prod_erase Finset.univ τ (Finset.mem_univ m)
  rw [hprod σ hσ] at h1
  rw [hprod τ hτ] at h2
  funext k
  by_cases hk : k = m
  · subst hk
    rw [hS] at h1
    exact mul_right_cancel (h1.trans h2.symm)
  · exact hστ k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)

theorem card_le_pow_sub_two {p : ℕ} [NeZero p] (hd : 3 ≤ d) (W : Subgroup (Fin d → Kˣ))
    (hW : ∀ σ ∈ W, ∀ k, σ k ^ p = 1) (hprod : ∀ σ ∈ W, ∏ k, σ k = 1) {k l : Fin d}
    (hkl : k ≠ l) (heq : ∀ σ ∈ W, σ k = σ l) : Nat.card W ≤ p ^ (d - 2) := by
  classical
  obtain ⟨m, hmk, hml⟩ : ∃ m : Fin d, m ≠ k ∧ m ≠ l := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin d)) ⊆ {k, l} := fun x _ => by
      by_cases hx : x = k
      · rw [hx]; exact Finset.mem_insert_self _ _
      · rw [hcon x hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_le_two (a := k) (b := l)
    omega
  set S := (Finset.univ.erase m).erase l with hS
  have hcard : S.card = d - 2 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hml, Finset.mem_univ l⟩),
      Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
    omega
  rw [← hcard]
  refine card_le_of_restrict W hW _ fun σ hσ τ hτ hστ => ?_
  have hkS : k ∈ S := Finset.mem_erase.mpr ⟨hkl, Finset.mem_erase.mpr ⟨Ne.symm hmk,
    Finset.mem_univ k⟩⟩
  have hoff : ∀ x, x ≠ m → σ x = τ x := by
    intro x hx
    by_cases hxl : x = l
    · rw [hxl, ← heq σ hσ, ← heq τ hτ]
      exact hστ k hkS
    · exact hστ x (Finset.mem_erase.mpr ⟨hxl, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩⟩)
  have hS' : ∏ x ∈ Finset.univ.erase m, σ x = ∏ x ∈ Finset.univ.erase m, τ x :=
    Finset.prod_congr rfl fun x hx => hoff x (Finset.mem_erase.mp hx).1
  have h1 := Finset.mul_prod_erase Finset.univ σ (Finset.mem_univ m)
  have h2 := Finset.mul_prod_erase Finset.univ τ (Finset.mem_univ m)
  rw [hprod σ hσ] at h1
  rw [hprod τ hτ] at h2
  funext x
  by_cases hx : x = m
  · subst hx
    rw [hS'] at h1
    exact mul_right_cancel (h1.trans h2.symm)
  · exact hoff x hx

theorem exists_diagHom_of_commute {W : Set (Fin d → Kˣ)}
    (hsep : ∀ k l : Fin d, k ≠ l → ∃ σ ∈ W, σ k ≠ σ l) {g : GL (Fin d) K}
    (hg : ∀ σ ∈ W, g * diagHom d σ = diagHom d σ * g) : ∃ β : Fin d → Kˣ, g = diagHom d β := by
  apply TableBUE.exists_diagHom_of_isDiag
  intro k l hkl
  obtain ⟨σ, hσ, hσkl⟩ := hsep k l hkl
  exact TableBUE.entry_eq_zero_of_commute (hg σ hσ) hσkl

section Mono

variable {i j : Fin d}

@[expose] def swapDiag (i j : Fin d) (c : Kˣ) : Fin d → Kˣ :=
  Pi.mulSingle i c * Pi.mulSingle j c⁻¹

theorem swapDiag_left (hij : i ≠ j) (c : Kˣ) : swapDiag i j c i = c := by
  simp [swapDiag, Pi.mulSingle_eq_of_ne hij]

theorem swapDiag_right (hij : i ≠ j) (c : Kˣ) : swapDiag i j c j = c⁻¹ := by
  simp [swapDiag, Pi.mulSingle_eq_of_ne (Ne.symm hij)]

theorem swapDiag_of_ne {k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) (c : Kˣ) :
    swapDiag i j c k = 1 := by
  simp [swapDiag, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj]

theorem prod_swapDiag (c : Kˣ) : ∏ k, swapDiag i j c k = 1 := by
  simp only [swapDiag, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle',
    mul_inv_cancel]

@[expose] noncomputable def monoSwap (i j : Fin d) (c : Kˣ) : GL (Fin d) K :=
  diagHom d (swapDiag i j c) * permGL (Equiv.swap i j)

theorem diagHom_mul_permGL_swap (σ : Fin d → Kˣ) :
    diagHom d σ * permGL (Equiv.swap i j) =
      (permGL (Equiv.swap i j) : GL (Fin d) K) * diagHom d (σ ∘ Equiv.swap i j) := by
  have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) (σ ∘ Equiv.swap i j)
  have hss : (σ ∘ Equiv.swap i j) ∘ (Equiv.swap i j).symm = σ := by
    funext k
    simp [Equiv.symm_swap, Equiv.swap_apply_self]
  rw [hss] at h1
  rw [← h1]
  group

theorem permGL_swap_mul_diagHom (σ : Fin d → Kˣ) :
    (permGL (Equiv.swap i j) : GL (Fin d) K) * diagHom d σ =
      diagHom d (σ ∘ Equiv.swap i j) * permGL (Equiv.swap i j) := by
  have hss : (σ ∘ Equiv.swap i j) ∘ Equiv.swap i j = σ := by
    funext k
    simp [Equiv.swap_apply_self]
  rw [diagHom_mul_permGL_swap, hss]

theorem monoSwap_mul_self (hij : i ≠ j) (c : Kˣ) :
    (monoSwap i j c : GL (Fin d) K) * monoSwap i j c = 1 := by
  have hsq : (permGL (Equiv.swap i j) : GL (Fin d) K) * permGL (Equiv.swap i j) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hτ : swapDiag i j c * (swapDiag i j c ∘ Equiv.swap i j) = 1 := by
    funext k
    rw [Pi.mul_apply, Function.comp_apply, Pi.one_apply]
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left, swapDiag_left hij, swapDiag_right hij, mul_inv_cancel]
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right, swapDiag_left hij, swapDiag_right hij, inv_mul_cancel]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, swapDiag_of_ne hki hkj, one_mul]
  rw [monoSwap, mul_assoc, ← mul_assoc (permGL (Equiv.swap i j)), permGL_swap_mul_diagHom]
  calc diagHom d (swapDiag i j c) * (diagHom d (swapDiag i j c ∘ Equiv.swap i j) *
        permGL (Equiv.swap i j) * permGL (Equiv.swap i j))
      = diagHom d (swapDiag i j c * (swapDiag i j c ∘ Equiv.swap i j)) *
          (permGL (Equiv.swap i j) * permGL (Equiv.swap i j)) := by
        rw [map_mul]
        group
    _ = 1 := by rw [hτ, hsq, map_one, one_mul]

theorem monoSwap_mem {n : ℕ} [Finite K] (h : UnitaryFieldData 2 n K) (hij : i ≠ j) {c : Kˣ}
    (hc : c ^ (2 ^ n + 1) = 1) : monoSwap i j c ∈ unitarySU 2 n K d := by
  refine Subgroup.mul_mem _ (TableBUE.diagHom_mem_unitarySU h (fun k => ?_) (prod_swapDiag c))
    (TableBUE.permGL_swap_mem h i j)
  by_cases hki : k = i
  · rw [hki, swapDiag_left hij, hc]
  · by_cases hkj : k = j
    · rw [hkj, swapDiag_right hij, inv_pow, hc, inv_one]
    · rw [swapDiag_of_ne hki hkj, one_pow]

theorem monoSwap_not_mem_scalars (hij : i ≠ j) (c : Kˣ) :
    (monoSwap i j c : GL (Fin d) K) ∉ LargeEvenScalars (Fin d) K := by
  rintro ⟨a, ha⟩
  have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K))
    ha) i) i
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    monoSwap, Units.val_mul, coe_diagHom, Matrix.diagonal_mul, TableBUE.permGL_apply,
    Equiv.swap_inv, Equiv.swap_apply_left] at h1
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (Ne.symm hij)), mul_zero] at h1
  exact a.ne_zero h1

theorem commute_monoSwap {σ : Fin d → Kˣ} (hσ : σ i = σ j) (c : Kˣ) :
    diagHom d σ * monoSwap i j c = monoSwap i j c * diagHom d σ := by
  have hσs : σ ∘ Equiv.swap i j = σ := by
    funext k
    rw [Function.comp_apply]
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left, hσ]
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right, hσ]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [monoSwap, ← mul_assoc, (diagHom_commute σ (swapDiag i j c)).eq, mul_assoc,
    diagHom_mul_permGL_swap, hσs, mul_assoc]

theorem glAut_diagHom (φ : K ≃+* K) (σ : Fin d → Kˣ) :
    glAut φ (diagHom d σ) = diagHom d (fun k => Units.map (φ : K →* K) (σ k)) := by
  apply Units.ext
  rw [coe_glAut, coe_diagHom, coe_diagHom, Matrix.diagonal_map (map_zero φ)]
  rfl

theorem glAut_permGL (φ : K ≃+* K) (π : Equiv.Perm (Fin d)) :
    glAut φ (permGL π) = (permGL π : GL (Fin d) K) := by
  apply Units.ext
  rw [coe_glAut]
  ext a b
  rw [Matrix.map_apply, TableBUE.permGL_apply]
  split_ifs <;> simp

theorem diagHom_conj_glAut_monoSwap (hij : i ≠ j) (φ : K ≃+* K) (β : Fin d → Kˣ) {c : Kˣ}
    (hc : Units.map (φ : K →* K) c = β j * (β i)⁻¹ * c) :
    diagHom d β * glAut φ (monoSwap i j c) * (diagHom d β)⁻¹ = monoSwap i j c := by
  have hτ : (fun k => Units.map (φ : K →* K) (swapDiag i j c k)) =
      swapDiag i j (Units.map (φ : K →* K) c) := by
    funext k
    by_cases hki : k = i
    · rw [hki, swapDiag_left hij, swapDiag_left hij]
    · by_cases hkj : k = j
      · rw [hkj, swapDiag_right hij, swapDiag_right hij, map_inv]
      · rw [swapDiag_of_ne hki hkj, swapDiag_of_ne hki hkj, map_one]
  have hβ : β * swapDiag i j (Units.map (φ : K →* K) c) * (β⁻¹ ∘ Equiv.swap i j) =
      swapDiag i j c := by
    funext k
    simp only [Pi.mul_apply, Function.comp_apply, Pi.inv_apply]
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left, swapDiag_left hij, swapDiag_left hij, hc]
      apply Units.ext
      push_cast
      field_simp
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right, swapDiag_right hij, swapDiag_right hij, hc]
        apply Units.ext
        push_cast
        field_simp
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, swapDiag_of_ne hki hkj,
          swapDiag_of_ne hki hkj, mul_one, mul_inv_cancel]
  rw [monoSwap, map_mul, glAut_diagHom, glAut_permGL, hτ, ← map_inv (diagHom d) β]
  calc diagHom d β * (diagHom d (swapDiag i j (Units.map (φ : K →* K) c)) *
        permGL (Equiv.swap i j)) * diagHom d β⁻¹
      = diagHom d β * diagHom d (swapDiag i j (Units.map (φ : K →* K) c)) *
          (permGL (Equiv.swap i j) * diagHom d β⁻¹) := by group
    _ = diagHom d β * diagHom d (swapDiag i j (Units.map (φ : K →* K) c)) *
          (diagHom d (β⁻¹ ∘ Equiv.swap i j) * permGL (Equiv.swap i j)) := by
        rw [permGL_swap_mul_diagHom]
    _ = diagHom d (β * swapDiag i j (Units.map (φ : K →* K) c) * (β⁻¹ ∘ Equiv.swap i j)) *
          permGL (Equiv.swap i j) := by
        rw [map_mul, map_mul]
        group
    _ = diagHom d (swapDiag i j c) * permGL (Equiv.swap i j) := by rw [hβ]

end Mono

end TableBUM

end CFSG.StandardType
