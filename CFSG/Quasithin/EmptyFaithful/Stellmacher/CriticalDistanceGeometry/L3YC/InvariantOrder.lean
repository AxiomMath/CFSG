module

public import Mathlib.LinearAlgebra.Matrix.Transvection

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC

section Invariant

variable {U : Type*} [CommGroup U] [Finite U]

theorem card_invariant_pow (act : Set (U →* U))
    (hirr : ∀ W : Subgroup U, (∀ f ∈ act, ∀ w ∈ W, f w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ (k : ℕ) (W : Subgroup (Fin k → U)), (∀ f ∈ act, ∀ w ∈ W, (fun i => f (w i)) ∈ W) →
      ∃ r : ℕ, Nat.card W = Nat.card U ^ r := by
  intro k
  induction k with
  | zero =>
    intro W _
    refine ⟨0, ?_⟩
    have : Subsingleton ↥W := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    simpa using Nat.card_of_subsingleton (1 : ↥W)
  | succ k ih =>
    intro W hW
    let π₀ : (Fin (k + 1) → U) →* U := Pi.evalMonoidHom (fun _ => U) 0
    let ι : (Fin k → U) →* (Fin (k + 1) → U) :=
      { toFun := fun v => Fin.cons 1 v
        map_one' := by ext i; refine Fin.cases rfl (fun _ => rfl) i
        map_mul' := fun a b => by ext i; refine Fin.cases (by simp) (fun _ => rfl) i }
    have hιinj : Function.Injective ι := fun a b h => by
      ext i
      have := congrFun h i.succ
      simpa [ι] using this
    set W' : Subgroup (Fin k → U) := W.comap ι with hW'
    have hW'inv : ∀ f ∈ act, ∀ w ∈ W', (fun i => f (w i)) ∈ W' := by
      intro f hf w hw
      show ι (fun i => f (w i)) ∈ W
      have : ι (fun i => f (w i)) = fun i => f (ι w i) := by
        ext i
        refine Fin.cases (by simp [ι]) (fun _ => rfl) i
      rw [this]
      exact hW f hf _ hw
    obtain ⟨r, hr⟩ := ih W' hW'inv
    have hrange : (π₀.domRestrict W).range = W.map π₀ := MonoidHom.domRestrict_range W π₀
    have hker : (π₀.domRestrict W).ker = π₀.ker.subgroupOf W := by
      ext x; simp [Subgroup.mem_subgroupOf]
    have h1 := Subgroup.card_ker_mul_card_range (π₀.domRestrict W)
    rw [hker, hrange] at h1
    have hkerc : Nat.card ↥(π₀.ker.subgroupOf W) = Nat.card W' := by
      have e1 : Nat.card ↥(π₀.ker.subgroupOf W) = Nat.card ↥(π₀.ker ⊓ W) := by
        rw [← Subgroup.card_map_of_injective W.subtype_injective, Subgroup.subgroupOf_map_subtype]
      have e2 : W'.map ι = π₀.ker ⊓ W := by
        ext x
        simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_inf, MonoidHom.mem_ker]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨by simp [π₀, ι], hv⟩
        · rintro ⟨h0, hx⟩
          refine ⟨fun i => x i.succ, ?_, ?_⟩
          · have : ι (fun i => x i.succ) = x := by
              ext i
              refine Fin.cases ?_ (fun _ => rfl) i
              simpa [ι, π₀] using h0.symm
            show ι (fun i => x i.succ) ∈ W
            rw [this]; exact hx
          · ext i
            refine Fin.cases ?_ (fun _ => rfl) i
            simpa [ι, π₀] using h0.symm
      rw [e1, ← e2, Subgroup.card_map_of_injective hιinj]
    have hWπ : ∀ f ∈ act, ∀ w ∈ W.map π₀, f w ∈ W.map π₀ := by
      rintro f hf _ ⟨w, hw, rfl⟩
      exact ⟨fun i => f (w i), hW f hf w hw, rfl⟩
    rw [hkerc] at h1
    rcases hirr _ hWπ with hbot | htop
    · refine ⟨r, ?_⟩
      rw [← h1, hr, hbot, Subgroup.card_bot, mul_one]
    · refine ⟨r + 1, ?_⟩
      rw [← h1, hr, htop, Subgroup.card_top, pow_succ]

end Invariant


section Irreducible

open Matrix

variable {F : Type*} [Field F]

@[expose] def matAct (A : Matrix (Fin 3) (Fin 3) F) : Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F) where
  toFun v := Multiplicative.ofAdd (A.mulVec (Multiplicative.toAdd v))
  map_one' := by simp
  map_mul' a b := by simp [Matrix.mulVec_add]

@[expose] def tvActs (F : Type*) [Field F] : Set (Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F)) :=
  {f | ∃ (l j : Fin 3) (_ : l ≠ j) (t : F), f = matAct (transvection l j t)}

theorem tv_apply (l j : Fin 3) (t : F) (v : Fin 3 → F) :
    (transvection l j t).mulVec v = v + Pi.single l (t * v j) := by
  ext m
  simp only [transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  rw [Matrix.single_mulVec]
  simp [Pi.single_apply, Function.update_apply]

theorem irreducible_tv (W : Subgroup (Multiplicative (Fin 3 → F)))
    (hW : ∀ f ∈ tvActs F, ∀ w ∈ W, f w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hne : ∀ i : Fin 3, i + 1 ≠ i := by decide
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra h
    push Not at h
    exact hbot ((Subgroup.eq_bot_iff_forall W).mpr h)
  set v := Multiplicative.toAdd w with hv
  have hv0 : v ≠ 0 := fun h => hw1 (by
    apply Multiplicative.toAdd.injective
    simpa [hv] using h)
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hsingle1 : ∀ l, l ≠ j → ∀ t : F,
      Multiplicative.ofAdd (Pi.single l t : Fin 3 → F) ∈ W := by
    intro l hl t
    have hf : matAct (transvection l j (t / v j)) ∈ tvActs F := ⟨l, j, hl, t / v j, rfl⟩
    have h1 := hW _ hf w hwW
    have h2 : Multiplicative.ofAdd (Pi.single l t : Fin 3 → F) =
        matAct (transvection l j (t / v j)) w * w⁻¹ := by
      apply Multiplicative.toAdd.injective
      simp [matAct, tv_apply, ← hv, div_mul_cancel₀ _ hj]
    rw [h2]
    exact W.mul_mem h1 (W.inv_mem hwW)
  have hsingle : ∀ (i : Fin 3) (t : F),
      Multiplicative.ofAdd (Pi.single i t : Fin 3 → F) ∈ W := by
    intro i t
    by_cases hi : i = j
    · subst hi
      obtain ⟨l, hl⟩ : ∃ l : Fin 3, l ≠ i := ⟨i + 1, hne i⟩
      have hel := hsingle1 l hl 1
      have hf : matAct (transvection i l t) ∈ tvActs F := ⟨i, l, hl.symm, t, rfl⟩
      have h1 := hW _ hf _ hel
      have h2 : Multiplicative.ofAdd (Pi.single i t : Fin 3 → F) =
          matAct (transvection i l t) (Multiplicative.ofAdd (Pi.single l 1 : Fin 3 → F)) *
            (Multiplicative.ofAdd (Pi.single l 1 : Fin 3 → F))⁻¹ := by
        apply Multiplicative.toAdd.injective
        simp [matAct, tv_apply]
      rw [h2]
      exact W.mul_mem h1 (W.inv_mem hel)
    · exact hsingle1 i hi t
  rw [eq_top_iff]
  intro x _
  have hx : x = ∏ i, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x i) : Fin 3 → F) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp [Finset.univ_sum_single]
  rw [hx]
  exact Subgroup.prod_mem _ fun i _ => hsingle i _

end Irreducible

end CFSG.Quasithin.Stellmacher.CD.L3YC
