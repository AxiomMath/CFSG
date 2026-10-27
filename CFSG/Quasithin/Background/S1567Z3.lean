module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.Quasithin.S1567

variable {U E : Type*} [CommGroup U] [Finite U] [CommGroup E] [Finite E]

private theorem eq_of_card_eq_four (hE : ∀ e : E, e ^ 2 = 1) (hE4 : Nat.card E = 4) {a b : E}
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (x : E) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  let _ : Fintype E := Fintype.ofFinite E
  have hinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by rw [← sq, hE])
  have hab1 : a * b ≠ 1 := fun h => hab ((eq_inv_of_mul_eq_one_left h).trans hinv)
  have haba : a * b ≠ a := fun h => hb (by simpa using h)
  have habb : a * b ≠ b := fun h => ha (by simpa using h)
  have hcard : ({1, a, b, a * b} : Finset E).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair habb.symm]
    all_goals simp [ha.symm, hb.symm, hab1.symm, hab, haba.symm]
  have huniv : ({1, a, b, a * b} : Finset E) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, ← Nat.card_eq_fintype_card, hE4])
  have hx : x ∈ ({1, a, b, a * b} : Finset E) := huniv ▸ Finset.mem_univ x
  simpa using hx

private theorem eq_one_of_apply_eq_self (hE : ∀ e : E, e ^ 2 = 1) (hE4 : Nat.card E = 4)
    (ε : E ≃* E) (hε3 : ∀ e, ε (ε (ε e)) = e) (hε : ∃ e, ε e ≠ e) {e : E} (he : ε e = e) :
    e = 1 := by
  by_contra he1
  obtain ⟨x, hx⟩ := hε
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx (map_one ε)
  have hex : e ≠ x := by
    rintro rfl
    exact hx he
  rcases eq_of_card_eq_four hE hE4 he1 hx1 hex (ε x) with h | h | h | h
  · exact hx1 (ε.injective (h.trans (map_one ε).symm))
  · exact hex (ε.injective (he.trans h.symm))
  · exact hx h
  · have h2 : ε (ε x) = x := by
      rw [h, map_mul, he, h, ← mul_assoc, ← sq, hE, one_mul]
    have h3 := hε3 x
    rw [h2] at h3
    exact hx h3

private theorem eq_one_of_map_eq_one {M : Type*} [Monoid M] (hE : ∀ e : E, e ^ 2 = 1)
    (hE4 : Nat.card E = 4) (ε : E ≃* E) (hε3 : ∀ e, ε (ε (ε e)) = e) (hε : ∃ e, ε e ≠ e)
    (χ : E →* M) {z : E} (hz : χ z ≠ 1) {e : E} (he : χ e = 1) (hεe : χ (ε e) = 1) : e = 1 := by
  by_contra he1
  have hεe1 : ε e ≠ 1 := fun h => he1 (ε.injective (h.trans (map_one ε).symm))
  have hne : e ≠ ε e := fun h => he1 (eq_one_of_apply_eq_self hE hE4 ε hε3 hε h.symm)
  rcases eq_of_card_eq_four hE hE4 he1 hεe1 hne z with h | h | h | h <;>
    simp [h, he, hεe] at hz

omit [Finite U] in
private theorem eq_one_of_eq_comp (hE : ∀ e : E, e ^ 2 = 1) (hE4 : Nat.card E = 4)
    (ε σ : E ≃* E) (hε3 : ∀ e, ε (ε (ε e)) = e) (hε : ∃ e, ε e ≠ e)
    (hσε : ∀ e, σ (ε e) = ε (ε (σ e))) (t : U → U) (Θ : Subgroup (U →* E))
    (ht : ∀ f ∈ Θ, ∀ u, f (t u) = σ (f u)) {f f' : U →* E} (hf : f ∈ Θ) (hf' : f' ∈ Θ)
    (h : ∀ u, f u = ε (f' u)) (u : U) : f' u = 1 := by
  have h1 : ε (σ (f' u)) = ε (ε (σ (f' u))) := by
    rw [← hσε, ← h u, ← ht f hf u, h (t u), ht f' hf' u]
  have h2 : σ (f' u) = 1 := eq_one_of_apply_eq_self hE hE4 ε hε3 hε (ε.injective h1).symm
  exact σ.injective (h2.trans (map_one σ).symm)

omit [Finite U] in
private theorem eq_one_of_map_comp_eq_one {M : Type*} [Monoid M] (hE : ∀ e : E, e ^ 2 = 1)
    (hE4 : Nat.card E = 4) (ε σ : E ≃* E) (hε3 : ∀ e, ε (ε (ε e)) = e) (hε : ∃ e, ε e ≠ e)
    (hσε : ∀ e, σ (ε e) = ε (ε (σ e))) (y t : U → U) (Θ : Subgroup (U →* E))
    (hy : ∀ f ∈ Θ, ∀ u, f (y u) = ε (f u)) (ht : ∀ f ∈ Θ, ∀ u, f (t u) = σ (f u))
    (χ : E →* M) {z : E} (hz : χ z ≠ 1) {F F' : U →* E} (hF : F ∈ Θ) (hF' : F' ∈ Θ)
    (hχ : ∀ u, χ (F u * ε (F' u)) = 1) : F = 1 ∧ F' = 1 := by
  have hg : ∀ u, F u * ε (F' u) = 1 := by
    intro u
    refine eq_one_of_map_eq_one hE hE4 ε hε3 hε χ hz (hχ u) ?_
    rw [map_mul, ← hy F hF u, ← hy F' hF' u]
    exact hχ (y u)
  have hF'1 : ∀ u, F' u = 1 := by
    intro u
    have := eq_one_of_eq_comp hE hE4 ε σ hε3 hε hσε t Θ ht hF (Θ.inv_mem hF')
      (fun v => by
        rw [MonoidHom.inv_apply, map_inv]
        exact eq_inv_of_mul_eq_one_left (hg v)) u
    rwa [MonoidHom.inv_apply, inv_eq_one] at this
  refine ⟨MonoidHom.ext fun u => ?_, MonoidHom.ext fun u => by simp [hF'1 u]⟩
  simpa [hF'1 u] using hg u

theorem card_sq_le_index_iInf_ker (hE : ∀ e : E, e ^ 2 = 1) (hE4 : Nat.card E = 4)
    (ε σ : E ≃* E) (hε3 : ∀ e, ε (ε (ε e)) = e) (hε : ∃ e, ε e ≠ e)
    (hσε : ∀ e, σ (ε e) = ε (ε (σ e)))
    (y t : U → U) (Θ : Subgroup (U →* E))
    (hy : ∀ f ∈ Θ, ∀ u, f (y u) = ε (f u)) (ht : ∀ f ∈ Θ, ∀ u, f (t u) = σ (f u)) :
    Nat.card Θ ^ 2 ≤ (⨅ f ∈ Θ, f.ker).index := by
  set K : Subgroup U := ⨅ f ∈ Θ, f.ker
  have hmemK : ∀ u ∈ K, ∀ f ∈ Θ, f u = 1 := fun u hu f hf =>
    MonoidHom.mem_ker.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hu f) hf)
  have : NeZero (Monoid.exponent E) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero (Monoid.exponent (U ⧸ K)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨z, hz⟩ : ∃ z : E, z ≠ 1 := by
    obtain ⟨e, he⟩ := hε
    exact ⟨e, fun h => he (by rw [h, map_one])⟩
  obtain ⟨χ, hχ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity E (AlgebraicClosure ℚ) hz
  let g : Θ × Θ → (U →* (AlgebraicClosure ℚ)ˣ) := fun a =>
    χ.comp (a.1.1 * ε.toMonoidHom.comp a.2.1)
  have hg : ∀ a u, g a u = χ (a.1.1 u * ε (a.2.1 u)) := fun a u => rfl
  have hgK : ∀ a, K ≤ (g a).ker := fun a u hu => by
    simp [hg, hmemK u hu _ a.1.2, hmemK u hu _ a.2.2]
  let Φ : Θ × Θ → (U ⧸ K →* (AlgebraicClosure ℚ)ˣ) := fun a => QuotientGroup.lift K (g a) (hgK a)
  have hΦ : Function.Injective Φ := by
    intro a b hab
    have h1 : ∀ u, χ (a.1.1 u * ε (a.2.1 u)) = χ (b.1.1 u * ε (b.2.1 u)) := by
      intro u
      have := DFunLike.congr_fun hab (u : U ⧸ K)
      simpa only [Φ, QuotientGroup.lift_mk, hg] using this
    obtain ⟨h2, h3⟩ := eq_one_of_map_comp_eq_one hE hE4 ε σ hε3 hε hσε y t Θ hy ht χ hχ
      (Θ.div_mem a.1.2 b.1.2) (Θ.div_mem a.2.2 b.2.2) fun u => by
        rw [MonoidHom.div_apply, MonoidHom.div_apply, map_div, div_mul_div_comm, map_div, h1 u,
          div_self']
    exact Prod.ext (Subtype.ext (div_eq_one.mp h2)) (Subtype.ext (div_eq_one.mp h3))
  have hcard : Nat.card (U ⧸ K →* (AlgebraicClosure ℚ)ˣ) = K.index :=
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (U ⧸ K) (AlgebraicClosure ℚ)).trans
      K.index_eq_card.symm
  have : Finite (U ⧸ K →* (AlgebraicClosure ℚ)ˣ) :=
    Nat.finite_of_card_ne_zero (hcard ▸ Subgroup.index_ne_zero_of_finite)
  calc Nat.card Θ ^ 2 = Nat.card (Θ × Θ) := by rw [Nat.card_prod, sq]
    _ ≤ Nat.card (U ⧸ K →* (AlgebraicClosure ℚ)ˣ) := Nat.card_le_card_of_injective Φ hΦ
    _ = K.index := hcard

end CFSG.Quasithin.S1567
