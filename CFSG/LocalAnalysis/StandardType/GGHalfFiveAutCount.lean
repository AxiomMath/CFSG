module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.StandardType.GGHalf

private lemma inv_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a * b⁻¹ = b⁻¹ * a := by
  have h1 : a * b⁻¹ * b = a := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have h2 : b⁻¹ * a * b = a := by rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  exact mul_right_cancel (by rw [h1, h2])

private lemma inv_comm' {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a⁻¹ * b = b * a⁻¹ := by
  exact (inv_comm h.symm).symm

private lemma comm_of_generators {E : Type*} [Group E] (e : Fin 4 → E)
    (hcomm : ∀ i j, e i * e j = e j * e i)
    (hgen : Subgroup.closure (Set.range e) = ⊤) : ∀ x y : E, x * y = y * x := by
  have hgcomm : ∀ (i : Fin 4) (y : E), e i * y = y * e i := by
    intro i y
    have hy : y ∈ Subgroup.closure (Set.range e) := by rw [hgen]; exact Subgroup.mem_top y
    refine Subgroup.closure_induction (k := Set.range e) (p := fun z _ => e i * z = z * e i)
      ?_ ?_ ?_ ?_ hy
    · intro z hz
      obtain ⟨j, rfl⟩ := hz
      exact hcomm i j
    · simp
    · intro a b ha hb ha' hb'
      calc e i * (a * b) = (e i * a) * b := by rw [mul_assoc]
        _ = (a * e i) * b := by rw [ha']
        _ = a * (e i * b) := by rw [mul_assoc]
        _ = a * (b * e i) := by rw [hb']
        _ = (a * b) * e i := by rw [mul_assoc]
    · intro a ha ha'
      exact inv_comm ha'
  intro x y
  have hx : x ∈ Subgroup.closure (Set.range e) := by rw [hgen]; exact Subgroup.mem_top x
  refine Subgroup.closure_induction (k := Set.range e) (p := fun z _ => z * y = y * z)
    ?_ ?_ ?_ ?_ hx
  · intro z hz
    obtain ⟨i, rfl⟩ := hz
    exact hgcomm i y
  · simp
  · intro a b ha hb ha' hb'
    calc (a * b) * y = a * (b * y) := by rw [mul_assoc]
      _ = a * (y * b) := by rw [hb']
      _ = (a * y) * b := by rw [mul_assoc]
      _ = (y * a) * b := by rw [ha']
      _ = y * (a * b) := by rw [mul_assoc]
  · intro a ha ha'
    exact inv_comm' ha'

private lemma indep_prod {E : Type*} [CommGroup E] (e : Fin 4 → E)
    (hindep : ∀ a b c d : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c * e 3 ^ d = 1 →
      (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d)
    (f : Fin 4 → ℤ) (hf : ∏ i : Fin 4, e i ^ f i = 1) : ∀ i, (3 : ℤ) ∣ f i := by
  have hf' : e 0 ^ f 0 * e 1 ^ f 1 * e 2 ^ f 2 * e 3 ^ f 3 = 1 := by
    rwa [Fin.prod_univ_four] at hf
  have h := hindep (f 0) (f 1) (f 2) (f 3) hf'
  intro i
  refine Fin.cases h.1 (fun i1 => ?_) i
  refine Fin.cases h.2.1 (fun i2 => ?_) i1
  refine Fin.cases h.2.2.1 (fun i3 => ?_) i2
  have hi3 : i3 = 0 := Subsingleton.elim i3 0
  subst hi3
  simpa using h.2.2.2

private lemma indep_two {E : Type*} [CommGroup E] (e : Fin 4 → E)
    (hindep : ∀ a b c d : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c * e 3 ^ d = 1 →
      (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d)
    {i j : Fin 4} (hij : i ≠ j) (a b : ℤ) (h : e i ^ a * e j ^ b = 1) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b := by
  let g : Fin 4 → ℤ := fun k => if k = i then a else if k = j then b else 0
  have hf : ∏ k : Fin 4, e k ^ g k = 1 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => e k ^ g k) (Finset.mem_univ i)]
    have hgi : g i = a := by simp [g]
    rw [hgi]
    have hprod : ∏ k ∈ Finset.univ.erase i, e k ^ g k = e j ^ b := by
      rw [Finset.prod_eq_single (s := Finset.univ.erase i) (f := fun k => e k ^ g k) j]
      · simp [g, Ne.symm hij]
      · intro k hk hkj
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        simp [g, hki, hkj]
      · intro hmem
        exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hmem
    rw [hprod]
    exact h
  have hall := indep_prod e hindep g hf
  constructor
  · have := hall i
    simpa [g] using this
  · have := hall j
    simpa [g, hij, Ne.symm hij] using this

theorem card_le_24_of_signed {E : Type} [Group E] (e : Fin 4 → E)
    (hcomm : ∀ i j, e i * e j = e j * e i) (hpow : ∀ i, e i ^ 3 = 1)
    (hgen : Subgroup.closure (Set.range e) = ⊤)
    (hindep : ∀ a b c d : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c * e 3 ^ d = 1 →
      (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d)
    (A : Subgroup (MulAut E))
    (hA : ∀ φ ∈ A, ∀ i, ∃ j, φ (e i) = e j ∨ φ (e i) = (e j)⁻¹)
    (hfix : ∀ φ ∈ A, φ (e 0 * e 1 * e 2 * e 3) = e 0 * e 1 * e 2 * e 3) :
    Nat.card A ≤ 24 := by
  classical
  have hcommE : ∀ x y : E, x * y = y * x := comm_of_generators e hcomm hgen
  letI : CommGroup E := { ‹Group E› with mul_comm := hcommE }
  let σ : A → Fin 4 → Fin 4 := fun φ i => Classical.choose (hA φ.val φ.property i)
  have hσ : ∀ (φ : A) (i : Fin 4),
      φ.val (e i) = e (σ φ i) ∨ φ.val (e i) = (e (σ φ i))⁻¹ :=
    fun φ i => Classical.choose_spec (hA φ.val φ.property i)
  let ε : A → Fin 4 → ℤ := fun φ i => if φ.val (e i) = e (σ φ i) then 1 else -1
  have hε : ∀ (φ : A) (i : Fin 4), φ.val (e i) = e (σ φ i) ^ ε φ i := by
    intro φ i
    by_cases h : φ.val (e i) = e (σ φ i)
    · simp [ε, h]
    · have h' := hσ φ i
      rcases h' with h' | h'
      · exact absurd h' h
      · rw [h']
        simp [ε, h]
  have hε_cases : ∀ (φ : A) (i : Fin 4), ε φ i = 1 ∨ ε φ i = -1 := by
    intro φ i
    unfold ε
    split <;> simp
  have hσ_inj : ∀ φ : A, Function.Injective (σ φ) := by
    intro φ i i' hii
    by_contra hne
    have hspec_i := hε φ i
    have hspec_i' : φ.val (e i') = e (σ φ i) ^ ε φ i' := by
      rw [hii]; exact hε φ i'
    have hsq : ε φ i * ε φ i = 1 := by
      rcases hε_cases φ i with h | h <;> rw [h] <;> decide
    have hsq' : ε φ i' * ε φ i' = 1 := by
      rcases hε_cases φ i' with h | h <;> rw [h] <;> decide
    have hpi : φ.val (e i ^ ε φ i) = e (σ φ i) := by
      rw [map_zpow, hspec_i, ← zpow_mul, hsq, zpow_one]
    have hpi' : φ.val (e i' ^ ε φ i') = e (σ φ i) := by
      rw [map_zpow, hspec_i', ← zpow_mul, hsq', zpow_one]
    have heq : e i ^ ε φ i = e i' ^ ε φ i' := by
      apply φ.val.injective
      rw [hpi, hpi']
    have hprod : e i ^ ε φ i * e i' ^ (-(ε φ i')) = 1 := by
      rw [zpow_neg, ← heq]
      exact mul_inv_cancel _
    have hdvd := indep_two e hindep hne (ε φ i) (-(ε φ i')) hprod
    rcases hε_cases φ i with h | h <;> rcases hε_cases φ i' with h' | h' <;>
      rw [h, h'] at hdvd
    all_goals exact absurd hdvd.1 (by decide)
  let π : A → Equiv.Perm (Fin 4) := fun φ =>
    Equiv.ofBijective (σ φ) ((hσ_inj φ).bijective_of_finite)
  have hsign : ∀ (φ : A) (i : Fin 4), ε φ i = 1 := by
    intro φ i
    have hfixφ := hfix φ.val φ.property
    have hmap : φ.val (e 0 * e 1 * e 2 * e 3) =
        φ.val (e 0) * φ.val (e 1) * φ.val (e 2) * φ.val (e 3) := by
      rw [map_mul, map_mul, map_mul]
    rw [hmap] at hfixφ
    have h1 : (∏ k : Fin 4, e (σ φ k) ^ ε φ k) = e 0 * e 1 * e 2 * e 3 := by
      rw [Fin.prod_univ_four]
      rw [← hε φ 0, ← hε φ 1, ← hε φ 2, ← hε φ 3]
      exact hfixφ
    have h2 : (∏ k : Fin 4, e k ^ ε φ ((π φ).symm k)) = e 0 * e 1 * e 2 * e 3 := by
      have hre := Equiv.prod_comp (π φ) (fun k : Fin 4 => e k ^ ε φ ((π φ).symm k))
      simp only [Equiv.symm_apply_apply] at hre
      rw [← hre]
      exact h1
    have h3 : (∏ k : Fin 4, e k ^ (ε φ ((π φ).symm k) - 1)) = 1 := by
      have h4 : (∏ k : Fin 4, e k ^ (ε φ ((π φ).symm k) - 1))
          = (∏ k : Fin 4, e k ^ ε φ ((π φ).symm k))
            / (∏ k : Fin 4, e k ^ (1 : ℤ)) := by
        rw [← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro k _
        rw [zpow_sub, div_eq_mul_inv]
      rw [h4, h2]
      rw [show (∏ k : Fin 4, e k ^ (1 : ℤ)) = e 0 * e 1 * e 2 * e 3 by
        rw [Fin.prod_univ_four]; simp]
      rw [div_eq_mul_inv, mul_inv_cancel]
    have hdvd : (3 : ℤ) ∣ ε φ i - 1 := by
      have h := indep_prod e hindep (fun k : Fin 4 => ε φ ((π φ).symm k) - 1) h3 ((π φ) i)
      simpa [Equiv.symm_apply_apply] using h
    rcases hε_cases φ i with h | h
    · exact h
    · rw [h] at hdvd
      exact absurd hdvd (by decide)
  have hact : ∀ (φ : A) (i : Fin 4), φ.val (e i) = e (π φ i) := by
    intro φ i
    have h := hε φ i
    rw [hsign φ i, zpow_one] at h
    exact h
  have hπ_inj : Function.Injective π := by
    intro φ ψ hφψ
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hEqAll : ∀ z ∈ Subgroup.closure (Set.range e), φ.val z = ψ.val z := by
      intro z hz
      refine Subgroup.closure_induction (k := Set.range e) (p := fun z _ => φ.val z = ψ.val z)
        ?_ ?_ ?_ ?_ hz
      · intro y hy
        obtain ⟨i, rfl⟩ := hy
        rw [hact φ i, hact ψ i, hφψ]
      · simp
      · intro a b ha hb ha' hb'
        rw [map_mul, map_mul, ha', hb']
      · intro a ha ha'
        rw [map_inv, map_inv, ha']
    exact hEqAll x (by rw [hgen]; exact Subgroup.mem_top x)
  have hcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  calc Nat.card A ≤ Nat.card (Equiv.Perm (Fin 4)) := Nat.card_le_card_of_injective π hπ_inj
    _ = 24 := hcard

end CFSG.StandardType.GGHalf

end
