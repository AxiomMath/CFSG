module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Lin
public import CFSG.Mathlib.Decide.Bounded
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.StdBasis

public section

namespace CFSG.StandardType.A6

open Matrix

@[expose] def a6Surv : List (V6 × V6) := [
  (![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2]),
  (![0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 2]),
  (![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 1]),
  (![0, 0, 0, 0, 0, 2], ![2, 2, 2, 2, 2, 1]),
  (![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1]),
  (![0, 0, 0, 0, 2, 2], ![0, 0, 0, 0, 2, 2]),
  (![0, 0, 1, 1, 1, 1], ![1, 1, 2, 2, 2, 2]),
  (![0, 0, 2, 2, 2, 2], ![2, 2, 1, 1, 1, 1]),
  (![0, 1, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1]),
  (![0, 1, 1, 1, 1, 1], ![2, 1, 1, 1, 1, 1]),
  (![0, 2, 2, 2, 2, 2], ![0, 2, 2, 2, 2, 2]),
  (![0, 2, 2, 2, 2, 2], ![1, 2, 2, 2, 2, 2]),
  (![1, 1, 1, 1, 1, 2], ![0, 0, 0, 0, 0, 1]),
  (![1, 1, 1, 1, 1, 2], ![1, 1, 1, 1, 1, 0]),
  (![1, 1, 1, 1, 2, 2], ![2, 2, 2, 2, 0, 0]),
  (![1, 1, 2, 2, 2, 2], ![0, 0, 1, 1, 1, 1]),
  (![1, 2, 2, 2, 2, 2], ![0, 2, 2, 2, 2, 2]),
  (![1, 2, 2, 2, 2, 2], ![2, 0, 0, 0, 0, 0])]

@[expose] def a6Excl : List (V6 × V6) := [
  (![0, 0, 0, 0, 1, 1], ![2, 2, 2, 2, 1, 1]),
  (![0, 0, 0, 0, 2, 2], ![1, 1, 1, 1, 2, 2]),
  (![0, 0, 0, 1, 1, 2], ![2, 2, 2, 0, 0, 1]),
  (![0, 0, 0, 1, 1, 2], ![2, 2, 2, 1, 1, 0]),
  (![0, 0, 0, 1, 2, 2], ![1, 1, 1, 0, 2, 2]),
  (![0, 0, 0, 1, 2, 2], ![1, 1, 1, 2, 0, 0]),
  (![0, 0, 1, 1, 1, 1], ![0, 0, 2, 2, 2, 2]),
  (![0, 0, 1, 1, 1, 2], ![0, 0, 2, 2, 2, 1]),
  (![0, 0, 1, 1, 1, 2], ![2, 2, 0, 0, 0, 1]),
  (![0, 0, 1, 2, 2, 2], ![0, 0, 2, 1, 1, 1]),
  (![0, 0, 1, 2, 2, 2], ![1, 1, 2, 0, 0, 0]),
  (![0, 0, 2, 2, 2, 2], ![0, 0, 1, 1, 1, 1]),
  (![0, 1, 1, 1, 2, 2], ![0, 1, 1, 1, 2, 2]),
  (![0, 1, 1, 1, 2, 2], ![1, 0, 0, 0, 2, 2]),
  (![0, 1, 1, 2, 2, 2], ![0, 1, 1, 2, 2, 2]),
  (![0, 1, 1, 2, 2, 2], ![2, 1, 1, 0, 0, 0]),
  (![1, 1, 1, 1, 2, 2], ![0, 0, 0, 0, 2, 2]),
  (![1, 1, 2, 2, 2, 2], ![1, 1, 0, 0, 0, 0])]


@[expose] def a6Sorted : List V6 := [
  ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 2], ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 1, 2],
  ![0, 0, 0, 1, 2, 2], ![0, 0, 0, 2, 2, 2], ![0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 2],
  ![0, 0, 1, 1, 2, 2], ![0, 0, 1, 2, 2, 2], ![0, 0, 2, 2, 2, 2], ![0, 1, 1, 1, 1, 1],
  ![0, 1, 1, 1, 1, 2], ![0, 1, 1, 1, 2, 2], ![0, 1, 1, 2, 2, 2], ![0, 1, 2, 2, 2, 2],
  ![0, 2, 2, 2, 2, 2], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 2], ![1, 1, 1, 1, 2, 2],
  ![1, 1, 1, 2, 2, 2], ![1, 1, 2, 2, 2, 2], ![1, 2, 2, 2, 2, 2], ![2, 2, 2, 2, 2, 2]]

open scoped CFSG.Decide.Bounded in
theorem a6_sorted_mem : ∀ c' : V6, Monotone (fun i => (c' i).val) → c' ∈ a6Sorted := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem a6_pattern_check :
    ∀ (c' : V6), c' ∈ a6Sorted → ∀ α : ZMod 3 → ZMod 3,
      (fun i => α (c' i)) ⬝ᵥ c' = 2 →
      (∀ i j, α (c' i) = α (c' j) ↔ c' i = c' j) →
      (fun i => α (c' i)) ⬝ᵥ one6 ≠ 0 → (∀ μ : ZMod 3, c' ≠ μ • one6) →
      (c', fun i => α (c' i)) ∈ a6Surv ∨ (c', fun i => α (c' i)) ∈ a6Excl := by
  decide +kernel

theorem a6_dot_comp (a c : V6) (σ : Equiv.Perm (Fin 6)) :
    (a ∘ σ) ⬝ᵥ (c ∘ σ) = a ⬝ᵥ c := by
  simpa [Function.comp_def] using dotProduct_comp_equiv_symm (e := σ.symm) (u := a ∘ σ) (x := c)

theorem a6_alpha_comp (c' a' : V6) (hsym : ∀ i j, a' i = a' j ↔ c' i = c' j) :
    ∃ α : ZMod 3 → ZMod 3, a' = fun i => α (c' i) := by
  classical
  let α : ZMod 3 → ZMod 3 :=
    fun y => if h : ∃ i, c' i = y then a' (Classical.choose h) else 0
  refine ⟨α, funext fun i => ?_⟩
  have hex : ∃ j, c' j = c' i := ⟨i, rfl⟩
  have hspec : c' (Classical.choose hex) = c' i := Classical.choose_spec hex
  have ha : a' (Classical.choose hex) = a' i := (hsym _ _).mpr hspec
  show a' i = α (c' i)
  simp only [α, dif_pos hex]
  exact ha.symm

theorem a6_swap_dot (i j : Fin 6) (hij : i ≠ j) :
    (e6 i - e6 j) ⬝ᵥ (e6 i - e6 j) = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

theorem a6_perm6_swap_single :
    ∀ (i j k : Fin 6) (x : ZMod 3),
      perm6 (Equiv.swap i j) (Pi.single k x) =
        Pi.single k x - ((e6 i - e6 j) ⬝ᵥ Pi.single k x) • (e6 i - e6 j) := by
  decide +kernel

theorem a6_perm6_swap (i j : Fin 6) (hij : i ≠ j) :
    perm6 (Equiv.swap i j) =
      refl6 (e6 i - e6 j) (e6 i - e6 j) (a6_swap_dot i j hij) := by
  have hm : (perm6 (Equiv.swap i j) : V6 →ₗ[ZMod 3] V6) =
      (refl6 (e6 i - e6 j) (e6 i - e6 j) (a6_swap_dot i j hij) :
        V6 →ₗ[ZMod 3] V6) := by
    apply LinearMap.pi_ext
    intro k x
    exact a6_perm6_swap_single i j k x
  apply LinearEquiv.ext
  intro v
  exact congrFun (congrArg (fun f : V6 →ₗ[ZMod 3] V6 => (f : V6 → V6)) hm) v

theorem a6_dot_sub_single (a : V6) (i j : Fin 6) :
    a ⬝ᵥ (e6 i - e6 j) = a i - a j := by
  rw [show e6 i = Pi.single i (1 : ZMod 3) from rfl,
    show e6 j = Pi.single j (1 : ZMod 3) from rfl,
    dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem a6_sub_single_dot (c : V6) (i j : Fin 6) :
    (e6 i - e6 j) ⬝ᵥ c = c i - c j := by
  rw [show e6 i = Pi.single i (1 : ZMod 3) from rfl,
    show e6 j = Pi.single j (1 : ZMod 3) from rfl,
    sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]

theorem a6_smul_one6_cases :
    ∀ t : ZMod 3, t • one6 = 0 ∨ t • one6 = one6 ∨ t • one6 = -one6 := by
  decide +kernel

theorem a6_one6_ne_zero : (one6 : V6) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [one6] at this

theorem a6_dot_one_ne {c a : V6} (hac : a ⬝ᵥ c = 2) {u : V6 ≃ₗ[ZMod 3] V6}
    (hu : u = refl6 c a hac) (h : MovesLine6 u) : a ⬝ᵥ one6 ≠ 0 := by
  intro h0
  apply h.1
  rw [hu, refl6_apply, h0, zero_smul, sub_zero]

theorem a6_c_ne_smul_one {c a : V6} (hac : a ⬝ᵥ c = 2) {u : V6 ≃ₗ[ZMod 3] V6}
    (hu : u = refl6 c a hac) (h : MovesLine6 u) : ∀ μ : ZMod 3, c ≠ μ • one6 := by
  intro μ hμ
  have hu0 : u one6 ≠ 0 := by
    intro h0
    have h10 : (one6 : V6) = 0 := by
      have := congrArg (fun x => u⁻¹ x) h0
      simpa using this
    exact a6_one6_ne_zero h10
  have hval : u one6 = (1 - (a ⬝ᵥ one6) * μ) • one6 := by
    rw [hu, refl6_apply, hμ, ← mul_smul]
    conv_rhs => rw [sub_smul, one_smul]
  rcases a6_smul_one6_cases (1 - (a ⬝ᵥ one6) * μ) with h0 | h1 | h1
  · exact hu0 (hval.trans h0)
  · exact h.1 (hval.trans h1)
  · exact h.2 (hval.trans h1)

theorem refl6_proof_irrel (c a : V6) (h h' : a ⬝ᵥ c = 2) :
    refl6 c a h = refl6 c a h' := by
  apply LinearEquiv.ext
  intro v
  rfl

theorem a6_excl_witness {A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (h : A6Hyp A M) {c a : V6}
    (hac : a ⬝ᵥ c = 2) (hu : refl6 c a hac ∈ A)
    (w w2 : Equiv.Perm (Fin 6)) (i j k : Fin 6) (_hij : i ≠ j)
    (hfix : FixesLine6 (refl6 c a hac * perm6 w * refl6 c a hac * perm6 w2 * refl6 c a hac))
    (hnot : ∀ m : Fin 6,
      ((refl6 c a hac * perm6 w * refl6 c a hac * perm6 w2 * refl6 c a hac) *
        perm6 (Equiv.swap i j) *
        (refl6 c a hac * perm6 w * refl6 c a hac * perm6 w2 * refl6 c a hac)⁻¹) (e6 k) ≠ e6 m) :
    False := by
  let u := refl6 c a hac
  have huA : u ∈ A := hu
  have hwA : perm6 w ∈ A := h.le (h.perm_mem w)
  have hw2A : perm6 w2 ∈ A := h.le (h.perm_mem w2)
  have hhA : u * perm6 w * u * perm6 w2 * u ∈ A := by
    exact A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem huA hwA) huA) hw2A) huA
  obtain ⟨τ, hτ⟩ := h.normW _ hhA hfix (Equiv.swap i j)
  have hval : (u * perm6 w * u * perm6 w2 * u * perm6 (Equiv.swap i j) *
      (u * perm6 w * u * perm6 w2 * u)⁻¹) (e6 k) = e6 (τ k) := by
    rw [hτ]
    exact perm6_e6 τ k
  exact hnot (τ k) hval

theorem a6_pattern (c a : V6) (hac : a ⬝ᵥ c = 2) (hsym : ∀ i j, a i = a j ↔ c i = c j)
    (h1 : a ⬝ᵥ one6 ≠ 0) (h2 : ∀ μ : ZMod 3, c ≠ μ • one6) :
    ∃ σ : Equiv.Perm (Fin 6), (c ∘ σ, a ∘ σ) ∈ a6Surv ∨ (c ∘ σ, a ∘ σ) ∈ a6Excl := by
  obtain ⟨σ, hmono⟩ := exists_perm_sorted c
  have hcmem : (c ∘ σ) ∈ a6Sorted := a6_sorted_mem (c ∘ σ) hmono
  have hsym' : ∀ i j, (a ∘ σ) i = (a ∘ σ) j ↔ (c ∘ σ) i = (c ∘ σ) j :=
    fun i j => hsym (σ i) (σ j)
  have hac' : (a ∘ σ) ⬝ᵥ (c ∘ σ) = 2 := by
    rw [a6_dot_comp]; exact hac
  have h1' : (a ∘ σ) ⬝ᵥ one6 ≠ 0 := by
    change (a ∘ σ) ⬝ᵥ (one6 ∘ σ) ≠ 0
    simpa [a6_dot_comp] using h1
  have h2' : ∀ μ : ZMod 3, (c ∘ σ) ≠ μ • one6 := by
    intro μ hμ
    apply h2 μ
    funext i
    have hi := congrFun hμ (σ.symm i)
    simpa [Function.comp_def, one6, Pi.smul_apply] using hi
  obtain ⟨α, hα⟩ := a6_alpha_comp (c ∘ σ) (a ∘ σ) hsym'
  rw [hα] at hac' hsym' h1'
  refine ⟨σ, ?_⟩
  rw [hα]
  exact a6_pattern_check (c ∘ σ) hcmem α hac' hsym' h1' h2'

theorem a6_excl {A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (h : A6Hyp A M) {c a : V6}
    (hp : (c, a) ∈ a6Excl) (hac : a ⬝ᵥ c = 2) (hu : refl6 c a hac ∈ A) : False := by
  simp only [a6Excl, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    exact a6_excl_witness h hac hu (c[2,4] * c[3,5]) (c[2,4] * c[3,5]) 0 2 0 (by decide)
      (by
        have hproof : hac = (by decide : (![2, 2, 2, 2, 1, 1] : V6) ⬝ᵥ (![0, 0, 0, 0, 1, 1] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![2, 2, 2, 2, 1, 1] : V6) ⬝ᵥ (![0, 0, 0, 0, 1, 1] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[2,4] * c[3,5]) (c[2,4] * c[3,5]) 0 2 0 (by decide)
      (by
        have hproof : hac = (by decide : (![1, 1, 1, 1, 2, 2] : V6) ⬝ᵥ (![0, 0, 0, 0, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![1, 1, 1, 1, 2, 2] : V6) ⬝ᵥ (![0, 0, 0, 0, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[1,3] * c[2,4,5]) (c[1,3] * c[2,5,4]) 0 1 0 (by decide)
      (by
        have hproof : hac = (by decide : (![2, 2, 2, 0, 0, 1] : V6) ⬝ᵥ (![0, 0, 0, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![2, 2, 2, 0, 0, 1] : V6) ⬝ᵥ (![0, 0, 0, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[2,3]) (c[0,2,5,4,1,3]) 0 3 0 (by decide)
      (by
        have hproof : hac = (by decide : (![2, 2, 2, 1, 1, 0] : V6) ⬝ᵥ (![0, 0, 0, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![2, 2, 2, 1, 1, 0] : V6) ⬝ᵥ (![0, 0, 0, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[2,4]) (c[0,2,4] * c[1,3,5]) 0 3 0 (by decide)
      (by
        have hproof : hac = (by decide : (![1, 1, 1, 0, 2, 2] : V6) ⬝ᵥ (![0, 0, 0, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![1, 1, 1, 0, 2, 2] : V6) ⬝ᵥ (![0, 0, 0, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[1,3] * c[2,4]) (c[0,1,3] * c[2,5,4]) 0 2 1 (by decide)
      (by
        have hproof : hac = (by decide : (![1, 1, 1, 2, 0, 0] : V6) ⬝ᵥ (![0, 0, 0, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![1, 1, 1, 2, 0, 0] : V6) ⬝ᵥ (![0, 0, 0, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[0,2] * c[1,3]) (c[0,2] * c[1,3]) 0 4 0 (by decide)
      (by
        have hproof : hac = (by decide : (![0, 0, 2, 2, 2, 2] : V6) ⬝ᵥ (![0, 0, 1, 1, 1, 1] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![0, 0, 2, 2, 2, 2] : V6) ⬝ᵥ (![0, 0, 1, 1, 1, 1] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[1,2]) (c[0,3,2,1,4,5]) 0 2 0 (by decide)
      (by
        have hproof : hac = (by decide : (![0, 0, 2, 2, 2, 1] : V6) ⬝ᵥ (![0, 0, 1, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![0, 0, 2, 2, 2, 1] : V6) ⬝ᵥ (![0, 0, 1, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[1,2] * c[4,5]) (c[0,1,2] * c[3,4,5]) 0 3 0 (by decide)
      (by
        have hproof : hac = (by decide : (![2, 2, 0, 0, 0, 1] : V6) ⬝ᵥ (![0, 0, 1, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![2, 2, 0, 0, 0, 1] : V6) ⬝ᵥ (![0, 0, 1, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[1,3]) (c[0,4,2] * c[1,5,3]) 0 2 0 (by decide)
      (by
        have hproof : hac = (by decide : (![0, 0, 2, 1, 1, 1] : V6) ⬝ᵥ (![0, 0, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![0, 0, 2, 1, 1, 1] : V6) ⬝ᵥ (![0, 0, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[1,3] * c[2,4]) (c[0,1,3] * c[2,5,4]) 0 2 0 (by decide)
      (by
        have hproof : hac = (by decide : (![1, 1, 2, 0, 0, 0] : V6) ⬝ᵥ (![0, 0, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![1, 1, 2, 0, 0, 0] : V6) ⬝ᵥ (![0, 0, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[0,2] * c[1,3]) (c[0,2] * c[1,3]) 0 4 0 (by decide)
      (by
        have hproof : hac = (by decide : (![0, 0, 1, 1, 1, 1] : V6) ⬝ᵥ (![0, 0, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![0, 0, 1, 1, 1, 1] : V6) ⬝ᵥ (![0, 0, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[0,1] * c[3,4]) (c[0,2,1] * c[3,5,4]) 0 3 0 (by decide)
      (by
        have hproof : hac = (by decide : (![0, 1, 1, 1, 2, 2] : V6) ⬝ᵥ (![0, 1, 1, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![0, 1, 1, 1, 2, 2] : V6) ⬝ᵥ (![0, 1, 1, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[3,4]) (c[0,5,2,3,4,1]) 0 1 0 (by decide)
      (by
        have hproof : hac = (by decide : (![1, 0, 0, 0, 2, 2] : V6) ⬝ᵥ (![0, 1, 1, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![1, 0, 0, 0, 2, 2] : V6) ⬝ᵥ (![0, 1, 1, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[0,1,3] * c[2,4]) (c[0,3,1] * c[2,4]) 0 2 0 (by decide)
      (by
        have hproof : hac = (by decide : (![0, 1, 1, 2, 2, 2] : V6) ⬝ᵥ (![0, 1, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![0, 1, 1, 2, 2, 2] : V6) ⬝ᵥ (![0, 1, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[2,3]) (c[0,1,4,2,5,3]) 0 1 0 (by decide)
      (by
        have hproof : hac = (by decide : (![2, 1, 1, 0, 0, 0] : V6) ⬝ᵥ (![0, 1, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![2, 1, 1, 0, 0, 0] : V6) ⬝ᵥ (![0, 1, 1, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[2,4] * c[3,5]) (c[2,4] * c[3,5]) 0 2 0 (by decide)
      (by
        have hproof : hac = (by decide : (![0, 0, 0, 0, 2, 2] : V6) ⬝ᵥ (![1, 1, 1, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![0, 0, 0, 0, 2, 2] : V6) ⬝ᵥ (![1, 1, 1, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)
  ·
    exact a6_excl_witness h hac hu (c[0,2] * c[1,3]) (c[0,2] * c[1,3]) 0 4 0 (by decide)
      (by
        have hproof : hac = (by decide : (![1, 1, 0, 0, 0, 0] : V6) ⬝ᵥ (![1, 1, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        simp only [FixesLine6]
        decide +kernel)
      (by
        have hproof : hac = (by decide : (![1, 1, 0, 0, 0, 0] : V6) ⬝ᵥ (![1, 1, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
        rw [hproof]
        decide +kernel)


private theorem a6s1_eq_of_basis {f g : V6 ≃ₗ[ZMod 3] V6} (h : ∀ i, f (e6 i) = g (e6 i)) :
    f = g := by
  apply LinearEquiv.ext
  have h' : (f : V6 →ₗ[ZMod 3] V6) = (g : V6 →ₗ[ZMod 3] V6) := by
    refine (Pi.basisFun (ZMod 3) (Fin 6)).ext fun i => ?_
    simpa [e6, Pi.basisFun_apply] using h i
  intro v
  exact congrArg (fun φ : V6 →ₗ[ZMod 3] V6 => φ v) h'

theorem a6_surv_transport {c a : V6} (hp : (c, a) ∈ a6Surv) (hac : a ⬝ᵥ c = 2) :
    ∃ (b : ZMod 3) (τ : Equiv.Perm (Fin 6)),
      phi6 b * perm6 τ * refl6 c a hac * (phi6 b * perm6 τ)⁻¹ = rB ∨
      phi6 b * perm6 τ * refl6 c a hac * (phi6 b * perm6 τ)⁻¹ = rD ∨
      phi6 b * perm6 τ * refl6 c a hac * (phi6 b * perm6 τ)⁻¹ = rS := by
  simp only [a6Surv, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    refine ⟨0, (1 : Equiv.Perm (Fin 6)), Or.inl ?_⟩
    have hproof : hac = (by decide : (![0, 0, 0, 0, 0, 2] : V6) ⬝ᵥ (![0, 0, 0, 0, 0, 1] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨0, (1 : Equiv.Perm (Fin 6)), Or.inr (Or.inr ?_)⟩
    have hproof : hac = (by decide : (![1, 1, 1, 1, 1, 2] : V6) ⬝ᵥ (![0, 0, 0, 0, 0, 1] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨0, (1 : Equiv.Perm (Fin 6)), Or.inl ?_⟩
    have hproof : hac = (by decide : (![0, 0, 0, 0, 0, 1] : V6) ⬝ᵥ (![0, 0, 0, 0, 0, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨0, (1 : Equiv.Perm (Fin 6)), Or.inr (Or.inr ?_)⟩
    have hproof : hac = (by decide : (![2, 2, 2, 2, 2, 1] : V6) ⬝ᵥ (![0, 0, 0, 0, 0, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨0, (1 : Equiv.Perm (Fin 6)), Or.inr (Or.inl ?_)⟩
    have hproof : hac = (by decide : (![0, 0, 0, 0, 1, 1] : V6) ⬝ᵥ (![0, 0, 0, 0, 1, 1] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨0, (1 : Equiv.Perm (Fin 6)), Or.inr (Or.inl ?_)⟩
    have hproof : hac = (by decide : (![0, 0, 0, 0, 2, 2] : V6) ⬝ᵥ (![0, 0, 0, 0, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨2, (c[0,4,2] * c[1,5,3]), Or.inr (Or.inl ?_)⟩
    have hproof : hac = (by decide : (![1, 1, 2, 2, 2, 2] : V6) ⬝ᵥ (![0, 0, 1, 1, 1, 1] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨2, (c[0,4,2] * c[1,5,3]), Or.inr (Or.inl ?_)⟩
    have hproof : hac = (by decide : (![2, 2, 1, 1, 1, 1] : V6) ⬝ᵥ (![0, 0, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨1, (c[0,5,4,3,2,1]), Or.inr (Or.inr ?_)⟩
    have hproof : hac = (by decide : (![0, 1, 1, 1, 1, 1] : V6) ⬝ᵥ (![0, 1, 1, 1, 1, 1] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨1, (c[0,5,4,3,2,1]), Or.inl ?_⟩
    have hproof : hac = (by decide : (![2, 1, 1, 1, 1, 1] : V6) ⬝ᵥ (![0, 1, 1, 1, 1, 1] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨1, (c[0,5,4,3,2,1]), Or.inr (Or.inr ?_)⟩
    have hproof : hac = (by decide : (![0, 2, 2, 2, 2, 2] : V6) ⬝ᵥ (![0, 2, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨1, (c[0,5,4,3,2,1]), Or.inl ?_⟩
    have hproof : hac = (by decide : (![1, 2, 2, 2, 2, 2] : V6) ⬝ᵥ (![0, 2, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨2, (1 : Equiv.Perm (Fin 6)), Or.inr (Or.inr ?_)⟩
    have hproof : hac = (by decide : (![0, 0, 0, 0, 0, 1] : V6) ⬝ᵥ (![1, 1, 1, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨2, (1 : Equiv.Perm (Fin 6)), Or.inl ?_⟩
    have hproof : hac = (by decide : (![1, 1, 1, 1, 1, 0] : V6) ⬝ᵥ (![1, 1, 1, 1, 1, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨1, (1 : Equiv.Perm (Fin 6)), Or.inr (Or.inl ?_)⟩
    have hproof : hac = (by decide : (![2, 2, 2, 2, 0, 0] : V6) ⬝ᵥ (![1, 1, 1, 1, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨1, (c[0,4,2] * c[1,5,3]), Or.inr (Or.inl ?_)⟩
    have hproof : hac = (by decide : (![0, 0, 1, 1, 1, 1] : V6) ⬝ᵥ (![1, 1, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨2, (c[0,5,4,3,2,1]), Or.inl ?_⟩
    have hproof : hac = (by decide : (![0, 2, 2, 2, 2, 2] : V6) ⬝ᵥ (![1, 2, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel
  ·
    refine ⟨2, (c[0,5,4,3,2,1]), Or.inr (Or.inr ?_)⟩
    have hproof : hac = (by decide : (![2, 0, 0, 0, 0, 0] : V6) ⬝ᵥ (![1, 2, 2, 2, 2, 2] : V6) = 2) := Subsingleton.elim _ _
    rw [hproof]
    apply a6s1_eq_of_basis
    decide +kernel


theorem a6_stage1 {A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (h : A6Hyp A M) {u : V6 ≃ₗ[ZMod 3] V6}
    (hu : u ∈ A) (huR : IsRefl6 u) (hux : MovesLine6 u) :
    ∃ (σ : Equiv.Perm (Fin 6)) (c a : V6) (hac : a ⬝ᵥ c = 2), (c, a) ∈ a6Surv ∧
      perm6 σ * u * (perm6 σ)⁻¹ = refl6 c a hac := by
  obtain ⟨c, a, hac, hu_eq⟩ := eq_refl6_of_isRefl6 huR
  have hsym : ∀ i j, a i = a j ↔ c i = c j := by
    intro i j
    by_cases hij : i = j
    · subst j; simp
    · have hswapA : perm6 (Equiv.swap i j) ∈ A := h.le (h.perm_mem (Equiv.swap i j))
      have hswap_eq : perm6 (Equiv.swap i j) =
          refl6 (e6 i - e6 j) (e6 i - e6 j) (a6_swap_dot i j hij) := a6_perm6_swap i j hij
      rw [hswap_eq] at hswapA
      have hs : refl6 c a hac ∈ A := by rw [← hu_eq]; exact hu
      have hsymm := sym_of_noTransv h.noTransv hac (a6_swap_dot i j hij) hs hswapA
      simp only [a6_dot_sub_single, a6_sub_single_dot] at hsymm
      simpa [sub_eq_zero] using hsymm
  have h1 : a ⬝ᵥ one6 ≠ 0 := a6_dot_one_ne hac hu_eq hux
  have h2 : ∀ μ : ZMod 3, c ≠ μ • one6 := a6_c_ne_smul_one hac hu_eq hux
  obtain ⟨σ, hmem⟩ := a6_pattern c a hac hsym h1 h2
  have hac' : (a ∘ σ) ⬝ᵥ (c ∘ σ) = 2 := by rw [a6_dot_comp]; exact hac
  have heq : perm6 σ⁻¹ * u * (perm6 σ⁻¹)⁻¹ = refl6 (c ∘ σ) (a ∘ σ) hac' := by
    rw [hu_eq]
    rw [perm6_conj_refl6 σ⁻¹ c a hac]
    exact refl6_proof_irrel _ _ _ _
  rcases hmem with hsurv | hexcl
  · exact ⟨σ⁻¹, c ∘ σ, a ∘ σ, hac', hsurv, heq⟩
  · exfalso
    have hσA : perm6 σ⁻¹ ∈ A := h.le (h.perm_mem σ⁻¹)
    have hmemA : perm6 σ⁻¹ * u * (perm6 σ⁻¹)⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem hσA hu) (A.inv_mem hσA)
    have hu' : refl6 (c ∘ σ) (a ∘ σ) hac' ∈ A := by
      rwa [heq] at hmemA
    exact a6_excl h hexcl hac' hu'

end CFSG.StandardType.A6

end
