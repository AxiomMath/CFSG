module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF.QuadExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG.RankThree.PartOne.KFQ

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def sact (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (x : Fin 3 → (Qext K)ˣ) :
    Fin 3 → (Qext K)ˣ :=
  fun j => if ε (π.symm j) then (x (π.symm j))⁻¹ else x (π.symm j)

theorem sact_apply (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (x : Fin 3 → (Qext K)ˣ) (j : Fin 3) :
    sact π ε x j = if ε (π.symm j) then (x (π.symm j))⁻¹ else x (π.symm j) := rfl

@[expose] noncomputable def phiv (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (x : Fin 3 → (Qext K)ˣ) :
    Fin 3 → (Qext K)ˣ := sact π ε x * x⁻¹

@[expose] noncomputable def evec (ζ : (Qext K)ˣ) (i : Fin 3) : Fin 3 → (Qext K)ˣ :=
  fun j => if j = i then ζ else 1

theorem sact_evec (ζ : (Qext K)ˣ) (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (i j : Fin 3) :
    sact π ε (evec ζ i) j =
      if π.symm j = i then (if ε i then ζ⁻¹ else ζ) else 1 := by
  by_cases h : π.symm j = i
  · subst h
    simp [sact_apply, evec]
  · simp [sact_apply, evec, h]

theorem evec_pow (ζ : (Qext K)ˣ) {p : ℕ} (hζ : ζ ^ p = 1) (i j : Fin 3) : evec ζ i j ^ p = 1 := by
  by_cases h : j = i
  · simp [evec, h, hζ]
  · simp [evec, h]

theorem zeta_pow_eq_one_iff {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ζ ^ m = 1 ↔ p ∣ m := hζ.pow_eq_one_iff_dvd m

theorem zeta_ne_one {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p) : ζ ≠ 1 := by
  intro h
  have := (zeta_pow_eq_one_iff hζ 1).mp (by rw [h, one_pow])
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem zeta_sq_ne_one {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p) :
    ζ⁻¹ * ζ⁻¹ ≠ 1 := by
  intro h
  have h2 : ζ ^ 2 = 1 := by
    have : ζ * ζ = 1 := by
      have h' := congrArg (fun u => u⁻¹) h
      simpa [mul_inv_rev] using h'
    simpa [sq] using this
  have := (zeta_pow_eq_one_iff hζ 2).mp h2
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem zeta_inv_ne_one {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p) : ζ⁻¹ ≠ 1 := by
  intro h
  exact zeta_ne_one hζ h5 (by simpa using congrArg (fun u => u⁻¹) h)

theorem zeta_ne_inv {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p) : ζ ≠ ζ⁻¹ := by
  intro h
  apply zeta_sq_ne_one hζ h5
  have : ζ⁻¹ * ζ⁻¹ = ζ⁻¹ * ζ := by rw [← h]
  rw [this, inv_mul_cancel]

@[expose] def ReflShape (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : Prop :=
  (π = 1 ∧ ∃ i, ε i = true ∧ ∀ j, j ≠ i → ε j = false) ∨
    (∃ a b c : Fin 3, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ π = Equiv.swap a b ∧ ε a = ε b ∧ ε c = false)

theorem perm_sq_eq_one : ∀ π : Equiv.Perm (Fin 3), (∀ i, π (π i) = i) →
    π = 1 ∨ ∃ a b : Fin 3, a ≠ b ∧ π = Equiv.swap a b := by decide +kernel

theorem exists_third : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide +kernel

theorem classify {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool} {ζ : (Qext K)ˣ}
    (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p)
    (hinv : ∀ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) → sact π ε (sact π ε x) = x)
    (hne : ∃ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) ∧ sact π ε x ≠ x)
    (hprop : ∀ x x' : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) → (∀ i, x' i ^ p = 1) →
      phiv π ε x ≠ 1 → ∃ k : ℕ, phiv π ε x' = (phiv π ε x) ^ k) :
    ReflShape π ε := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hev : ∀ i j, evec ζ i j ^ p = 1 := evec_pow ζ hζp
  have hz1 : ∀ b : Bool, (if b then ζ⁻¹ else ζ) ≠ 1 := by
    intro b
    cases b <;> simp [zeta_ne_one hζ h5, zeta_inv_ne_one hζ h5]
  have hz2 : ∀ (u : (Qext K)ˣ), u ≠ 1 → ∀ b : Bool, (if b then u⁻¹ else u) ≠ 1 := by
    intro u hu b
    cases b <;> simp [hu]
  have hζ2 : ζ⁻¹ * ζ⁻¹ ≠ 1 := zeta_sq_ne_one hζ h5
  have hπ2 : ∀ i, π (π i) = i := by
    intro i
    by_contra hne2
    have h1 := congrFun (hinv (evec ζ i) (hev i)) (π (π i))
    rw [sact_apply, Equiv.symm_apply_apply, sact_evec, Equiv.symm_apply_apply] at h1
    have hζ1 := zeta_ne_one hζ h5
    rcases Bool.eq_false_or_eq_true (ε i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (ε (π i)) with h' | h' <;>
      simp [h, h', evec, hne2, hζ1] at h1
  rcases perm_sq_eq_one π hπ2 with rfl | ⟨a, b, hab, rfl⟩
  ·
    left
    refine ⟨rfl, ?_⟩
    have hA : ∀ (x : Fin 3 → (Qext K)ˣ) (j : Fin 3), sact 1 ε x j = if ε j then (x j)⁻¹ else x j :=
      fun x j => rfl
    have hex : ∃ i, ε i = true := by
      by_contra hall
      push Not at hall
      obtain ⟨x, -, hx⟩ := hne
      apply hx
      funext j
      rw [hA]
      have : ε j = false := by simpa using hall j
      simp [this]
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, hi, fun j hj => ?_⟩
    by_contra hεj
    have hεj' : ε j = true := by simpa using hεj
    have hφi : phiv 1 ε (evec ζ i) ≠ 1 := by
      intro h
      have := congrFun h i
      simp only [phiv, Pi.mul_apply, Pi.inv_apply, Pi.one_apply, hA, evec, hi, ite_true] at this
      apply hζ2
      simpa using this
    obtain ⟨k, hk⟩ := hprop (evec ζ i) (evec ζ j) (hev i) (hev j) hφi
    have := congrFun hk j
    simp only [phiv, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, hA, evec, hεj', ite_true] at this
    simp only [hj, ite_false, inv_one, mul_one, one_pow] at this
    exact hζ2 (by simpa using this)
  ·
    right
    obtain ⟨c, hca, hcb⟩ := exists_third a b hab
    have hba : b ≠ a := hab.symm
    have hsa : ∀ (x : Fin 3 → (Qext K)ˣ) (j : Fin 3), sact (Equiv.swap a b) ε x j =
        if ε (Equiv.swap a b j) then (x (Equiv.swap a b j))⁻¹ else x (Equiv.swap a b j) := by
      intro x j
      rw [sact_apply, Equiv.symm_swap]
    have hζne : ζ⁻¹ ≠ ζ := (zeta_ne_inv hζ h5).symm
    refine ⟨a, b, c, hab, hca, hcb, rfl, ?_, ?_⟩
    ·
      have h1 := congrFun (hinv (evec ζ a) (hev a)) a
      simp only [hsa, Equiv.swap_apply_left, Equiv.swap_apply_right, evec, ite_true] at h1
      rcases Bool.eq_false_or_eq_true (ε a) with h | h <;>
        rcases Bool.eq_false_or_eq_true (ε b) with h' | h' <;>
        simp [h, h', hζne] at h1 ⊢
    ·
      by_contra hεc
      have hεc' : ε c = true := by simpa using hεc
      have hφa : phiv (Equiv.swap a b) ε (evec ζ a) ≠ 1 := by
        intro h
        have := congrFun h b
        simp only [phiv, Pi.mul_apply, Pi.inv_apply, Pi.one_apply, hsa, Equiv.swap_apply_right,
          evec, ite_true, hba, ite_false, inv_one, mul_one] at this
        exact hz1 (ε a) this
      obtain ⟨k, hk⟩ := hprop (evec ζ a) (evec ζ c) (hev a) (hev c) hφa
      have := congrFun hk c
      simp only [phiv, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, hsa,
        Equiv.swap_apply_of_ne_of_ne hca hcb, evec, ite_true, hca, ite_false, inv_one, mul_one,
        one_pow, hεc'] at this
      exact hζ2 this

end CFSG.RankThree.PartOne.S13K
