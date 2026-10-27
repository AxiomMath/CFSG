module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs3
import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

private theorem w183k3_self_mul_eq_one_comm {Q : Type*} [Group Q] {X : Subgroup Q}
    (hel : ∀ x ∈ X, x * x = 1) : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  intro x hx y hy
  have hxy : (x * y) * (x * y) = 1 := hel (x * y) (X.mul_mem hx hy)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hel x hx)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hel y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxinv, hyinv]

theorem exists_three_members_quasi (h : Assumption131 G Γ VA i)
    {L₁ L₂ X₁ X₂ D₀ : Subgroup (LGL 2 V)}
    (hodd₁ : Odd (Nat.card ↥(Subgroup.center ↥L₁))) (hL₁G : L₁ ≤ G)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hX₁ : X₁ ≤ L₁) (hX₂ : X₂ ≤ L₂)
    (hX₁c : Nat.card ↥X₁ = 4) (hX₁sq : ∀ x ∈ X₁, x * x = 1) (φ : ↥X₁ ≃* ↥X₂)
    (hD₀ : D₀ ∈ Γ) (hD₀r : mRank D₀ ≤ i)
    (hD₀eq : ∀ d, d ∈ D₀ ↔ ∃ x : ↥X₁, d = (x : LGL 2 V) * (φ x : LGL 2 V))
    {n : LGL 2 V} (hn : n ∈ L₁) (hnX : ∀ x ∈ X₁, n * x * n⁻¹ ∈ X₁)
    (hfpf : ∀ x ∈ X₁, x ≠ 1 → n * x * n⁻¹ ≠ x) :
    ∃ D : Fin 3 → Subgroup (LGL 2 V), (∀ k, D k ∈ Γ) ∧ (∀ k, mRank (D k) ≤ i) ∧
      (∀ j k, j ≠ k → D j ≠ D k) ∧ (∀ j k, ∀ a ∈ D j, ∀ b ∈ D k, a * b = b * a) ∧
      X₁ ⊔ X₂ ≤ D 0 ⊔ D 1 ⊔ D 2 ∧
      (∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∃ k, s * u ∈ D k) ∧
      (∀ u ∈ X₂, u ≠ 1 → ∀ k, ∃ s ∈ X₁, s ≠ 1 ∧ s * u ∈ D k) := by
  classical
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, hXchar, hna, hnb⟩ :=
    w183_exists_klein_basis hX₁c hX₁sq hnX hfpf
  have hcommX₁ : ∀ x ∈ X₁, ∀ y ∈ X₁, x * y = y * x := w183k3_self_mul_eq_one_comm hX₁sq
  have hX₁0 : X₁ ≠ ⊥ := by
    intro hb0
    rw [hb0, Subgroup.card_bot] at hX₁c
    norm_num at hX₁c
  have hab_a : a ≠ a * b := by
    intro hh
    have h1 : a * 1 = a * b := by rw [mul_one]; exact hh
    exact hb1 (mul_left_cancel h1).symm
  have hab_b : b ≠ a * b := by
    intro hh
    have h1 : 1 * b = a * b := by rw [one_mul]; exact hh
    exact ha1 (mul_right_cancel h1).symm
  let w : ℕ → LGL 2 V → LGL 2 V := fun k x => n ^ k * x * (n ^ k)⁻¹
  have hw_succ : ∀ k x, w (k + 1) x = n * w k x * n⁻¹ := by
    intro k x; simp only [w, pow_succ]; group
  have hw_mem : ∀ k x, x ∈ X₁ → w k x ∈ X₁ := by
    intro k
    induction k with
    | zero => intro x hx; simpa [w] using hx
    | succ k ih => intro x hx; rw [hw_succ]; exact hnX _ (ih x hx)
  have hnpow_mem : ∀ k : ℕ, n ^ k ∈ L₁ := fun k => L₁.pow_mem hn k
  have hconj_phi : ∀ (k : ℕ) (x : ↥X₁),
      n ^ k * (φ x : LGL 2 V) * (n ^ k)⁻¹ = (φ x : LGL 2 V) := by
    intro k x
    have hh := hcomm (n ^ k) (hnpow_mem k) (φ x : LGL 2 V) (hX₂ (φ x).2)
    rw [hh]; group
  have hconj_phi' : ∀ (k : ℕ) (x : ↥X₁),
      (n ^ k)⁻¹ * (φ x : LGL 2 V) * n ^ k = (φ x : LGL 2 V) := by
    intro k x
    have hh := hconj_phi k x
    calc (n ^ k)⁻¹ * (φ x : LGL 2 V) * n ^ k
        = (n ^ k)⁻¹ * (n ^ k * (φ x : LGL 2 V) * (n ^ k)⁻¹) * n ^ k := by rw [hh]
      _ = (φ x : LGL 2 V) := by group
  have hphi_sq : ∀ x : ↥X₁, (φ x : LGL 2 V) * (φ x : LGL 2 V) = 1 := by
    intro x
    have h : x * x = 1 := Subtype.ext (hX₁sq (x : LGL 2 V) x.2)
    calc (φ x : LGL 2 V) * (φ x : LGL 2 V) = (φ (x * x) : LGL 2 V) := by rw [map_mul]; rfl
      _ = 1 := by rw [h, map_one]; rfl
  have hphi_comm : ∀ x y : ↥X₁,
      (φ x : LGL 2 V) * (φ y : LGL 2 V) = (φ y : LGL 2 V) * (φ x : LGL 2 V) := by
    intro x y
    have hxy : x * y = y * x :=
      Subtype.ext (hcommX₁ (x : LGL 2 V) x.2 (y : LGL 2 V) y.2)
    have h1 : (φ (x * y) : LGL 2 V) = (φ x : LGL 2 V) * (φ y : LGL 2 V) := by
      rw [map_mul]; rfl
    have h2 : (φ (y * x) : LGL 2 V) = (φ y : LGL 2 V) * (φ x : LGL 2 V) := by
      rw [map_mul]; rfl
    rw [← h1, ← h2, hxy]
  have hbb : b * b = 1 := hX₁sq b hb
  have haa : a * a = 1 := hX₁sq a ha
  have habc : a * b = b * a := hcommX₁ a ha b hb
  have hba : b * (a * b) = a := by rw [habc, ← mul_assoc, hbb, one_mul]
  have haba : (a * b) * a = b := by rw [mul_assoc, ← habc, ← mul_assoc, haa, one_mul]
  have hr1ab : n * (a * b) * n⁻¹ = a := by
    rw [show n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) by group, hna, hnb, hba]
  have hr2a : n ^ 2 * a * (n ^ 2)⁻¹ = a * b := by
    have e : n ^ 2 * a * (n ^ 2)⁻¹ = n * (n * a * n⁻¹) * n⁻¹ := by
      simp only [pow_two]
      group
    rw [e, hna, hnb]
  have hr2b : n ^ 2 * b * (n ^ 2)⁻¹ = a := by
    have e : n ^ 2 * b * (n ^ 2)⁻¹ = n * (n * b * n⁻¹) * n⁻¹ := by
      simp only [pow_two]
      group
    rw [e, hnb, hr1ab]
  have hr2ab : n ^ 2 * (a * b) * (n ^ 2)⁻¹ = b := by
    have e : n ^ 2 * (a * b) * (n ^ 2)⁻¹ = n * (n * (a * b) * n⁻¹) * n⁻¹ := by
      simp only [pow_two]
      group
    rw [e, hr1ab, hna]
  have hw0 : ∀ x : LGL 2 V, w 0 x = x := by intro x; simp [w]
  have hw1a : w 1 a = b := by
    change n ^ 1 * a * (n ^ 1)⁻¹ = b
    rw [pow_one]; exact hna
  have hw1b : w 1 b = a * b := by
    change n ^ 1 * b * (n ^ 1)⁻¹ = a * b
    rw [pow_one]; exact hnb
  have hw1ab : w 1 (a * b) = a := by
    change n ^ 1 * (a * b) * (n ^ 1)⁻¹ = a
    rw [pow_one]; exact hr1ab
  have hw2a : w 2 a = a * b := by
    change n ^ 2 * a * (n ^ 2)⁻¹ = a * b
    exact hr2a
  have hw2b : w 2 b = a := by
    change n ^ 2 * b * (n ^ 2)⁻¹ = a
    exact hr2b
  have hw2ab : w 2 (a * b) = b := by
    change n ^ 2 * (a * b) * (n ^ 2)⁻¹ = b
    exact hr2ab
  have hne_ba : b ≠ a := hab.symm
  have hne_aba : a * b ≠ a := hab_a.symm
  have hne_abb : a * b ≠ b := hab_b.symm
  have hw_inj : ∀ x ∈ X₁, x ≠ 1 → ∀ j k : Fin 3, j ≠ k → w (j : ℕ) x ≠ w (k : ℕ) x := by
    intro x hx hx1 j k hjk
    rcases (hXchar x).mp hx with hx' | hx' | hx' | hx'
    · exact absurd hx' hx1
    · rw [hx']
      fin_cases j <;> fin_cases k <;>
        simp only [hw0, hw1a, hw2a] <;>
        first
          | exact absurd rfl hjk
          | exact hab
          | exact hab.symm
          | exact hab_a
          | exact hab_a.symm
          | exact hab_b
          | exact hab_b.symm
    · rw [hx']
      fin_cases j <;> fin_cases k <;>
        simp only [hw0, hw1b, hw2b] <;>
        first
          | exact absurd rfl hjk
          | exact hab
          | exact hab.symm
          | exact hab_a
          | exact hab_a.symm
          | exact hab_b
          | exact hab_b.symm
    · rw [hx']
      fin_cases j <;> fin_cases k <;>
        simp only [hw0, hw1ab, hw2ab] <;>
        first
          | exact absurd rfl hjk
          | exact hab
          | exact hab.symm
          | exact hab_a
          | exact hab_a.symm
          | exact hab_b
          | exact hab_b.symm
  have hw_surj : ∀ x ∈ X₁, x ≠ 1 → ∀ s ∈ X₁, s ≠ 1 → ∃ k : Fin 3, w (k : ℕ) x = s := by
    intro x hx hx1 s hs hs1
    rcases (hXchar x).mp hx with hx' | hx' | hx' | hx'
    · exact absurd hx' hx1
    · rw [hx']
      rcases (hXchar s).mp hs with hs' | hs' | hs' | hs'
      · exact absurd hs' hs1
      · exact ⟨0, by rw [hs']; exact hw0 a⟩
      · exact ⟨1, by rw [hs']; exact hw1a⟩
      · exact ⟨2, by rw [hs']; exact hw2a⟩
    · rw [hx']
      rcases (hXchar s).mp hs with hs' | hs' | hs' | hs'
      · exact absurd hs' hs1
      · exact ⟨2, by rw [hs']; exact hw2b⟩
      · exact ⟨0, by rw [hs']; exact hw0 b⟩
      · exact ⟨1, by rw [hs']; exact hw1b⟩
    · rw [hx']
      rcases (hXchar s).mp hs with hs' | hs' | hs' | hs'
      · exact absurd hs' hs1
      · exact ⟨1, by rw [hs']; exact hw1ab⟩
      · exact ⟨2, by rw [hs']; exact hw2ab⟩
      · exact ⟨0, by rw [hs']; exact hw0 (a * b)⟩
  let D : Fin 3 → Subgroup (LGL 2 V) := fun k => cj (n ^ (k : ℕ)) D₀
  have mem_D : ∀ (k : Fin 3) (d : LGL 2 V),
      d ∈ D k ↔ ∃ x : ↥X₁, d = w (k : ℕ) (x : LGL 2 V) * (φ x : LGL 2 V) := by
    intro k d
    constructor
    · intro hd
      have hd0 : (n ^ (k : ℕ))⁻¹ * d * n ^ (k : ℕ) ∈ D₀ :=
        mem_cj.mp (show d ∈ cj (n ^ (k : ℕ)) D₀ from hd)
      obtain ⟨x, hx⟩ := (hD₀eq _).mp hd0
      refine ⟨x, ?_⟩
      have hd' : d = n ^ (k : ℕ) * ((x : LGL 2 V) * (φ x : LGL 2 V)) * (n ^ (k : ℕ))⁻¹ := by
        rw [← hx]; group
      rw [hd']
      change n ^ (k : ℕ) * ((x : LGL 2 V) * (φ x : LGL 2 V)) * (n ^ (k : ℕ))⁻¹
        = n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹ * (φ x : LGL 2 V)
      rw [show n ^ (k : ℕ) * ((x : LGL 2 V) * (φ x : LGL 2 V)) * (n ^ (k : ℕ))⁻¹
          = (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹)
            * (n ^ (k : ℕ) * (φ x : LGL 2 V) * (n ^ (k : ℕ))⁻¹) by group,
        hconj_phi k x]
    · rintro ⟨x, rfl⟩
      show w (k : ℕ) (x : LGL 2 V) * (φ x : LGL 2 V) ∈ cj (n ^ (k : ℕ)) D₀
      rw [mem_cj, hD₀eq]
      refine ⟨x, ?_⟩
      change (n ^ (k : ℕ))⁻¹ * (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹
          * (φ x : LGL 2 V)) * n ^ (k : ℕ) = (x : LGL 2 V) * (φ x : LGL 2 V)
      rw [show (n ^ (k : ℕ))⁻¹ * (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹
            * (φ x : LGL 2 V)) * n ^ (k : ℕ)
          = (x : LGL 2 V) * ((n ^ (k : ℕ))⁻¹ * (φ x : LGL 2 V) * n ^ (k : ℕ)) by group,
        hconj_phi' k x]
  have hDΓ : ∀ k, D k ∈ Γ := by
    intro k
    exact h.invariant D₀ hD₀ (n ^ (k : ℕ)) (hL₁G (hnpow_mem _))
  have hDr : ∀ k, mRank (D k) ≤ i := by
    intro k
    show mRank (cj (n ^ (k : ℕ)) D₀) ≤ i
    unfold mRank
    rw [card_cj]
    exact hD₀r
  have hDne : ∀ j k, j ≠ k → D j ≠ D k := by
    intro j k hjk hEq
    obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁0
    let x₀' : ↥X₁ := ⟨x₀, hx₀⟩
    have hx₀1' : (x₀' : LGL 2 V) ≠ 1 := fun hh => hx₀1 (Subtype.ext hh)
    have hdj : w (j : ℕ) (x₀' : LGL 2 V) * (φ x₀' : LGL 2 V) ∈ D j :=
      (mem_D j _).mpr ⟨x₀', rfl⟩
    have hdk : w (j : ℕ) (x₀' : LGL 2 V) * (φ x₀' : LGL 2 V) ∈ D k := hEq ▸ hdj
    obtain ⟨y, hy⟩ := (mem_D k _).mp hdk
    have hL₁ : w (j : ℕ) (x₀' : LGL 2 V) ∈ L₁ := hX₁ (hw_mem (j : ℕ) _ x₀'.2)
    have hL₂ : (φ x₀' : LGL 2 V) ∈ L₂ := hX₂ (φ x₀').2
    have hyL₁ : w (k : ℕ) (y : LGL 2 V) ∈ L₁ := hX₁ (hw_mem (k : ℕ) _ y.2)
    have hyL₂ : (φ y : LGL 2 V) ∈ L₂ := hX₂ (φ y).2
    have huy : w (k : ℕ) (y : LGL 2 V)
        = w (j : ℕ) (x₀' : LGL 2 V) * (φ x₀' : LGL 2 V) * (φ y : LGL 2 V)⁻¹ := by
      rw [hy]; group
    have h2 : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V)
        = (φ y : LGL 2 V) * (φ x₀' : LGL 2 V)⁻¹ := by
      rw [huy]; group
    have heL₁ : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V) ∈ L₁ :=
      L₁.mul_mem (L₁.inv_mem hyL₁) hL₁
    have heL₂ : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V) ∈ L₂ := by
      rw [h2]; exact L₂.mul_mem hyL₂ (L₂.inv_mem hL₂)
    have heX : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V) ∈ X₁ :=
      X₁.mul_mem (X₁.inv_mem (hw_mem (k : ℕ) _ y.2)) (hw_mem (j : ℕ) _ x₀'.2)
    have heZ : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V)
        ∈ W183K3.quasiCentre L₁ := by
      rw [W183K3.mem_quasiCentre]
      exact ⟨heL₁, fun l hl => (hcomm l hl _ heL₂).symm⟩
    have he1 : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V) = 1 :=
      W183K3.quasi_centre_two_pow_eq_one hodd₁ heZ (k := 1) (by
        show ((w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V)) ^ 2 = 1
        rw [pow_two]; exact hX₁sq _ heX)
    have heq : w (j : ℕ) (x₀' : LGL 2 V) = w (k : ℕ) (y : LGL 2 V) :=
      (inv_mul_eq_one.mp he1).symm
    have hphi_eq : (φ x₀' : LGL 2 V) = (φ y : LGL 2 V) := by
      rw [heq] at hy
      exact mul_left_cancel hy
    have hxy : x₀' = y := φ.injective (Subtype.ext hphi_eq)
    have heq' : w (j : ℕ) (x₀' : LGL 2 V) = w (k : ℕ) (x₀' : LGL 2 V) := by
      have h1 : w (k : ℕ) (x₀' : LGL 2 V) = w (k : ℕ) (y : LGL 2 V) := by rw [hxy]
      rw [h1]; exact heq
    exact hw_inj (x₀' : LGL 2 V) x₀'.2 hx₀1' j k hjk heq'
  have hDcomm : ∀ j k, ∀ a ∈ D j, ∀ b ∈ D k, a * b = b * a := by
    intro j k a ha b hb
    obtain ⟨x, rfl⟩ := (mem_D j a).mp ha
    obtain ⟨y, rfl⟩ := (mem_D k b).mp hb
    have hux : w (j : ℕ) (x : LGL 2 V) ∈ X₁ := hw_mem (j : ℕ) _ x.2
    have huy : w (k : ℕ) (y : LGL 2 V) ∈ X₁ := hw_mem (k : ℕ) _ y.2
    have hAC : Commute (w (j : ℕ) (x : LGL 2 V)) (w (k : ℕ) (y : LGL 2 V)) :=
      hcommX₁ _ hux _ huy
    have hAD : Commute (w (j : ℕ) (x : LGL 2 V)) (φ y : LGL 2 V) :=
      hcomm _ (hX₁ hux) _ (hX₂ (φ y).2)
    have hCB : Commute (w (k : ℕ) (y : LGL 2 V)) (φ x : LGL 2 V) :=
      hcomm _ (hX₁ huy) _ (hX₂ (φ x).2)
    have hBD : Commute (φ x : LGL 2 V) (φ y : LGL 2 V) := hphi_comm x y
    exact Commute.mul_left (Commute.mul_right hAC hAD) (Commute.mul_right hCB.symm hBD)
  have hmemD0 : ∀ y : ↥X₁, (y : LGL 2 V) * (φ y : LGL 2 V) ∈ D 0 := by
    intro y
    refine (mem_D 0 _).mpr ⟨y, ?_⟩
    show (y : LGL 2 V) * (φ y : LGL 2 V) = w 0 (y : LGL 2 V) * (φ y : LGL 2 V)
    rw [hw0]
  have hmemD1 : ∀ y : ↥X₁, w 1 (y : LGL 2 V) * (φ y : LGL 2 V) ∈ D 1 :=
    fun y => (mem_D 1 _).mpr ⟨y, rfl⟩
  have hkey : ∀ y : ↥X₁,
      ((y : LGL 2 V) * (φ y : LGL 2 V)) * (w 1 (y : LGL 2 V) * (φ y : LGL 2 V))
        = (y : LGL 2 V) * w 1 (y : LGL 2 V) := by
    intro y
    have hc : w 1 (y : LGL 2 V) * (φ y : LGL 2 V) = (φ y : LGL 2 V) * w 1 (y : LGL 2 V) :=
      hcomm _ (hX₁ (hw_mem 1 _ y.2)) _ (hX₂ (φ y).2)
    have hpsq := hphi_sq y
    calc ((y : LGL 2 V) * (φ y : LGL 2 V)) * (w 1 (y : LGL 2 V) * (φ y : LGL 2 V))
        = (y : LGL 2 V) * ((φ y : LGL 2 V) * w 1 (y : LGL 2 V)) * (φ y : LGL 2 V) := by
          group
      _ = (y : LGL 2 V) * (w 1 (y : LGL 2 V) * (φ y : LGL 2 V)) * (φ y : LGL 2 V) := by
          rw [← hc]
      _ = (y : LGL 2 V) * w 1 (y : LGL 2 V) * ((φ y : LGL 2 V) * (φ y : LGL 2 V)) := by
          group
      _ = (y : LGL 2 V) * w 1 (y : LGL 2 V) := by rw [hpsq, mul_one]
  have hmem_a : a ∈ D 0 ⊔ D 1 ⊔ D 2 := by
    have hprod : ((⟨b, hb⟩ : ↥X₁) : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)
        * (w 1 (b : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)) ∈ D 0 ⊔ D 1 :=
      (D 0 ⊔ D 1).mul_mem (Subgroup.mem_sup_left (hmemD0 ⟨b, hb⟩))
        (Subgroup.mem_sup_right (hmemD1 ⟨b, hb⟩))
    have heq : ((⟨b, hb⟩ : ↥X₁) : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)
        * (w 1 (b : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)) = a := by
      rw [hkey ⟨b, hb⟩]
      show b * w 1 b = a
      rw [hw1b, hba]
    rw [← heq]
    exact Subgroup.mem_sup_left hprod
  have hmem_b : b ∈ D 0 ⊔ D 1 ⊔ D 2 := by
    have hprod : ((⟨a * b, X₁.mul_mem ha hb⟩ : ↥X₁) : LGL 2 V)
          * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)
        * (w 1 (a * b) * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)) ∈ D 0 ⊔ D 1 :=
      (D 0 ⊔ D 1).mul_mem (Subgroup.mem_sup_left (hmemD0 ⟨a * b, X₁.mul_mem ha hb⟩))
        (Subgroup.mem_sup_right (hmemD1 ⟨a * b, X₁.mul_mem ha hb⟩))
    have heq : ((⟨a * b, X₁.mul_mem ha hb⟩ : ↥X₁) : LGL 2 V)
          * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)
        * (w 1 (a * b) * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)) = b := by
      rw [hkey ⟨a * b, X₁.mul_mem ha hb⟩]
      show (a * b) * w 1 (a * b) = b
      rw [hw1ab, haba]
    rw [← heq]
    exact Subgroup.mem_sup_left hprod
  have hmem_ab : a * b ∈ D 0 ⊔ D 1 ⊔ D 2 := by
    have hprod : ((⟨a, ha⟩ : ↥X₁) : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)
        * (w 1 (a : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)) ∈ D 0 ⊔ D 1 :=
      (D 0 ⊔ D 1).mul_mem (Subgroup.mem_sup_left (hmemD0 ⟨a, ha⟩))
        (Subgroup.mem_sup_right (hmemD1 ⟨a, ha⟩))
    have heq : ((⟨a, ha⟩ : ↥X₁) : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)
        * (w 1 (a : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)) = a * b := by
      rw [hkey ⟨a, ha⟩]
      show a * w 1 a = a * b
      rw [hw1a]
    rw [← heq]
    exact Subgroup.mem_sup_left hprod
  have hX₁_le : X₁ ≤ D 0 ⊔ D 1 ⊔ D 2 := by
    intro y hy
    rcases (hXchar y).mp hy with h1 | h1 | h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact hmem_a
    · rw [h1]; exact hmem_b
    · rw [h1]; exact hmem_ab
  have hX₂_le : X₂ ≤ D 0 ⊔ D 1 ⊔ D 2 := by
    intro z hz
    obtain ⟨x, hx⟩ := φ.surjective ⟨z, hz⟩
    have hzx : z = (φ x : LGL 2 V) := congrArg Subtype.val hx.symm
    rw [hzx]
    have hxD : (x : LGL 2 V) ∈ D 0 ⊔ D 1 ⊔ D 2 := hX₁_le x.2
    have hxD0 : (x : LGL 2 V) * (φ x : LGL 2 V) ∈ D 0 ⊔ D 1 ⊔ D 2 :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left (hmemD0 x))
    have hxinv : (x : LGL 2 V)⁻¹ * ((x : LGL 2 V) * (φ x : LGL 2 V)) = (φ x : LGL 2 V) := by
      group
    rw [← hxinv]
    exact (D 0 ⊔ D 1 ⊔ D 2).mul_mem ((D 0 ⊔ D 1 ⊔ D 2).inv_mem hxD) hxD0
  have hgen : X₁ ⊔ X₂ ≤ D 0 ⊔ D 1 ⊔ D 2 := sup_le hX₁_le hX₂_le
  have hcover : ∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∃ k, s * u ∈ D k := by
    intro s hs hs1 u hu hu1
    obtain ⟨x, hx⟩ := φ.surjective ⟨u, hu⟩
    have hux : u = (φ x : LGL 2 V) := congrArg Subtype.val hx.symm
    rw [hux] at hu1 ⊢
    have hx1 : (x : LGL 2 V) ≠ 1 := by
      intro h1
      apply hu1
      have hx1' : x = 1 := Subtype.ext h1
      rw [hx1', map_one]; rfl
    obtain ⟨k, hk⟩ := hw_surj (x : LGL 2 V) x.2 hx1 s hs hs1
    exact ⟨k, (mem_D k _).mpr ⟨x, by rw [← hk]⟩⟩
  have hcover' : ∀ u ∈ X₂, u ≠ 1 → ∀ k, ∃ s ∈ X₁, s ≠ 1 ∧ s * u ∈ D k := by
    intro u hu hu1 k
    obtain ⟨x, hx⟩ := φ.surjective ⟨u, hu⟩
    have hux : u = (φ x : LGL 2 V) := congrArg Subtype.val hx.symm
    rw [hux] at hu1 ⊢
    have hx1 : (x : LGL 2 V) ≠ 1 := by
      intro h1
      apply hu1
      have hx1' : x = 1 := Subtype.ext h1
      rw [hx1', map_one]; rfl
    have hwne : w (k : ℕ) (x : LGL 2 V) ≠ 1 := by
      intro h1
      apply hx1
      have h2 : (x : LGL 2 V)
          = (n ^ (k : ℕ))⁻¹ * w (k : ℕ) (x : LGL 2 V) * n ^ (k : ℕ) := by
        show (x : LGL 2 V)
          = (n ^ (k : ℕ))⁻¹ * (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹) * n ^ (k : ℕ)
        group
      rw [h2, h1]; group
    exact ⟨w (k : ℕ) (x : LGL 2 V), hw_mem (k : ℕ) _ x.2, hwne,
      (mem_D k _).mpr ⟨x, rfl⟩⟩
  exact ⟨D, hDΓ, hDr, hDne, hDcomm, hgen, hcover, hcover'⟩

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
