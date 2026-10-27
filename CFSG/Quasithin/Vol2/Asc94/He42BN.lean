module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaGen1
public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace CFSG.Quasithin.A94.He42BN

open CFSG.Quasithin.H13.F431.U42Aut

variable {Δ : Type*} [Group Δ]

private theorem he42bn_lmul_rankOne {K P : Subgroup Δ} {r : Δ} {U : List Δ} {X : Δ → Prop}
    (hr : RankOne K P r U) (hr' : ∀ x, X x → X (r * x)) (hK : ∀ b ∈ K, ∀ x, X x → X (b * x))
    {p : Δ} (hp : p ∈ P) {x : Δ} (hx : X x) : X (p * x) := by
  rcases hr.cos p hp with hpK | ⟨v, hv, b, hb, hvb⟩
  · exact hK p hpK x hx
  · have hp_eq : p = v⁻¹ * (r * b) := by
      rw [← hvb]
      group
    have key : p * x = v⁻¹ * (r * (b * x)) := by
      rw [hp_eq]
      simp only [mul_assoc]
    rw [key]
    exact hK _ (K.inv_mem (hr.U_mem v hv)) _ (hr' _ (hK _ hb _ hx))

theorem mem_mul_of_bnpair {K P₁ P₂ : Subgroup Δ} {s t : Δ} {us ut : List Δ}
    (hBN : BNPairGen K P₁ P₂ s t us ut 3) :
    ∀ g ∈ P₁ ⊔ P₂, ∃ h ∈ P₁, ∃ m ∈ P₂, ∃ h' ∈ P₁, g = h * m * h' := by
  have hK : ∀ b ∈ K, ∀ x, InCellsGen K s t 3 x → InCellsGen K s t 3 (b * x) :=
    fun b hb x hx => InCellsGen.lmul hb hx
  have hs : ∀ x, InCellsGen K s t 3 x → InCellsGen K s t 3 (s * x) :=
    fun x hx => hBN.mul_s hx
  have ht : ∀ x, InCellsGen K s t 3 x → InCellsGen K s t 3 (t * x) :=
    fun x hx => hBN.mul_t hx
  have hP₁ : ∀ p ∈ P₁, ∀ x, InCellsGen K s t 3 x → InCellsGen K s t 3 (p * x) :=
    fun p hp x hx => he42bn_lmul_rankOne (X := InCellsGen K s t 3) hBN.r1 hs hK hp hx
  have hP₂ : ∀ p ∈ P₂, ∀ x, InCellsGen K s t 3 x → InCellsGen K s t 3 (p * x) :=
    fun p hp x hx => he42bn_lmul_rankOne (X := InCellsGen K s t 3) hBN.r2 ht hK hp hx
  let Q : Subgroup Δ :=
    { carrier := {g | ∀ x, InCellsGen K s t 3 x →
        InCellsGen K s t 3 (g * x) ∧ InCellsGen K s t 3 (g⁻¹ * x)}
      one_mem' := by
        intro x hx
        rw [one_mul, inv_one, one_mul]
        exact ⟨hx, hx⟩
      mul_mem' := by
        intro a b ha hb x hx
        constructor
        · rw [mul_assoc]
          exact (ha _ (hb x hx).1).1
        · rw [mul_inv_rev, mul_assoc]
          exact (hb _ (ha x hx).2).2
      inv_mem' := by
        intro a ha x hx
        rw [inv_inv]
        exact ⟨(ha x hx).2, (ha x hx).1⟩ }
  have hQ : ∀ g, g ∈ Q ↔ ∀ x, InCellsGen K s t 3 x →
      InCellsGen K s t 3 (g * x) ∧ InCellsGen K s t 3 (g⁻¹ * x) := fun g => Iff.rfl
  have hle : P₁ ⊔ P₂ ≤ Q := by
    refine sup_le ?_ ?_
    · intro p hp
      exact (hQ p).2 fun x hx => ⟨hP₁ p hp x hx, hP₁ p⁻¹ (P₁.inv_mem hp) x hx⟩
    · intro p hp
      exact (hQ p).2 fun x hx => ⟨hP₂ p hp x hx, hP₂ p⁻¹ (P₂.inv_mem hp) x hx⟩
  have hword : ∀ k : ℕ, k ≤ 3 →
      (∃ h ∈ P₁, ∃ m ∈ P₂, ∃ h' ∈ P₁, altW s t k = h * m * h') ∧
      (∃ h ∈ P₁, ∃ m ∈ P₂, ∃ h' ∈ P₁, altW t s k = h * m * h') := by
    intro k hk
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact ⟨⟨1, P₁.one_mem, 1, P₂.one_mem, 1, P₁.one_mem, by simp [altW]⟩,
        ⟨1, P₁.one_mem, 1, P₂.one_mem, 1, P₁.one_mem, by simp [altW]⟩⟩
    · exact ⟨⟨s, hBN.r1.mem, 1, P₂.one_mem, 1, P₁.one_mem, by simp [altW]⟩,
        ⟨1, P₁.one_mem, t, hBN.r2.mem, 1, P₁.one_mem, by simp [altW]⟩⟩
    · exact ⟨⟨s, hBN.r1.mem, t, hBN.r2.mem, 1, P₁.one_mem, by simp [altW]⟩,
        ⟨1, P₁.one_mem, t, hBN.r2.mem, s, hBN.r1.mem, by simp [altW]⟩⟩
    · exact ⟨⟨s, hBN.r1.mem, t, hBN.r2.mem, s, hBN.r1.mem, by simp [altW, mul_assoc]⟩,
        ⟨s, hBN.r1.mem, t, hBN.r2.mem, s, hBN.r1.mem, by
          rw [← hBN.braid]
          simp [altW, mul_assoc]⟩⟩
  have hfin : ∀ w, (∃ h ∈ P₁, ∃ m ∈ P₂, ∃ h' ∈ P₁, w = h * m * h') →
      ∀ b₁ ∈ K, ∀ b₂ ∈ K, ∃ h ∈ P₁, ∃ m ∈ P₂, ∃ h' ∈ P₁, b₁ * w * b₂ = h * m * h' := by
    rintro w ⟨h, hh, m, hm, h', hh', rfl⟩ b₁ hb₁ b₂ hb₂
    exact ⟨b₁ * h, P₁.mul_mem (hBN.r1.le hb₁) hh, m, hm, h' * b₂,
      P₁.mul_mem hh' (hBN.r1.le hb₂), by simp only [mul_assoc]⟩
  intro g hg
  have hgQ := (hQ g).1 (hle hg)
  have hX1 : InCellsGen K s t 3 g := by
    have h1 := (hgQ 1 (inCellsGen_one K s t 3)).1
    rwa [mul_one] at h1
  obtain ⟨k, hk, hcell | hcell⟩ := hX1
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hcell
    exact hfin _ (hword k hk).1 b₁ hb₁ b₂ hb₂
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hcell
    exact hfin _ (hword k hk).2 b₁ hb₁ b₂ hb₂

end CFSG.Quasithin.A94.He42BN
