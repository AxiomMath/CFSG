module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.IndepRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CoxeterSystem
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} {D : CurtisDatum G cs p}
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  {X : Type*} [MulAction W X]

private theorem smul_eq_of_inv_mul_smul_eq_self {a b : W} {v : X}
    (h : (a⁻¹ * b) • v = v) : b • v = a • v := by
  calc b • v = (a * (a⁻¹ * b)) • v := by rw [mul_inv_cancel_left]
    _ = a • (a⁻¹ * b) • v := by rw [mul_smul]
    _ = a • v := by rw [h]

theorem wordProd_smul_eq_self {v : X} {ω : List B} (h : ∀ s ∈ ω, cs.simple s • v = v) :
    cs.wordProd ω • v = v := by
  induction ω with
  | nil => rw [cs.wordProd_nil, one_smul]
  | cons s ω ih =>
      have hs : cs.simple s • v = v := h s (by simp)
      have hω : ∀ t ∈ ω, cs.simple t • v = v := fun t ht => h t (by simp [ht])
      rw [cs.wordProd_cons, mul_smul, ih hω, hs]

variable [Finite G]

theorem exists_mem_mu_eq_dScalar_of_smul_ne {χ : G → k} {μ : B → k} {v : X}
    (hv : ∀ s, μ s ≠ D.dScalar χ s → cs.simple s • v = v) {ω : List B}
    (h : cs.wordProd ω • v ≠ v) : ∃ s ∈ ω, μ s = D.dScalar χ s := by
  by_contra hc
  exact h (wordProd_smul_eq_self fun s hs => hv s fun heq => hc ⟨s, hs, heq⟩)

theorem card_le_finrank_of_mem_orbit [Fact p.Prime] [CharP k p] [Module.Finite k V]
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {v : X} (hv : ∀ s, μ s ≠ D.dScalar χ s → cs.simple s • v = v) {m : ℕ} (u : Fin m → X)
    (hu : ∀ i, u i ∈ MulAction.orbit W v) (hinj : Function.Injective u) :
    m ≤ Module.finrank k V := by
  choose w hw using fun i => MulAction.mem_orbit_iff.mp (hu i)
  refine card_le_finrank (D := D) hρ ht w ?_
  intro i j hij ω _ hωe
  apply exists_mem_mu_eq_dScalar_of_smul_ne hv
  intro hfix0
  have hfix : ((w i)⁻¹ * w j) • v = v := by rw [← hωe]; exact hfix0
  have hwij : w j • v = w i • v := smul_eq_of_inv_mul_smul_eq_self hfix
  exact hij (hinj (by rw [← hw i, ← hw j]; exact hwij.symm))

theorem le_finrank_range_sub_one_of_mem_orbit [Fact p.Prime] [CharP k p] [Module.Finite k V]
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {v : X} (hv : ∀ s, μ s ≠ D.dScalar χ s → cs.simple s • v = v) (x : W) {m : ℕ}
    (u : Fin m → X) (hu : ∀ i, u i ∈ MulAction.orbit W v) (hinj : Function.Injective u)
    (hmove : ∀ i j, u i ≠ x • u j) :
    m ≤ Module.finrank k (LinearMap.range (ρ (D.nW x) - 1)) := by
  choose b hb using fun i => MulAction.mem_orbit_iff.mp (hu i)
  refine le_finrank_range_sub_one (D := D) hρ ht x b ?_ ?_
  · intro i j hij ω _ hωe
    apply exists_mem_mu_eq_dScalar_of_smul_ne hv
    intro hfix0
    have hfix : ((b i)⁻¹ * b j) • v = v := by rw [← hωe]; exact hfix0
    have hbij : b j • v = b i • v := smul_eq_of_inv_mul_smul_eq_self hfix
    exact hij (hinj (by rw [← hb i, ← hb j]; exact hbij.symm))
  · intro i j ω _ hωe
    apply exists_mem_mu_eq_dScalar_of_smul_ne hv
    intro hfix0
    have hfix : ((b i)⁻¹ * (x * b j)) • v = v := by rw [← hωe]; exact hfix0
    have hx : (x * b j) • v = b i • v := smul_eq_of_inv_mul_smul_eq_self hfix
    have hxu : x • u j = u i := by
      rw [← hb j, ← hb i, ← mul_smul]
      exact hx
    exact hmove i j hxu.symm

end CFSG.LocalAnalysis.WeakClosure81
