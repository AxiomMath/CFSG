module

public import CFSG.RankThree.PartOne.N1322.Core
public import CFSG.RankThree.PartOne.N1322.CaseBasic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory

variable {K : Type*} [Field K]

theorem A5_pow : ∀ σ : alternatingGroup (Fin 5), σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by decide +kernel

theorem case3_false {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHX : H ≤ d.X) (e : H ≃* alternatingGroup (Fin 5))
    (hdec : ∀ g ∈ d.X, ∃ a ∈ H, ∃ z ∈ d.X, (∀ y ∈ d.X, z * y = y * z) ∧ g = a * z)
    (hinter : ∀ z ∈ H, (∀ y ∈ d.X, z * y = y * z) → z = 1) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_five_le h.p5
  have hirr' : IsIrreducibleMatrixRep d.X.subtype := h.irr
  have hperf : Group.IsPerfect H := by
    have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hXD : ∀ t ∈ d.D, t ∈ d.X := fun t ht => by
    rw [h.gen]; exact Subgroup.subset_closure ht
  have hD : ∀ t ∈ d.D, ∃ a ∈ H, t = (-1 : GL (Fin 3) (ZMod p)) * a := by
    intro t ht
    obtain ⟨a, haH, z, hzX, hzc, hta⟩ := hdec t (hXD t ht)
    have hrefl := h.refl t ht
    have ht2 : t * t = 1 := hrefl.sq
    have haX : a ∈ d.X := hHX haH
    have hza : z * a = a * z := hzc a haX
    have hsq : a * a * (z * z) = 1 := by
      calc a * a * (z * z) = a * (a * z) * z := by group
        _ = a * (z * a) * z := by rw [hza]
        _ = (a * z) * (a * z) := by group
        _ = 1 := by rw [← hta]; exact ht2
    have hcent : ∀ y ∈ d.X, a * a * y = y * (a * a) := by
      intro y hy
      have haa : a * a = (z * z)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [haa]
      have hc : Commute z y := hzc y hy
      exact ((hc.mul_left hc).inv_left).eq
    have haa1 : a * a = 1 := hinter (a * a) (H.mul_mem haH haH) hcent
    have hzz : z * z = 1 := by rw [haa1, one_mul] at hsq; exact hsq
    rcases central_sq_eq_one hirr' hzz hzc with hz | hz
    · exfalso
      have hdet : (t : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
        have : t = a := by rw [hta, hz, mul_one]
        rw [this]
        exact det_eq_one_of_perfect haH
      rw [hrefl.det_eq] at hdet
      apply h2
      linear_combination -hdet
    · exact ⟨a, haH, by rw [hta, hz, ← neg_one_comm]⟩
  obtain ⟨e'⟩ := h.Ldih
  obtain ⟨ρ, t₀, hg⟩ := exists_gens h.n_mem e'
  have hcover := hcover_of_hyp h2 h.toMonoHyp
  have nc1 : IsNCInv t₀ := (hg.nc_iff t₀).mpr ⟨0, by simp⟩
  have nc2 : IsNCInv (t₀ * ρ) := (hg.nc_iff _).mpr ⟨1, by simp⟩
  obtain ⟨a₁, ha₁, h1⟩ := hD _ (hcover t₀ nc1)
  obtain ⟨a₂, ha₂, h2'⟩ := hD _ (hcover (t₀ * ρ) nc2)
  have hprod : (t₀ : GL (Fin 3) (ZMod p)) * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) =
      (ρ : GL (Fin 3) (ZMod p)) := by
    have := congrArg Subtype.val (show t₀ * (t₀ * ρ) = ρ by rw [← mul_assoc, hg.sq, one_mul])
    simpa using this
  have hmul : a₁ * a₂ = (ρ : GL (Fin 3) (ZMod p)) := by
    calc a₁ * a₂ = ((-1 : GL (Fin 3) (ZMod p)) * (-1)) * a₁ * a₂ := by
          rw [neg_one_mul_neg_one, one_mul]
      _ = (-1) * ((-1) * a₁) * a₂ := by group
      _ = (-1) * (a₁ * (-1)) * a₂ := by rw [neg_one_comm a₁]
      _ = ((-1) * a₁) * ((-1) * a₂) := by group
      _ = (t₀ : GL (Fin 3) (ZMod p)) * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) := by
          rw [← h1, ← h2']
      _ = ρ := hprod
  have hmem : a₁ * a₂ ∈ H := H.mul_mem ha₁ ha₂
  have hord : orderOf (a₁ * a₂) = d.n := by
    rw [hmul]
    have := hg.ord
    rw [← this]
    exact Subgroup.orderOf_coe ρ
  have hord' : orderOf (e ⟨a₁ * a₂, hmem⟩) = d.n := by
    rw [MulEquiv.orderOf_eq, ← hord]
    exact Subgroup.orderOf_mk _ _
  have hdiv : d.n ∣ 2 ∨ d.n ∣ 3 ∨ d.n ∣ 5 := by
    rcases A5_pow (e ⟨a₁ * a₂, hmem⟩) with hp | hp | hp
    · left; rw [← hord']; exact orderOf_dvd_of_pow_eq_one hp
    · right; left; rw [← hord']; exact orderOf_dvd_of_pow_eq_one hp
    · right; right; rw [← hord']; exact orderOf_dvd_of_pow_eq_one hp
  rcases h.n_mem with hn | hn | hn <;> (rw [hn] at hdiv; omega)

end CFSG.RankThree.PartOne.N1322
