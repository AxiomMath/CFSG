module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteen

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

theorem eq_one_of_mul_self_eq_one_of_isElemAbelian {p : ℕ} (hp : Odd p) {E : Subgroup G}
    (hE : IsElemAbelian p E) {e : G} (he : e ∈ E) (h : e * e = 1) : e = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h1 := hE.2 e he
  rwa [pow_succ, pow_mul, sq, h, one_pow, one_mul] at h1

theorem conj_eq_self_of_conj_eq_of_commute {E P : Subgroup G}
    (hE : ∀ e ∈ E, e * e = 1 → e = 1) (hEP : E ≤ Subgroup.normalizer (P : Set G)) {a b : G}
    (ha : a ∈ P) (hbP : ∀ g ∈ P, g * b = b * g) (haE : ∀ e ∈ E, a * e * a⁻¹ ∈ E)
    (hab : ∀ e ∈ E, a * e * a⁻¹ = b * e * b⁻¹) (hinv : ∀ e ∈ E, a * (a * e * a⁻¹) * a⁻¹ = e)
    {e : G} (he : e ∈ E) : a * e * a⁻¹ = e := by
  have hdE : a * e * a⁻¹ * e⁻¹ ∈ E := E.mul_mem (haE e he) (E.inv_mem he)
  have hdP : a * e * a⁻¹ * e⁻¹ ∈ P := by
    have h : e * a⁻¹ * e⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hEP he) a⁻¹).mp (P.inv_mem ha)
    have h' := P.mul_mem ha h
    rwa [← mul_assoc, ← mul_assoc] at h'
  have hbd : b * (a * e * a⁻¹ * e⁻¹) * b⁻¹ = a * e * a⁻¹ * e⁻¹ := by
    rw [← hbP _ hdP, mul_inv_cancel_right]
  have had : a * (a * e * a⁻¹ * e⁻¹) * a⁻¹ = (a * e * a⁻¹ * e⁻¹)⁻¹ := by
    calc a * (a * e * a⁻¹ * e⁻¹) * a⁻¹ = a * (a * e * a⁻¹) * a⁻¹ * (a * e * a⁻¹)⁻¹ := by group
      _ = (a * e * a⁻¹ * e⁻¹)⁻¹ := by rw [hinv e he]; group
  have hdd : (a * e * a⁻¹ * e⁻¹) * (a * e * a⁻¹ * e⁻¹) = 1 := by
    have h := ((hab _ hdE).trans hbd).symm.trans had
    rw [mul_eq_one_iff_eq_inv]
    exact h
  exact mul_inv_eq_one.mp (hE _ hdE hdd)

theorem ggAutomizer_eq_one_of_commute {Bs P Q : Subgroup G}
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1) (hBP : Bs ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ∀ g ∈ P, ∀ h ∈ Q, g * h = h * g) {r : MulAut ↥Bs}
    (hrP : r ∈ ggAutomizer P Bs) (hrQ : r ∈ ggAutomizer Q Bs) (hr2 : r ^ 2 = 1) : r = 1 := by
  obtain ⟨a, ha, -, hra⟩ := mem_ggAutomizer_iff.mp hrP
  obtain ⟨b, hb, -, hrb⟩ := mem_ggAutomizer_iff.mp hrQ
  have hrr (e : ↥Bs) : r (r e) = e := by
    rw [← MulAut.mul_apply, ← sq, hr2, MulAut.one_apply]
  have key : ∀ e ∈ Bs, a * e * a⁻¹ = e := by
    refine fun e he => conj_eq_self_of_conj_eq_of_commute hBs hBP ha (fun g hg => hPQ g hg b hb)
      (fun e he => ?_) (fun e he => ?_) (fun e he => ?_) he
    · rw [← hra ⟨e, he⟩]
      exact (r ⟨e, he⟩).2
    · rw [← hra ⟨e, he⟩, ← hrb ⟨e, he⟩]
    · have h := hra (r ⟨e, he⟩)
      rw [hrr, hra ⟨e, he⟩] at h
      exact h.symm
  refine MulEquiv.ext fun e => Subtype.ext ?_
  rw [MulAut.one_apply, hra e]
  exact key e e.2

theorem eq_of_isComponentOf_of_mem_ggAutomizer [Finite G] {H Bs P Q : Subgroup G}
    (hP : IsComponentOf P H) (hQ : IsComponentOf Q H)
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1) (hBP : Bs ≤ Subgroup.normalizer (P : Set G))
    {r : MulAut ↥Bs} (hrP : r ∈ ggAutomizer P Bs) (hrQ : r ∈ ggAutomizer Q Bs)
    (hr2 : r ^ 2 = 1) (hr1 : r ≠ 1) : P = Q := by
  by_contra hne
  have hP' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hP.1).mp hP
  have hQ' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hQ.1).mp hQ
  have hne' : P.subgroupOf H ≠ Q.subgroupOf H := fun h => by
    have h' := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hP.1, inf_eq_left.mpr hQ.1] at h'
    exact hne h'
  refine hr1 (ggAutomizer_eq_one_of_commute hBs hBP (fun g hg h hh => ?_) hrP hrQ hr2)
  have h := ggCommute_of_isComponent_ne hQ' hP' hne' (x := ⟨g, hP.1 hg⟩) (y := ⟨h, hQ.1 hh⟩)
    hg hh
  exact congrArg Subtype.val h

end CFSG.StandardType
