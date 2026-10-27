module

public import CFSG.OddTranspositions.PartThree.CommSetConj
public import CFSG.Mathlib.GroupTheory.ConjCentralizer

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem commSet_conj_eq_image (hN : IsNormalSet D) (g z : G) :
    commSet D (g * z * g⁻¹) = (MulAut.conj g).toMonoidHom '' commSet D z := by
  ext x
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have h := conj_mem_commSet hN g⁻¹ hx
      simpa [mul_assoc] using h
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    simpa using conj_mem_commSet hN g hy

theorem closure_commSet_inf_centralizer_conj (hN : IsNormalSet D) (g : G) {u : G}
    (h : ∀ s ∈ D, ¬ Commute s u →
      Subgroup.closure (commSet D u) ⊓ Subgroup.centralizer {s} =
        Subgroup.closure (commSet D u ∩ commSet D s))
    {s : G} (hs : s ∈ D) (hsu : ¬ Commute s (g * u * g⁻¹)) :
    Subgroup.closure (commSet D (g * u * g⁻¹)) ⊓ Subgroup.centralizer {s} =
      Subgroup.closure (commSet D (g * u * g⁻¹) ∩ commSet D s) := by
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have hφinj : Function.Injective φ := by rw [hφ]; exact (MulAut.conj g).injective
  let s' : G := g⁻¹ * s * g
  have hs'def : s' = g⁻¹ * s * g := rfl
  have hs'mem : s' ∈ D := by
    rw [hs'def]
    simpa using hN g⁻¹ s hs
  have hsu' : ¬ Commute s' u := by
    intro hc
    apply hsu
    rw [hs'def] at hc
    simpa [mul_assoc] using (Commute.conj_iff (a := g⁻¹ * s * g) (b := u) g).2 hc
  have hcomm_u : commSet D (g * u * g⁻¹) = φ '' commSet D u := by
    rw [hφ]
    exact commSet_conj_eq_image hN g u
  have hcomm_s : commSet D s = φ '' commSet D s' := by
    have h : g * s' * g⁻¹ = s := by rw [hs'def]; simp [mul_assoc]
    rw [hφ, ← h, commSet_conj_eq_image hN g s']
  have hA : Subgroup.closure (commSet D (g * u * g⁻¹)) =
      (Subgroup.closure (commSet D u)).map φ := by
    rw [hcomm_u, ← MonoidHom.map_closure]
  have hB : Subgroup.centralizer {s} = (Subgroup.centralizer {s'}).map φ := by
    have h : g * s' * g⁻¹ = s := by rw [hs'def]; simp [mul_assoc]
    rw [hφ, ← h, Subgroup.map_conj_centralizer_singleton g s']
  have hC : Subgroup.closure (commSet D (g * u * g⁻¹) ∩ commSet D s) =
      (Subgroup.closure (commSet D u ∩ commSet D s')).map φ := by
    have hinter : commSet D (g * u * g⁻¹) ∩ commSet D s =
        φ '' (commSet D u ∩ commSet D s') := by
      rw [hcomm_u, hcomm_s, ← Set.image_inter hφinj]
    rw [hinter, ← MonoidHom.map_closure]
  rw [hA, hB, hC]
  rw [← Subgroup.map_inf_eq (Subgroup.closure (commSet D u)) (Subgroup.centralizer {s'}) φ hφinj]
  rw [h s' hs'mem hsu']

end CFSG.OddTranspositions.PartThree
