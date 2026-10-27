module

public import CFSG.Blueprint.Catalog

import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeMax

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open Subgroup CFSG.ClassicalInvolution.G2D4Models CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

private theorem comap_centralizer_singleton {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (z : A) : (centralizer ({e z} : Set B)).comap e.toMonoidHom = centralizer ({z} : Set A) := by
  ext x
  simp only [mem_comap, MulEquiv.coe_toMonoidHom, mem_centralizer_singleton_iff]
  rw [← map_mul, ← map_mul]
  exact e.injective.eq_iff

private theorem sup_centralizer_eq_top_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {z z' : A} (h : centralizer ({e z} : Set B) ⊔ centralizer ({e z'} : Set B) = ⊤) :
    centralizer ({z} : Set A) ⊔ centralizer ({z'} : Set A) = ⊤ := by
  rw [← comap_centralizer_singleton e z, ← comap_centralizer_singleton e z',
    comap_sup_eq e.toMonoidHom _ _ e.surjective, h, comap_top]

private theorem eqLocus_conj_eq_centralizer {X : Type} [Group X] (z : X) :
    (MulAut.conj z).toMonoidHom.eqLocus (MonoidHom.id X) = centralizer ({z} : Set X) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  show z * x * z⁻¹ = x ↔ x * z = z * x
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

private theorem sup_centralizer_eq_top_of_isCoatom {X : Type} [Group X] {z z' : X} (hz1' : z' ≠ 1)
    (hne : z ≠ z')
    (hZ : ∀ w : X, (∀ x : X, x * z = z * x → w * x = x * w) → w = 1 ∨ w = z)
    (h : IsCoatom (centralizer ({z} : Set X))) (h' : IsCoatom (centralizer ({z'} : Set X))) :
    centralizer ({z} : Set X) ⊔ centralizer ({z'} : Set X) = ⊤ := by
  by_contra hsup
  have h1 := (h.le_iff.mp le_sup_left).resolve_left hsup
  have h2 := (h'.le_iff.mp le_sup_right).resolve_left hsup
  have hcc : centralizer ({z} : Set X) = centralizer ({z'} : Set X) := h1.symm.trans h2
  have hcent : ∀ x : X, x * z = z * x → z' * x = x * z' := fun x hx => by
    have hxz : x ∈ centralizer ({z} : Set X) := mem_centralizer_singleton_iff.mpr hx
    rw [hcc] at hxz
    exact (mem_centralizer_singleton_iff.mp hxz).symm
  rcases hZ z' hcent with h0 | h0
  · exact hz1' h0
  · exact hne h0.symm

theorem g2_sup_centralizer_eq_top {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hX : CFSG.Blueprint.LieModel X .G2 0 r 1) {z z' : X} (hz : z * z = 1)
    (hz' : z' * z' = 1) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) (hne : z ≠ z') (hc : z * z' = z' * z)
    (hZ : ∀ w : X, (∀ x : X, x * z = z * x → w * x = x * w) → w = 1 ∨ w = z) :
    Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer {z'} = ⊤ := by
  by_cases hr3 : r = 3
  · subst hr3
    have hcoat : ∀ w : X, w * w = 1 → ¬ (∀ x : X, x * w = w * x) →
        IsCoatom (centralizer ({w} : Set X)) := by
      intro w hw hwc
      have h := g2ThreeMax_of_cert X hX (MulAut.conj w) (by rw [← map_mul, hw, map_one])
        fun h1 => hwc fun x => by
          have := congrArg (fun σ : MulAut X => σ x) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          exact (mul_inv_eq_iff_eq_mul.mp this).symm
      rwa [eqLocus_conj_eq_centralizer] at h
    by_cases hzc : ∀ x : X, x * z = z * x
    · have : centralizer ({z} : Set X) = ⊤ :=
        eq_top_iff.mpr fun x _ => mem_centralizer_singleton_iff.mpr (hzc x)
      rw [this, top_sup_eq]
    by_cases hzc' : ∀ x : X, x * z' = z' * x
    · have : centralizer ({z'} : Set X) = ⊤ :=
        eq_top_iff.mpr fun x _ => mem_centralizer_singleton_iff.mpr (hzc' x)
      rw [this, sup_top_eq]
    exact sup_centralizer_eq_top_of_isCoatom hz1' hne hZ (hcoat z hz hzc) (hcoat z' hz' hzc')
  · have hr5 : 5 ≤ r := by
      have h2 := hr.two_le
      by_contra hlt
      have h4 : r = 4 := by omega
      subst h4
      exact absurd hr (by norm_num)
    obtain ⟨F, hF, hFin, hcard, ⟨ψ⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hX
    have hcard' : Nat.card F = r := by simpa using hcard
    have hodd : Odd (Nat.card F) := Ivk47ab.odd_card_of_model hr hr2 hcard
    refine sup_centralizer_eq_top_of_equiv ψ ?_
    have hψz : ψ z * ψ z = 1 := by rw [← map_mul, hz, map_one]
    have hψz' : ψ z' * ψ z' = 1 := by rw [← map_mul, hz', map_one]
    have hψ1 : ψ z ≠ 1 := fun h => hz1 (ψ.injective (by rw [h, map_one]))
    have hψ1' : ψ z' ≠ 1 := fun h => hz1' (ψ.injective (by rw [h, map_one]))
    have hψne : ψ z ≠ ψ z' := fun h => hne (ψ.injective h)
    have hψc : ψ z * ψ z' = ψ z' * ψ z := by rw [← map_mul, ← map_mul, hc]
    by_cases h7 : 7 ≤ r
    · exact centralizer_sup_eq_top_g2_large7 hodd (by rw [hcard']; exact h7) hψz hψz' hψ1 hψ1'
        hψne hψc
    · have h6 : r ≠ 6 := by
        rintro rfl
        exact absurd hr (by norm_num)
      have h5 : Nat.card F = 5 := by rw [hcard']; omega
      by_cases hT : ToralPair (F := F) (ψ z) (ψ z')
      · have hK2 : ringChar F ≠ 2 := CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hodd
        have hneg : (-1 : Fˣ) ≠ 1 := fun h =>
          Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)
        exact centralizer_sup_eq_top_of_toralPair hneg hT
      · exact centralizer_sup_eq_top_g2_five hodd h5 hψz hψz' hψ1 hψ1' hψne hψc hT

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

end
