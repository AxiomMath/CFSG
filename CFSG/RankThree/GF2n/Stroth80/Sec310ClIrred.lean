module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem exists_fixed_of_two_group (D : Subgroup (V ≃ₗ[K] V)) (hD : ∀ g ∈ D, g * g = 1)
    (U : Submodule K V) (hU : ∀ g ∈ D, ∀ u ∈ U, g u ∈ U) (hne : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ g ∈ D, g u = u := by
  have hVfin : Finite V := Module.finite_of_finite K
  letI act : MulAction D U :=
    { smul := fun g u => ⟨(g : V ≃ₗ[K] V) (u : V), hU (g : V ≃ₗ[K] V) g.2 (u : V) u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun g h u => Subtype.ext rfl }
  have hp : IsPGroup 2 D := by
    refine isPGroup_iff_pow_pow_eq_one.mpr fun g => ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (hD (g : V ≃ₗ[K] V) g.2)
  have h2K : 2 ∣ Nat.card K := by
    have hord : addOrderOf (1 : K) = 2 :=
      addOrderOf_eq_prime (by rw [two_nsmul, charTwo_add_self]) one_ne_zero
    have hdvd := addOrderOf_dvd_natCard (1 : K)
    rwa [hord] at hdvd
  have hfin : 1 ≤ Module.finrank K U := Submodule.one_le_finrank_iff.mpr hne
  have h2U : 2 ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := K)]
    exact dvd_pow h2K (by omega)
  have hfix0 : (0 : U) ∈ MulAction.fixedPoints D U :=
    MulAction.mem_fixedPoints.mpr fun g => Subtype.ext (map_zero (g : V ≃ₗ[K] V))
  obtain ⟨b, hb, hab⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point U h2U hfix0
  refine ⟨(b : V), b.2, fun hb0 => hab (Subtype.ext (by simp [hb0])), fun g hg => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨g, hg⟩)

theorem fixed_eq_of_elationFull (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 3 ≤ Module.finrank K V) {e f : V} (hef : F e f = 1) {D : Set (V ≃ₗ[K] V)}
    (hD : D ⊆ pointRad F e) (hfull : ElationFull F D e) {v : V} (hv : ∀ g ∈ D, g v = v) :
    ∃ c : K, v = c • e := by
  have he : e ≠ 0 := ne_zero_of_form_eq_one hef
  by_cases hve : F v e = 0
  · apply perp_perp hnd halt e v
    intro w hw
    obtain ⟨g, hgD, c, hc⟩ := ElationFull.om hnd halt hef hD hfull hw
    have h1 := pointRad_apply_perp halt hef (hD hgD) v hve
    rw [hv g hgD] at h1
    have h2 : F (g f - f) v • e = 0 := by
      have h3 : v + F (g f - f) v • e = v + 0 := by rw [add_zero, ← h1]
      exact add_left_cancel h3
    have h3 : F (g f - f) v = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h he
    have hev : F e v = 0 := by rw [form_comm halt]; exact hve
    rw [hc] at h3
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hev,
      mul_zero, add_zero] at h3
    rw [form_comm halt]
    exact h3
  · exfalso
    have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
    have hT : ∀ g ∈ D, ∃ c : K, g f - f = c • e := by
      intro g hgD
      have hy : F (v - F v e • f) e = 0 := by
        simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hfe,
          smul_eq_mul, mul_one, sub_self]
      have h1 := pointRad_apply_perp halt hef (hD hgD) (v - F v e • f) hy
      have h2 : g (v - F v e • f) = v - F v e • g f := by
        rw [map_sub, map_smul, hv g hgD]
      rw [h2] at h1
      have h9 : F v e • g f = F v e • f - F (g f - f) (v - F v e • f) • e := by
        have h10 : F v e • g f = v - (v - F v e • g f) := by abel
        rw [h10, h1]
        abel
      have hT' : F v e • (g f - f) = F (g f - f) (v - F v e • f) • e := by
        rw [smul_sub, h9, sub_sub_cancel_left, vec_neg_eq K]
      refine ⟨(F v e)⁻¹ * F (g f - f) (v - F v e • f), ?_⟩
      rw [mul_smul, ← hT', inv_smul_smul₀ hve]
    obtain ⟨ω, hω, hωne⟩ := exists_perp_not_mem_span (F := F) hdim he
    obtain ⟨g', hg'D, c', hc'⟩ := ElationFull.om hnd halt hef hD hfull hω
    obtain ⟨d, hd⟩ := hT g' hg'D
    apply hωne (d - c')
    rw [sub_smul]
    apply eq_sub_of_add_eq
    rw [← hc', hd]

theorem eq_top_of_invariant (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 3 ≤ Module.finrank K V) {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ sympSubgroup F)
    {P : Set V} (hP0 : ∀ e ∈ P, e ≠ 0)
    (hfull : ∀ e ∈ P, ElationFull F ((H : Set _) ∩ pointRad F e) e)
    (hspan : Submodule.span K P = ⊤) (U : Submodule K V)
    (hU : ∀ g ∈ H, ∀ u ∈ U, g u ∈ U) (hne : U ≠ ⊥) : U = ⊤ := by
  have hPU : ∀ e ∈ P, e ∈ U := by
    intro e heP
    have he : e ≠ 0 := hP0 e heP
    obtain ⟨z, hz⟩ : ∃ z : V, F e z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact he (hnd.1 e hcon)
    obtain ⟨f, hef⟩ : ∃ f : V, F e f = 1 :=
      ⟨(F e z)⁻¹ • z, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hz]⟩
    have hD2 : ∀ g ∈ H ⊓ pointRadSubgroup F e, g * g = 1 :=
      fun g hg => pointRad_mul_self halt hef (Subgroup.mem_inf.mp hg).2
    have hDU : ∀ g ∈ H ⊓ pointRadSubgroup F e, ∀ u ∈ U, g u ∈ U :=
      fun g hg => hU g (Subgroup.mem_inf.mp hg).1
    obtain ⟨u, huU, hu0, hufix⟩ :=
      exists_fixed_of_two_group (H ⊓ pointRadSubgroup F e) hD2 U hDU hne
    have hsub : (H : Set (V ≃ₗ[K] V)) ∩ pointRad F e ⊆ pointRad F e := Set.inter_subset_right
    have hfix : ∀ g ∈ (H : Set (V ≃ₗ[K] V)) ∩ pointRad F e, g u = u :=
      fun g hg => hufix g (Subgroup.mem_inf.mpr ⟨hg.1, hg.2⟩)
    obtain ⟨c, hc⟩ := fixed_eq_of_elationFull hnd halt hdim hef hsub (hfull e heP) hfix
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hu0
      rw [hc, zero_smul]
    have hke : e = c⁻¹ • u := by
      rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hke]
    exact U.smul_mem c⁻¹ huU
  rw [eq_top_iff, ← hspan]
  exact Submodule.span_le.mpr hPU

end CFSG.RankThree.GF2n.Stroth80.Classify
