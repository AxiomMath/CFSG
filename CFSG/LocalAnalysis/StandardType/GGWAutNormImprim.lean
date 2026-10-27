module

public import CFSG.LocalAnalysis.StandardType.GGWAutMonoNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggWAut_imprim_norm [Module.Finite (ZMod 3) V] (hn : 5 ≤ Module.finrank (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (himp : CFSG.Quasithin.SimsG4.IsImprimitiveOnV R) (hneg : ∀ r ∈ R, ¬ ∀ v, r v = -v)
    {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  classical
  let n : ℕ := Module.finrank (ZMod 3) V
  have hn5 : 5 ≤ n := hn
  obtain ⟨f, hfmono⟩ := ggWAut_imprim_frame (n := n) rfl R habs hgen himp
  have htype := ggWAut_monomial_type (n := n) hn5 f R habs hgen hfmono
  have hmono : GGMonomialIn f a := ggWAut_monomial_normalizer hn5 f R habs htype a ha
  obtain ⟨σ, ε, hε, hact⟩ := hmono
  rcases htype with hB | hD
  · exact ⟨a, (hB a).mpr ⟨σ, ε, hε, hact⟩, Or.inl fun _ => rfl⟩
  · let m : V ≃ₗ[ZMod 3] V := LinearEquiv.neg (ZMod 3)
    have hm_apply : ∀ v, m v = -v := fun v => LinearEquiv.neg_apply v
    by_cases hneven : Even n
    · exfalso
      have hsign : ∀ _ : Fin n, (-1 : ZMod 3) ≠ 0 := fun _ => by decide
      have hm_even : GGMonomialEvenIn f m := by
        refine ⟨Equiv.refl _, fun _ => (-1 : ZMod 3), hsign, ?_, fun i => ?_⟩
        · rw [Fin.prod_const]
          exact hneven.neg_one_pow
        · rw [hm_apply (f i), ← neg_one_smul (ZMod 3) (f i)]
          rfl
      exact hneg m ((hD m).mpr hm_even) hm_apply
    · have hnodd : Odd n := Nat.not_even_iff_odd.mp hneven
      have hne0 : ∏ i, ε i ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hε i)
      have hpm1 : ∏ i, ε i = 1 ∨ ∏ i, ε i = -1 :=
        (by decide : ∀ y : ZMod 3, y ≠ 0 → y = 1 ∨ y = -1) _ hne0
      rcases hpm1 with hprod | hprod
      · exact ⟨a, (hD a).mpr ⟨σ, ε, hε, hprod, hact⟩, Or.inl fun _ => rfl⟩
      · let b : V ≃ₗ[ZMod 3] V := m * a
        have hb_apply : ∀ v, b v = -(a v) := by
          intro v
          show (m * a) v = -(a v)
          rw [LinearEquiv.mul_apply, hm_apply]
        have hbact : ∀ i, b (f i) = (-ε i) • f (σ i) := by
          intro i
          show (m * a) (f i) = (-ε i) • f (σ i)
          rw [LinearEquiv.mul_apply, hact i, map_smul, hm_apply (f (σ i)), smul_neg, neg_smul]
        have hbprod : ∏ i, (-ε i) = 1 := by
          have h1 : ∏ i, (-ε i) = (∏ _i : Fin n, (-1 : ZMod 3)) * ∏ i, ε i := by
            rw [← Finset.prod_mul_distrib]
            exact Finset.prod_congr rfl fun i _ => (neg_one_mul (ε i)).symm
          rw [h1, Fin.prod_const, hnodd.neg_one_pow, hprod]
          decide
        exact ⟨b, (hD b).mpr ⟨σ, fun i => -ε i, fun i => neg_ne_zero.mpr (hε i), hbprod, hbact⟩,
          Or.inr fun v => by rw [hb_apply v, neg_neg]⟩

private theorem ggWAutNImprim_det_refl [Module.Finite (ZMod 3) V] {t : V ≃ₗ[ZMod 3] V}
    (h : IsReflLin t) : LinearEquiv.det t = -1 := by
  obtain ⟨c, φ, hc, rfl⟩ := h
  exact Module.det_reflection hc

theorem ggWAut_SL_neg_mem [Module.Finite (ZMod 3) V] (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (hSL : ∀ g : V ≃ₗ[ZMod 3] V, LinearEquiv.det g = 1 → g ∈ R)
    (hrefl : ∃ t ∈ R, GGLinRefl t) : ∃ r ∈ R, ∀ v, r v = -v := by
  obtain ⟨t, htR, hreflt⟩ := hrefl
  have hdet : LinearEquiv.det t = -1 :=
    ggWAutNImprim_det_refl ((ggLinRefl_iff_isReflLin t).mp hreflt)
  let m : V ≃ₗ[ZMod 3] V := LinearEquiv.neg (ZMod 3)
  have hm_apply : ∀ v, m v = -v := fun v => LinearEquiv.neg_apply v
  have hdetm : LinearEquiv.det m = 1 ∨ LinearEquiv.det m = -1 :=
    (by decide : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1) (LinearEquiv.det m)
  refine ⟨m, ?_, hm_apply⟩
  rcases hdetm with h | h
  · exact hSL m h
  · have htm : LinearEquiv.det (t * m) = 1 := by
      rw [map_mul, hdet, h]
      decide
    have hmem : t * m ∈ R := hSL (t * m) htm
    have heq : m = t⁻¹ * (t * m) := by group
    rw [heq]
    exact R.mul_mem (R.inv_mem htR) hmem

end CFSG.StandardType

end
