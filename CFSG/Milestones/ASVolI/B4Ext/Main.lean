module

public import CFSG.Milestones.ASVolI.B4Ext.StepD
public import CFSG.Milestones.ASVolI.B4Ext.Base
public import CFSG.Milestones.ASVolI.B4Ext.Four

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section H1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49x_H1N {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : 4 ≤ finrank (ZMod 2) W)
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W)} (hδ : δ ∈ Z1A (burnsideB49x_muN W)) :
    δ ∈ B1A (burnsideB49x_muN W) :=
  burnsideB49x_H1N_of_base (fun W _ _ _ hW _ hδ => burnsideB49x_baseN W hW hδ) _ hW W rfl δ hδ

theorem burnsideB49x_H1D {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : 5 ≤ finrank (ZMod 2) W)
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)}
    (hδ : δ ∈ Z1A (burnsideB49x_muD W)) : δ ∈ B1A (burnsideB49x_muD W) :=
  burnsideB49x_H1D_of_base (fun W _ _ _ hW _ hδ => burnsideB49x_baseD W hW hδ) _ hW W rfl δ hδ

end H1

section Translate

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49x_defect_mem (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρ g v) = g (q v)) (s : W →ₗ[ZMod 2] V)
    (hs : ∀ x, q (s x) = x) (g : W ≃ₗ[ZMod 2] W) (x : W) :
    ρ g (s (g.symm x)) - s x ∈ LinearMap.ker q := by
  rw [LinearMap.mem_ker, map_sub, hq, hs, hs, LinearEquiv.apply_symm_apply, sub_self]

@[expose] noncomputable def burnsideB49x_defect (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρ g v) = g (q v)) (s : W →ₗ[ZMod 2] V)
    (hs : ∀ x, q (s x) = x) (g : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] ↥(LinearMap.ker q) :=
  LinearMap.codRestrict (LinearMap.ker q)
    ((ρ g : V →ₗ[ZMod 2] V) ∘ₗ s ∘ₗ (g.symm : W →ₗ[ZMod 2] W) - s)
    (fun x => burnsideB49x_defect_mem ρ q hq s hs g x)

theorem burnsideB49x_defect_apply (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρ g v) = g (q v)) (s : W →ₗ[ZMod 2] V)
    (hs : ∀ x, q (s x) = x) (g : W ≃ₗ[ZMod 2] W) (x : W) :
    ((burnsideB49x_defect ρ q hq s hs g x : ↥(LinearMap.ker q)) : V) =
      ρ g (s (g.symm x)) - s x := rfl

theorem burnsideB49x_defect_mul (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρ g v) = g (q v)) (s : W →ₗ[ZMod 2] V)
    (hs : ∀ x, q (s x) = x) (g h : W ≃ₗ[ZMod 2] W) (x : W) :
    ((burnsideB49x_defect ρ q hq s hs (g * h) x : ↥(LinearMap.ker q)) : V) =
      ((burnsideB49x_defect ρ q hq s hs g x : ↥(LinearMap.ker q)) : V) +
        ρ g ((burnsideB49x_defect ρ q hq s hs h (g.symm x) : ↥(LinearMap.ker q)) : V) := by
  simp only [burnsideB49x_defect_apply, map_sub, map_mul, LinearEquiv.mul_apply]
  have e : (g * h).symm x = h.symm (g.symm x) := rfl
  rw [e]
  abel

theorem burnsideB49x_complement_nat (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (q : V →ₗ[ZMod 2] W) (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    (θ : W ≃ₗ[ZMod 2] ↥(LinearMap.ker q))
    (hθ : ∀ g w, ((θ (g w) : ↥(LinearMap.ker q)) : V) = ρ g ((θ w : ↥(LinearMap.ker q)) : V))
    (hH : ∀ δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W),
      δ ∈ Z1A (burnsideB49x_muN W) → δ ∈ B1A (burnsideB49x_muN W)) :
    ∃ U' : Submodule (ZMod 2) V, (∀ g, ∀ x ∈ U', ρ g x ∈ U') ∧
      IsCompl (LinearMap.ker q) U' := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.2 hqs)
  have hs' : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  let δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W) := fun g =>
    (θ.symm : ↥(LinearMap.ker q) →ₗ[ZMod 2] W) ∘ₗ burnsideB49x_defect ρ q hq s hs' g
  have hθδ : ∀ g x, ((θ (δ g x) : ↥(LinearMap.ker q)) : V) = ρ g (s (g.symm x)) - s x := by
    intro g x
    simp only [δ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      burnsideB49x_defect_apply]
  have hδ : δ ∈ Z1A (burnsideB49x_muN W) := by
    intro g h
    ext x
    apply θ.injective
    apply Subtype.ext
    rw [hθδ, LinearMap.add_apply, map_add, Submodule.coe_add, hθδ, burnsideB49x_muN_apply, hθ,
      hθδ]
    simp only [map_sub, map_mul, LinearEquiv.mul_apply]
    have e : (g * h).symm x = h.symm (g.symm x) := rfl
    rw [e]
    abel
  obtain ⟨Y, hY⟩ := hH δ hδ
  let s' : W →ₗ[ZMod 2] V :=
    s - (LinearMap.ker q).subtype ∘ₗ (θ : W →ₗ[ZMod 2] ↥(LinearMap.ker q)) ∘ₗ Y
  have hs'q : ∀ x, q (s' x) = x := fun x => by
    simp only [s', LinearMap.sub_apply, map_sub, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe, hs', LinearMap.mem_ker.1 (θ (Y x)).2, sub_zero]
  have hs'e : ∀ g x, ρ g (s' x) = s' (g x) := by
    intro g x
    have h1 := congrArg (fun f : W →ₗ[ZMod 2] W => ((θ (f (g x)) : ↥(LinearMap.ker q)) : V))
      (congrFun hY g)
    simp only [coboundaryA_apply, LinearMap.sub_apply, burnsideB49x_muN_apply,
      LinearEquiv.symm_apply_apply, map_sub, Submodule.coe_sub, hθ, hθδ] at h1
    simp only [s', LinearMap.sub_apply, map_sub, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h1.symm
  refine ⟨LinearMap.range s', ?_, burnsideB49_isCompl_of_section hs'q⟩
  rintro g _ ⟨y, rfl⟩
  exact ⟨g y, (hs'e g y).symm⟩

theorem burnsideB49x_complement_dual [Finite V] (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (q : V →ₗ[ZMod 2] W) (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    (θ' : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥(LinearMap.ker q))
    (hθ' : ∀ g w (u u' : ↥(LinearMap.ker q)), ρ g (u' : V) = (u : V) → θ' (g w) u = θ' w u')
    (hH : ∀ δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2),
      δ ∈ Z1A (burnsideB49x_muD W) → δ ∈ B1A (burnsideB49x_muD W)) :
    ∃ U' : Submodule (ZMod 2) V, (∀ g, ∀ x ∈ U', ρ g x ∈ U') ∧
      IsCompl (LinearMap.ker q) U' := by
  haveI : Finite ↥(LinearMap.ker q) := inferInstance
  haveI : FiniteDimensional (ZMod 2) ↥(LinearMap.ker q) := Module.Finite.of_finite
  let Θ : ↥(LinearMap.ker q) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W :=
    (Module.evalEquiv (ZMod 2) ↥(LinearMap.ker q)).trans θ'.dualMap
  have hΘ : ∀ u w, Θ u w = θ' w u := fun u w => rfl
  have hmem2 : ∀ (g : W ≃ₗ[ZMod 2] W) (y : V), y ∈ LinearMap.ker q → ρ g y ∈ LinearMap.ker q :=
    fun g y hy => by rw [LinearMap.mem_ker, hq, LinearMap.mem_ker.1 hy, map_zero]
  have hΘg : ∀ (g : W ≃ₗ[ZMod 2] W) (u : ↥(LinearMap.ker q)) w,
      Θ ⟨ρ g (u : V), hmem2 g _ u.2⟩ w = Θ u (g.symm w) := by
    intro g u w
    rw [hΘ, hΘ]
    have := hθ' g (g.symm w) ⟨ρ g (u : V), hmem2 g _ u.2⟩ u rfl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.2 hqs)
  have hs' : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  let δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) := fun g =>
    (Θ : ↥(LinearMap.ker q) →ₗ[ZMod 2] Module.Dual (ZMod 2) W) ∘ₗ
      burnsideB49x_defect ρ q hq s hs' g
  have hδapp : ∀ g x, δ g x = Θ (burnsideB49x_defect ρ q hq s hs' g x) := fun g x => rfl
  have hδ : δ ∈ Z1A (burnsideB49x_muD W) := by
    intro g h
    ext x y
    rw [LinearMap.add_apply, LinearMap.add_apply, burnsideB49x_muD_apply, hδapp, hδapp, hδapp]
    have e1 : burnsideB49x_defect ρ q hq s hs' (g * h) x = burnsideB49x_defect ρ q hq s hs' g x +
        ⟨ρ g ((burnsideB49x_defect ρ q hq s hs' h (g.symm x) : ↥(LinearMap.ker q)) : V),
          hmem2 g _ (burnsideB49x_defect ρ q hq s hs' h (g.symm x)).2⟩ :=
      Subtype.ext (burnsideB49x_defect_mul ρ q hq s hs' g h x)
    rw [e1, map_add, LinearMap.add_apply, hΘg]
  obtain ⟨Y, hY⟩ := hH δ hδ
  let s' : W →ₗ[ZMod 2] V :=
    s - (LinearMap.ker q).subtype ∘ₗ (Θ.symm : Module.Dual (ZMod 2) W →ₗ[ZMod 2]
      ↥(LinearMap.ker q)) ∘ₗ Y
  have hs'q : ∀ x, q (s' x) = x := fun x => by
    simp only [s', LinearMap.sub_apply, map_sub, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe, hs', LinearMap.mem_ker.1 (Θ.symm (Y x)).2, sub_zero]
  have hs'e : ∀ g x, ρ g (s' x) = s' (g x) := by
    intro g x
    have h1 : Θ (burnsideB49x_defect ρ q hq s hs' g (g x)) =
        Θ ⟨ρ g ((Θ.symm (Y x) : ↥(LinearMap.ker q)) : V), hmem2 g _ (Θ.symm (Y x)).2⟩ -
          Θ (Θ.symm (Y (g x))) := by
      rw [← hδapp, ← congrFun hY g, coboundaryA_apply]
      ext y
      simp only [LinearMap.sub_apply, burnsideB49x_muD_apply, hΘg, LinearEquiv.apply_symm_apply,
        LinearEquiv.symm_apply_apply]
    rw [← map_sub] at h1
    have h2 := congrArg (fun u : ↥(LinearMap.ker q) => (u : V)) (Θ.injective h1)
    simp only [burnsideB49x_defect_apply, LinearEquiv.symm_apply_apply, Submodule.coe_sub] at h2
    simp only [s', LinearMap.sub_apply, map_sub, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe]
    rw [sub_eq_sub_iff_sub_eq_sub] at h2
    rw [h2]
  refine ⟨LinearMap.range s', ?_, burnsideB49_isCompl_of_section hs'q⟩
  rintro g _ ⟨y, rfl⟩
  exact ⟨g y, (hs'e g y).symm⟩

end Translate

section Part2iF1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V}
  {G : Subgroup (MulAut V)} {n : ℕ} {K : Type} [Field K] [Finite K]
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49x_split_nat (hn : 4 ≤ n) (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hsub : CFSG.ASVolI.ChB.QuotIsoSub G U) : CFSG.ASVolI.ChB.SplitsOver G U := by
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inl hsub
  set hG := burnsideB49_hG hreal with hGdef
  set hb := burnsideB49_iota_bijective hV hK hreal hquot with hbdef
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hdim : 4 ≤ Module.finrank (ZMod 2) (burnsideB49_W hV U) := by
    rw [burnsideB49_finrank_W hV hK hreal hquot]
    exact hn
  obtain ⟨φ_, hφ_⟩ := hsub
  obtain ⟨U', hinv, hc⟩ := burnsideB49x_complement_nat (burnsideB49_rho hV U G hG hb)
    (burnsideB49_q hV U) (burnsideB49_q_surjective hV U) (burnsideB49_q_rho hV U G hG hb)
    (burnsideB49_thetaNat hV U φ_)
    (fun g' w => by
      obtain ⟨g, rfl⟩ := hb.2 g'
      rw [burnsideB49_rho_iota]
      exact burnsideB49_thetaNat_equiv hV U G hG φ_ hφ_ g w)
    (fun δ hδ => burnsideB49x_H1N hdim hδ)
  refine burnsideB49_splits_of_complement hV U G hG U' (fun g x hx => ?_) hc
  have := hinv (burnsideB49_iota hV U G hG g) x hx
  rwa [burnsideB49_rho_iota] at this

include hV in
theorem burnsideB49x_split_dual (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) : CFSG.ASVolI.ChB.SplitsOver G U := by
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  set hG := burnsideB49_hG hreal with hGdef
  set hb := burnsideB49_iota_bijective hV hK hreal hquot with hbdef
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hdim : 5 ≤ Module.finrank (ZMod 2) (burnsideB49_W hV U) := by
    rw [burnsideB49_finrank_W hV hK hreal hquot]
    exact hn
  obtain ⟨φ_, hφ_⟩ := hdual
  obtain ⟨U', hinv, hc⟩ := burnsideB49x_complement_dual (burnsideB49_rho hV U G hG hb)
    (burnsideB49_q hV U) (burnsideB49_q_surjective hV U) (burnsideB49_q_rho hV U G hG hb)
    (burnsideB49_thetaDual hV U φ_)
    (fun g' w u u' h => by
      obtain ⟨g, rfl⟩ := hb.2 g'
      rw [burnsideB49_rho_iota] at h
      exact burnsideB49_thetaDual_equiv hV U G hG φ_ hφ_ g w u u' h)
    (fun δ hδ => burnsideB49x_H1D hdim hδ)
  refine burnsideB49_splits_of_complement hV U G hG U' (fun g x hx => ?_) hc
  have := hinv (burnsideB49_iota hV U G hG g) x hx
  rwa [burnsideB49_rho_iota] at this

include hV in
theorem burnsideB49x_part2i_f1 (hn : 4 ≤ n) (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    {T : Subgroup (MulAut V)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender T A) : CFSG.ASVolI.ChB.SplitsOver G U := by
  rcases hquot with hsub | hdual
  · exact burnsideB49x_split_nat hV hn hK hreal hsub
  · by_cases h4 : n = 4
    · subst h4
      exact burnsideB49x_part2i_four_five hV (Or.inl rfl) hK hreal (Or.inr hdual) hT hA
    · exact burnsideB49x_split_dual hV (by omega) hK hreal hdual

end Part2iF1

end CFSG.ASVolI
