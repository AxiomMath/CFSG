module

public import CFSG.Milestones.ASVolI.F431.RA35Out
public import CFSG.Milestones.ASVolI.F431.RU42
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF4r_ringEquiv_eq_bar {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (τ : K ≃+* K) (hτ : τ ≠ 1) : τ = barEquiv h := by
  have hcard : Nat.card K = 2 ^ 2 := by rw [h.card]
  obtain ⟨σ, hσ, hord, htop, -, -, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 2 2
      Nat.prime_two (by norm_num) K hcard
  have hbar : barEquiv h = σ := by
    ext c
    rw [barEquiv_apply, h.bar_apply, hσ]
    norm_num
  rw [hbar]
  have hτσ : τ ∈ Subgroup.zpowers σ := by rw [← htop]; exact Subgroup.mem_top τ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτσ
  rw [← zpow_mod_orderOf, hord] at hτ ⊢
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [Nat.cast_ofNat, hk, zpow_zero] at hτ
    exact absurd rfl hτ
  · rw [Nat.cast_ofNat, hk, zpow_one]

section U4Out

set_option linter.unusedSectionVars false


variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4r_u4_outer_act (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) {K : Type} [Field K]
    (h : UnitaryFieldData 2 1 K) (Φ : hypSU h 2 0 ≃* ↥Gp) {e : E} (he : e ∉ Gp) :
    ∃ a : hypSU h 2 0, ∀ g : hypSU h 2 0,
      e * (Φ g : E) * e⁻¹ = (Φ (a * frobElt h g * a⁻¹) : E) := by
  haveI := hyp.normal
  set Θ : E →* MulAut (hypSU h 2 0) :=
    (MulAut.congr Φ.symm).toMonoidHom.comp (burnsideF4d_rho Gp) with hΘdef
  have hΘinj : Function.Injective Θ :=
    (MulAut.congr Φ.symm).injective.comp (burnsideF4d_rho_injective hyp.centralizer_trivial)
  have hΘapp : ∀ (e : E) (y : hypSU h 2 0), ((Φ (Θ e y) : ↥Gp) : E) = e * Φ y * e⁻¹ := by
    intro e y
    show ((Φ (Φ.symm (burnsideF4d_rho Gp e (Φ y))) : ↥Gp) : E) = _
    rw [MulEquiv.apply_symm_apply, burnsideF4d_rho_apply]
  obtain ⟨a, τ, hδ⟩ := burnsideF4m_U4_normalForm h (Θ e)
  have hΘb : Θ ((Φ a : ↥Gp) : E) = MulAut.conj a := by
    refine MulEquiv.ext fun y => Φ.injective (Subtype.ext ?_)
    rw [hΘapp, MulAut.conj_apply]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hτ : τ ≠ 1 := by
    intro h1
    apply he
    rw [h1, map_one, mul_one, ← hΘb] at hδ
    rw [hΘinj hδ]
    exact (Φ a).2
  have hτb := burnsideF4r_ringEquiv_eq_bar h τ hτ
  refine ⟨a, fun g => ?_⟩
  rw [← hΘapp, hδ, MulAut.mul_apply, MulAut.conj_apply, hτb]
  congr 3

theorem burnsideF4r_u4_mul_mem (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) {e e' : E} (he : e ∉ Gp)
    (he' : e' ∉ Gp) : e * e' ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, fK, h, Φ, -, -⟩ := burnsideF4m_U4_chart hyp
  obtain ⟨a, ha⟩ := burnsideF4r_u4_outer_act hyp h Φ he
  obtain ⟨a', ha'⟩ := burnsideF4r_u4_outer_act hyp h Φ he'
  set c : hypSU h 2 0 := a * frobElt h a' with hc
  have hact : ∀ g : hypSU h 2 0, (e * e') * (Φ g : E) * (e * e')⁻¹ = (Φ (c * g * c⁻¹) : E) := by
    intro g
    have e1 : (e * e') * (Φ g : E) * (e * e')⁻¹ = e * (e' * (Φ g : E) * e'⁻¹) * e⁻¹ := by group
    rw [e1, ha', ha]
    congr 2
    rw [hc]
    have hf : ∀ x y : hypSU h 2 0, frobElt h (x * y) = frobElt h x * frobElt h y := fun x y =>
      map_mul (frob h) x y
    have hfi : ∀ x : hypSU h 2 0, frobElt h x⁻¹ = (frobElt h x)⁻¹ := fun x => map_inv (frob h) x
    rw [hf, hf, hfi, frobElt_frobElt]
    group
  have hcen : (Φ c : E)⁻¹ * (e * e') ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨g, hg⟩ := Φ.surjective ⟨y, hy⟩
    have hy' : y = (Φ g : E) := by rw [hg]
    rw [hy']
    have h1 := hact g
    have h2 : (Φ (c * g * c⁻¹) : E) = (Φ c : E) * (Φ g : E) * (Φ c : E)⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2] at h1
    calc (Φ g : E) * ((Φ c : E)⁻¹ * (e * e'))
        = (Φ c : E)⁻¹ * ((Φ c : E) * (Φ g : E) * (Φ c : E)⁻¹) * (e * e') := by group
      _ = (Φ c : E)⁻¹ * ((e * e') * (Φ g : E) * (e * e')⁻¹) * (e * e') := by rw [h1]
      _ = (Φ c : E)⁻¹ * (e * e') * (Φ g : E) := by group
  rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcen
  have : e * e' = (Φ c : E) := by
    calc e * e' = (Φ c : E) * ((Φ c : E)⁻¹ * (e * e')) := by group
      _ = (Φ c : E) := by rw [hcen, mul_one]
  rw [this]
  exact (Φ c).2

theorem burnsideF4r_u4_graph_exists (hyp : HypF_4_4 .U4 2 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
    ∃ s ∈ M₁ ⊓ M₂, s ∉ Gp ∧ s * s = 1 ∧ hyp.toHypF_4_4g.chart.IsGraphInv s := by
  classical
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨e, -, he⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hGp)
  have hfits := hyp.toHypF_4_4g.chart.coordinatePayload_fits
  have hm := hyp.toHypF_4_4g.chart_matches
  unfold NativeChart.IsGraphInv NativeCoordinates.GraphAction
  generalize hcp : hyp.toHypF_4_4g.chart.coordinatePayload = cp at hfits ⊢
  cases cp with
  | classical c hk mk =>
    obtain rfl : c = .U4 := by
      cases c <;> first | rfl | exact absurd hk (by decide)
    obtain ⟨-, hpts, hlns, -, -⟩ := hfits
    set h := burnsideF4gU4_fieldData mk with hhdef
    set Φ := burnsideF4gU4_Phi mk with hΦdef
    have hPhi : ∀ g, Φ g = mk.transport (burnsideF4gU4_T mk g) := fun g =>
      congrArg (fun φ : hypSU h 2 0 →* ↥Gp => φ g) (burnsideF4gU4_Phi_toMonoidHom mk)
    have h1 : Gp ⊓ M₁ = (parP h).map (Gp.subtype.comp Φ.toMonoidHom) := by
      rw [hm.2.1, hpts, ← Subgroup.map_map]
      congr 1
      show (nativeParabolic .U4 (2 ^ 1) mk.field mk.basis false).map mk.transport = _
      rw [burnsideF4gU4_parabolic_false, Subgroup.map_map, burnsideF4gU4_Phi_toMonoidHom]
    have h2 : Gp ⊓ M₂ = (parP2 h).map (Gp.subtype.comp Φ.toMonoidHom) := by
      rw [hm.2.2, hlns, ← Subgroup.map_map]
      congr 1
      show (nativeParabolic .U4 (2 ^ 1) mk.field mk.basis true).map mk.transport = _
      rw [burnsideF4gU4_parabolic_true, Subgroup.map_map, burnsideF4gU4_Phi_toMonoidHom]
    obtain ⟨a, ha⟩ := burnsideF4r_u4_outer_act hyp.toHypF_4_4g h Φ he
    set s : E := (Φ a : E)⁻¹ * e with hsdef
    have hsact : ∀ g : hypSU h 2 0, s * (Φ g : E) * s⁻¹ = (Φ (frobElt h g) : E) := by
      intro g
      have e1 : s * (Φ g : E) * s⁻¹ = (Φ a : E)⁻¹ * (e * (Φ g : E) * e⁻¹) * (Φ a : E) := by
        rw [hsdef]
        group
      rw [e1, ha]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hsG : s ∉ Gp := by
      intro hs
      apply he
      have : e = (Φ a : E) * s := by rw [hsdef]; group
      rw [this]
      exact Gp.mul_mem (Φ a).2 hs
    have hs2 : s * s = 1 := by
      have hcen : s * s ∈ Subgroup.centralizer (Gp : Set E) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨g, hg⟩ := Φ.surjective ⟨y, hy⟩
        have hy' : y = (Φ g : E) := by rw [hg]
        rw [hy']
        have e2 : (s * s) * (Φ g : E) * (s * s)⁻¹ = (Φ g : E) := by
          calc (s * s) * (Φ g : E) * (s * s)⁻¹ = s * (s * (Φ g : E) * s⁻¹) * s⁻¹ := by group
            _ = (Φ g : E) := by rw [hsact, hsact, frobElt_frobElt]
        calc (Φ g : E) * (s * s) = ((s * s) * (Φ g : E) * (s * s)⁻¹) * (s * s) := by
              rw [e2]
          _ = (s * s) * (Φ g : E) := by group
      rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcen
      exact hcen
    set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
    have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
    have hrange : φ.range = Gp := by
      rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hsφ : ∀ g, s * φ g * s⁻¹ = φ (frobElt h g) := hsact
    have hff : ∀ g, frobElt h (frobElt h g) = g := frobElt_frobElt h
    have hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₁ ⊓ M₂, e = n * k := fun e => by
      obtain ⟨n, hn, k, hk, he⟩ := hyp.split e
      exact ⟨n, hn, k, hk, he⟩
    have hsM1 : s ∈ M₁ := by
      have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := parP h) (frobElt h) hsφ
        (fun g hg => frobElt_mem_parP h hg) hff
      rw [← h1] at hN
      have hsplit' : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₂ ⊓ M₁, e = n * k := fun e => by
        obtain ⟨n, hn, k, hk, he⟩ := hsplit e
        exact ⟨n, hn, k, ⟨hk.2, hk.1⟩, he⟩
      exact burnsideF4m_normalizer_inf_le (M₁ := M₂) hsplit' φ hφ hrange h1
        (fun g hg => burnsideF4d_selfNorm (isYAmalgamPair_parP_parP2 h) g
          (Subgroup.mem_normalizer_iff.mp hg)) hN
    have hsM2 : s ∈ M₂ := by
      have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := parP2 h) (frobElt h) hsφ
        (fun g hg => frobElt_mem_parP2 h hg) hff
      rw [← h2] at hN
      exact burnsideF4m_normalizer_inf_le (M₁ := M₁) hsplit φ hφ hrange h2
        (burnsideF4m_U4_parP2_selfNorm h) hN
    refine ⟨s, ⟨hsM1, hsM2⟩, hsG, hs2, hsG, hs2, Nat.one_pos, 1, ?_, ?_⟩
    ·
      refine ⟨1, ?_, fun A => ⟨A, by simp, rfl⟩⟩
      rw [map_one]
      exact Subgroup.map_id _
    ·
      simp only [NativeCoordinates.transport, NativeCoordinates.PureGraphAction,
        NativeRepresentativeAction]
      refine ⟨Or.inl trivial, h.bar, fun p => by rw [h.bar_apply], fun A => ?_⟩
      obtain ⟨g, rfl⟩ := (burnsideF4gU4_T mk).surjective A
      refine ⟨burnsideF4gU4_T mk (frobElt h g), ?_, ?_⟩
      · exact (burnsideF4m_u4_T_frob mk h.bar (fun p => by rw [h.bar_apply]) g).symm
      · show ((mk.transport (burnsideF4gU4_T mk (frobElt h g)) : ↥Gp) : E) =
          s * ((mk.transport (burnsideF4gU4_T mk g) : ↥Gp) : E) * s⁻¹
        rw [← hPhi, ← hPhi, hsact]
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

variable {Yc : Type} [Group Yc] {β : Cpl M₁ M₂ Yc} {M : Type} [Group M] {ε : Yc →* M}
  {z : M} {f : ℕ}

theorem burnsideF4r_A35_U4 (hyp : HypF_4_31 .U4 f Gp M₁ M₂ β ε z) (hf : f < 2)
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hj1 : j ≠ 1)
    (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  obtain rfl : f = 1 := by omega
  have hv : ∃ v : ↥(M₁ ⊓ M₂), (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ v ≠ 1 ∧ v * v = 1 ∧
      ¬ IsConj z (bM β ε v) := by
    by_cases hGp : Gp = ⊤
    · exact burnsideF4r_U4_top_nonfused hyp hf hGp
    · obtain ⟨s, hsM, hsG, hs2, hgraph⟩ := burnsideF4r_u4_graph_exists hyp.amalgam hGp
      exact burnsideF4r_nonfused_of_graph hyp (Or.inl rfl) rfl hsM hsG hs2 hgraph
        (fun e he => burnsideF4r_u4_mul_mem hyp.amalgam.toHypF_4_4g he hsG)
  obtain ⟨v, hvS, hv1, hv2, hnc⟩ := hv
  exact burnsideF4r_F_4_35_of_nonfused hyp (by decide) (by decide) hvS hv1 hv2 hnc i j hi hj
    hi1 hj1 hi2 hj2

end U4Out

end CFSG.ASVolI
