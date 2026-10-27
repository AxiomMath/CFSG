module

public import CFSG.Milestones.ASVolI.F431.RA35Out
public import CFSG.Milestones.ASVolI.F431.RA35U5
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LocalAnalysis.EvenBN.U5
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF.ClassicalRoots

section U5Out

set_option linter.unusedSectionVars false


variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4r_u5_frob_frob {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (y : hypPSU h 2 1) :
    fieldP h (Un.OL5.bar5 h) (fieldP h (Un.OL5.bar5 h) y) = y := by
  have e : fieldP h (Un.OL5.bar5 h) * fieldP h (Un.OL5.bar5 h) = 1 := by
    rw [← map_mul, Un.OL5.fld5_bar_mul_self, map_one]
  have := congrArg (fun β : MulAut (hypPSU h 2 1) => β y) e
  simpa only [MulAut.mul_apply, MulAut.one_apply] using this

theorem burnsideF4r_u5_outer_act (hyp : HypF_4_4g .U5 2 1 Gp M₁ M₂) {K : Type} [Field K]
    (h : UnitaryFieldData 2 1 K) (Ψ : hypPSU h 2 1 ≃* ↥Gp) {e : E} (he : e ∉ Gp) :
    ∃ a : hypPSU h 2 1, ∀ y : hypPSU h 2 1,
      e * (Ψ y : E) * e⁻¹ = (Ψ (a * fieldP h (Un.OL5.bar5 h) y * a⁻¹) : E) := by
  haveI := hyp.normal
  set Θ : E →* MulAut (hypPSU h 2 1) :=
    (MulAut.congr Ψ.symm).toMonoidHom.comp (burnsideF4d_rho Gp) with hΘdef
  have hΘinj : Function.Injective Θ :=
    (MulAut.congr Ψ.symm).injective.comp (burnsideF4d_rho_injective hyp.centralizer_trivial)
  have hΘapp : ∀ (e : E) (y : hypPSU h 2 1), ((Ψ (Θ e y) : ↥Gp) : E) = e * Ψ y * e⁻¹ := by
    intro e y
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp e (Ψ y))) : ↥Gp) : E) = _
    rw [MulEquiv.apply_symm_apply, burnsideF4d_rho_apply]
  obtain ⟨g, τ, hδ⟩ := burnsideF4m_u5_normalForm h (Θ e)
  have hΘb : Θ ((Ψ (hypProj h 2 1 g) : ↥Gp) : E) = innM h g := by
    refine MulEquiv.ext fun y => Ψ.injective (Subtype.ext ?_)
    rw [hΘapp, innM_apply]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hτ : τ ≠ 1 := by
    intro h1
    apply he
    rw [h1, map_one, mul_one, ← hΘb] at hδ
    rw [hΘinj hδ]
    exact (Ψ (hypProj h 2 1 g)).2
  have hτb : τ = Un.OL5.bar5 h := Un.OL5.fld5_eq_bar h (burnsideF4m_ringEquiv_sq h τ) hτ
  refine ⟨hypProj h 2 1 g, fun y => ?_⟩
  rw [← hΘapp, hδ, MulAut.mul_apply, innM_apply, hτb]

theorem burnsideF4r_u5_mul_mem (hyp : HypF_4_4g .U5 2 1 Gp M₁ M₂) {e e' : E} (he : e ∉ Gp)
    (he' : e' ∉ Gp) : e * e' ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, fK, h, Ψ, -, -⟩ := burnsideF4m_U5_chart hyp
  obtain ⟨a, ha⟩ := burnsideF4r_u5_outer_act hyp h Ψ he
  obtain ⟨a', ha'⟩ := burnsideF4r_u5_outer_act hyp h Ψ he'
  have hFF := burnsideF4r_u5_frob_frob h
  set F := fieldP h (Un.OL5.bar5 h) with hF
  set c : hypPSU h 2 1 := a * F a' with hc
  have hact : ∀ y : hypPSU h 2 1, (e * e') * (Ψ y : E) * (e * e')⁻¹ = (Ψ (c * y * c⁻¹) : E) := by
    intro y
    have e1 : (e * e') * (Ψ y : E) * (e * e')⁻¹ = e * (e' * (Ψ y : E) * e'⁻¹) * e⁻¹ := by group
    rw [e1, ha', ha]
    congr 2
    rw [hc, map_mul, map_mul, map_inv, hFF]
    group
  have hcen : (Ψ c : E)⁻¹ * (e * e') ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨g, hg⟩ := Ψ.surjective ⟨y, hy⟩
    have hy' : y = (Ψ g : E) := by rw [hg]
    rw [hy']
    have h1 := hact g
    have h2 : (Ψ (c * g * c⁻¹) : E) = (Ψ c : E) * (Ψ g : E) * (Ψ c : E)⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2] at h1
    calc (Ψ g : E) * ((Ψ c : E)⁻¹ * (e * e'))
        = (Ψ c : E)⁻¹ * ((Ψ c : E) * (Ψ g : E) * (Ψ c : E)⁻¹) * (e * e') := by group
      _ = (Ψ c : E)⁻¹ * ((e * e') * (Ψ g : E) * (e * e')⁻¹) * (e * e') := by rw [h1]
      _ = (Ψ c : E)⁻¹ * (e * e') * (Ψ g : E) := by group
  rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcen
  have : e * e' = (Ψ c : E) := by
    calc e * e' = (Ψ c : E) * ((Ψ c : E)⁻¹ * (e * e')) := by group
      _ = (Ψ c : E) := by rw [hcen, mul_one]
  rw [this]
  exact (Ψ c).2

theorem burnsideF4r_u5_graph_exists (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
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
    obtain rfl : c = .U5 := by
      cases c <;> first | rfl | exact absurd hk (by decide)
    obtain ⟨-, hpts, hlns, -, -⟩ := hfits
    set h := burnsideF4m_U5_fieldData mk with hhdef
    set Ψ := burnsideF4m_U5_Psi mk with hΨdef
    obtain ⟨hpar1, hpar2⟩ := burnsideF4m_U5_Psi_parabolics mk
    have h1' : Gp ⊓ M₁ = (mk.parabolic false).map Gp.subtype := by
      rw [hm.2.1]
      exact hpts
    have h2' : Gp ⊓ M₂ = (mk.parabolic true).map Gp.subtype := by
      rw [hm.2.2]
      exact hlns
    have h1 : Gp ⊓ M₁ = (u5PtP h).map (Gp.subtype.comp Ψ.toMonoidHom) := by
      rw [h1', hpar1, Subgroup.map_map]
    have h2 : Gp ⊓ M₂ = (u5LnP h).map (Gp.subtype.comp Ψ.toMonoidHom) := by
      rw [h2', hpar2, Subgroup.map_map]
    obtain ⟨a, ha⟩ := burnsideF4r_u5_outer_act hyp.toHypF_4_4g h Ψ he
    have hFF := burnsideF4r_u5_frob_frob h
    set F := fieldP h (Un.OL5.bar5 h) with hF
    set s : E := (Ψ a : E)⁻¹ * e with hsdef
    have hsact : ∀ y : hypPSU h 2 1, s * (Ψ y : E) * s⁻¹ = (Ψ (F y) : E) := by
      intro y
      have e1 : s * (Ψ y : E) * s⁻¹ = (Ψ a : E)⁻¹ * (e * (Ψ y : E) * e⁻¹) * (Ψ a : E) := by
        rw [hsdef]
        group
      rw [e1, ha]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hsG : s ∉ Gp := by
      intro hs
      apply he
      have : e = (Ψ a : E) * s := by rw [hsdef]; group
      rw [this]
      exact Gp.mul_mem (Ψ a).2 hs
    have hs2 : s * s = 1 := by
      have hcen : s * s ∈ Subgroup.centralizer (Gp : Set E) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨g, hg⟩ := Ψ.surjective ⟨y, hy⟩
        have hy' : y = (Ψ g : E) := by rw [hg]
        rw [hy']
        have e2 : (s * s) * (Ψ g : E) * (s * s)⁻¹ = (Ψ g : E) := by
          calc (s * s) * (Ψ g : E) * (s * s)⁻¹ = s * (s * (Ψ g : E) * s⁻¹) * s⁻¹ := by group
            _ = (Ψ g : E) := by rw [hsact, hsact, hFF]
        calc (Ψ g : E) * (s * s) = ((s * s) * (Ψ g : E) * (s * s)⁻¹) * (s * s) := by
              rw [e2]
          _ = (s * s) * (Ψ g : E) := by group
      rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcen
      exact hcen
    set φ : hypPSU h 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
    have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
    have hrange : φ.range = Gp := by
      rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Ψ.surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hsφ : ∀ y, s * φ y * s⁻¹ = φ (F y) := hsact
    have hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₁ ⊓ M₂, e = n * k := fun e => by
      obtain ⟨n, hn, k, hk, he⟩ := hyp.split e
      exact ⟨n, hn, k, hk, he⟩
    have hyam := (u5_yamStd (h := h)).isYAmalgamPair
    have hself1 : ∀ g : hypPSU h 2 1,
        g ∈ Subgroup.normalizer ((u5PtP h : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) →
          g ∈ u5PtP h :=
      fun g hg => burnsideF4d_selfNorm hyam g (Subgroup.mem_normalizer_iff.mp hg)
    have hyam' : IsYAmalgamPair (hypProjUnitriangular h 2 1) (u5LnP h) (u5PtP h) := by
      refine ⟨hyam.1, hyam.2.1.symm, fun X => ?_⟩
      rw [hyam.2.2 X, or_comm]
    have hself2 : ∀ g : hypPSU h 2 1,
        g ∈ Subgroup.normalizer ((u5LnP h : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) →
          g ∈ u5LnP h :=
      fun g hg => burnsideF4d_selfNorm hyam' g (Subgroup.mem_normalizer_iff.mp hg)
    have hsM1 : s ∈ M₁ := by
      have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := u5PtP h) F hsφ
        (fun g hg => (Un.OL5.fStab5_Pt h (Un.OL5.bar5 h) g).2 hg) hFF
      rw [← h1] at hN
      have hsplit' : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₂ ⊓ M₁, e = n * k := fun e => by
        obtain ⟨n, hn, k, hk, he⟩ := hsplit e
        exact ⟨n, hn, k, ⟨hk.2, hk.1⟩, he⟩
      exact burnsideF4m_normalizer_inf_le (M₁ := M₂) hsplit' φ hφ hrange h1 hself1 hN
    have hsM2 : s ∈ M₂ := by
      have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := u5LnP h) F hsφ
        (fun g hg => (Un.OL5.fStab5_Ln h (Un.OL5.bar5 h) g).2 hg) hFF
      rw [← h2] at hN
      exact burnsideF4m_normalizer_inf_le (M₁ := M₁) hsplit φ hφ hrange h2 hself2 hN
    refine ⟨s, ⟨hsM1, hsM2⟩, hsG, hs2, hsG, hs2, Nat.one_pos, 1, ?_, ?_⟩
    ·
      refine ⟨1, ?_, fun A => ⟨A, by simp, rfl⟩⟩
      rw [map_one]
      exact Subgroup.map_id _
    ·
      simp only [NativeCoordinates.transport, NativeCoordinates.PureGraphAction,
        NativeRepresentativeAction]
      refine ⟨Or.inr trivial, h.bar, fun p => by rw [h.bar_apply], fun A => ?_⟩
      obtain ⟨g, rfl⟩ := (burnsideF4m_U5_T mk).surjective A
      refine ⟨burnsideF4m_U5_T mk (fieldAut h (Un.OL5.bar5 h) g), ?_, ?_⟩
      · exact (burnsideF4m_u5_T_frob mk h.bar (fun p => by rw [h.bar_apply]) g).symm
      · show ((mk.transport (burnsideF4m_U5_T mk (fieldAut h (Un.OL5.bar5 h) g)) : ↥Gp) : E) =
          s * ((mk.transport (burnsideF4m_U5_T mk g) : ↥Gp) : E) * s⁻¹
        rw [← burnsideF4m_U5_Psi_proj, ← burnsideF4m_U5_Psi_proj, hsact, hF, fieldP_apply]
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

variable {Yc : Type} [Group Yc] {β : Cpl M₁ M₂ Yc} {M : Type} [Group M] {ε : Yc →* M}
  {z : M} {f : ℕ}

theorem burnsideF4r_A35_U5 (hyp : HypF_4_31 .U5 f Gp M₁ M₂ β ε z) (hf : f < 2)
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hj1 : j ≠ 1)
    (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  obtain rfl : f = 1 := by omega
  have hv : ∃ v : ↥(M₁ ⊓ M₂), (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ v ≠ 1 ∧ v * v = 1 ∧
      ¬ IsConj z (bM β ε v) := by
    by_cases hGp : Gp = ⊤
    · exact burnsideF4r_U5_top_nonfused hyp hGp
    · obtain ⟨s, hsM, hsG, hs2, hgraph⟩ := burnsideF4r_u5_graph_exists hyp.amalgam hGp
      exact burnsideF4r_nonfused_of_graph hyp (Or.inr rfl) rfl hsM hsG hs2 hgraph
        (fun e he => burnsideF4r_u5_mul_mem hyp.amalgam.toHypF_4_4g he hsG)
  obtain ⟨v, hvS, hv1, hv2, hnc⟩ := hv
  exact burnsideF4r_F_4_35_of_nonfused hyp (by decide) (by decide) hvS hv1 hv2 hnc i j hi hj
    hi1 hj1 hi2 hj2

end U5Out

end CFSG.ASVolI
