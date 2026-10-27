module

public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.Assembly.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.SpNsRootGen

open QuadraticMap CFSG.ClassicalGroups.Alternating CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.RankThree.PartOne.KCOrthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

section Helpers

variable {p k : ℕ} {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)}

private theorem maps_to_of_mem_gspFixPerp {W : Submodule F V} {g : Gsp (polarBilin Q)}
    (hQ : (polarBilin Q).Nondegenerate) (hg : g ∈ gspFixPerp (polarBilin Q) W) :
    ∀ u ∈ W, g.app u ∈ W := by
  intro u hu
  have hmem : g.app u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
        (LinearMap.BilinForm.orthogonal (polarBilin Q) W) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have hwfix : g⁻¹.app w = w := (mem_gspFixPerp.mp (inv_mem hg)) w hw
    have h1 : (polarBilin Q) w (g.app u) = (polarBilin Q) (g⁻¹.app w) u := by
      calc (polarBilin Q) w (g.app u)
          = (polarBilin Q) (g.app (g⁻¹.app w)) (g.app u) := by rw [Gsp.app_app_inv]
        _ = (polarBilin Q) (g⁻¹.app w) u := Gsp.form_app g _ _
    rw [h1, hwfix]
    exact isRefl_polarBilin Q u w (LinearMap.BilinForm.mem_orthogonal_iff.mp hw u hu)
  rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q) W] at hmem

private theorem apply_of_perp_of_ne (hF : IsPlaneFrame Q p U e E) {a b : Fin k} (hb : b ≠ a)
    {x : V} (hx : x ∈ U a) : (e b : V ≃ₗ[F] V) x = x := by
  refine hF.apply_of_perp b x (mem_polarPerp_iff.mpr fun y hy => ?_)
  rw [QuadraticMap.polar_comm]
  exact hF.perp a b (fun h => hb h.symm) x hx y hy

private theorem apply_mem_polarPerp_of_ne (hF : IsPlaneFrame Q p U e E) {a b : Fin k}
    (hb : b ≠ a) {w : V} (hw : w ∈ polarPerp Q (U a)) :
    (e b : V ≃ₗ[F] V) w ∈ polarPerp Q (U a) := by
  refine mem_polarPerp_iff.mpr fun y hy => ?_
  have hy' : (e b : V ≃ₗ[F] V) y = y := apply_of_perp_of_ne hF hb hy
  calc QuadraticMap.polar Q y ((e b : V ≃ₗ[F] V) w)
      = QuadraticMap.polar Q ((e b : V ≃ₗ[F] V) y) ((e b : V ≃ₗ[F] V) w) := by rw [hy']
    _ = QuadraticMap.polar Q y w := by
        rw [← polarBilin_apply_apply, ← polarBilin_apply_apply]
        exact Gsp.form_app (omegaToGsp Q (e b)) y w
    _ = 0 := mem_polarPerp_iff.mp hw y hy

private theorem apply_mem_polarPerp_of_commute (hF : IsPlaneFrame Q p U e E) {b : Fin k}
    {h : Gsp (polarBilin Q)}
    (hcomm : omegaToGsp Q (e b) * h = h * omegaToGsp Q (e b)) {x : V}
    (hx : x ∈ polarPerp Q (U b)) : h.app x ∈ polarPerp Q (U b) := by
  have hxfix : (e b : V ≃ₗ[F] V) x = x := by
    rw [← hF.fixedSpace_eq_polarPerp b] at hx
    exact mem_fixedSpace.mp hx
  rw [← hF.fixedSpace_eq_polarPerp b, mem_fixedSpace]
  have h2 := congrArg (fun z : Gsp (polarBilin Q) => z.app x) hcomm
  rw [Gsp.app_mul, Gsp.app_mul, omegaToGsp_app, omegaToGsp_app, hxfix] at h2
  exact h2

private theorem commute_omegaToGsp_of_mem_gspFixPerp (hQ : (polarBilin Q).Nondegenerate)
    (hF : IsPlaneFrame Q p U e E) {a b : Fin k} (hb : b ≠ a)
    {g : Gsp (polarBilin Q)} (hg : g ∈ gspFixPerp (polarBilin Q) (U a)) :
    omegaToGsp Q (e b) * g = g * omegaToGsp Q (e b) := by
  have hga : ∀ u ∈ U a, g.app u ∈ U a := maps_to_of_mem_gspFixPerp hQ hg
  have hfixa : ∀ y ∈ U a, (e b : V ≃ₗ[F] V) y = y := fun y hy => apply_of_perp_of_ne hF hb hy
  have hfixw : ∀ w ∈ polarPerp Q (U a), g.app w = w := fun w hw => mem_gspFixPerp.mp hg w hw
  have hpresw : ∀ w ∈ polarPerp Q (U a), (e b : V ≃ₗ[F] V) w ∈ polarPerp Q (U a) :=
    fun w hw => apply_mem_polarPerp_of_ne hF hb hw
  refine Gsp.ext' fun v => ?_
  rw [Gsp.app_mul, Gsp.app_mul, omegaToGsp_app, omegaToGsp_app]
  have hv : v ∈ U a ⊔ polarPerp Q (U a) := by
    rw [(isCompl_polarPerp (hF.nondeg a)).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  calc (e b : V ≃ₗ[F] V) (g.app (u + w))
      = (e b : V ≃ₗ[F] V) (g.app u + w) := by rw [Gsp.map_add, hfixw w hw]
    _ = (e b : V ≃ₗ[F] V) (g.app u) + (e b : V ≃ₗ[F] V) w := map_add _ _ _
    _ = g.app u + (e b : V ≃ₗ[F] V) w := by rw [hfixa (g.app u) (hga u hu)]
    _ = g.app u + g.app ((e b : V ≃ₗ[F] V) w) := by
        rw [hfixw ((e b : V ≃ₗ[F] V) w) (hpresw w hw)]
    _ = g.app (u + (e b : V ≃ₗ[F] V) w) := (Gsp.map_add g u _).symm
    _ = g.app ((e b : V ≃ₗ[F] V) u + (e b : V ≃ₗ[F] V) w) := by rw [hfixa u hu]
    _ = g.app ((e b : V ≃ₗ[F] V) (u + w)) := by rw [map_add]

private theorem iInf_polarPerp_erase_eq (hQ : (polarBilin Q).Nondegenerate)
    (hF : IsPlaneFrame Q p U e E) (htop : (⨆ j, U j) = ⊤) (a : Fin k) :
    (⨅ b ∈ Finset.univ.erase a, polarPerp Q (U b)) = U a := by
  have hV : Module.finrank F V = 2 * k := by
    have h : Module.finrank F ↥(⨆ j, U j) = 2 * k := by
      rw [show (⨆ j, U j) = ⨆ j ∈ Finset.univ, U j by simp]
      simpa using hF.toIsPlaneSystem.finrank_biSup (Finset.univ)
    rw [htop, finrank_top] at h
    exact h
  have hP : Module.finrank F (polarPerp Q (U a)) = 2 * (Finset.univ.erase a).card := by
    rw [finrank_polarPerp hQ, hF.finrank_eq a, hV,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  have hWle : (⨆ b ∈ Finset.univ.erase a, U b) ≤ polarPerp Q (U a) :=
    hF.toIsPlaneSystem.biSup_le_polarPerp (by simp)
  have hWeq : (⨆ b ∈ Finset.univ.erase a, U b) = polarPerp Q (U a) := by
    refine Submodule.eq_of_le_of_finrank_eq hWle ?_
    rw [hF.toIsPlaneSystem.finrank_biSup, hP]
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q)
        (⨆ b ∈ Finset.univ.erase a, U b) =
      ⨅ b ∈ Finset.univ.erase a, polarPerp Q (U b) := by
    change Submodule.orthogonalBilin (polarBilin Q)
      (⨆ b, ⨆ (_ : b ∈ Finset.univ.erase a), U b) = _
    rw [Submodule.orthogonalBilin_iSup]
    simp only [Submodule.orthogonalBilin_iSup, polarPerp]
    rfl
  calc (⨅ b ∈ Finset.univ.erase a, polarPerp Q (U b))
      = LinearMap.BilinForm.orthogonal (polarBilin Q)
          (⨆ b ∈ Finset.univ.erase a, U b) := horth.symm
    _ = LinearMap.BilinForm.orthogonal (polarBilin Q) (polarPerp Q (U a)) := by rw [hWeq]
    _ = U a := LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q) (U a)

end Helpers

theorem isComponentOf_gspFixPerp_frame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p k : ℕ} {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e E) (htop : (⨆ j, U j) = ⊤)
    (a : Fin k) {X : Set (Gsp (QuadraticMap.polarBilin Q))}
    (hXe : ∀ b, b ≠ a → omegaToGsp Q (e b) ∈ X)
    (hX : X ⊆ Subgroup.closure ((fun b => omegaToGsp Q (e b)) '' {b | b ≠ a}))
    (hq : CFSG.Assembly.IsQuasisimple ↥(gspFixPerp (QuadraticMap.polarBilin Q) (U a))) :
    CFSG.Assembly.IsComponentOf (gspFixPerp (QuadraticMap.polarBilin Q) (U a))
      (Subgroup.centralizer X) := by
  have hle : gspFixPerp (polarBilin Q) (U a) ≤ Subgroup.centralizer X := by
    intro g hg
    have hgc : g ∈ Subgroup.centralizer
        (Subgroup.closure ((fun b => omegaToGsp Q (e b)) '' {b | b ≠ a})) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      exact commute_omegaToGsp_of_mem_gspFixPerp hQ hF hb hg
    exact Subgroup.centralizer_le hX hgc
  have hpres : ∀ h ∈ Subgroup.centralizer X, ∀ u ∈ U a, h.app u ∈ U a := by
    intro h hh u hu
    have hcomm : ∀ b, b ≠ a → omegaToGsp Q (e b) * h = h * omegaToGsp Q (e b) :=
      fun b hb => Subgroup.mem_centralizer_iff.mp hh (omegaToGsp Q (e b)) (hXe b hb)
    have hu' : ∀ b, b ≠ a → u ∈ polarPerp Q (U b) := by
      intro b hb
      refine mem_polarPerp_iff.mpr fun y hy => ?_
      rw [QuadraticMap.polar_comm]
      exact hF.perp a b (fun h => hb h.symm) u hu y hy
    have hmem : h.app u ∈ ⨅ b ∈ Finset.univ.erase a, polarPerp Q (U b) := by
      simp only [Submodule.mem_iInf, Finset.mem_erase]
      intro b hb
      exact apply_mem_polarPerp_of_commute hF (hcomm b hb.1) (hu' b hb.1)
    rwa [iInf_polarPerp_erase_eq hQ hF htop a] at hmem
  have hnormal :
      ((gspFixPerp (polarBilin Q) (U a)).subgroupOf (Subgroup.centralizer X)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact conj_mem_gspFixPerp (hpres k hk) hh
  exact ⟨hle, CFSG.Assembly.IsSubnormal.step hle hnormal (CFSG.Assembly.IsSubnormal.refl _),
    hq⟩

end CFSG.StandardType.SpNsRootGen

end
