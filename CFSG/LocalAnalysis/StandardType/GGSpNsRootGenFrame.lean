module

public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
import CFSG.ClassicalGroups.Alternating.Transvections
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkCore
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockForm
import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.SpNsRootGen

open QuadraticMap CFSG.ClassicalGroups.Alternating CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_coherentFrame_of_selfCentralizing_gsp
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ)
    {E : Subgroup (Gsp (QuadraticMap.polarBilin Q))} (hE : CFSG.Open.IsElemAbelian p E)
    (hEΩ : E ≤ (omegaToGsp Q).range)
    (hsc : ∀ g : Gsp (QuadraticMap.polarBilin Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hW : ∀ W : Submodule F V, Module.finrank F W = 2 →
      (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W).Nondegenerate →
      ∃ g ∈ gspFixPerp (QuadraticMap.polarBilin Q) W, orderOf g = p) :
    ∃ (U : Fin ℓ → Submodule F V) (e : Fin ℓ → ↥(orthDerived Q)) (u : Fin ℓ → V) (c t : F),
      IsCoherentFrame Q p U e (E.comap (omegaToGsp Q)) u c t ∧ (⨆ j, U j) = ⊤ := by
  classical
  let E' : Subgroup ↥(orthDerived Q) := E.comap (omegaToGsp Q)
  have hωinj : Function.Injective (omegaToGsp Q) := omegaToGsp_injective Q
  have hmap : E'.map (omegaToGsp Q) = E := Subgroup.map_comap_eq_self hEΩ
  have hE'ab : CFSG.Open.IsElemAbelian p E' := hE.comap hωinj
  have hsc' : ∀ g : ↥(orthDerived Q), (∀ x ∈ E', g * x = x * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    refine Subgroup.mem_comap.mpr ?_
    refine hsc ((omegaToGsp Q) g) (fun x hx => ?_) ?_
    · rw [← hmap] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_mul, ← map_mul, hg y hy]
    · rw [← map_pow, hgp, map_one]
  obtain ⟨k, U, e, hframe, hcases⟩ :=
    exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq hdim hℓ hE'ab hsc'
  rcases hcases with ⟨hk, hspan⟩ | ⟨hk, f, f', hfZ, hf'Z, hQf, hQf', hpol⟩
  ·
    subst k
    obtain ⟨e', u, c, t, hcoh, -⟩ := exists_coherentFrame hframe hp hp2 hpq (by omega : 1 ≤ ℓ)
    exact ⟨U, e', u, c, t, hcoh, hspan⟩
  ·
    exfalso
    have hBalt : (QuadraticMap.polarBilin Q).IsAlt := fun v => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul,
        CharTwo.add_self_eq_zero]
    have hf0 : f ≠ 0 := by
      rintro rfl
      simpa using hpol
    have hff' : (QuadraticMap.polarBilin Q) f f' = 1 := by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hpol
    obtain ⟨hdimW, hWnd, -, hcompl, -, -⟩ :=
      (alternating_hyperbolic_splitting hBalt hQ hf0).2 f' hff'
    let W : Submodule F V := Submodule.span F {f, f'}
    have hdimW' : Module.finrank F W = 2 := hdimW
    have hWnd' : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W).Nondegenerate :=
      hWnd
    have hcompl' : IsCompl W (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W) :=
      hcompl
    have hWZ : W ≤ polarPerp Q (⨆ j, U j) := by
      show Submodule.span F {f, f'} ≤ polarPerp Q (⨆ j, U j)
      refine Submodule.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · exact hfZ
      · exact hf'Z
    have hEfixZ : ∀ x ∈ E, ∀ z ∈ polarPerp Q (⨆ j, U j), x.app z = z := by
      intro x hx z hz
      rw [← hmap] at hx
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
      rw [omegaToGsp_app]
      exact hframe.apply_eq_of_mem_polarPerp_iSup hd hz
    have hNW : CFSG.StandardType.SUTB.NondegOn (QuadraticMap.polarBilin Q) W := by
      intro m hm h
      have hzero : (⟨m, hm⟩ : W) = 0 := by
        refine hWnd'.2 ⟨m, hm⟩ fun n => ?_
        exact h n n.2
      exact congrArg Subtype.val hzero
    obtain ⟨g, hgfix, hgord⟩ := hW W hdimW' hWnd'
    have hgfix' : ∀ y ∈ W.orthogonalBilin (QuadraticMap.polarBilin Q), g.app y = y := by
      intro y hy
      exact mem_gspFixPerp.mp hgfix y (by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        exact Submodule.mem_orthogonalBilin.mp hy)
    have hgX : ∀ w ∈ W, g.app w ∈ W := by
      intro w hw
      rw [← CFSG.StandardType.WitOmBlk.orthogonalBilin_orthogonalBilin hQ W]
      rw [Submodule.mem_orthogonalBilin]
      intro y hy
      rw [Submodule.mem_orthogonalBilin] at hy
      have hyinv : g⁻¹ ∈ gspFixPerp (QuadraticMap.polarBilin Q) W :=
        (gspFixPerp (QuadraticMap.polarBilin Q) W).inv_mem hgfix
      have hyfix : g⁻¹.app y = y := mem_gspFixPerp.mp hyinv y (by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        exact hy)
      have hsymm : (QuadraticMap.polarBilin Q) y w = (QuadraticMap.polarBilin Q) w y := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
          QuadraticMap.polar_comm]
      calc (QuadraticMap.polarBilin Q) y (g.app w)
          = (QuadraticMap.polarBilin Q) (g.app (g⁻¹.app y)) (g.app w) := by
            rw [Gsp.app_app_inv]
        _ = (QuadraticMap.polarBilin Q) (g⁻¹.app y) w := Gsp.form_app g _ _
        _ = (QuadraticMap.polarBilin Q) y w := by rw [hyfix]
        _ = (QuadraticMap.polarBilin Q) w y := hsymm
        _ = 0 := hy w hw
    have hcomm : ∀ x ∈ E, g * x = x * g := by
      intro x hx
      have hxW : ∀ w ∈ W, x.app w = w := fun w hw => hEfixZ x hx w (hWZ hw)
      have hxP : ∀ y ∈ W.orthogonalBilin (QuadraticMap.polarBilin Q),
          x.app y ∈ W.orthogonalBilin (QuadraticMap.polarBilin Q) := by
        intro y hy
        rw [Submodule.mem_orthogonalBilin] at hy ⊢
        intro w hw
        have hwfix : x⁻¹.app w = w := by
          have h1 : x⁻¹.app (x.app w) = x⁻¹.app w := congrArg (fun t => x⁻¹.app t) (hxW w hw)
          rw [Gsp.app_inv_app] at h1
          exact h1.symm
        calc (QuadraticMap.polarBilin Q) w (x.app y)
            = (QuadraticMap.polarBilin Q) (x.app (x⁻¹.app w)) (x.app y) := by
              rw [Gsp.app_app_inv]
          _ = (QuadraticMap.polarBilin Q) (x⁻¹.app w) y := Gsp.form_app x _ _
          _ = (QuadraticMap.polarBilin Q) w y := by rw [hwfix]
          _ = 0 := hy w hw
      have hlin := CFSG.StandardType.WitOmBlk.commute_of_fix (Q := Q) hNW
        (g := LinearMap.GeneralLinearGroup.toLinearEquiv (g : LinearMap.GeneralLinearGroup F V))
        (h := LinearMap.GeneralLinearGroup.toLinearEquiv (x : LinearMap.GeneralLinearGroup F V))
        hgfix' hgX hxW hxP
      refine Gsp.ext' fun v => ?_
      have hv := congrArg (fun φ : V ≃ₗ[F] V => φ v) hlin
      simpa [Gsp.app, LinearEquiv.mul_apply,
        LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using hv
    have hgp : g ^ p = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
    have hgE : g ∈ E := hsc g hcomm hgp
    have hgWfix : ∀ w ∈ W, g.app w = w := fun w hw => hEfixZ g hgE w (hWZ hw)
    have hg1 : g = 1 := by
      refine Gsp.ext' fun v => ?_
      have hv : v ∈ W ⊔ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W := by
        rw [hcompl'.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      have hzfix : g.app z = z := hgfix' z (by
        rw [Submodule.mem_orthogonalBilin]
        rw [LinearMap.BilinForm.mem_orthogonal_iff] at hz
        exact hz)
      rw [Gsp.map_add, hgWfix w hw, hzfix, Gsp.app_one]
    rw [hg1, orderOf_one] at hgord
    exact hp.ne_one hgord.symm

end CFSG.StandardType.SpNsRootGen

end
