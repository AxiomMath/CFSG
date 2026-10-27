module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAmbDSel
public import CFSG.LocalAnalysis.StandardType.GGQTwoDLeafNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDLeafTail
public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbSpan
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosAmb
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrPosE6
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2ad_four_ne : ((4 : ℤ) : ZMod 3) ≠ 0 := by decide

theorem ggQ2_gammaNbr_of_ambD (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hsel : GGQ2NbrAmbDSel p Bs x y L K) {u : ↥Bs}
    (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) : GGGammaAt p B Bs x L D J u := by
  subst hp
  classical
  obtain ⟨M, hbas, k, hk, f, hf⟩ := hsel
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  have hG0K : K ≤ ggG0 3 B x L D J := le_ggG0_of_ggNbr hnb
  have hG0L : L ≤ ggG0 3 B x L D J := le_ggG0_left _ _ _ _ _ _
  have hG0KLK : K ⊔ (L ⊔ K) ≤ ggG0 3 B x L D J := sup_le hG0K (sup_le hG0L hG0K)
  have hDyx : D = Subgroup.closure ({y, x} : Set G) := by
    rw [hnb.2.1, Set.pair_comm]
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : FiniteDimensional (ZMod 3) M.V := Module.Finite.of_finite
  intro φ hφ hφu
  have finL : (∃ w' ∈ M.toLin.parab {k | k ≠ M.a}, ∀ z : M.V,
      ∀ v ∈ Submodule.span (ZMod 3) {M.xV, z},
        w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, z}) →
      φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
    rintro ⟨w', hw', h⟩
    obtain ⟨ψ, hψ, hD⟩ :=
      ggQ2xa_bridge M hDyx (le_of_eq M.parabL_L) ⟨w', hw', fun v hv => h M.yV v hv⟩
    exact ggQ2_finish_of_le hLB hP hS hAJS hK1 hnb hG0K hφ hψ hD
  have finW : (∃ w' ∈ M.toLin.weyl, ∀ z : M.V, ∀ v ∈ Submodule.span (ZMod 3) {M.xV, z},
        w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, z}) →
      φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
    rintro ⟨w', hw', h⟩
    obtain ⟨ψ, hψ, hD⟩ :=
      ggQ2xa_bridge (S := Set.univ) M hDyx M.weyl_le ⟨w', hw', fun v hv => h M.yV v hv⟩
    exact ggQ2_finish_of_le hLB hP hS hAJS hK1 hnb hG0KLK hφ hψ hD
  have hφy : φ ⟨y, M.hx⟩ ∈ Subgroup.zpowers (⟨y, M.hx⟩ : ↥Bs) := ggQ2xa_x_stable M.hx hu hφu
  have hφyV : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV} := by
    have h1 : ggLin (p := 3) M.model φ M.xV = M.model (Additive.ofMul (φ ⟨y, M.hx⟩)) := by
      rw [GGQTwoAmbModel.xV, ggLin_apply_ofMul]
    rw [h1]
    exact ggQ2xa_model_mem_span M (φ ⟨y, M.hx⟩) ⟨y, M.hx⟩ hφy
  have hyne : y ≠ 1 := hnb.1.2.2.1
  have hy0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨y, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hyne (Subtype.ext_iff.mp h1)
  have hdet : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) ≠ 0 := by
    have hsub : M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι)) =
        (CartanMatrix.D (2 * k)).submatrix f.symm f.symm := by
      ext i j
      simp only [Matrix.submatrix_apply]
      rw [← hf (f.symm i) (f.symm j)]
      simp
    rw [hsub, Matrix.det_submatrix_equiv_self, CartanMatrix.D_det (by omega)]
    exact ggQ2ad_four_ne
  have hV := M.span_insert_xV rfl hbas hdet hy0
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (M.V ≃ₗ[ZMod 3] M.V),
      A = (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model) := ⟨_, rfl⟩
  have hWA : M.toLin.weyl ≤ A := by
    rw [hAdef]
    exact M.weyl_le.trans (Subgroup.map_mono (ggAutomizer_mono Bs le_top))
  have hΦ : (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V) ∈ A := by
    rw [hAdef]
    exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
  have hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ M.a} => M.coroot i) :=
    hbas.1.comp (fun i : {k // k ≠ M.a} => (i : M.ι)) Subtype.val_injective
  have hnorm : ∀ g ∈ A, g M.xV ∈ Submodule.span (ZMod 3) {M.xV} →
      ∃ (π : {i // i ≠ M.toLin.a} ≃ {i // i ≠ M.toLin.a}) (c : ZMod 3), c ≠ 0 ∧
        (∀ i j : {i // i ≠ M.toLin.a}, M.toLin.cartan (π i) (π j) = M.toLin.cartan i j) ∧
        ∃ w ∈ M.toLin.parab {i | i ≠ M.toLin.a}, ∀ i : {i // i ≠ M.toLin.a},
          g (M.toLin.coroot i) = c • w (M.toLin.coroot (π i)) := by
    intro g hg hgx
    rw [hAdef, Subgroup.mem_map] at hg
    obtain ⟨φ', hφ', rfl⟩ := hg
    exact ggQ2_tbwNormNbrAmb_of_dLeaf hLB hP h5 hS rfl hI1 hnb M hind (n := 2 * k) (by omega) f hf
      hφ' hgx
  rcases ggQ2_dLeaf_stablePlane M.toLin hbas hk f hf M.xV hy0 M.fixed_lin hV A hWA hnorm hΦ hφyV
    with h | h
  · exact finL h
  · exact finW h

theorem ggQ2_gammaNbrPosAmbDCell_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrPosAmbDCell := by
  intro G _ _ p B Bs x L D J hS hp hI _ _ y K hnb _ _ hsel u hu
  exact ggQ2_gammaNbr_of_ambD hLB hP h5 hS hp hI hnb hsel hu

@[expose] def GGQ2GammaNbrPosRestAmbDInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    ¬ GGQ2NbrE6Sel p Bs x y D L J K → ¬ GGQ2SelInner G p Bs y J K →
    ¬ GGQ2NbrAmbDSel p Bs x y L K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

theorem ggQ2_gammaNbrPosRest_of_ambD (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (h : GGQ2GammaNbrPosRestAmbDInput) :
    GGQ2GammaNbrPosRestInput := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb hrow hleaf hE6 hin u hu
  by_cases hsel : GGQ2NbrAmbDSel p Bs x y L K
  · exact ggQ2_gammaNbrPosAmbDCell_holds hLB hP h5 hS hp hI hxL hnb hrow hleaf hsel hu
  · exact h hS hp hI hxL hnb hrow hleaf hE6 hin hsel hu

end CFSG.StandardType

end
