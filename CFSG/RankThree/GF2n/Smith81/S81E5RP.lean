module

public import CFSG.RankThree.GF2n.Smith81.S81E5Tr
public import CFSG.RankThree.GF2n.Smith81.S81E7Reg
public import CFSG.RankThree.GF2n.Smith81.S81BBridge
public import CFSG.RankThree.GF2n.Smith81.S81LS5

public section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


variable {K : Type} [Field K]

theorem IsRootElt.conj_E {g a : (Module.End K (V K))ˣ} (hg : IsRootElt g) (ha : a ∈ EGrp K) :
    IsRootElt (a * g * a⁻¹) := by
  obtain ⟨h, hh, γ, c, hγ, hc, rfl⟩ := hg
  refine ⟨a * h, mul_mem ha hh, γ, c, hγ, hc, ?_⟩
  group

end CFSG.RankThree.GF2n.Smith81.E7Model

namespace CFSG.RankThree.GF2n.Smith81.E5Tr

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model
open scoped commutatorElement

section Setup

variable
  {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {z v : G}

theorem e5_setup_rel (hFE1 : Smith24E5UniformStatement) (hFE2 : E5RootEltStatement)
    (hW : E3L45World M Q Z B z v) (hc : InCaseE5 M Q Z B) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ψ : M₀.E ≃ₗ[K] V K) (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)),
        EUniData M Q Z B M₀ ψ φ (EAut K) (w0 : V K) (rootRad7 K) ∧
        ∃ Θ : ↥(H0 M Z) →* (Module.End K (V K))ˣ,
          E5Act (Lgen_le_H0 hW.rem.ctx) M₀ ψ Θ ∧
          (∀ s : Lgen M (LB M Q B), vAut K (Θ (Subgroup.inclusion (Lgen_le_H0 hW.rem.ctx) s)) = φ s) ∧
          (∀ t : G, t ∈ M → IsConj z t → t ∉ Q → ∃ ht : t ∈ H0 M Z, IsRootElt (Θ ⟨t, ht⟩)) := by
  have Hs : StrothHyp M Q Z := hW.hStroth
  have hL : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hW.rem.ctx
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData Hs
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B hW.below hW.rem hc K γ M₀ hg
  obtain ⟨Θ, hact, hrel⟩ := exists_E5Act Hs hL hg d
  refine ⟨K, inferInstance, inferInstance, inferInstance, γ, M₀, hg, ψ, φ, d, Θ, hact, hrel, ?_⟩
  intro t htM hzt htQ
  obtain ⟨s, hsQ, hs⟩ := hFE2 G M Q Z B hW.below hW.rem hc K γ M₀ hg ψ φ d z hW.hz hW.hz1 t hzt
    htM htQ
  have htH : t ∈ H0 M Z := by
    have e : t = ((s : G) * t⁻¹)⁻¹ * (s : G) := by group
    rw [e]
    exact mul_mem (inv_mem (Q_le_H0 Hs hsQ)) (hL s.2)
  exact ⟨htH, hact.isRootElt hrel htH ⟨s, hsQ, hs⟩⟩

end Setup

end CFSG.RankThree.GF2n.Smith81.E5Tr

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model
open scoped commutatorElement

section Main


theorem e5RootPoint_of_inputs
    (hFE1 : Smith24E5UniformStatement) (hFE2 : E5RootEltStatement) :
    E5RootPointStatement := by
  intro G _ _ M Q Z B z v hW hc t hzt htMv htQ
  have Hs : StrothHyp M Q Z := hW.hStroth
  have hC : Ctx M Q Z B := hW.rem.ctx
  obtain ⟨K, _, _, _, γ, M₀, hg, ψ, φ, d, Θ, hact, hrel, hroot⟩ :=
    E5Tr.e5_setup_rel hFE1 hFE2 hW hc
  obtain ⟨x, y, hzx, hzy, hxH, hyH, hxQ, hyQ, hv⟩ := E5Tr.E3L45World.factors hW
  have hvH : v ∈ H0 M Z := hW.v_mem_H0
  have hodd : Odd (orderOf v) := hW.hv.2.1
  have hv1 : v ≠ 1 := by
    intro h1
    have := hW.hv.2.2
    rw [h1, orderOf_one] at this
    exact lt_irrefl _ this
  obtain ⟨_, hrx⟩ := hroot x hxH.1 hzx hxQ
  obtain ⟨_, hry⟩ := hroot y hyH.1 hzy hyQ
  obtain ⟨a, ha, hF⟩ := hact.exists_vframe Hs hxH hyH hvH hv hrx hry hodd hv1
  have hact' := hact.changeFrame ha
  have htM : t ∈ M := htMv.1
  obtain ⟨htH, hrt⟩ := hroot t htM hzt htQ
  have hq : 4 ≤ Nat.card K := by
    rw [hg.card]
    exact Hs.q4
  have hrt' : IsRootElt (((MulAut.conj a).toMonoidHom.comp Θ) ⟨t, htH⟩) := hrt.conj_E ha
  have htv : t * v = v * t := mem_Cv.mp htMv.2
  have hcomm : ((MulAut.conj a).toMonoidHom.comp Θ) ⟨t, htH⟩ *
      ((MulAut.conj a).toMonoidHom.comp Θ) ⟨v, hvH⟩ =
      ((MulAut.conj a).toMonoidHom.comp Θ) ⟨v, hvH⟩ *
        ((MulAut.conj a).toMonoidHom.comp Θ) ⟨t, htH⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htv
  obtain ⟨w, hw0, hwV0, hwR, hwH⟩ :=
    rootPoint_of_commuting_rootElt_of_odd hq hF.mem hF.ne hF.odd hrt' hcomm
  obtain ⟨u, hu⟩ := hwR
  obtain ⟨c, hcQ, rfl⟩ := E5Tr.exists_psi_pi (M₀ := M₀) (ψ.trans (vAut K a)) u
  have hQn : ∀ y ∈ Q, ∀ k ∈ M, k * y * k⁻¹ ∈ Q := fun y hy k hk =>
    (Subgroup.mem_normalizer_iff.mp (Hs.Q_normal.2 hk) y).mp hy
  have htcQ : t * c * t⁻¹ ∈ Q := hQn c hcQ t htM
  have hs₁Q : t * c * t⁻¹ * c⁻¹ ∈ Q := Q.mul_mem htcQ (Q.inv_mem hcQ)
  have hψs₁ : (ψ.trans (vAut K a)) (M₀.π (t * c * t⁻¹ * c⁻¹)) = w := by
    rw [← hu]
    have e1 : (((MulAut.conj a).toMonoidHom.comp Θ) ⟨t, htH⟩ : Module.End K (V K))
        ((ψ.trans (vAut K a)) (M₀.π c)) = (ψ.trans (vAut K a)) (M₀.π (t * c * t⁻¹)) :=
      hact'.equivariant ⟨t, htH⟩ c hcQ
    rw [LinearMap.sub_apply, Module.End.one_apply, e1, M₀.π_mul _ htcQ _ (Q.inv_mem hcQ),
      Tim79.QuadModel.pi_inv M₀ hcQ, map_add, map_neg, sub_eq_add_neg]
  obtain ⟨g, hgE, c₀, hc₀, hwg⟩ := hwH
  have hh : vAut K (a⁻¹ * g) ∈ EAut K :=
    Subgroup.mem_map.mpr ⟨a⁻¹ * g, mul_mem (inv_mem ha) hgE, rfl⟩
  have hp₀ : (w0 : V K) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
  obtain ⟨D, hD, himg⟩ := d.exists_ctx_point hC hp₀ hh
  have hmem : ((a⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) w ∈
      ((Submodule.span K {vAut K (a⁻¹ * g) (w0 : V K)} : Submodule K (V K)) : Set (V K)) := by
    rw [hwg, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rw [← himg] at hmem
  obtain ⟨r, hrD, hre⟩ := hmem
  have hrQ : r ∈ Q := hD.le hrD
  have hψr : (ψ.trans (vAut K a)) (M₀.π r) = w := by
    show (a : Module.End K (V K)) (ψ (M₀.π r)) = w
    have hre' : ψ (M₀.π r) = ((a⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) w := hre
    rw [hre']
    have h1 := LinearMap.congr_fun (Units.mul_inv a) w
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h1
  have hr1 : r ≠ 1 := by
    intro h1
    apply hw0
    rw [← hψr, h1, Tim79.QuadModel.pi_one M₀, map_zero]
  refine ⟨r, ?_, ⟨hrQ, ?_⟩, ?_, ?_⟩
  ·
    obtain ⟨g', z', hz', hz'1, hrz⟩ := Ctx.inZClass_of_mem_sup hD (Subgroup.mem_sup_right hrD) hr1
    obtain ⟨m, -, hm⟩ := Z_isConj Hs hW.hz hW.hz1 hz' hz'1
    exact isConj_iff.mpr ⟨g' * m, by rw [hrz, ← hm]; group⟩
  ·
    have hV0 : (ψ.trans (vAut K a)) (M₀.π r) ∈ V0 K := by rw [hψr]; exact hwV0
    exact mem_Cv.mpr
      ((hact'.mem_Cv_iff Hs hvH hodd hF.mem hF.ne hF.odd hrQ).mpr hV0).symm
  · intro hrZ
    apply hw0
    rw [← hψr, (M₀.π_ker r hrQ).mpr hrZ, map_zero]
  · have hπ : M₀.π (t * c * t⁻¹ * c⁻¹) = M₀.π r :=
      (ψ.trans (vAut K a)).injective (hψs₁.trans hψr.symm)
    have h2 : (t * c * t⁻¹ * c⁻¹)⁻¹ * r ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hs₁Q hrQ).mp hπ
    have h3 : r = (t * c * t⁻¹ * c⁻¹) * ((t * c * t⁻¹ * c⁻¹)⁻¹ * r) := by group
    have h4 : t * c * t⁻¹ * c⁻¹ ∈ ⁅Q, Subgroup.zpowers t⁆ := by
      have h5 : ⁅c, t⁆ ∈ ⁅Q, Subgroup.zpowers t⁆ :=
        Subgroup.commutator_mem_commutator hcQ (Subgroup.mem_zpowers t)
      have h6 : t * c * t⁻¹ * c⁻¹ = (⁅c, t⁆)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h6]
      exact inv_mem h5
    rw [h3]
    exact mul_mem (Subgroup.mem_sup_left h4) (Subgroup.mem_sup_right h2)

theorem e5FusionCore_of_inputs (h212 : Smith212Statement)
    (hFE1 : Smith24E5UniformStatement) (hFE2 : E5RootEltStatement) : E5FusionCoreStatement :=
  e5FusionCore_of_pieces h212
    (fun G _ _ M Q Z B z v hW _ => e3l45S5_holds G M Q Z B z v hW)
    (e5RootPoint_of_inputs hFE1 hFE2)

end Main

end CFSG.RankThree.GF2n.Smith81
