module

public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart26
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCartanAdj
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart15

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.StandardType.F4ExplicitPos.AmbientAction

variable {U X : Type*} [Group U] [Group X]

theorem psi_injective_of_center (ψ : U →* X) (hker : ψ.ker ≤ Subgroup.center U)
    (hcenter : Subgroup.center U = ⊥) : Function.Injective ψ := by
  apply (MonoidHom.ker_eq_bot_iff ψ).mp
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Subgroup.center U := hker hx
  rw [hcenter] at hx'
  simpa using hx'

noncomputable def psiEquiv (ψ : U →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥) : U ≃* G0 :=
  (MonoidHom.ofInjective (psi_injective_of_center ψ hker hcenter)).trans
    (MulEquiv.subgroupCongr hG0)

theorem subgroupCongr_coe {G : Type*} [Group G] {H K : Subgroup G} (h : H = K) (x : H) :
    (((MulEquiv.subgroupCongr h) x : K) : G) = (x : G) :=
  rfl

theorem psiEquiv_apply (ψ : U →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥) (u : U) :
    ((psiEquiv ψ G0 hG0 hker hcenter u : G0) : X) = ψ u := by
  rw [psiEquiv, MulEquiv.trans_apply, subgroupCongr_coe, MonoidHom.ofInjective_apply]

noncomputable def alpha (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X)) : B1 →* MulAut U :=
  (MulAut.congr (psiEquiv ψ G0 hG0 hker hcenter).symm).toMonoidHom.comp
    ((G0.normalizerMonoidHom).comp (Subgroup.inclusion hBN))

theorem psiEquiv_alpha_apply (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X)) (b : B1) (u : U) :
    psiEquiv ψ G0 hG0 hker hcenter (alpha ψ G0 B1 hG0 hker hcenter hBN b u) =
      (G0.normalizerMonoidHom (Subgroup.inclusion hBN b))
        (psiEquiv ψ G0 hG0 hker hcenter u) := by
  change psiEquiv ψ G0 hG0 hker hcenter
      ((MulAut.congr (psiEquiv ψ G0 hG0 hker hcenter).symm
        (G0.normalizerMonoidHom (Subgroup.inclusion hBN b))) u) = _
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

theorem psi_alpha_apply (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X)) (b : B1) (u : U) :
    ψ (alpha ψ G0 B1 hG0 hker hcenter hBN b u) = (b : X) * ψ u * (b : X)⁻¹ := by
  rw [← psiEquiv_apply ψ G0 hG0 hker hcenter
    (alpha ψ G0 B1 hG0 hker hcenter hBN b u), psiEquiv_alpha_apply,
    Subgroup.normalizerMonoidHom_apply_apply_coe, psiEquiv_apply]
  rfl

theorem conj_mem_centralizer_of_mem {G : Type*} [Group G] {H : Subgroup G} {z g : G}
    (hz : z ∈ Subgroup.centralizer (H : Set G)) (hg : g ∈ H) :
    g * z * g⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) hy) hg
  have h := hz (g⁻¹ * y * g) hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = (g * z * g⁻¹) * y := by group

theorem alpha_mem_conj_range (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (b : B1) : alpha ψ G0 B1 hG0 hker hcenter hBN b ∈ (MulAut.conj : U →* MulAut U).range := by
  classical
  obtain ⟨g, hg, hc⟩ := hinner b b.property
  obtain ⟨u, hu⟩ : ∃ u : U, ψ u = g := by
    have hg' : g ∈ ψ.range := by rw [hG0]; exact hg
    exact hg'
  refine MonoidHom.mem_range.mpr ⟨u⁻¹, ?_⟩
  ext x
  refine psi_injective_of_center ψ hker hcenter ?_
  have hψ2 : ψ (u⁻¹ * x * u) = g⁻¹ * ψ x * g := by
    rw [map_mul, map_mul, map_inv, hu]
  rw [psi_alpha_apply, MulAut.conj_apply]
  simp only [inv_inv]
  rw [hψ2]
  have hgb : g * (b : X) ∈ Subgroup.centralizer (G0 : Set X) := by
    have := conj_mem_centralizer_of_mem hc hg
    convert this using 1
    group
  have hmem : ψ x ∈ (G0 : Set X) := by
    have : ψ x ∈ ψ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
    rwa [hG0] at this
  have hcomm := Subgroup.mem_centralizer_iff.mp hgb (ψ x) hmem
  have h' : (b : X) * ψ x = g⁻¹ * ψ x * g * (b : X) := by
    have := congrArg (fun t => g⁻¹ * t) hcomm
    exact (by simpa [mul_assoc] using this.symm)
  have hb_eq : (b : X) * ψ x * (b : X)⁻¹ = g⁻¹ * ψ x * g := by
    calc (b : X) * ψ x * (b : X)⁻¹ = g⁻¹ * ψ x * g * (b : X) * (b : X)⁻¹ := by rw [h']
      _ = g⁻¹ * ψ x * g := by group
  exact hb_eq.symm

theorem conj_injective (hcenter : Subgroup.center U = ⊥) :
    Function.Injective (MulAut.conj : U →* MulAut U) :=
  (MonoidHom.ker_eq_bot_iff (MulAut.conj : U →* MulAut U)).mp
    (CFSG.GroupTheory.ker_conj_eq_center.trans hcenter)

noncomputable def betaOf (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) : B1 →* U :=
  (MonoidHom.ofInjective (conj_injective hcenter)).symm.toMonoidHom.comp
    ((alpha ψ G0 B1 hG0 hker hcenter hBN).codRestrict
      (MulAut.conj : U →* MulAut U).range
      (fun b => alpha_mem_conj_range ψ G0 B1 hG0 hker hcenter hBN hinner b))

theorem beta_conj (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) (b : B1) :
    (MulAut.conj : U →* MulAut U) (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b) =
      alpha ψ G0 B1 hG0 hker hcenter hBN b := by
  set eκ := MonoidHom.ofInjective (conj_injective hcenter)
  have h := MonoidHom.ofInjective_apply (conj_injective hcenter)
    (x := eκ.symm (((alpha ψ G0 B1 hG0 hker hcenter hBN).codRestrict
      (MulAut.conj : U →* MulAut U).range
      (fun b => alpha_mem_conj_range ψ G0 B1 hG0 hker hcenter hBN hinner b)) b))
  rw [eκ.apply_symm_apply] at h
  rw [MonoidHom.codRestrict_apply] at h
  exact h.symm

theorem normalizerMonoidHom_inclusion_eq_one_iff (G0 B1 : Subgroup X)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X)) (b : B1) :
    G0.normalizerMonoidHom (Subgroup.inclusion hBN b) = 1 ↔
      (b : X) ∈ Subgroup.centralizer (G0 : Set X) := by
  constructor
  · intro h
    have hker : Subgroup.inclusion hBN b ∈ G0.normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.mpr h
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    have hX : ((Subgroup.inclusion hBN b : Subgroup.normalizer (G0 : Set X)) : X) ∈
        Subgroup.centralizer (G0 : Set X) := Subgroup.mem_subgroupOf.mp hker
    simpa using hX
  · intro h
    have hX : ((Subgroup.inclusion hBN b : Subgroup.normalizer (G0 : Set X)) : X) ∈
        Subgroup.centralizer (G0 : Set X) := by simpa using h
    have hker : Subgroup.inclusion hBN b ∈ G0.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      exact hX
    exact MonoidHom.mem_ker.mp hker

theorem alpha_eq_one_iff (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X)) (b : B1) :
    alpha ψ G0 B1 hG0 hker hcenter hBN b = 1 ↔
      (b : X) ∈ Subgroup.centralizer (G0 : Set X) := by
  have h : alpha ψ G0 B1 hG0 hker hcenter hBN b = 1 ↔
      G0.normalizerMonoidHom (Subgroup.inclusion hBN b) = 1 := by
    constructor
    · intro hb
      refine (MulAut.congr (psiEquiv ψ G0 hG0 hker hcenter).symm).injective ?_
      change alpha ψ G0 B1 hG0 hker hcenter hBN b =
        (MulAut.congr (psiEquiv ψ G0 hG0 hker hcenter).symm) 1
      rw [hb, map_one]
    · intro hb
      change (MulAut.congr (psiEquiv ψ G0 hG0 hker hcenter).symm)
        (G0.normalizerMonoidHom (Subgroup.inclusion hBN b)) = 1
      rw [hb, map_one]
  rw [h]
  exact normalizerMonoidHom_inclusion_eq_one_iff G0 B1 hBN b

theorem beta_eq_one_iff (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) (b : B1) :
    betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b = 1 ↔
      (b : X) ∈ Subgroup.centralizer (G0 : Set X) := by
  constructor
  · intro hb
    have h : (MulAut.conj : U →* MulAut U)
        (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b) = 1 := by rw [hb, map_one]
    rw [beta_conj] at h
    exact (alpha_eq_one_iff ψ G0 B1 hG0 hker hcenter hBN b).mp h
  · intro hb
    apply conj_injective hcenter
    rw [beta_conj, (alpha_eq_one_iff ψ G0 B1 hG0 hker hcenter hBN b).mpr hb, map_one]

theorem beta_ker (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) :
    (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner).ker =
      (Subgroup.centralizer (G0 : Set X)).subgroupOf B1 := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact beta_eq_one_iff ψ G0 B1 hG0 hker hcenter hBN hinner b

theorem psi_beta_action (ψ : U →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center U) (hcenter : Subgroup.center U = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (b : B1) (u : U) :
    ψ (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b * u *
        (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b)⁻¹) = (b : X) * ψ u * (b : X)⁻¹ := by
  rw [← MulAut.conj_apply, beta_conj]
  exact psi_alpha_apply ψ G0 B1 hG0 hker hcenter hBN b u

section Frobenius

open CFSG.StandardType.F4ExplicitPos.BaseChange

variable {K L : Type} [Field K] [Field L] [Algebra K L] [Finite K]

theorem algebraMap_injective_of_field : Function.Injective (algebraMap K L) :=
  FaithfulSMul.algebraMap_injective K L

noncomputable def jF4
    : adjointGroup .F4 K →* adjointGroup .F4 L :=
  CFSG.StandardType.F4ExplicitPos.BaseChange.j (τ := .F4) (algebraMap K L)

theorem jF4_apply
    (u : adjointGroup .F4 K) :
    ((jF4 u : adjointGroup .F4 L) : ModGL .F4 L) =
      bcGL (τ := .F4) (algebraMap K L) (u : ModGL .F4 K) :=
  rfl

theorem jF4_injective
    : Function.Injective (jF4 : adjointGroup .F4 K →* adjointGroup .F4 L) :=
  CFSG.StandardType.F4ExplicitPos.BaseChange.j_injective (τ := .F4) (algebraMap K L)
    algebraMap_injective_of_field

noncomputable def frobF4
    (Fr : L →+* L) (_hFr : ∀ c, Fr c = c ^ Nat.card K) :
    adjointGroup .F4 L →* adjointGroup .F4 L :=
  ((bcGL (τ := .F4) Fr).comp (adjointGroup .F4 L).subtype).codRestrict
    (adjointGroup .F4 L) (fun g => bcGL_mem_adjointGroup (τ := .F4) Fr g.2)

theorem frobF4_apply_coe
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (g : adjointGroup .F4 L) :
    ((frobF4 Fr hFr g : adjointGroup .F4 L) : ModGL .F4 L) =
      bcGL (τ := .F4) Fr (g : ModGL .F4 L) :=
  rfl

theorem frobF4_jF4
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (u : adjointGroup .F4 K) :
    frobF4 Fr hFr (jF4 u) =
      jF4 u := by
  refine Subtype.ext ?_
  rw [frobF4_apply_coe, jF4_apply u, bcGL_comp,
    frobenius_comp_algebraMap Fr hFr]

end Frobenius

section F4Equations

open CFSG.StandardType.F4ExplicitPos.BaseChange

variable {K L : Type} {X : Type*} [Field K] [Field L] [Algebra K L] [Finite K] [Group X] [Finite X]

noncomputable def eF4 (ψ : adjointGroup .F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥) : adjointGroup .F4 K ≃* G0 :=
  psiEquiv ψ G0 hG0 hker hcenter

noncomputable def betaF4 (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) : B1 →* ↥(adjointGroup
        .F4 K) :=
  betaOf ψ G0 B1 hG0 hker hcenter hBN hinner

noncomputable def iotaF4
    (ψ : adjointGroup .F4 K →* X) (G0 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥) : G0 →* adjointGroup .F4 L :=
  (jF4).comp (eF4 ψ G0 hG0 hker hcenter).symm.toMonoidHom

theorem iotaF4_apply
    (ψ : adjointGroup .F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥) (y : G0) :
    iotaF4 ψ G0 hG0 hker hcenter y =
      jF4 (K := K) (L := L) ((psiEquiv ψ G0 hG0 hker hcenter).symm y) :=
  rfl

noncomputable def thetaF4
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) :
    B1 →* adjointGroup .F4 L :=
  (jF4).comp
    (betaF4 ψ G0 B1 hG0 hker hcenter hBN hinner)

theorem iotaF4_e
    (ψ : adjointGroup .F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥) (u : adjointGroup .F4 K) :
    (iotaF4 ψ G0 hG0 hker hcenter
      (eF4 ψ G0 hG0 hker hcenter u) : adjointGroup .F4 L) =
      jF4 u := by
  rw [iotaF4, MonoidHom.comp_apply]
  change jF4 ((eF4 ψ G0 hG0 hker hcenter).symm ((eF4 ψ G0 hG0 hker hcenter) u)) = jF4 u
  rw [MulEquiv.symm_apply_apply]

end F4Equations
end CFSG.StandardType.F4ExplicitPos.AmbientAction
end

end
