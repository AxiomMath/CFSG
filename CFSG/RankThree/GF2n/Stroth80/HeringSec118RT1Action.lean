module

public import CFSG.RankThree.GF2n.Stroth80.Sec118CommBridge
public import CFSG.RankThree.GF2n.Stroth80.CarterSec11CMRanked
public import CFSG.RankThree.GF2n.Stroth80.Sec11A2Linear
public import CFSG.HardMathSupport.Kantor79.CommutatorSpace

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open CFSG.HardMathSupport.Kantor79 QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] {M Q Z : Subgroup G} [(Q.subgroupOf M).Normal] {K : Type} [Field K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] noncomputable def cmCommQf (B : Subgroup G) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) :
    QuadraticForm K ↥(cmComm M Q Z B K γ M₀ φ) :=
  M₀.toQuadraticForm.comp (cmComm M Q Z B K γ M₀ φ).subtype

theorem cmCommQf_apply (B : Subgroup G) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (v : ↥(cmComm M Q Z B K γ M₀ φ)) : cmCommQf B φ v = M₀.Qf (v : M₀.E) := rfl

theorem polar_cmCommQf (B : Subgroup G) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (x y : ↥(cmComm M Q Z B K γ M₀ φ)) :
    polar (cmCommQf B φ) x y = M₀.B (x : M₀.E) (y : M₀.E) := by
  rw [← Tim79.QuadModel.polar_toQuadraticForm M₀ (x : M₀.E) (y : M₀.E)]
  rfl

variable [Finite G]

theorem Ctx.cmCommQf_nondegenerate [Finite K] {B : Subgroup G} (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y)) :
    ∀ x : ↥(cmComm M Q Z B K γ M₀ φ), (∀ y, polar (cmCommQf B φ) x y = 0) → x = 0 := by
  intro x hx
  refine Subtype.ext (hc.eq_zero_of_mem_cmComm_of_orthogonal hD φ hφπ x.2 fun z hz => ?_)
  have := hx ⟨z, hz⟩
  rwa [polar_cmCommQf] at this

@[expose] noncomputable def cmCommAct {B : Subgroup G} (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) :
    ↥(XbarH M Q Z B) →*
      (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)) where
  toFun s := LinearEquiv.ofSubmodules (φ (s : ↥(H0 M Z))) _ _
    (cmComm_map_eq_self_of_mem_XbarH hc φ s)
  map_one' := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    simp [LinearEquiv.ofSubmodules_apply]
  map_mul' s t := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    simp [LinearEquiv.ofSubmodules_apply]

theorem coe_cmCommAct {B : Subgroup G} (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (s : ↥(XbarH M Q Z B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)) :
    ((cmCommAct hc φ s v : ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E) =
      φ (s : ↥(H0 M Z)) (v : M₀.E) := rfl

theorem cmCommQf_cmCommAct {B : Subgroup G} (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) (s : ↥(XbarH M Q Z B))
    (v : ↥(cmComm M Q Z B K γ M₀ φ)) :
    cmCommQf B φ (cmCommAct hc φ s v) = cmCommQf B φ v := hφQ _ _

theorem Ctx.exists_rho_factor {B : Subgroup G} (hc : Ctx M Q Z B) {m : ℕ} {F : Type} [Field F]
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) (Θ : ↥(XbarH M Q Z B) →* StatedSp m F)
    (hΘ : Function.Surjective Θ) (hker : ∀ s, Θ s = 1 → φ (s : ↥(H0 M Z)) = 1) :
    ∃ ρV : Gsp (spForm m F) →*
        (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)),
      ∀ s, ρV (spEquiv (Θ s)) = cmCommAct hc φ s := by
  classical
  let Θ' : ↥(XbarH M Q Z B) →* Gsp (spForm m F) :=
    (spEquiv (m := m) (K := F)).toMonoidHom.comp Θ
  have hΘ' : Function.Surjective Θ' := (spEquiv (m := m) (K := F)).surjective.comp hΘ
  have hk : Θ'.ker ≤ (cmCommAct hc φ).ker := by
    intro s hs
    have h1 : Θ s = 1 := by
      have h2 : spEquiv (Θ s) = 1 := hs
      rwa [← map_one (spEquiv (m := m) (K := F)), (spEquiv (m := m) (K := F)).injective.eq_iff]
        at h2
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [coe_cmCommAct, hker s h1]
    rfl
  refine ⟨MonoidHom.liftOfSurjective Θ' hΘ' ⟨cmCommAct hc φ, hk⟩, fun s => ?_⟩
  exact MonoidHom.liftOfRightInverse_comp_apply Θ' _ _ ⟨cmCommAct hc φ, hk⟩ s

theorem Ctx.fix_of_mem_orthogonal_cmComm [Finite K] {B : Subgroup G} (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφB : ∀ (g : ↥(H0 M Z)) e f, M₀.B (φ g e) (φ g f) = M₀.B e f)
    (s : ↥(XbarH M Q Z B)) {e : M₀.E}
    (he : e ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) :
    φ (s : ↥(H0 M Z)) e = e := by
  have hperp : φ (s : ↥(H0 M Z)) e ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    rw [← cmComm_map_eq_self_of_mem_XbarH hc φ s] at hz
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hz
    exact (hφB (s : ↥(H0 M Z)) v' e).trans
      ((LinearMap.BilinForm.mem_orthogonal_iff.mp he) v' hv')
  have hmemV : φ (s : ↥(H0 M Z)) e - e ∈ cmComm M Q Z B K γ M₀ φ := by
    have h1 : (((φ (s : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) e ∈
        LinearMap.range (((φ (s : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) :=
      LinearMap.mem_range_self _ e
    have h2 : (((φ (s : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) e ∈
        cmComm M Q Z B K γ M₀ φ :=
      le_iSup (fun h : ↥(XbarH M Q Z B) =>
        LinearMap.range (((φ (h : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) s h1
    simpa using h2
  have hmemV' : φ (s : ↥(H0 M Z)) e - e ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) :=
    Submodule.sub_mem _ hperp he
  have hdisj := (hc.isCompl_cmComm_orthogonal hD φ hφπ).disjoint
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hdisj _ hmemV hmemV')

theorem Ctx.eq_zero_of_fixed_of_mem_cmComm [Finite K] {B : Subgroup G} (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφB : ∀ (g : ↥(H0 M Z)) e f, M₀.B (φ g e) (φ g f) = M₀.B e f) {v : M₀.E}
    (hv : v ∈ cmComm M Q Z B K γ M₀ φ) (hfix : ∀ s : ↥(XbarH M Q Z B), φ (s : ↥(H0 M Z)) v = v) :
    v = 0 := by
  refine hc.eq_zero_of_mem_cmComm_of_orthogonal hD φ hφπ hv fun z hz => ?_
  have hle : cmComm M Q Z B K γ M₀ φ ≤ LinearMap.ker (M₀.B v) := by
    refine iSup_le fun s => ?_
    rintro _ ⟨e, rfl⟩
    have h1 : M₀.B v (φ (s : ↥(H0 M Z)) e) = M₀.B v e := by
      have h := hφB (s : ↥(H0 M Z)) v e
      rwa [hfix s] at h
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, map_sub, h1, sub_self]
  exact LinearMap.mem_ker.mp (hle hz)

theorem Ctx.commutatorSpace_cmCommAct_eq_top [Finite K] {B : Subgroup G} (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφB : ∀ (g : ↥(H0 M Z)) e f, M₀.B (φ g e) (φ g f) = M₀.B e f) :
    commutatorSpace (cmCommAct hc φ).range = ⊤ := by
  have hmapEq : Submodule.map (cmComm M Q Z B K γ M₀ φ).subtype
      (commutatorSpace (cmCommAct hc φ).range) = cmComm M Q Z B K γ M₀ φ := by
    refine le_antisymm (Submodule.map_subtype_le _ _) ?_
    refine iSup_le fun s => ?_
    rintro _ ⟨e', rfl⟩
    have hsup : e' ∈ cmComm M Q Z B K γ M₀ φ ⊔
        M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
      rw [(hc.isCompl_cmComm_orthogonal hD φ hφπ).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Submodule.mem_sup.mp hsup
    have h0 : (((φ (s : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) e₂ = 0 := by
      have hfix := fix_of_mem_orthogonal_cmComm hc hD φ hφπ hφB s he₂
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, hfix, sub_self]
    rw [map_add, h0, add_zero]
    have hy : (cmCommAct hc φ s) ⟨e₁, he₁⟩ - ⟨e₁, he₁⟩ ∈
        commutatorSpace (cmCommAct hc φ).range :=
      Submodule.subset_span ⟨cmCommAct hc φ s, ⟨s, rfl⟩, ⟨e₁, he₁⟩, rfl⟩
    refine Submodule.mem_map.mpr ⟨_, hy, ?_⟩
    simp [coe_cmCommAct]
  refine Submodule.map_injective_of_injective (Submodule.injective_subtype _) ?_
  rw [Submodule.map_subtype_top, hmapEq]

theorem Ctx.cmCommAct_moved [Finite K] {B : Subgroup G} [CharP K 2] (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (hKZ : Nat.card K = Nat.card Z)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {s : ↥(XbarH M Q Z B)}
    (hsL : ((s : ↥(H0 M Z)) : G) ∈ LB M Q B) (hsA : IsA2 Q Z ((s : ↥(H0 M Z)) : G)) :
    Module.finrank K ↥(movedSpace (cmCommAct hc φ s)) = 2 ∧
      ∀ w ∈ movedSpace (cmCommAct hc φ s), cmCommQf B φ w = 0 := by
  obtain ⟨T, hTπ, -, -, -, hdim, hQfker, -⟩ := exists_a2_linear_of_IsA2 hc hD hKZ hsL hsA
  have hTeq : T = φ (s : ↥(H0 M Z)) := by
    refine LinearEquiv.ext fun e => ?_
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    rw [← hTπ x hx]
    exact hφπ _ x hx
  subst hTeq
  have hmap : Submodule.map (cmComm M Q Z B K γ M₀ φ).subtype (movedSpace (cmCommAct hc φ s)) =
      LinearMap.range (((φ (s : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := by
    have key : (cmComm M Q Z B K γ M₀ φ).subtype.comp
        (((cmCommAct hc φ s : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)) :
          ↥(cmComm M Q Z B K γ M₀ φ) →ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)) - 1) =
        (((φ (s : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1).comp
          (cmComm M Q Z B K γ M₀ φ).subtype := by
      ext v
      simp [coe_cmCommAct]
    unfold movedSpace
    rw [← LinearMap.range_comp, key, LinearMap.range_comp, Submodule.range_subtype]
    exact (hc.range_sub_one_eq_map_cmComm hD φ hφπ ha2 hsL (s : ↥(H0 M Z)).2).symm
  refine ⟨?_, fun w hw => ?_⟩
  · rw [← Submodule.finrank_map_subtype_eq (cmComm M Q Z B K γ M₀ φ)
      (movedSpace (cmCommAct hc φ s)), hmap]
    exact hdim
  · have hw' := Submodule.mem_map_of_mem (f := (cmComm M Q Z B K γ M₀ φ).subtype) hw
    rw [hmap] at hw'
    obtain ⟨e, he⟩ := LinearMap.mem_range.mp hw'
    rw [cmCommQf_apply]
    have hwe : (w : M₀.E) = (((φ (s : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) e :=
      he.symm
    rw [hwe]
    exact hQfker e

end CFSG.RankThree.GF2n.Stroth80
