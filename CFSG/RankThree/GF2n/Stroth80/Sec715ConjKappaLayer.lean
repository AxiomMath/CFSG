module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappaFix
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappaSiegel

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715K

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin
open scoped Matrix commutatorElement

section LayerGen

variable {K U H : Type*} [Field K] [AddCommGroup U] [Module K U] [Group H]

theorem finrank_range_sub_id_of_isCompl [FiniteDimensional K U] {act : H →* (U ≃ₗ[K] U)}
    {Y₁ Y₂ : Submodule K U} (hc : IsCompl Y₁ Y₂) (h₁ : S715L.IsInvSub act Y₁)
    (h₂ : S715L.IsInvSub act Y₂) (r : H)
    (hr₁ : Module.finrank K (Y₁.map ((act r : U →ₗ[K] U) - LinearMap.id)) = 2)
    (hr₂ : Module.finrank K (Y₂.map ((act r : U →ₗ[K] U) - LinearMap.id)) = 2) :
    Module.finrank K (LinearMap.range ((act r : U →ₗ[K] U) - LinearMap.id)) = 4 := by
  set f := (act r : U →ₗ[K] U) - LinearMap.id with hf
  have hle : ∀ (Y : Submodule K U), S715L.IsInvSub act Y → Y.map f ≤ Y := by
    rintro Y hY _ ⟨y, hy, rfl⟩
    exact Y.sub_mem (hY r y hy) hy
  have hrange : LinearMap.range f = Y₁.map f ⊔ Y₂.map f := by
    rw [← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top]
  have hinf : Y₁.map f ⊓ Y₂.map f = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf (hle Y₁ h₁) (hle Y₂ h₂)).trans hc.inf_eq_bot.le)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Y₁.map f) (Y₂.map f)
  rw [hinf, finrank_bot, add_zero, hr₁, hr₂] at h
  rw [hrange, h]

theorem sub_eq_smul_of_isCompl {act : H →* (U ≃ₗ[K] U)} {Y₁ Y₂ : Submodule K U}
    (hc : IsCompl Y₁ Y₂) {r r' : H} {κ : K}
    (h₁ : ∀ y ∈ Y₁, act r' y - y = κ • (act r y - y))
    (h₂ : ∀ y ∈ Y₂, act r' y - y = κ • (act r y - y)) (y : U) :
    act r' y - y = κ • (act r y - y) := by
  have hy : y ∈ Y₁ ⊔ Y₂ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add, h₁ y₁ hy₁ |> fun h => (sub_eq_iff_eq_add.mp h),
    h₂ y₂ hy₂ |> fun h => (sub_eq_iff_eq_add.mp h)]
  module

theorem finrank_map_mkQ_add [FiniteDimensional K U] (S N : Submodule K U) :
    Module.finrank K (S.map N.mkQ) + Module.finrank K N = Module.finrank K ↥(S ⊔ N) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (N.mkQ.domRestrict (S ⊔ N))
  rw [LinearMap.range_domRestrict, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq,
    LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h1
  have h2 : Module.finrank K ↥(N.comap (S ⊔ N).subtype) = Module.finrank K N := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      inf_eq_right.mpr le_sup_right]
  omega

theorem finrank_range_conj {U' : Type*} [AddCommGroup U'] [Module K U'] (f : U ≃ₗ[K] U')
    (A : U →ₗ[K] U) :
    Module.finrank K (LinearMap.range (f.conj A)) = Module.finrank K (LinearMap.range A) := by
  rw [LinearEquiv.conj_apply, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range f.symm), LinearMap.range_comp, LinearEquiv.finrank_map_eq]

end LayerGen

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

namespace KModel

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {Z0 : Subgroup G} {ψ : M₀.E →ₗ[K] M₀.E}
  {φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K}
  {e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}

theorem vtSub_le_wsub (hK : KModel hS t Z0 ψ φ₈ e) :
    hc.VtSub hS.model t ≤ S714.wsub hS t := by
  intro v hv
  obtain ⟨x, rfl⟩ := hK.psi_V' v hv
  exact (hK.psi_W _).mp (hK.psi_sq x)

theorem finrank_vInW (hK : KModel hS t Z0 ψ φ₈ e) :
    Module.finrank K ↥(S715L.vInW hS t) = Module.finrank K ↥(hc.VtSub hS.model t) := by
  rw [← Submodule.finrank_map_subtype_eq, S715L.vInW, Submodule.map_comap_subtype,
    inf_eq_right.mpr hK.vtSub_le_wsub]

theorem finrank_V (hK : KModel hS t Z0 ψ φ₈ e) :
    Module.finrank K ↥(hc.VtSub hS.model t) = 8 := by
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem rho_inv_of_root {Y : M₀.E →ₗ[K] M₀.E} (hY : ∀ x, Y (Y x) = 0) {g : Mbar M Q} {c : K}
    (hg : ∀ y, (ρ g).toAdd y = y + c • Y y) (w : M₀.E) : (ρ g⁻¹).toAdd w = w - c • Y w := by
  apply (ρ g).toAdd.injective
  rw [← act_mul_apply, mul_inv_cancel, S715L.act_one_apply, hg, map_sub, map_smul, hY,
    smul_zero, sub_zero, sub_add_cancel]

theorem le_finrank_of_wvQ (hK : KModel hS t Z0 ψ φ₈ e) {x : ↥(bar M Q (Rt M (LB M Q B) t))}
    {A : M₀.E →ₗ[K] M₀.E} (hx : ∀ y, (ρ (x : Mbar M Q)).toAdd y = y + A y)
    (h4 : Module.finrank K (LinearMap.range ((S715L.wvAct hS hK.mem x :
      S715L.wvQ hS t →ₗ[K] S715L.wvQ hS t) - LinearMap.id)) = 4) :
    12 ≤ Module.finrank K ↥((LinearMap.ker ψ).map A ⊔ hc.VtSub hS.model t) := by
  haveI : Module.Finite K M₀.E := M₀.fin
  set W := S714.wsub hS t with hW
  set N := S715L.vInW hS t with hN
  set f : ↥W →ₗ[K] ↥W := (S715L.wAct hS hK.mem x : ↥W →ₗ[K] ↥W) - LinearMap.id with hf
  have hcomp : ((S715L.wvAct hS hK.mem x : S715L.wvQ hS t →ₗ[K] S715L.wvQ hS t) -
      LinearMap.id) ∘ₗ N.mkQ = N.mkQ ∘ₗ f := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Submodule.mkQ_apply, hf]
    rw [S715L.wvAct_mk, Submodule.Quotient.mk_sub]
  have hrange : LinearMap.range ((S715L.wvAct hS hK.mem x : S715L.wvQ hS t →ₗ[K]
      S715L.wvQ hS t) - LinearMap.id) = (LinearMap.range f).map N.mkQ := by
    rw [← LinearMap.range_comp_of_range_eq_top _ (Submodule.range_mkQ N), hcomp,
      LinearMap.range_comp]
  have hfw : ∀ w : ↥W, ((f w : ↥W) : M₀.E) = A w := fun w => by
    simp only [hf, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Submodule.coe_sub]
    rw [S715L.wAct_apply, hx, add_sub_cancel_left]
  have hmapf : (LinearMap.range f).map W.subtype = (LinearMap.ker ψ).map A := by
    ext y
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, LinearMap.mem_ker.mpr ((hK.psi_W w).mpr w.2), (hfw w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨f ⟨w, (hK.psi_W w).mp (LinearMap.mem_ker.mp hw)⟩, LinearMap.mem_range_self _ _, ?_⟩
      exact hfw _
  have hmapN : N.map W.subtype = hc.VtSub hS.model t := by
    rw [hN, S715L.vInW, Submodule.map_comap_subtype, inf_eq_right.mpr hK.vtSub_le_wsub]
  have hsup : (LinearMap.range f ⊔ N).map W.subtype =
      (LinearMap.ker ψ).map A ⊔ hc.VtSub hS.model t := by
    rw [Submodule.map_sup, hmapf, hmapN]
  have hN8 : Module.finrank K ↥N = 8 := by rw [hN, hK.finrank_vInW, hK.finrank_V]
  have h1 := finrank_map_mkQ_add (LinearMap.range f) N
  rw [← hrange, h4, hN8] at h1
  rw [← hsup, Submodule.finrank_map_subtype_eq]
  omega

theorem deltaAct_sub_apply (hK : KModel hS t Z0 ψ φ₈ e) {x : ↥(bar M Q (Rt M (LB M Q B) t))}
    {Y : M₀.E →ₗ[K] M₀.E} (hY : ∀ y, Y (Y y) = 0)
    (hYW : ∀ w ∈ S714.wsub hS t, Y w ∈ S714.wsub hS t) {c : K}
    (hx : ∀ y, (ρ (x : Mbar M Q)).toAdd y = y + c • Y y) (D : ↥(S715L.deltaSub hS t))
    (w : ↥(S714.wsub hS t)) :
    ((S715L.deltaAct hS hK.mem x D : ↥(S715L.deltaSub hS t)) :
        ↥(S714.wsub hS t) →ₗ[K] M₀.E) w - (D : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w =
      c • (Y ((D : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w) -
          (D : ↥(S714.wsub hS t) →ₗ[K] M₀.E) ⟨Y w, hYW w w.2⟩) -
        (c * c) • Y ((D : ↥(S714.wsub hS t) →ₗ[K] M₀.E) ⟨Y w, hYW w w.2⟩) := by
  have hinv : S715L.wAct hS hK.mem x⁻¹ w = w - c • ⟨Y w, hYW w w.2⟩ := Subtype.ext (by
    rw [S715L.wAct_apply, Subgroup.coe_inv, rho_inv_of_root hY hx]
    rfl)
  rw [S715L.coe_deltaAct, S715L.conjHom_apply, hinv, map_sub, map_smul, hx, map_sub, map_smul]
  module

theorem ydy_of_rel (hK : KModel hS t Z0 ψ φ₈ e) {Y : M₀.E →ₗ[K] M₀.E} (hY : ∀ y, Y (Y y) = 0)
    (hYW : ∀ w ∈ S714.wsub hS t, Y w ∈ S714.wsub hS t) {x₁ x₀ : ↥(bar M Q (Rt M (LB M Q B) t))}
    {c₀ : K} (hc₀ : c₀ ≠ 0) (hc₁ : c₀ ≠ 1) (hx₁ : ∀ y, (ρ (x₁ : Mbar M Q)).toAdd y = y + Y y)
    (hx₀ : ∀ y, (ρ (x₀ : Mbar M Q)).toAdd y = y + c₀ • Y y)
    (hrel : ∀ D : ↥(S715L.deltaSub hS t), S715L.deltaAct hS hK.mem x₀ D - D =
      c₀ • (S715L.deltaAct hS hK.mem x₁ D - D))
    (D : ↥(S715L.deltaSub hS t)) (w : ↥(S714.wsub hS t)) :
    Y ((D : ↥(S714.wsub hS t) →ₗ[K] M₀.E) ⟨Y w, hYW w w.2⟩) = 0 := by
  have hx₁' : ∀ y, (ρ (x₁ : Mbar M Q)).toAdd y = y + (1 : K) • Y y := fun y => by
    rw [hx₁, one_smul]
  have h := congrArg (fun f : ↥(S715L.deltaSub hS t) => (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w)
    (hrel D)
  simp only [Submodule.coe_sub, Submodule.coe_smul, LinearMap.sub_apply,
    LinearMap.smul_apply] at h
  rw [deltaAct_sub_apply hK hY hYW hx₀, deltaAct_sub_apply hK hY hYW hx₁'] at h
  have h2 : (c₀ * (c₀ - 1)) • Y ((D : ↥(S714.wsub hS t) →ₗ[K] M₀.E) ⟨Y w, hYW w w.2⟩) = 0 := by
    linear_combination (norm := module) -h
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero hc₀ (sub_ne_zero.mpr hc₁))
  · exact h3

theorem matrix_sub_one_eq {A B : GL (Fin 4 ⊕ Fin 4) K}
    {T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} {c₀ : K}
    (hA : ∀ v, (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + c₀ • T v)
    (hB : ∀ v, (B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + (1 : K) • T v) :
    (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1 =
      c₀ • ((B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, hA, hB, one_smul, add_sub_cancel_left,
    add_sub_cancel_left]

section Frame

variable {Tt : ↥(bar M Q (H0 M Z)) → Submodule K M₀.E}

theorem psiX_basic (hK : KModel hS t Z0 ψ φ₈ e)
    (F : Sec715Frame (S715L.hAct hS) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) Tt)
    {h : ↥(bar M Q (H0 M Z))}
    (hL : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z))) :
    (∀ x, ψ ((S715L.hAct hS h).conj ψ x) = (S715L.hAct hS h).conj ψ (ψ x)) ∧
      (∀ x, (S715L.hAct hS h).conj ψ ((S715L.hAct hS h).conj ψ x) = 0) ∧
      (∀ v ∈ hc.VtSub hS.model t, (S715L.hAct hS h).conj ψ v ∈ hc.VtSub hS.model t) ∧
      (∀ w ∈ S714.wsub hS t, (S715L.hAct hS h).conj ψ w ∈ S714.wsub hS t) := by
  obtain ⟨z₁, hz₁, hz₁x⟩ := hK.par' 1
  set a₁ : ↥(bar M Q (H0 M Z)) := ⟨z₁, hK.Z0_le_H0 hz₁⟩ with ha₁
  have ha₁V : a₁ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hz₁
  have ha₁x : ∀ x, S715L.hAct hS a₁ x = x + ψ x := fun x => by
    rw [S715L.hAct_apply, hz₁x, one_smul]
  have hY1 : ∀ x, S715L.hAct hS (h * a₁ * h⁻¹) x = x + (1 : K) • (S715L.hAct hS h).conj ψ x :=
    conj_apply_of_eq (S715L.hAct hS) (fun x => by rw [ha₁x, one_smul]) h
  have hcomm : a₁ * (h * a₁ * h⁻¹) = (h * a₁ * h⁻¹) * a₁ :=
    F.L_comm _ (F.V_le_L ha₁V) _ (hL a₁ ha₁V)
  have h1 : ∀ x, ψ ((S715L.hAct hS h).conj ψ x) = (S715L.hAct hS h).conj ψ (ψ x) :=
    comm_of_comm (S715L.hAct hS) hcomm one_ne_zero ha₁x hY1
  have h2 : ∀ x, (S715L.hAct hS h).conj ψ ((S715L.hAct hS h).conj ψ x) = 0 := by
    intro x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      hK.psi_sq, map_zero]
  refine ⟨h1, h2, fun v hv => ?_, fun w hw => ?_⟩
  · obtain ⟨x, rfl⟩ := hK.psi_V' v hv
    rw [← h1]
    exact hK.psi_V _
  · refine (hK.psi_W _).mp ?_
    rw [h1, (hK.psi_W w).mpr hw, map_zero]

theorem rootT (hK : KModel hS t Z0 ψ φ₈ e)
    (F : Sec715Frame (S715L.hAct hS) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) Tt)
    {h : ↥(bar M Q (H0 M Z))}
    (hL : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)))
    (hout : ¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
    {u : Fin 4 ⊕ Fin 4 → K} (hu0 : u ≠ 0) (hQu : quadPlus 4 K u = 0)
    (hLu : ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), (x : Mbar M Q) ∈ bar M Q (LB M Q B) →
      φ₈ x ∈ LomGLPlus (by norm_num : 3 ≤ 4) u)
    (hV : ∀ v ∈ hc.VtSub hS.model t, (S715L.hAct hS h).conj ψ v ∈ hc.VtSub hS.model t) :
    (∀ (a : ↥(bar M Q (H0 M Z))) (ha : a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) (c : K),
      (∀ x, S715L.hAct hS a x = x + c • ψ x) → ∀ v : Fin 4 ⊕ Fin 4 → K,
        (φ₈ ⟨((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q),
          Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL a ha))⟩ :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v =
          v + c • e.conj (((S715L.hAct hS h).conj ψ).restrict hV) v) ∧
      (∀ v, quadPlus 4 K (e.conj (((S715L.hAct hS h).conj ψ).restrict hV) v) = 0 ∧
        polar (quadPlus 4 K) v (e.conj (((S715L.hAct hS h).conj ψ).restrict hV) v) = 0) ∧
      Module.finrank K (LinearMap.range (e.conj (((S715L.hAct hS h).conj ψ).restrict hV))) = 2 := by
  classical
  set T := e.conj (((S715L.hAct hS h).conj ψ).restrict hV) with hT
  have hact : ∀ (a : ↥(bar M Q (H0 M Z))) (c : K), (∀ x, S715L.hAct hS a x = x + c • ψ x) →
      ∀ y, (ρ ((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q)).toAdd y =
        y + c • (S715L.hAct hS h).conj ψ y := fun a c hac y => by
    rw [← S715L.hAct_apply]
    exact conj_apply_of_eq (S715L.hAct hS) hac h y
  have hmv : ∀ (a : ↥(bar M Q (H0 M Z))) (ha : a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (c : K), (∀ x, S715L.hAct hS a x = x + c • ψ x) → ∀ v : Fin 4 ⊕ Fin 4 → K,
        (φ₈ ⟨((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q),
          Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL a ha))⟩ :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + c • T v :=
    fun a ha c hac v => hK.mulVec_of_act hV (hact a c hac) v
  have hpar : ∀ c : K, ∃ x : ↥(bar M Q (Rt M (LB M Q B) t)),
      ∀ y, (ρ (x : Mbar M Q)).toAdd y = y + c • (S715L.hAct hS h).conj ψ y := by
    intro c
    obtain ⟨z, hz, hzx⟩ := hK.par' c
    have haV : (⟨z, hK.Z0_le_H0 hz⟩ : ↥(bar M Q (H0 M Z))) ∈
        (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hz
    exact ⟨⟨_, Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL _ haV))⟩,
      hact _ c (fun x => by rw [S715L.hAct_apply]; exact hzx x)⟩
  have hq : ∀ v, quadPlus 4 K (T v) = 0 ∧ polar (quadPlus 4 K) v (T v) = 0 :=
    fun v => hK.quad_T hV hpar v
  refine ⟨hmv, hq, ?_⟩
  have hT0 : Module.finrank K (LinearMap.range T) ≠ 0 := by
    intro h0
    apply hout
    intro a ha
    obtain ⟨c, hc⟩ := hK.par (a : Mbar M Q) (Subgroup.mem_subgroupOf.mp ha)
    have hac : ∀ x, S715L.hAct hS a x = x + c • ψ x := fun x => by
      rw [S715L.hAct_apply]; exact hc x
    have hTz : ∀ v, T v = 0 := fun v => by
      have hr : LinearMap.range T = ⊥ := Submodule.finrank_eq_zero.mp h0
      exact (LinearMap.range_eq_bot.mp hr) ▸ rfl
    have h1 : φ₈ ⟨((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q),
        Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL a ha))⟩ = 1 := by
      refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hmv a ha c hac v, hTz, smul_zero, add_zero,
        Units.val_one, Matrix.one_mulVec]
    exact Subgroup.mem_subgroupOf.mpr ((hK.phi_ker _).mp h1)
  obtain ⟨z₁, hz₁, hz₁x⟩ := hK.par' 1
  have ha₁V : (⟨z₁, hK.Z0_le_H0 hz₁⟩ : ↥(bar M Q (H0 M Z))) ∈
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hz₁
  have ha₁x : ∀ x, S715L.hAct hS ⟨z₁, hK.Z0_le_H0 hz₁⟩ x = x + (1 : K) • ψ x := fun x => by
    rw [S715L.hAct_apply]; exact hz₁x x
  have hle2 : Module.finrank K (LinearMap.range T) ≤ 2 := by
    have hmem := hLu ⟨_, Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL _ ha₁V))⟩
      (Subgroup.mem_subgroupOf.mp (hL _ ha₁V))
    have h2 := finrank_LB_le_two hu0 hQu hmem
    have heq : Matrix.toLin' ((φ₈ ⟨_, Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL _ ha₁V))⟩ :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1) = T := LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, hmv _ ha₁V 1 ha₁x v,
        one_smul, add_sub_cancel_left]
    rw [heq] at h2
    exact h2
  have hne1 := finrank_range_ne_one (Qf := quadPlus 4 K) (nondegenerate_polarBilin_quadPlus 4 K)
    (T := T) (fun v => (hq v).2)
  omega

theorem layer_facts (hK : KModel hS t Z0 ψ φ₈ e)
    (F : Sec715Frame (S715L.hAct hS) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) Tt)
    {h : ↥(bar M Q (H0 M Z))}
    (hL : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)))
    (hout : ¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
    {u : Fin 4 ⊕ Fin 4 → K} (hu0 : u ≠ 0) (hQu : quadPlus 4 K u = 0)
    (hLu : ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), (x : Mbar M Q) ∈ bar M Q (LB M Q B) →
      φ₈ x ∈ LomGLPlus (by norm_num : 3 ≤ 4) u)
    (hW : S715L.IsLayerSplit φ₈ (S715L.wvAct hS hK.mem))
    (hD : S715L.IsLayerSplit φ₈ (S715L.deltaAct hS hK.mem)) :
    Module.finrank K ((hc.VtSub hS.model t).map ((S715L.hAct hS h).conj ψ)) = 2 ∧
      12 ≤ Module.finrank K ↥((LinearMap.ker ψ).map ((S715L.hAct hS h).conj ψ) ⊔
        hc.VtSub hS.model t) ∧
      (∀ g ∈ bar M Q (hc.CN t), ∀ w ∈ S714.wsub hS t,
        (S715L.hAct hS h).conj ψ (S714.dmap ρ g ((S715L.hAct hS h).conj ψ w)) = 0) ∧
      (∀ (a : ↥(bar M Q (H0 M Z))) (ha : a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))),
        a ≠ 1 → Module.finrank K (LinearMap.range ((S715L.deltaAct hS hK.mem
          ⟨((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q),
            Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL a ha))⟩ :
            ↥(S715L.deltaSub hS t) →ₗ[K] ↥(S715L.deltaSub hS t)) - LinearMap.id)) = 4) := by
  classical
  obtain ⟨-, hYsq, hYV, hYW⟩ := psiX_basic hK F hL
  obtain ⟨hmv, hq, hT2⟩ := rootT hK F hL hout hu0 hQu hLu hYV
  set Y := (S715L.hAct hS h).conj ψ with hYdef
  set T := e.conj (Y.restrict hYV) with hTdef
  obtain ⟨u₈, w₈, hTS, hLR⟩ := exists_tsLine hT2
    (fun v => by rw [← coe_quadPlus]; exact (hq v).1) (fun v => (hq v).2)
  have hne : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (c : K), c ≠ 0 →
      (∀ v, (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + c • T v) →
      φ₈ x ≠ 1 := by
    intro x c hc hx h1
    have hT0 : ∀ v, T v = 0 := fun v => by
      have h2 := hx v
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact (smul_eq_zero.mp (left_eq_add.mp h2)).resolve_left hc
    have hbot : LinearMap.range T = ⊥ := LinearMap.range_eq_bot.mpr (LinearMap.ext hT0)
    rw [hbot, finrank_bot] at hT2
    exact absurd hT2 (by norm_num)
  have hact : ∀ (a : ↥(bar M Q (H0 M Z))) (c : K), (∀ x, S715L.hAct hS a x = x + c • ψ x) →
      ∀ y, (ρ ((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q)).toAdd y = y + c • Y y :=
    fun a c hac y => by
      rw [← S715L.hAct_apply]
      exact conj_apply_of_eq (S715L.hAct hS) hac h y
  have ho3 : Module.finrank K ((hc.VtSub hS.model t).map Y) = 2 := by
    rw [← map_range_restrict Y hYV, Submodule.finrank_map_subtype_eq, ← finrank_range_conj e,
      ← hTdef, hT2]
  obtain ⟨z₁, hz₁, hz₁x⟩ := hK.par' 1
  have ha₁V : (⟨z₁, hK.Z0_le_H0 hz₁⟩ : ↥(bar M Q (H0 M Z))) ∈
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hz₁
  have ha₁x : ∀ x, S715L.hAct hS ⟨z₁, hK.Z0_le_H0 hz₁⟩ x = x + (1 : K) • ψ x := fun x => by
    rw [S715L.hAct_apply]; exact hz₁x x
  set x₁ : ↥(bar M Q (Rt M (LB M Q B) t)) :=
    ⟨_, Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL _ ha₁V))⟩ with hx₁def
  have hx₁ : ∀ y, (ρ (x₁ : Mbar M Q)).toAdd y = y + Y y := fun y => by
    rw [hact _ 1 ha₁x y, one_smul]
  have hφx₁ := hmv _ ha₁V 1 ha₁x
  have hx₁R := hLR _ 1 hφx₁
  have hx₁ne := hne x₁ 1 one_ne_zero hφx₁
  obtain ⟨Y₁, Y₂, hc12, hirr1, hirr2, -, -, hrs1, hrs2⟩ := hW
  have h4 := finrank_range_sub_id_of_isCompl hc12 hirr1.2.1 hirr2.2.1 x₁
    ((hrs1 u₈ w₈ hTS).1 x₁ hx₁R hx₁ne) ((hrs2 u₈ w₈ hTS).1 x₁ hx₁R hx₁ne)
  have ho1 := hK.le_finrank_of_wvQ hx₁ h4
  obtain ⟨c₀, hc₀0, hc₀1⟩ := hK.exists_ne_zero_one
  obtain ⟨z₀, hz₀, hz₀x⟩ := hK.par' c₀
  have ha₀V : (⟨z₀, hK.Z0_le_H0 hz₀⟩ : ↥(bar M Q (H0 M Z))) ∈
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hz₀
  have ha₀x : ∀ x, S715L.hAct hS ⟨z₀, hK.Z0_le_H0 hz₀⟩ x = x + c₀ • ψ x := fun x => by
    rw [S715L.hAct_apply]; exact hz₀x x
  set x₀ : ↥(bar M Q (Rt M (LB M Q B) t)) :=
    ⟨_, Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL _ ha₀V))⟩ with hx₀def
  have hx₀ : ∀ y, (ρ (x₀ : Mbar M Q)).toAdd y = y + c₀ • Y y := hact _ c₀ ha₀x
  have hφx₀ := hmv _ ha₀V c₀ ha₀x
  have hx₀R := hLR _ c₀ hφx₀
  have hmat := matrix_sub_one_eq hφx₀ hφx₁
  obtain ⟨D₁, D₂, hcD, hirrD1, hirrD2, -, -, hrsD1, hrsD2⟩ := hD
  have hrel := sub_eq_smul_of_isCompl hcD ((hrsD1 u₈ w₈ hTS).2 x₁ x₀ hx₁R hx₀R c₀ hmat)
    ((hrsD2 u₈ w₈ hTS).2 x₁ x₀ hx₁R hx₀R c₀ hmat)
  have ho2 : ∀ g ∈ bar M Q (hc.CN t), ∀ w ∈ S714.wsub hS t, Y (S714.dmap ρ g (Y w)) = 0 := by
    intro g hg w hw
    have h5 := ydy_of_rel hK hYsq hYW hc₀0 hc₀1 hx₁ hx₀ hrel
      ⟨S714.delta hS t g (S714.mem_bar_H0_of_CN hg), S715L.delta_mem_deltaSub hS hg⟩ ⟨w, hw⟩
    simpa [S714.delta_apply] using h5
  have ho4 : ∀ (a : ↥(bar M Q (H0 M Z))) (ha : a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))),
      a ≠ 1 → Module.finrank K (LinearMap.range ((S715L.deltaAct hS hK.mem
        ⟨((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q),
          Subgroup.mem_subgroupOf.mp (F.L_le_Rb (hL a ha))⟩ :
          ↥(S715L.deltaSub hS t) →ₗ[K] ↥(S715L.deltaSub hS t)) - LinearMap.id)) = 4 := by
    intro a ha ha1
    obtain ⟨c, hc⟩ := hK.par (a : Mbar M Q) (Subgroup.mem_subgroupOf.mp ha)
    have hac : ∀ x, S715L.hAct hS a x = x + c • ψ x := fun x => by
      rw [S715L.hAct_apply]; exact hc x
    have hc0 : c ≠ 0 := by
      rintro rfl
      refine ha1 (Subtype.ext (hK.faith _ _ fun x => ?_))
      rw [hc x, zero_smul, add_zero]
      exact (S715L.act_one_apply x).symm
    have hφa := hmv a ha c hac
    have haR := hLR _ c hφa
    have hane := hne _ c hc0 hφa
    exact finrank_range_sub_id_of_isCompl hcD hirrD1.2.1 hirrD2.2.1 _
      ((hrsD1 u₈ w₈ hTS).1 _ haR hane) ((hrsD2 u₈ w₈ hTS).1 _ haR hane)
  exact ⟨ho3, ho1, ho2, ho4⟩

end Frame

end KModel

end CFSG.RankThree.GF2n.Stroth80.S715K
