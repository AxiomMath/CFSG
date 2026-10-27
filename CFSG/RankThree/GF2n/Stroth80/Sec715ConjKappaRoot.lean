module

public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaFacts
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappaAlg
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715K

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin
open scoped Matrix

section Generic

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [Group X]

theorem conj_apply_of_eq (φ : X →* (E ≃ₗ[K] E)) {z : X} {c : K} {ψ : E →ₗ[K] E}
    (hz : ∀ x, φ z x = x + c • ψ x) (g : X) (x : E) :
    φ (g * z * g⁻¹) x = x + c • (φ g).conj ψ x := by
  rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hz, map_add,
    map_smul, LinearEquiv.conj_apply_apply]
  congr 1
  exact (φ g).apply_symm_apply x

theorem comm_of_comm (φ : X →* (E ≃ₗ[K] E)) {a b : X} (hab : a * b = b * a)
    {ψ ψ' : E →ₗ[K] E} {c : K} (hc : c ≠ 0) (ha : ∀ x, φ a x = x + ψ x)
    (hb : ∀ x, φ b x = x + c • ψ' x) (x : E) : ψ (ψ' x) = ψ' (ψ x) := by
  have e1 : φ a (φ b x) = (x + ψ x + c • ψ' x) + c • ψ (ψ' x) := by
    rw [ha, hb, map_add, map_smul]
    abel
  have e2 : φ b (φ a x) = (x + ψ x + c • ψ' x) + c • ψ' (ψ x) := by
    rw [hb, ha, map_add, smul_add]
    abel
  have h : φ a (φ b x) = φ b (φ a x) := by
    rw [← LinearEquiv.mul_apply, ← map_mul, hab, map_mul, LinearEquiv.mul_apply]
  have h3 := add_left_cancel (e1.symm.trans (h.trans e2))
  exact smul_right_injective E hc h3

theorem inv_apply_of_eq (φ : X →* (E ≃ₗ[K] E)) {z : X} {c : K} {ψ : E →ₗ[K] E}
    (hψ : ∀ x, ψ (ψ x) = 0) (hz : ∀ x, φ z x = x + c • ψ x) (x : E) :
    φ z⁻¹ x = x - c • ψ x := by
  apply (φ z).injective
  have h1 : φ z (φ z⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h1, hz, map_sub, map_smul, hψ, smul_zero, sub_zero, sub_add_cancel]

end Generic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

structure KModel (hS : IsTensorSetup hc n M₀ ρ b) (t : G) (Z0 : Subgroup G)
    (ψ : M₀.E →ₗ[K] M₀.E) (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K)
    (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) : Prop where
  mem : t ∈ LB M Q B
  Z0_le_H0 : bar M Q Z0 ≤ bar M Q (H0 M Z)
  Z0_le_Rt : bar M Q Z0 ≤ bar M Q (Rt M (LB M Q B) t)
  psi_sq : ∀ x, ψ (ψ x) = 0
  psi_V : ∀ x, ψ x ∈ hc.VtSub hS.model t
  psi_V' : ∀ v ∈ hc.VtSub hS.model t, ∃ x, ψ x = v
  psi_W : ∀ x, ψ x = 0 ↔ x ∈ S714.wsub hS t
  par : ∀ z ∈ bar M Q Z0, ∃ c : K, ∀ x, (ρ z).toAdd x = x + c • ψ x
  par' : ∀ c : K, ∃ z ∈ bar M Q Z0, ∀ x, (ρ z).toAdd x = x + c • ψ x
  faith : ∀ a a' : Mbar M Q, (∀ x, (ρ a).toAdd x = (ρ a').toAdd x) → a = a'
  phi_range : φ₈.range = StatedOmega (StatedQuadPlus 4 K)
  phi_ker : ∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)
  phi_e : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
    e ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS mem _ x.2 _ w.2⟩ =
      (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e w
  three_lt : 3 < Nat.card K

namespace KModel

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {Z0 : Subgroup G} {ψ : M₀.E →ₗ[K] M₀.E}
  {φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K}
  {e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}

theorem exists_ne_zero_one (hK : KModel hS t Z0 ψ φ₈ e) : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
    intro c _
    by_cases hc : c = 0
    · simp [hc]
    · simp [h c hc]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  have := hK.three_lt
  omega

theorem mulVec_of_act (hK : KModel hS t Z0 ψ φ₈ e) {A : M₀.E →ₗ[K] M₀.E}
    (hA : ∀ w ∈ hc.VtSub hS.model t, A w ∈ hc.VtSub hS.model t)
    {x : ↥(bar M Q (Rt M (LB M Q B) t))} {c : K}
    (hx : ∀ y, (ρ (x : Mbar M Q)).toAdd y = y + c • A y) (v : Fin 4 ⊕ Fin 4 → K) :
    (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + c • e.conj (A.restrict hA) v := by
  obtain ⟨w, rfl⟩ := e.surjective v
  rw [← hK.phi_e x w, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  have h1 : (⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS hK.mem _ x.2 _ w.2⟩ :
      ↥(hc.VtSub hS.model t)) = w + c • A.restrict hA w :=
    Subtype.ext (hx w)
  rw [h1, map_add, map_smul]

theorem quad_mulVec (hK : KModel hS t Z0 ψ φ₈ e) (x : ↥(bar M Q (Rt M (LB M Q B) t)))
    (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K ((φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) = quadPlus 4 K v := by
  have hx : φ₈ x ∈ StatedOmega (StatedQuadPlus 4 K) :=
    hK.phi_range ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
  exact (ElemMatrixIso.plus (by norm_num : 3 ≤ 4)).quad_mulVec hx v

theorem quad_T (hK : KModel hS t Z0 ψ φ₈ e) {A : M₀.E →ₗ[K] M₀.E}
    (hA : ∀ w ∈ hc.VtSub hS.model t, A w ∈ hc.VtSub hS.model t)
    (hpar : ∀ c : K, ∃ x : ↥(bar M Q (Rt M (LB M Q B) t)),
      ∀ y, (ρ (x : Mbar M Q)).toAdd y = y + c • A y) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K (e.conj (A.restrict hA) v) = 0 ∧
      polar (quadPlus 4 K) v (e.conj (A.restrict hA) v) = 0 := by
  obtain ⟨c₀, hc₀, hc₁⟩ := hK.exists_ne_zero_one
  obtain ⟨x₁, hx₁⟩ := hpar 1
  obtain ⟨x₀, hx₀⟩ := hpar c₀
  refine quad_eq_zero_of_isometry (Qf := quadPlus 4 K) (T := e.conj (A.restrict hA)) hc₀ hc₁
    (fun w => ?_) (fun w => ?_) v
  · rw [← one_smul K (e.conj (A.restrict hA) w), ← hK.mulVec_of_act hA hx₁ w, hK.quad_mulVec]
  · rw [← hK.mulVec_of_act hA hx₀ w, hK.quad_mulVec]

end KModel

end CFSG.RankThree.GF2n.Stroth80.S715K
