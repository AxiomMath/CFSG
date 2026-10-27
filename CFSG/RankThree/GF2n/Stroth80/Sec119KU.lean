module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec11Torus
public import CFSG.RankThree.GF2n.Stroth80.Sec111Order
import CFSG.LinearAlgebra.PlaneTwoGroupCommutator
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110LineCent
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

@[expose] def fixA2Plane (M Q Z : Subgroup G) [(Q.subgroupOf M).Normal] (a : G) :
    Set (Mbar M Q) :=
  {c | ∃ k : ↥(H0 M Z), mkH M Q Z k = c ∧ ⁅(k : G), a⁆ ∈ Q ∧
    ∀ x ∈ ⁅Q, Subgroup.zpowers a⁆, ⁅(k : G), x⁆ ∈ Z}

omit [(Q.subgroupOf M).Normal] in
private theorem Ctx.commutator_zpowers_le_Q (hc : Ctx M Q Z B) {a : G} (ha : a ∈ M) :
    ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact hc.comm_mem_Q (M.zpow_mem ha n) hx

theorem Ctx.mem_fixA2Plane_of_liftF_fix (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {a : G} (haH : a ∈ H0 M Z)
    {c : Mbar M Q} (hcH : c ∈ bar M Q (H0 M Z))
    (hca : c * (QuotientGroup.mk (⟨a, H0_le_M haH⟩ : ↥M) : Mbar M Q) =
      (QuotientGroup.mk (⟨a, H0_le_M haH⟩ : ↥M) : Mbar M Q) * c)
    (hfix : ∀ u ∈ LinearMap.range ((φ ⟨a, haH⟩ : M₀.E →ₗ[K] M₀.E) - 1), liftF φ c u = u) :
    c ∈ fixA2Plane M Q Z a := by
  obtain ⟨k, rfl⟩ := mem_bar_H0_iff.mp hcH
  refine ⟨k, rfl, (mk_commute_iff ⟨(k : G), H0_le_M k.2⟩ ⟨a, H0_le_M haH⟩).mp hca,
    fun x hx => ?_⟩
  have hxQ : x ∈ Q := hc.commutator_zpowers_le_Q (H0_le_M haH) hx
  have hkx : (k : G) * x * (k : G)⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M (H0_le_M k.2)).1 x hxQ
  obtain ⟨haQ, haQ'⟩ := hc.conj_mem_Q_of_mem_M (H0_le_M haH)
  have hu : M₀.π x ∈ LinearMap.range ((φ ⟨a, haH⟩ : M₀.E →ₗ[K] M₀.E) - 1) :=
    (Tim79.QuadModel.mem_img_commutator_zpowers (φ ⟨a, haH⟩) haQ haQ'
      (fun y hy => hφπ ⟨a, haH⟩ y hy)).mp (M₀.pi_mem_img hx hxQ)
  have h1 := hfix _ hu
  rw [liftF_mkH hφker] at h1
  rw [Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ hkx, hφπ k x hxQ, h1]

noncomputable def xbarAct (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) :
    ↥(Xbar M Q Z B) →* (M₀.E ≃ₗ[K] M₀.E) where
  toFun c := liftF φ (c : Mbar M Q)
  map_one' := by
    have h := liftF_mkH hφker 1
    rw [map_one, map_one] at h
    exact h
  map_mul' c d := liftF_mul hφker (mem_bar_H0_iff.mp (hc.Xbar_le_bar_H0 c.2))
    (mem_bar_H0_iff.mp (hc.Xbar_le_bar_H0 d.2))

theorem xbarAct_apply (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) (c : ↥(Xbar M Q Z B)) :
    xbarAct hc φ hφker c = liftF φ (c : Mbar M Q) := by
  rfl

theorem xbarAct_comm (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {t p : ↥(Xbar M Q Z B)}
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : xbarAct hc φ hφker t = T) (htp : t * p = p * t) (e : M₀.E) :
    xbarAct hc φ hφker p (T e) = T (xbarAct hc φ hφker p e) := by
  calc xbarAct hc φ hφker p (T e) = (xbarAct hc φ hφker p * xbarAct hc φ hφker t) e := by
        rw [hT]
        rfl
    _ = (xbarAct hc φ hφker t * xbarAct hc φ hφker p) e := by rw [← map_mul, ← map_mul, htp]
    _ = T (xbarAct hc φ hφker p e) := by
        rw [hT]
        rfl

theorem xbarAct_mem_range (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {t p : ↥(Xbar M Q Z B)}
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : xbarAct hc φ hφker t = T) (htp : t * p = p * t)
    {u : M₀.E} (hu : u ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :
    xbarAct hc φ hφker p u ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
  obtain ⟨w, rfl⟩ := hu
  refine ⟨xbarAct hc φ hφker p w, ?_⟩
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub,
    xbarAct_comm hc hφker hT htp]

theorem Ctx.forall_mem_fixA2Plane_or (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M))
    {S : Set ↥(Xbar M Q Z B)} {P R : Subgroup ↥(Xbar M Q Z B)}
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1) (hPS : Subgroup.closure S = P)
    (hPt : P ≤ Subgroup.centralizer {t}) (hRP : R ≤ P)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hR : IsPGroup 2 R) :
    (∀ r ∈ R, (r : Mbar M Q) ∈ fixA2Plane M Q Z a) ∨
      ∀ c ∈ ⁅P, P⁆, (c : Mbar M Q) ∈ fixA2Plane M Q Z a := by
  obtain ⟨n, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hD
  have haH : a ∈ H0 M Z := hc.LB_le_H0 ha
  have hK : 1 < Nat.card (GaloisField 2 n) := by
    have := hc.hyp.q4
    rw [hD.card]
    omega
  obtain ⟨haQ, haQ'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M ha)
  have hU := ((isA2_iff M₀ hD.reg hD.card hK (φ ⟨a, haH⟩) haQ haQ'
    (fun x hx => hφπ ⟨a, haH⟩ x hx)).mp hA).2.2.1
  have hT : xbarAct hc φ hφker t = φ ⟨a, haH⟩ := by
    show liftF φ (t : Mbar M Q) = φ ⟨a, haH⟩
    rw [ht]
    exact liftF_mkH hφker ⟨a, haH⟩
  have hcomm : ∀ p ∈ P, t * p = p * t := fun p hp =>
    Subgroup.mem_centralizer_iff.mp (hPt hp) t (Set.mem_singleton t)
  have hbridge : ∀ c ∈ P, (∀ u ∈ LinearMap.range
      ((φ ⟨a, haH⟩ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1), xbarAct hc φ hφker c u = u) →
      (c : Mbar M Q) ∈ fixA2Plane M Q Z a := by
    intro c hcP hfix
    refine hc.mem_fixA2Plane_of_liftF_fix hφπ hφker haH (hc.Xbar_le_bar_H0 c.2) ?_ hfix
    have h1 := congrArg (fun g : ↥(Xbar M Q Z B) => (g : Mbar M Q)) (hcomm c hcP)
    simp only [Subgroup.coe_mul, ht] at h1
    exact h1.symm
  have hPP : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  rcases CFSG.LinearAlgebra.fix_or_commutator_fix_of_finrank_eq_two (xbarAct hc φ hφker) hU hS
    hPS (fun p hp u hu => xbarAct_mem_range hc hφker hT (hcomm p hp) hu) hRP hRn hR with h | h
  · exact Or.inl fun r hr => hbridge r (hRP hr) (h r hr)
  · exact Or.inr fun c hc' => hbridge c (hPP hc') (h c hc')

theorem IsLBTorus.commute_of_mem_fixA2Plane {y : G}
    (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a)
    {c : Mbar M Q} (hcK : c ∈ fixA2Plane M Q Z a) {i : ℕ} {m : ↥M}
    (hm : (m : G) = y ^ i * a * (y ^ i)⁻¹) :
    c * QuotientGroup.mk m = QuotientGroup.mk m * c := by
  obtain ⟨k, rfl, hka, hkfix⟩ := hcK
  have h := hy.comm_conj_mem_Q_of_fix hc ha hA k.2 hka hkfix i
  rw [← hm] at h
  exact (mk_commute_iff ⟨(k : G), H0_le_M k.2⟩ m).mpr h

end CFSG.RankThree.GF2n.Stroth80
