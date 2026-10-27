module

public import CFSG.RankThree.GF2n.Stroth80.Sec714NotTwelve
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem nonempty_range_mulEquiv {A B E F : Type} [Group A] [Group B] [Group E] [Group F]
    (θ : A →* B) (hθ : Function.Surjective θ) (ψ : B →* E) (φ : A →* F)
    (hker : (ψ.comp θ).ker = φ.ker) : Nonempty (ψ.range ≃* φ.range) := by
  have hr : (ψ.comp θ).range = ψ.range := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨θ a, rfl⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hθ b
      exact ⟨a, rfl⟩
  have e1 := QuotientGroup.quotientKerEquivRange (ψ.comp θ)
  have e2 := QuotientGroup.quotientKerEquivRange φ
  have e3 := QuotientGroup.quotientMulEquivOfEq hker
  exact ⟨((MulEquiv.subgroupCongr hr).symm.trans (e1.symm.trans (e3.trans e2)))⟩


theorem normal_subgroupOf_of_conj_invariant {G : Type} [Group G] {R Y : Subgroup G}
    (h : ∀ r ∈ R, conjSubgroup r Y = Y) : (Y.subgroupOf R).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hx : (g : G) * (n : G) * (g : G)⁻¹ ∈ conjSubgroup (g : G) Y :=
    mem_conjSubgroup.mpr (by simpa [mul_assoc] using (Subgroup.mem_subgroupOf.mp hn))
  rw [h (g : G) g.2] at hx
  exact Subgroup.mem_subgroupOf.mpr hx

@[expose] def Sec715ZNModelStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 Zn Y : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsCentrePre Zn (hc.CN t) Q → Zn ≠ Z0 → Q ≤ Y → Y ≤ Zn →
    Y ⊓ Z0 = Q → Y ⊔ Z0 = Zn →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
    ∀ (H : Type) [Group H] (θ : ↥(Rt M (LB M Q B) t) →* H),
      Function.Surjective θ → θ.ker = Y.subgroupOf (Rt M (LB M Q B) t) →
      ∃ (γ : H → K) (M₀ : Tim79.QuadModel
          (((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ)
          ((Z0.subgroupOf (Rt M (LB M Q B) t)).map θ) K γ)
        (ψ : H →* (M₀.E ≃ₗ[K] M₀.E)),
        Tim79.GammaReg (((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ)
          ((Z0.subgroupOf (Rt M (LB M Q B) t)).map θ) γ ∧ CharP K 2 ∧
        Module.finrank K M₀.E = 8 ∧
        (∀ g : H, ∀ x ∈ ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ,
          M₀.π (g * x * g⁻¹) = ψ g (M₀.π x)) ∧
        (∀ g : H, ∀ v, M₀.Qf (ψ g v) = M₀.Qf v) ∧
        (∀ g : H, ψ g = 1 ↔ g ∈ ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ)

theorem step715ZN_of_model (hModel : Sec715ZNModelStatement) (hSplit : Sec715SplitStatement)
    (h714 : Stroth714Statement) (h711 : Stroth711StrongStatement)
    (hPerf : StatedOmegaPlusFourPerfectStatement) (hPlus : QuadraticPlusTypeStatement) :
    Step715ZNStatement := by
  intro G _ _ M Q Z B hc n t hs hn4 Z0 hZ0
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQCN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  obtain ⟨Zn, hZn⟩ := exists_isCentrePre hQCN
  by_cases hEq : Z0 = Zn
  · rw [hEq]
    exact hZn
  exfalso
  have hn16 : n = 16 := h714 G M Q Z B hc n t hs hn4
  have hnc : ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q := h711 G M Q Z B hc n t hs
  obtain ⟨Y, hQY, hYZn, hYinv, hYint, hYsup⟩ :=
    hSplit G M Q Z B hc n t hs hn4 hn16 Z0 hZ0 hnc Zn hZn (fun h => hEq h.symm)
  have hn4' := hn4
  obtain ⟨K, hKf, hKfin, hcard, φ, hrange, hkerφ, -⟩ := hn4'
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := sec9_CN_le_Rt hc t
  have hYCN : Y ≤ hc.CN t := hYZn.trans hZn.le
  haveI : (Y.subgroupOf (Rt M (LB M Q B) t)).Normal := normal_subgroupOf_of_conj_invariant hYinv
  have hNn : ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).Normal := by
    rw [← hkerφ]
    exact φ.normal_ker
  let θ : ↥(Rt M (LB M Q B) t) →* (↥(Rt M (LB M Q B) t) ⧸ Y.subgroupOf (Rt M (LB M Q B) t)) :=
    QuotientGroup.mk' _
  have hθsurj : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hθker : θ.ker = Y.subgroupOf (Rt M (LB M Q B) t) := QuotientGroup.ker_mk' _
  obtain ⟨γ, M₀, ψ, hR, hchar, hdim, hcomp, hiso, hkerψ⟩ :=
    hModel G M Q Z B hc n t hs hn4 hn16 Z0 Zn Y hZ0 hZn (fun h => hEq h.symm) hQY hYZn hYint
      hYsup K hcard _ θ hθsurj hθker
  have hPmem : ∀ r : ↥(Rt M (LB M Q B) t), θ r ∈ ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ
      ↔ (r : G) ∈ hc.CN t := by
    intro r
    constructor
    · rintro ⟨c, hc', hcr⟩
      have hk : c⁻¹ * r ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcr, inv_mul_cancel]
      rw [hθker, Subgroup.mem_subgroupOf] at hk
      have hcG : (c : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hc'
      have hrG : (r : G) = (c : G) * ((c⁻¹ * r : ↥(Rt M (LB M Q B) t)) : G) := by simp
      rw [hrG]
      exact (hc.CN t).mul_mem hcG (hYCN hk)
    · intro hr
      exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.mpr hr)
  have hψθ : ∀ r : ↥(Rt M (LB M Q B) t), ψ (θ r) = 1 ↔ (r : G) ∈ hc.CN t := fun r => by
    rw [hkerψ (θ r)]
    exact hPmem r
  have hφiff : ∀ r : ↥(Rt M (LB M Q B) t), φ r = 1 ↔ (r : G) ∈ hc.CN t := fun r => by
    rw [← MonoidHom.mem_ker, hkerφ, Subgroup.mem_subgroupOf]
  have hZcent : ∀ r z : ↥(Rt M (LB M Q B) t), (z : G) ∈ Z0 →
      θ (r * z * r⁻¹) = θ z := by
    intro r z hz
    have h1 : ⁅(z : G), (r : G)⁆ ∈ Q := hZ0.comm_mem hz (SetLike.coe_mem r)
    have h2 : ⁅(r : G), (z : G)⁆ ∈ Q := by
      have h := Q.inv_mem h1
      rwa [commutatorElement_inv] at h
    have hk : r * z * r⁻¹ * z⁻¹ ∈ θ.ker := by
      rw [hθker, Subgroup.mem_subgroupOf]
      have e : ((r * z * r⁻¹ * z⁻¹ : ↥(Rt M (LB M Q B) t)) : G) = ⁅(r : G), (z : G)⁆ := by
        simp [commutatorElement_def]
      rw [e]
      exact hQY (h2)
    rw [MonoidHom.mem_ker, map_mul, map_inv] at hk
    exact mul_inv_eq_one.mp hk
  have hnorm : ∀ g ∈ (⊤ : Subgroup (↥(Rt M (LB M Q B) t) ⧸ Y.subgroupOf (Rt M (LB M Q B) t))),
      ∀ x ∈ ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ, g * x * g⁻¹ ∈
        ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ := by
    intro g _ x hx
    obtain ⟨r, rfl⟩ := hθsurj g
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem θ (hNn.conj_mem c hc' r)
  have hcent : ∀ g ∈ (⊤ : Subgroup (↥(Rt M (LB M Q B) t) ⧸ Y.subgroupOf (Rt M (LB M Q B) t))),
      ∀ z ∈ (Z0.subgroupOf (Rt M (LB M Q B) t)).map θ, g * z * g⁻¹ = z := by
    intro g _ z hz
    obtain ⟨r, rfl⟩ := hθsurj g
    obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_inv, ← map_mul, ← map_mul, hZcent r z0 (Subgroup.mem_subgroupOf.mp hz0)]
  let ψ' := ψ.comp (⊤ : Subgroup (↥(Rt M (LB M Q B) t) ⧸
    Y.subgroupOf (Rt M (LB M Q B) t))).subtype
  let θ' : ↥(Rt M (LB M Q B) t) →* ↥(⊤ : Subgroup (↥(Rt M (LB M Q B) t) ⧸
      Y.subgroupOf (Rt M (LB M Q B) t))) :=
    θ.codRestrict _ (fun r => Subgroup.mem_top _)
  have hθ'surj : Function.Surjective θ' := by
    intro g
    obtain ⟨r, hr⟩ := hθsurj g.1
    exact ⟨r, Subtype.ext hr⟩
  have hγ' : Nonempty (ψ'.range ≃* StatedOmega (StatedQuadPlus 4 K)) := by
    have hker : (ψ'.comp θ').ker = φ.ker := by
      ext r
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact (hψθ r).trans (hφiff r).symm
    obtain ⟨e⟩ := nonempty_range_mulEquiv θ' hθ'surj ψ' φ hker
    exact ⟨e.trans (MulEquiv.subgroupCongr hrange)⟩
  have hK : 2 < Nat.card K := by
    rw [hcard]
    have := hc.hyp.q4
    omega
  have hperf := hPerf K (by rw [hcard]; exact hc.hyp.q4)
  exact false_of_range_model M₀ hR hchar hdim hK hnorm hcent ψ'
    (fun g x hx => hcomp g.1 x hx) (fun g v => hiso g.1 v) (fun g hg => (hkerψ g.1).mp hg)
    hperf hPlus hγ'

end CFSG.RankThree.GF2n.Stroth80
