module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.RankThree.GF2n.Stroth80.Sec310NotQB
public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem sec7ctr_phi_eq_one {R : Type} [Group R] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [CharP K 2] (φ : R →* GL ι K)
    {Qf : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQf : ⇑Qf = Q₀)
    (hX : AddCommutantScalar φ.range) (hXQ : φ.range ≤ StatedOmega Q₀)
    {v₀ : ι → K} (hv₀ : Qf v₀ ≠ 0) {z : R} (hz : ∀ r : R, φ z * φ r = φ r * φ z) :
    φ z = 1 := by
  have hcomm : ∀ g ∈ φ.range, ∀ v : ι → K,
      (φ z : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ v) =
        (g : Matrix ι ι K) *ᵥ ((φ z : Matrix ι ι K) *ᵥ v) := by
    intro g hg v
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hg
    have h := congrArg Units.val (hz r)
    rw [Units.val_mul, Units.val_mul] at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  obtain ⟨c, hc⟩ := hX (AddMonoidHom.mk' (fun v => (φ z : Matrix ι ι K) *ᵥ v)
    (fun a b => Matrix.mulVec_add _ a b)) hcomm
  have hc' : ∀ v : ι → K, (φ z : Matrix ι ι K) *ᵥ v = c • v := fun v => hc v
  have hsω : φ z ∈ StatedOmega Q₀ := hXQ (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  have hsq : c * c * Qf v₀ = Qf v₀ := by
    have h1 := QuadraticMap.map_smul Qf c v₀
    rw [← hc' v₀, mem_statedOmega_preserves hQf hsω v₀, smul_eq_mul] at h1
    exact h1.symm
  have hcc : c * c = 1 := by
    have h2 : (c * c - 1) * Qf v₀ = 0 := by linear_combination hsq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hv₀)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc1 : c = 1 := by
    have h3 : (c - 1) * (c - 1) = 0 := by linear_combination hcc + (1 - c) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  have hA1 : (φ z : Matrix ι ι K) = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [hc' v, hc1, one_smul, Matrix.one_mulVec]
  exact Units.ext (by rw [Units.val_one]; exact hA1)

private theorem sec7ctr_le_of_phi {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [CharP K 2] {R N Z0 Qs : Subgroup G} (hQN : Qs ≤ N) (hZ0 : IsCentrePre Z0 R Qs)
    (φ : ↥R →* GL ι K) (hker : φ.ker = N.subgroupOf R)
    {Qf : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQf : ⇑Qf = Q₀)
    (hX : AddCommutantScalar φ.range) (hXQ : φ.range ≤ StatedOmega Q₀)
    (hv : ∃ v : ι → K, Qf v ≠ 0) : Z0 ≤ N := by
  obtain ⟨v₀, hv₀⟩ := hv
  intro x hx
  obtain ⟨hxR, hcomm⟩ := (hZ0 x).mp hx
  have hz : ∀ r : ↥R, φ ⟨x, hxR⟩ * φ r = φ r * φ ⟨x, hxR⟩ := by
    intro r
    have hkerm : ⁅(⟨x, hxR⟩ : ↥R), r⁆ ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hQN (hcomm r.1 r.2)
    have h1 : φ ⁅(⟨x, hxR⟩ : ↥R), r⁆ = 1 := hkerm
    have e : (⟨x, hxR⟩ : ↥R) * r = ⁅(⟨x, hxR⟩ : ↥R), r⁆ * (r * ⟨x, hxR⟩) := by
      simp only [commutatorElement_def]
      group
    have h2 : φ ((⟨x, hxR⟩ : ↥R) * r) = φ (r * ⟨x, hxR⟩) := by
      rw [e, map_mul, h1, one_mul]
    rwa [map_mul, map_mul] at h2
  have h1 : φ ⟨x, hxR⟩ = 1 :=
    sec7ctr_phi_eq_one φ hQf hX hXQ hv₀ (z := ⟨x, hxR⟩) hz
  have h4 : (⟨x, hxR⟩ : ↥R) ∈ φ.ker := h1
  rw [hker, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem sec7ctr_Z0_le_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ hc.CN t := by
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc hs.toSec5.mem
  obtain ⟨m, hm, hor⟩ := hs.orth
  rcases hor with h | h
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have hm2 : m = 2 := by omega
      subst hm2
      exact hs.notPlus4 h
    obtain ⟨K, fK, finK, hK, φ, hrange, hker, -⟩ := h
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    have hX : AddCommutantScalar φ.range := by
      rw [hrange]
      exact addCommutantScalar_statedOmegaPlus hm3
    have hv : ∃ v : Fin m ⊕ Fin m → K, quadPlus m K v ≠ 0 := by
      refine ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin m)) 1 +
        Pi.single (Sum.inr (⟨0, by omega⟩ : Fin m)) 1, ?_⟩
      rw [quadPlus_apply]
      simp [Pi.single_apply]
    exact sec7ctr_le_of_phi hQN hZ0 φ hker (coe_quadPlus m K) hX hrange.le hv
  · obtain ⟨K, fK, finK, hK, b, c, hirr, φ, hrange, hker, -⟩ := h
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    have hX : AddCommutantScalar φ.range := by
      rw [hrange]
      exact addCommutantScalar_statedOmegaMinus hm hirr
    have hv : ∃ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K, quadMinus m K b c v ≠ 0 := by
      refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
      rw [quadMinus_apply]
      simp [Pi.single_apply]
    exact sec7ctr_le_of_phi hQN hZ0 φ hker (coe_quadMinus m K b c) hX hrange.le hv

end CFSG.RankThree.GF2n.Stroth80
