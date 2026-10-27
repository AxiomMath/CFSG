module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNormLB
public import CFSG.RankThree.GF2n.Stroth80.Sec713YCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_pow_two_mem_Q [(Q.subgroupOf M).Normal] {N : Subgroup G} (hQN : Q ≤ N)
    (hNM : N ≤ M) (hN2 : IsPGroup 2 ↥(bar M Q N)) {n : G} (hn : n ∈ N) :
    ∃ k : ℕ, n ^ (2 ^ k) ∈ Q := by
  have hnM : n ∈ M := hNM hn
  have hx : QuotientGroup.mk' (Q.subgroupOf M) ⟨n, hnM⟩ ∈ bar M Q N :=
    (mk_mem_bar_iff_sec4 hQN ⟨n, hnM⟩).mpr hn
  obtain ⟨k, hk⟩ := hN2 ⟨_, hx⟩
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk' (Q.subgroupOf M) ⟨n, hnM⟩) ^ (2 ^ k) = 1 :=
    congrArg Subtype.val hk
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem sec713Y_of_inputs (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) : Sec713YStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hnormQ : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hNnorm : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, g * y * g⁻¹ ∈ hc.CN t := by
    intro g hg y hy
    refine mem_CN_conj_of_normalizes hc (hRM hg) ?_ ?_ hy
    · exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
    · exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hg)
  have hZ0n : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, g * y * g⁻¹ ∈ Z0 := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer (fun ρ hρ y hy => hnormQ ρ (hRM hρ) y hy) hg) y).mp hy
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQN : Q ≤ hc.CN t := hQZ0.trans hZN
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hCNM : hc.CN t ≤ M := fun x hx => hRM (hCNR hx)
  have hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)) := sec7_CN_pgroup_bar h34 h311a hc hs
  have key : ∃ g : ↥(Rt M (LB M Q B) t), g ^ 3 ∈ (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      g ∉ (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      ∀ s : ℕ, s % 3 = 1 → ∀ c ∈ hc.CN t, ⁅((g ^ s : ↥(Rt M (LB M Q B) t)) : G), c⁆ ∈ Z0 →
        c ∈ Z0 := by
    obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
      hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
    · have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      have hLu₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.plus hm').LomGL u := by
        rw [ElemMatrixIso.LomGL_plus hm']
        exact hLu
      have hLu₂ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.plus hm').LomGL u' := by
        rw [hLA, ElemMatrixIso.LomGL_plus hm']
        exact hLu'
      exact exists_fpf_of_hom (ElemMatrixIso.plus hm')
        (nondegenerate_polarBilin_quadPlus m' K) (by omega) φ hrange hker hNnorm hZ0n hNcomm hopp
        hLR hL2R hu hu' huu' hLu₁ hLu₂
    · have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      have hLu₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.minus hm' hirr).LomGL u := by
        rw [ElemMatrixIso.LomGL_minus hm' hirr]
        exact hLu
      have hLu₂ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.minus hm' hirr).LomGL u' := by
        rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]
        exact hLu'
      exact exists_fpf_of_hom (ElemMatrixIso.minus hm' hirr)
        (nondegenerate_polarBilin_quadMinus_of_finite m' K hirr) (by omega) φ hrange hker hNnorm
        hZ0n hNcomm hopp hLR hL2R hu hu' huu' hLu₁ hLu₂
  obtain ⟨g, hg3, hgN, hgfix⟩ := key
  have hg3N : ((g : G)) ^ 3 ∈ hc.CN t := by
    have := Subgroup.mem_subgroupOf.mp hg3
    simpa using this
  have hgNn : (g : G) ∉ hc.CN t := fun h => hgN (Subgroup.mem_subgroupOf.mpr h)
  obtain ⟨k, hk⟩ := exists_pow_two_mem_Q hQN hCNM hN2 hg3N
  obtain ⟨c, hc4⟩ : ∃ c : ℕ, 4 ^ k = 3 * c + 1 := ⟨4 ^ k / 3, by
    have : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    omega⟩
  refine ⟨((g ^ (4 ^ k) : ↥(Rt M (LB M Q B) t)) : G), (g ^ (4 ^ k)).2, ?_, ?_, ?_⟩
  ·
    intro hyQ
    apply hgNn
    have hyN : (g : G) ^ (4 ^ k) ∈ hc.CN t := by
      have := hQN hyQ
      rwa [Subgroup.coe_pow] at this
    have e : (g : G) = (((g : G) ^ 3) ^ c)⁻¹ * ((g : G) ^ (4 ^ k)) := by
      rw [hc4, ← pow_mul, pow_succ]
      exact (inv_mul_cancel_left _ _).symm
    rw [e]
    exact (hc.CN t).mul_mem ((hc.CN t).inv_mem ((hc.CN t).pow_mem hg3N c)) hyN
  ·
    have h1 : ((g ^ (4 ^ k) : ↥(Rt M (LB M Q B) t)) : G) ^ 3 =
        (((g : G) ^ 3) ^ (2 ^ k)) ^ (2 ^ k) := by
      rw [Subgroup.coe_pow, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      rw [show (4 : ℕ) ^ k = 2 ^ k * 2 ^ k from by rw [← mul_pow]; norm_num]
      ring
    rw [h1]
    exact Q.pow_mem hk _
  · intro x hx hcomm
    exact hgfix (4 ^ k) (by rw [Nat.pow_mod]; norm_num) x hx (hQZ0 hcomm)

end CFSG.RankThree.GF2n.Stroth80
