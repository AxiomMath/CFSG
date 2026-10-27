module

public import CFSG.RankThree.PartOne.SEITZ12.SylowTwo
public import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.RankThree.PartOne.SEITZ12.TConj

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover
  CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable (m) (K) in
@[expose] def inTwoA (x : ModGL F4.tag K) : Prop :=
  ∃ g ∈ F4.reeGamma K m, g * centralZ K m 1 * g⁻¹ = x

theorem inTwoA_conj {x g : ModGL F4.tag K} (hx : inTwoA m K x) (hg : g ∈ F4.reeGamma K m) :
    inTwoA m K (g * x * g⁻¹) := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨g * h, mul_mem hg hh, by group⟩

theorem inTwoA_centralZ (hK : Nat.card K = 2 ^ (2 * m + 1)) {c : K} (hc : c ≠ 0) :
    inTwoA m K (centralZ K m c) := by
  obtain ⟨h, hh, hh'⟩ := exists_torus_conj_sylowH hK (one_ne_zero (α := K)) hc
  refine ⟨h, reeFixedTorus_le_reeGamma' hh, ?_⟩
  rw [← sylowH_zero_eq_centralZ, ← sylowH_zero_eq_centralZ]
  exact hh'

theorem inTwoA_sylowB_zero (hK : Nat.card K = 2 ^ (2 * m + 1)) {c : K} (hc : c ≠ 0) :
    inTwoA m K (sylowB m K 0 c) := by
  have hn : weylOne K * weylTwo K * weylOne K ∈ F4.reeGamma K m :=
    mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem
  have h1 := weyl_conj_sylowB_zero (m := m) (K := K) c
  rw [sylowH_zero_eq_centralZ] at h1
  have h2 : sylowB m K 0 c = (weylOne K * weylTwo K * weylOne K)⁻¹ * centralZ K m c *
      (weylOne K * weylTwo K * weylOne K) := by
    rw [← h1]; group
  rw [h2]
  have := inTwoA_conj (inTwoA_centralZ hK hc) (inv_mem hn)
  simpa using this

theorem inTwoA_of_involution_rankOneGroupTwo (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {x : ModGL F4.tag K} (hx : x ∈ rankOneGroupTwo K m) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    inTwoA m K x := by
  obtain ⟨g, hg, c, hc, hgx⟩ := phi4_involution_conj hm hK hx hx2 hx1
  have hΓ : g⁻¹ ∈ F4.reeGamma K m := inv_mem (rankOneGroupTwo_le_reeGamma hK hg)
  have h := inTwoA_conj (inTwoA_sylowB_zero hK hc) hΓ
  rw [← hgx] at h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

omit [Finite K] [CharP K F4.prime] in
theorem phi4_fixedOrbitElement_sq (j : Fin F4.fixedOrbitCount) :
    F4.fixedOrbitElement j * F4.fixedOrbitElement j = 1 := by
  refine ext_single fun i => ?_
  rw [mul_smul, one_smul, fixedOrbitElement_smul, fixedOrbitElement_smul]
  revert i j
  decide +kernel

theorem weylOne_mul_self : weylOne K * weylOne K = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h := Q1327T.canonicalRep_mul_charTwo (τ := F4.tag) (R := K)
    (F4.fixedOrbitElement ⟨0, by decide⟩) (F4.fixedOrbitElement ⟨0, by decide⟩)
  rw [phi4_fixedOrbitElement_sq, canonicalRep_one] at h
  exact h.symm

theorem weylTwo_mul_self : weylTwo K * weylTwo K = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h := Q1327T.canonicalRep_mul_charTwo (τ := F4.tag) (R := K)
    (F4.fixedOrbitElement ⟨1, by decide⟩) (F4.fixedOrbitElement ⟨1, by decide⟩)
  rw [phi4_fixedOrbitElement_sq, canonicalRep_one] at h
  exact h.symm

theorem phi4_sylowB_ne_centralZ (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    sylowB m K 0 1 ≠ centralZ K m 1 := by
  intro h
  have hB : sylowVec m K (Pi.single 2 1) = sylowB m K 0 1 := by
    simp [sylowVec, sylowV, sylowA, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  have hZ : sylowVec m K (Pi.single 8 1) = centralZ K m 1 := by
    rw [← sylowH_zero_eq_centralZ]
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  have h1 := (bijOn_sylowVec hK).injOn (Set.mem_univ _) (Set.mem_univ _)
    (hB.trans (h.trans hZ.symm))
  have h2 := congrFun h1 2
  simp at h2

theorem inTwoA_szNw (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    inTwoA m K (szNw K) := by
  have h1 : (weylOne K)⁻¹ = weylOne K := inv_eq_of_mul_eq_one_right weylOne_mul_self
  have ht : szNw K = weylOne K * weylTwo K * (weylOne K)⁻¹ := by rw [szNw_eq_weyl, h1]
  have hne : weylTwo K ≠ 1 := by
    intro h2
    have h3 : szNw K = 1 := by rw [szNw_eq_weyl, h2, mul_one, weylOne_mul_self]
    have h4 := szNw_conj_sylowB_zero (m := m) (K := K) 1
    rw [h3] at h4
    exact phi4_sylowB_ne_centralZ hK (by simpa using h4)
  have h2 : inTwoA m K (weylTwo K) :=
    inTwoA_of_involution_rankOneGroupTwo hm hK weylTwo_mem_rankOneGroupTwo weylTwo_mul_self hne
  rw [ht]
  exact inTwoA_conj h2 weylOne_mem

theorem mixed_conj_sylowL (hK : Nat.card K = 2 ^ (2 * m + 1)) {c i : K} (hc : c ≠ 0) (hi : i ≠ 0) :
    ∃ g ∈ F4.reeGamma K m, g * (sylowB m K 0 c * sylowH m K 0 i) * g⁻¹ = sylowL m K 1 := by
  obtain ⟨h, hh, hh'⟩ := exists_torus_conj_sylowB_mul_sylowH hK hc hi (one_ne_zero (α := K))
    (one_ne_zero (α := K))
  have hBU : sylowB m K 1 0 ∈ F4.reeGamma K m :=
    reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK 1 0))
  have hAU : sylowA m K 1 ∈ F4.reeGamma K m :=
    reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK 1))
  refine ⟨(sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h,
    mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hBU weylTwo_mem) hBU) hAU) weylOne_mem)
      (reeFixedTorus_le_reeGamma' hh), ?_⟩
  calc (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h *
        (sylowB m K 0 c * sylowH m K 0 i) *
          ((sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h)⁻¹ =
      (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) *
        (h * (sylowB m K 0 c * sylowH m K 0 i) * h⁻¹) *
          (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K)⁻¹ := by group
    _ = sylowL m K 1 := by rw [hh', fusion_word]

theorem phi4c_centralZ_ne_sylowL (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∀ g ∈ F4.reeGamma K m, g * centralZ K m 1 * g⁻¹ ≠ sylowL m K 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hne⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  exact hne

theorem phi4c_centralZ_comm (c c' : K) :
    centralZ K m c * sylowB m K 0 c' = sylowB m K 0 c' * centralZ K m c := by
  have H : ∀ {i j : ℕ}, 24 ≤ i ∧ i ≤ 47 → 24 ≤ j ∧ j ≤ 47 → i ≠ j → commFactors i j = [] →
      ∀ s t : K, Commute (sylowX K i s) (sylowX K j t) :=
    fun hi hj hij h s t => sylowX_commute_of_commFactors hi hj hij h s t
  rw [← sylowH_zero_eq_centralZ, sylowH_zero_left, sylowB_zero_left]
  have h1 := H (i := 44) (j := 28) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have h2 := H (i := 44) (j := 30) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have h3 := H (i := 47) (j := 28) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have h4 := H (i := 47) (j := 30) (by norm_num) (by norm_num) (by norm_num) (by decide)
  exact (((h1 c c').mul_right (h2 c (largeReeSigma m c'))).mul_left
    ((h3 (largeReeSigma m c) c').mul_right (h4 (largeReeSigma m c) (largeReeSigma m c')))).eq

theorem not_inTwoA_mixed (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {c c' : K}
    (hc : c ≠ 0) (hc' : c' ≠ 0) : ¬ inTwoA m K (centralZ K m c * sylowB m K 0 c') := by
  rintro ⟨g, hg, hgx⟩
  obtain ⟨g', hg', hg'x⟩ := mixed_conj_sylowL hK hc' (i := c) hc
  have hy : sylowB m K 0 c' * sylowH m K 0 c = g * centralZ K m 1 * g⁻¹ := by
    rw [sylowH_zero_eq_centralZ, ← phi4c_centralZ_comm c c', hgx]
  rw [hy] at hg'x
  refine phi4c_centralZ_ne_sylowL hm hK (g' * g) (mul_mem hg' hg) ?_
  rw [← hg'x]
  group

end CFSG.RankThree.PartOne.SEITZ12
