module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.11.1)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

public theorem section14_theorem_14_11_1_arithmetic_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        Nat.Prime p ∧
          Nat.Prime q ∧
          u ≤ (p ^ q - 1) / (p - 1) ∧
          v = (q ^ p - 1) / (q - 1) := by
  intro hctx h143
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, _htypeII, _hUcomm, _hUfrob, _hPelem, _hPcard, hu,
      _hSfamCoh, _hTI, _hTauS⟩
  have hv : v = (q ^ p - 1) / (q - 1) :=
    (section14_theorem_14_4_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143).2
  exact ⟨hp, hq, hu, hv⟩


public theorem section14_index_ratio_lt_of_bounds {p q v k e : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hv : 0 < v) (hqp : q < p)
    (hepos : 0 < e) (hkgt : 2 * p * v < k) (he_le : e ≤ p * q) :
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) < ((k - 1 : ℕ) : ℝ) / (e : ℝ) := by
  have hq_lt_2p : q < 2 * p := by nlinarith
  have hqv_lt_k : q * v < k := by
    have hqv_lt_2pv : q * v < (2 * p) * v :=
      Nat.mul_lt_mul_of_pos_right hq_lt_2p hv
    exact lt_trans
      (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hqv_lt_2pv)
      hkgt
  have hqv_le_k_sub : q * v ≤ k - 1 := by omega
  have hq_v_sub_lt : q * (v - 1) < k - 1 := by
    have hpred_lt : v - 1 < v := by omega
    have hq_v_sub_lt_qv : q * (v - 1) < q * v :=
      Nat.mul_lt_mul_of_pos_left hpred_lt hq
    exact lt_of_lt_of_le hq_v_sub_lt_qv hqv_le_k_sub
  have hnat : e * (v - 1) < p * (k - 1) := by
    calc
      e * (v - 1) ≤ (p * q) * (v - 1) := Nat.mul_le_mul_right (v - 1) he_le
      _ = p * (q * (v - 1)) := by ring
      _ < p * (k - 1) := Nat.mul_lt_mul_of_pos_left hq_v_sub_lt hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have heR : (0 : ℝ) < e := by exact_mod_cast hepos
  field_simp [ne_of_gt hpR, ne_of_gt heR]
  have hnat' : (v - 1) * e < p * (k - 1) := by
    simpa [Nat.mul_comm] using hnat
  exact_mod_cast hnat'

public theorem section14_two_mul_lt_mul_of_odd_factor
    {p v x k : ℕ}
    (hpOdd : Odd p)
    (hv : 0 < v)
    (hk : k = v * x)
    (hxOdd : Odd x)
    (hxne : x ≠ 1)
    (hdiv : p ∣ x - 1) :
    2 * p * v < k := by
  rcases hdiv with ⟨t, ht⟩
  rcases hpOdd with ⟨rp, hrp⟩
  rcases hxOdd with ⟨rx, hrx⟩
  have hx_pos : 0 < x := by omega
  have hx_eq : x = p * t + 1 := by
    calc
      x = (x - 1) + 1 := (Nat.succ_pred_eq_of_pos hx_pos).symm
      _ = p * t + 1 := by rw [ht]
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    apply hxne
    rw [hx_eq, ht0]
    simp
  have ht_ne_one : t ≠ 1 := by
    intro ht1
    have hx_eq_p : x = p + 1 := by simpa [ht1] using hx_eq
    rw [hrx, hrp] at hx_eq_p
    omega
  have ht_ge_two : 2 ≤ t := by omega
  have hpt_ge : 2 * p ≤ p * t := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_left p ht_ge_two
  have hle : 2 * p * v ≤ (p * t) * v :=
    Nat.mul_le_mul_right v hpt_ge
  have hlt : (p * t) * v < (p * t + 1) * v :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self (p * t)) hv
  have hmain : 2 * p * v < (p * t + 1) * v := lt_of_le_of_lt hle hlt
  rw [hk, hx_eq]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmain

public theorem section14_odd_W1_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Odd (Nat.card W1) := by
  rcases hctx.1 with
    ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, hNotation, _hChoice, _hMin⟩
  rcases hcase with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
      _hTType, _hCover⟩
  rcases hNotation with
    ⟨_ω, _η, _μ, _ν, _μsum, _νsum, _δ, _δ', _σ, hNotationFor⟩
  rcases hNotationFor with
    ⟨hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hω with ⟨h31, _hqpos, _hppos, _ωFin, _hωNotation, _hωNat⟩
  change Section3.isCyclicTIHypothesis W1 W2 W at h31
  rcases h31 with
    ⟨_hW1le, _hW2le, _hprod31, _hcyc31, hWOdd, _hW1card, _hW2card, _hTI⟩
  exact Odd.of_dvd_nat hWOdd (Subgroup.card_dvd_of_le hprod.1)

public theorem section14_two_lt_q_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    2 < q := by
  rcases section14_context_primes_of_sourceData hctx with ⟨_hpPrime, hqPrime⟩
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hqOdd : Odd q := by
    rw [hq_card]
    exact section14_odd_W1_of_sourceData hctx
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    rw [hq2] at hqOdd
    rcases hqOdd with ⟨k, hk⟩
    omega
  exact lt_of_le_of_ne hqPrime.two_le (Ne.symm hq_ne_two)

public theorem section14_natCard_actor_dvd_group_card_sub_one
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [MulDistribMulAction A G]
    (hfree : ∀ a : A, a ≠ 1 → ∀ g : G, a • g = g → g = 1) :
    Nat.card A ∣ Nat.card G - 1 := by
  classical
  let α := {g : G // g ≠ 1}
  letI : MulAction A α :=
    { smul := fun a x => ⟨a • (x : G), by
        intro h
        apply x.2
        have h' := congrArg (fun y : G => a⁻¹ • y) h
        simpa using h'⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change (1 : A) • (x : G) = (x : G)
        simp
      mul_smul := by
        intro a b x
        apply Subtype.ext
        change (a * b) • (x : G) = a • (b • (x : G))
        rw [mul_smul] }
  have hstab : ∀ x : α, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (x : G) = (x : G) := congrArg Subtype.val hax
    exact x.2 (hfree a ha_ne (x : G) hfix)
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardα : Nat.card α = Nat.card G - 1 := by
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {g : G // g ≠ 1} = Fintype.card G - 1
    simp
  rw [hcardα, Nat.card_prod] at hcard_equiv
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A α)), by
    rw [mul_comm]
    exact hcard_equiv⟩

public theorem section14_frobeniusJoin_complement_card_dvd_kernel_card_sub_one
    {G : Type*} [Group G] [Finite G]
    (K R : Subgroup G)
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    Nat.card R ∣ Nat.card K - 1 := by
  classical
  let S : Subgroup G := K ⊔ R
  let Ksub : Subgroup S := K.subgroupOf S
  let Rsub : Subgroup S := R.subgroupOf S
  have hcardRsub : Nat.card Rsub = Nat.card R :=
    natCard_subgroupOf_eq R S le_sup_right
  have hcardKsub : Nat.card Ksub = Nat.card K :=
    natCard_subgroupOf_eq K S le_sup_left
  haveI : Ksub.Normal := IsFrobeniusGroupWithKernelComplement.normal hfrob
  letI : MulDistribMulAction Rsub Ksub :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := S) Rsub Ksub
      (Subgroup.le_normalizer_of_normal (H := Ksub))
  have hregular : ActsRegularly Rsub Ksub :=
    IsFrobeniusGroupWithKernelComplement.regular_conj_action Ksub Rsub hfrob
  have hfree : ∀ a : Rsub, a ≠ 1 → ∀ g : Ksub, a • g = g → g = 1 := by
    intro a ha g hfix
    have hgmem : g ∈ fixedPointSubgroup (↥(Subgroup.zpowers a)) Ksub := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro z
      exact smul_eq_self_of_mem_zpowers z.2 hfix
    have hgbot : g ∈ (⊥ : Subgroup Ksub) := by
      simpa [hregular a ha] using hgmem
    exact Subtype.ext (by simpa using hgbot)
  have hdiv : Nat.card Rsub ∣ Nat.card Ksub - 1 :=
    section14_natCard_actor_dvd_group_card_sub_one hfree
  rw [hcardRsub, hcardKsub] at hdiv
  exact hdiv

public theorem section14_frobeniusWithKernel_complement_card_dvd_kernel_card_sub_one
    {G : Type u} [Group G] [Finite G]
    {L H E : Subgroup G}
    (hfrob : Section7.frobeniusWithKernel L H)
    (hsemi : Section2.IsInternalSemidirectProduct L H E) :
    Nat.card E ∣ Nat.card H - 1 := by
  classical
  rcases hfrob with ⟨hHL, hHnorm, R, hcompR, _hHne, _hRne, hcent⟩
  let Hsub : Subgroup L := H.subgroupOf L
  have hcardHsub : Nat.card Hsub = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  haveI : Hsub.Normal := by
    simpa [Hsub] using hHnorm
  letI : MulDistribMulAction R Hsub :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := L) R Hsub
      (Subgroup.le_normalizer_of_normal (H := Hsub))
  have hfree : ∀ a : R, a ≠ 1 → ∀ g : Hsub, a • g = g → g = 1 := by
    intro r hr x hfix
    have hconj : (r : L) * (x : L) * (r : L)⁻¹ = (x : L) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have hcomm : (r : L) * (x : L) = (x : L) * (r : L) := by
      have h := congrArg (fun t : L => t * (r : L)) hconj
      simpa [mul_assoc] using h
    have hxcent : (x : L) ∈ Section2.centralizerIn Hsub (r : L) := by
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent_eq : Section2.centralizerIn Hsub (r : L) = ⊥ := by
      simpa [Hsub] using hcent r hr
    have hxbot : (x : L) ∈ (⊥ : Subgroup L) := by
      simpa [hcent_eq] using hxcent
    exact Subtype.ext (by simpa using hxbot)
  have hdiv : Nat.card R ∣ Nat.card Hsub - 1 :=
    section14_natCard_actor_dvd_group_card_sub_one hfree
  have hrelR : H.relIndex L = Nat.card R := by
    simpa [Subgroup.relIndex] using hcompR.symm.index_eq_card
  have hrelE : H.relIndex L = Nat.card E :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hcardRE : Nat.card R = Nat.card E := by
    rw [← hrelR, hrelE]
  rw [hcardRE, hcardHsub] at hdiv
  exact hdiv

public theorem section14_right_factor_sub_one_dvd_of_mul_sub_one_dvd
    {p v x k : ℕ}
    (hvpos : 0 < v)
    (hxpos : 0 < x)
    (hk : k = v * x)
    (hkdiv : p ∣ k - 1)
    (hvdiv : p ∣ v - 1) :
    p ∣ x - 1 := by
  have hkpos : 0 < k := by
    rw [hk]
    exact Nat.mul_pos hvpos hxpos
  have hkmod : 1 ≡ k [MOD p] :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ k)).mpr hkdiv
  have hvmod : 1 ≡ v [MOD p] :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ v)).mpr hvdiv
  have hmul : x ≡ v * x [MOD p] := by
    simpa [one_mul] using
      hvmod.mul (Nat.ModEq.refl x : x ≡ x [MOD p])
  have hkmod' : v * x ≡ 1 [MOD p] := by
    simpa [hk] using hkmod.symm
  exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ x)).mp (hmul.trans hkmod').symm

public theorem section14_card_sup_conjBy_eq_mul_of_directProduct_of_mem_centralizer
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G} {y : G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hycent : y ∈ Subgroup.centralizer (W1 : Set G)) :
    Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) = Nat.card W1 * Nat.card W2 := by
  classical
  rcases hprod with ⟨_hW1le, _hW2le, _hW, hWdisj, hcent⟩
  let E : Subgroup G := W2.conjBy y ⊔ W1
  have hW2y_cent_W1 : W2.conjBy y ≤ Subgroup.centralizer (W1 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, hzw⟩
    have hz_eq : y * w * y⁻¹ = z := by
      simpa [Subgroup.conjBy, MulAut.conj_apply] using hzw
    have hya : a * y = y * a :=
      Subgroup.mem_centralizer_iff.mp hycent a ha
    have hyinv_comm : y⁻¹ * a = a * y⁻¹ := by
      simpa [mul_assoc] using congrArg (fun t : G => y⁻¹ * t * y⁻¹) hya
    have hwa : w * a = a * w :=
      Subgroup.mem_centralizer_iff.mp (hcent ha) w hw
    calc
      a * z = a * (y * w * y⁻¹) := by rw [hz_eq]
      _ = (a * y) * w * y⁻¹ := by simp [mul_assoc]
      _ = (y * a) * w * y⁻¹ := by rw [hya]
      _ = y * (a * w) * y⁻¹ := by simp [mul_assoc]
      _ = y * (w * a) * y⁻¹ := by rw [← hwa]
      _ = y * w * (a * y⁻¹) := by simp [mul_assoc]
      _ = y * w * (y⁻¹ * a) := by rw [hyinv_comm.symm]
      _ = (y * w * y⁻¹) * a := by simp [mul_assoc]
      _ = z * a := by rw [hz_eq]
  have hW2y_norm_W1 : W2.conjBy y ≤ Subgroup.normalizer (W1 : Set G) :=
    hW2y_cent_W1.trans (centralizer_le_normalizer W1)
  haveI : (W1.subgroupOf E).Normal := by
    simpa [E] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W2.conjBy y) (N := W1) hW2y_norm_W1)
  have hWdisj_y : Disjoint W1 (W2.conjBy y) := by
    rw [disjoint_iff] at hWdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxW1 : x ∈ W1 := hx.1
      have hxW2y : x ∈ W2.conjBy y := hx.2
      rcases Subgroup.mem_map.mp hxW2y with ⟨w, hw, hzw⟩
      have hx_eq : y * w * y⁻¹ = x := by
        simpa [Subgroup.conjBy, MulAut.conj_apply] using hzw
      have hxy : x * y = y * x :=
        Subgroup.mem_centralizer_iff.mp hycent x hxW1
      have hx_conj_eq : y⁻¹ * x * y = x := by
        calc
          y⁻¹ * x * y = y⁻¹ * (x * y) := by simp [mul_assoc]
          _ = y⁻¹ * (y * x) := by rw [hxy]
          _ = x := by simp
      have hw_eq : y⁻¹ * x * y = w := by
        rw [← hx_eq]
        simp [mul_assoc]
      have hwW1 : w ∈ W1 := by
        have hx_eq_w : x = w := by
          rw [← hx_conj_eq, hw_eq]
        simpa [← hx_eq_w] using hxW1
      have hwbot : w ∈ (⊥ : Subgroup G) := by
        have hwinf : w ∈ W1 ⊓ W2 := ⟨hwW1, hw⟩
        simpa [hWdisj] using hwinf
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        have hwone : w = 1 := by simpa using hwbot
        simpa [hwone] using hx_eq.symm
      exact hxbot
    · exact bot_le
  have hWdisj_y_sub :
      Disjoint (W1.subgroupOf E) ((W2.conjBy y).subgroupOf E) := by
    rw [disjoint_iff] at hWdisj_y ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ W1 ⊓ W2.conjBy y := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, E] using hx.1,
          by simpa [Subgroup.mem_subgroupOf, E] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hWdisj_y] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hsupE :
      W1.subgroupOf E ⊔ (W2.conjBy y).subgroupOf E = ⊤ := by
    have hsupE' :
        (W2.conjBy y).subgroupOf E ⊔ W1.subgroupOf E = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (A := W2.conjBy y) (A' := W1)
        (B := E) le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_eq_top.2 le_rfl
    simpa [sup_comm] using hsupE'
  have hcomp :
      (W1.subgroupOf E).IsComplement' ((W2.conjBy y).subgroupOf E) :=
    isComplement'_of_disjoint_sup_eq_top_of_normal
      (W1.subgroupOf E) ((W2.conjBy y).subgroupOf E) hWdisj_y_sub hsupE
  have hcardE : Nat.card E = Nat.card W1 * Nat.card (W2.conjBy y) := by
    have hmul := hcomp.card_mul
    have hcardW1E : Nat.card (W1.subgroupOf E) = Nat.card W1 :=
      natCard_subgroupOf_eq W1 E le_sup_right
    have hcardW2yE :
        Nat.card ((W2.conjBy y).subgroupOf E) = Nat.card (W2.conjBy y) :=
      natCard_subgroupOf_eq (W2.conjBy y) E le_sup_left
    rw [hcardW1E, hcardW2yE] at hmul
    exact hmul.symm
  have hcardConj : Nat.card (W2.conjBy y) = Nat.card W2 :=
    section11_card_conjBy (G := G) W2 y
  rw [hcardConj] at hcardE
  simpa [E, sup_comm] using hcardE

public theorem section14_theorem_14_11_1_K_tail_typeII_formal_inputs
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D M K : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (htypeT : Section8.typeIIDefinitionData Tmax Q) :
    V ≤ K ∧ p ∣ Nat.card K - 1 ∧ K.relIndex M ≤ p * q := by
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases h1410 with
    ⟨hMmax, _hModd, hNormVleM, hKMF, _hTypeI, _hDadeM, _hPunctM, _h52M, _hCoherM,
      _hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases Section13.theorem_13_17 Tmax Smax W W2 W1 Q P V U D C M K
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hsrc)
      htypeT hMmax hNormVleM hKMF with
    ⟨hfrobMK, hVK, hcomp⟩
  have hp_card : p = Nat.card W2 := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, _hq_card, _hC, _hD,
        _hc, _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS,
        _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hp_card
  have hq_card : q = Nat.card W1 := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp_card, hq_card, _hC, _hD,
        _hc, _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS,
        _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hq_card
  have hprod : section12InternalDirectProduct W1 W2 W := by
    rcases hsrc with
      ⟨hcase, _hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD,
        _hc, _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS,
        _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hcase.1
  have hcentW2 :
      subgroupCentralizerIn (⊤ : Subgroup G) W2 = P ⊔ W1 := by
    exact (Section13.theorem_13_16 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hsrc)).2
  have hW2div_idx :
      Nat.card W2 ∣ Nat.card K - 1 ∧ K.relIndex M ≤ p * q := by
    rcases hcomp with hcompW2 | hcompSup
    · have hsemi :
          Section2.IsInternalSemidirectProduct M K W2 :=
        section14_semidirectProduct_of_frobenius_complement hfrobMK hcompW2
      have hdiv : Nat.card W2 ∣ Nat.card K - 1 :=
        section14_frobeniusWithKernel_complement_card_dvd_kernel_card_sub_one
          hfrobMK hsemi
      have hrel : K.relIndex M = Nat.card W2 :=
        Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
      have hrelp : K.relIndex M = p := by
        rw [hrel, ← hp_card]
      have hqpos : 0 < q := by
        rw [hq_card]
        exact Nat.card_pos
      exact ⟨hdiv, by rw [hrelp]; nlinarith⟩
    · rcases hcompSup with ⟨y, hyP, hcompSup⟩
      have hsemi :
          Section2.IsInternalSemidirectProduct M K (W2 ⊔ W1.conjBy y) :=
        section14_semidirectProduct_of_frobenius_complement hfrobMK hcompSup
      have hdivSup :
          Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) ∣ Nat.card K - 1 :=
        section14_frobeniusWithKernel_complement_card_dvd_kernel_card_sub_one
          hfrobMK hsemi
      have hW2dvdSup :
          Nat.card W2 ∣ Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) :=
        Subgroup.card_dvd_of_le (show W2 ≤ W2 ⊔ W1.conjBy y from le_sup_left)
      have hycent : y ∈ Subgroup.centralizer (W2 : Set G) := by
        have hySup : y ∈ P ⊔ W1 := (show P ≤ P ⊔ W1 from le_sup_left) hyP
        have hyCentIn : y ∈ subgroupCentralizerIn (⊤ : Subgroup G) W2 := by
          simpa [hcentW2] using hySup
        exact hyCentIn.2
      have hcardSup :
          Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) = p * q := by
        calc
          Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) =
              Nat.card W2 * Nat.card W1 :=
            section14_card_sup_conjBy_eq_mul_of_directProduct_of_mem_centralizer
              (section14_section12InternalDirectProduct_swap hprod) hycent
          _ = p * q := by rw [← hp_card, ← hq_card]
      have hrel : K.relIndex M = Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) :=
        Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
      exact ⟨hW2dvdSup.trans hdivSup, by rw [hrel, hcardSup]⟩
  exact ⟨hVK, by simpa [hp_card] using hW2div_idx.1, hW2div_idx.2⟩

public theorem section14_odd_right_factor_of_mul_eq
    {h u x : ℕ} (hhOdd : Odd h) (hh : h = u * x) : Odd x := by
  have hprod : Odd (u * x) := by
    simpa [hh] using hhOdd
  exact Nat.Odd.of_mul_right hprod

public theorem section14_odd_K_of_hypothesis_14_10_data
    {G : Type u} [Group G] [Finite G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Odd (Nat.card K) := by
  rcases h1410 with
    ⟨_hMmax, hModd, _hNormVleM, hKMF, _hTypeI, _hDadeM, _hPunctM, _h52M, _hCoherM,
      _hψmem, _hψirr, _hψdeg, _hβM⟩
  exact odd_of_card_dvd hModd
    (Subgroup.card_dvd_of_le (Section12.section16MFSubgroup_le hKMF))

public theorem section14_theorem_14_11_1_K_quotient_tail_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            V ≤ K ∧
              p ∣ Nat.card K - 1 ∧
              ∀ x : ℕ, Nat.card K = v * x → Odd x ∧ K.relIndex M ≤ p * q := by
  intro hctx h143 h1410 hKV
  have _hctx := hctx
  have _h143 := h143
  have _h1410 := h1410
  have _hKV := hKV
  have htypeT : Section8.typeIIDefinitionData Tmax Q := by
    have htypeT16 : section16TypeII Tmax Q :=
      section14_theorem_14_9_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
    rcases hctx.1 with
      ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
        _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rcases hcase with
      ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, hTmax, _hSMF,
        hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
        _hTType, _hCover⟩
    exact Section8.theorem_8_8_typeII_to_source_public hTmax hTMF htypeT16
  have hKodd : Odd (Nat.card K) :=
    section14_odd_K_of_hypothesis_14_10_data h1410
  rcases section14_theorem_14_11_1_K_tail_typeII_formal_inputs
      (hctx := hctx) (h1410 := h1410) htypeT with
    ⟨hVK, hKdiv, hidx⟩
  exact ⟨hVK, hKdiv,
    fun x hx => ⟨section14_odd_right_factor_of_mul_eq hKodd hx, hidx⟩⟩

public theorem section14_theorem_14_11_1_K_index_congruence_fixedPoint_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            (∃ x : ℕ, Nat.card K = v * x ∧ Odd x ∧ x ≠ 1 ∧ p ∣ x - 1) ∧
              K.relIndex M ≤ p * q := by
  intro hctx h143 h1410 hKV
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, _hq_card, _hC, _hD, _hc, _hd,
      _hUcard, hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hd_one : d = 1 :=
    Section13.theorem_13_12 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  have hVcard_eq : Nat.card V = v := by
    rw [hVcard, hd_one, Nat.mul_one]
  rcases Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1) with
    ⟨_hTmaxMF, _htypeT, _htypeII_T, _hVcomm, hVfrob, _hQelem,
      _hQcard, _hvBound, _hTfamCoh, _hTti, _hTauT⟩
  have hVdivCard : Nat.card W2 ∣ Nat.card V - 1 :=
    section14_frobeniusJoin_complement_card_dvd_kernel_card_sub_one V W2 hVfrob
  have hVdiv : p ∣ v - 1 := by
    rw [← hp_card, hVcard_eq] at hVdivCard
    exact hVdivCard
  rcases section14_theorem_14_11_1_K_quotient_tail_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨hVK, hKdiv, htail⟩
  rcases Subgroup.card_dvd_of_le hVK with ⟨x, hx⟩
  have hxcard : Nat.card K = v * x := by
    rw [hx, hVcard_eq]
  have hvpos : 0 < v := by
    rw [← hVcard_eq]
    exact Nat.card_pos
  have hxpos : 0 < x := by
    have hxne0 : x ≠ 0 := by
      intro hx0
      have hKzero : Nat.card K = 0 := by
        rw [hxcard, hx0, Nat.mul_zero]
      exact Nat.card_pos.ne' hKzero
    exact Nat.pos_of_ne_zero hxne0
  have hxdvd : p ∣ x - 1 :=
    section14_right_factor_sub_one_dvd_of_mul_sub_one_dvd
      hvpos hxpos hxcard hKdiv hVdiv
  have hxne : x ≠ 1 := by
    intro hx1
    have hcard_ge : Nat.card K ≤ Nat.card V := by
      rw [hxcard, hx1, Nat.mul_one, hVcard_eq]
    have hVK_eq : V = K := Subgroup.eq_of_le_of_card_ge hVK hcard_ge
    exact hKV hVK_eq.symm
  rcases htail x hxcard with ⟨hxOdd, hrel_le⟩
  exact ⟨⟨x, hxcard, hxOdd, hxne, hxdvd⟩, hrel_le⟩


public theorem section14_theorem_14_11_1_K_index_bounds_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            Nat.card K > 2 * p * v ∧
              K.relIndex M ≤ p * q := by
  intro hctx h143 h1410 hKV
  rcases section14_theorem_14_11_1_K_index_congruence_fixedPoint_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨hxpack, hrel_le⟩
  rcases hxpack with ⟨x, hk, hxOdd, hxne, hxdiv⟩
  have hW1odd : Odd (Nat.card W1) := section14_odd_W1_of_sourceData hctx
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, hqcard, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases section14_theorem_14_11_1_arithmetic_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨hpPrime, hqPrime, _hu, hv_formula⟩
  have hqOdd : Odd q := by
    rwa [hqcard]
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    have hnot : ¬ Odd (2 : ℕ) := by decide
    exact hnot (by simpa [hq2] using hqOdd)
  have h2q : 2 < q := lt_of_le_of_ne hqPrime.two_le (Ne.symm hq_ne_two)
  have hp_gt_two : 2 < p := lt_trans h2q hctx.2
  have hp_ne_two : p ≠ 2 := ne_of_gt hp_gt_two
  have hpOdd : Odd p := hpPrime.odd_of_ne_two hp_ne_two
  have hv_gt : p * q < v := by
    rw [hv_formula]
    exact section14_geom_quotient_gt_mul_of_prime_lt hqPrime hctx.2
  have hv_pos : 0 < v := by omega
  have hKgt : Nat.card K > 2 * p * v :=
    section14_two_mul_lt_mul_of_odd_factor hpOdd hv_pos hk hxOdd hxne hxdiv
  exact ⟨hKgt, hrel_le⟩

public theorem section14_theorem_14_11_1_K_index_source_inputs_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            2 < q ∧
              Nat.card K > 2 * p * v ∧
              K.relIndex M ≤ p * q := by
  intro hctx h143 h1410 hKV
  rcases section14_theorem_14_11_1_K_index_bounds_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨hKgt, hrel_le⟩
  have hW1odd : Odd (Nat.card W1) := section14_odd_W1_of_sourceData hctx
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, hqcard, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases section14_context_primes_of_sourceData hctx with ⟨_hpPrime, hqPrime⟩
  have hqOdd : Odd q := by
    rwa [hqcard]
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    have hnot : ¬ Odd (2 : ℕ) := by decide
    exact hnot (by simpa [hq2] using hqOdd)
  have h2q : 2 < q := lt_of_le_of_ne hqPrime.two_le (Ne.symm hq_ne_two)
  exact ⟨h2q, hKgt, hrel_le⟩

public theorem section14_theorem_14_11_1_K_index_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            2 < q ∧
              Nat.card K > 2 * p * v ∧
              ((v - 1 : ℕ) : ℝ) / (p : ℝ) <
                ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ) := by
  intro hctx h143 h1410 hKV
  rcases section14_theorem_14_11_1_K_index_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨h2q, hKgt, hrel_le⟩
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
  have hvpos : 0 < v := by
    rcases hctx.1 with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD, _hc, _hd,
        _hUcard, hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    have hv_ne_zero : v ≠ 0 := by
      intro hv0
      have hVzero : Nat.card V = 0 := by
        rw [hVcard, hv0, Nat.zero_mul]
      exact Nat.card_pos.ne' hVzero
    exact Nat.pos_of_ne_zero hv_ne_zero
  have hrel_pos : 0 < K.relIndex M := by
    have hne : (K.subgroupOf M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (G := M) (H := K.subgroupOf M)
    exact Nat.pos_of_ne_zero (by simpa [Subgroup.relIndex] using hne)
  have hqpos : 0 < q := by omega
  exact ⟨h2q, hKgt,
    section14_index_ratio_lt_of_bounds hp.pos hqpos hvpos hctx.2 hrel_pos hKgt hrel_le⟩

public theorem section14_theorem_14_11_1_source_core_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            Nat.Prime p ∧
              Nat.Prime q ∧
              2 < q ∧
              u ≤ (p ^ q - 1) / (p - 1) ∧
              v = (q ^ p - 1) / (q - 1) ∧
              Nat.card K > 2 * p * v ∧
              ((v - 1 : ℕ) : ℝ) / (p : ℝ) <
              ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ) := by
  intro hctx h143 h1410 hKV
  rcases section14_theorem_14_11_1_arithmetic_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨hp, hq, hu, hv⟩
  rcases section14_theorem_14_11_1_K_index_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨h2q, hKgt, hKineq⟩
  exact ⟨hp, hq, h2q, hu, hv, hKgt, hKineq⟩

public theorem section14_theorem_14_11_1_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            theorem_14_11_1_data M K p q u v := by
  intro hctx h143 h1410 hKV
  rcases section14_theorem_14_11_1_source_core_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨hp, hq, h2q, hu, hv, hKgt, hKineq⟩
  have hpow : q ^ (p + 1) > p ^ (q + 1) :=
    section14_pow_gt_pow_of_prime_lt hp hq h2q hctx.2
  have hratio :
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) :=
    section14_ratio_ineq_of_bounds hp hq h2q hctx.2 hu hv hpow
  exact ⟨hKgt, hratio, hKineq⟩


end CFSG.Section14
