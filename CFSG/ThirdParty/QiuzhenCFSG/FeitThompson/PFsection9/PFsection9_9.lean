module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

public theorem theorem_9_9_equal_degree_H0Cprime
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
      ∀ X Y : SH0Cprime,
        Section1.degree (X : Section1.ClassFunction M) =
          Section1.degree (Y : Section1.ClassFunction M) := by
  intro hdata X Y
  rcases hdata with ⟨_hdiv, hdeg, _hreducibles, _hnoirr⟩
  trans (q * u : ℂ)
  · exact (hdeg (X : Section1.ClassFunction M) X.property).1
  · exact ((hdeg (Y : Section1.ClassFunction M) Y.property).1).symm

private theorem theorem_9_9_case_b_count_arithmetic_sec9
    {p q u : ℕ} (hp : Nat.Prime p)
    (hdiv : u ∣ (p ^ q - 1) / (p - 1))
    (hcount : (p ^ q - 1) / u = p - 1) :
    u = (p ^ q - 1) / (p - 1) := by
  let m := p ^ q - 1
  let k := p - 1
  let n := m / k
  have hk_pos : 0 < k := by
    dsimp [k]
    exact Nat.sub_pos_of_lt hp.one_lt
  have hk_dvd_m : k ∣ m := by
    dsimp [m, k]
    exact Nat.sub_one_dvd_pow_sub_one p q
  have hm_eq_k_n : m = k * n :=
    Nat.eq_mul_of_div_eq_right hk_dvd_m rfl
  have hdivn : u ∣ n := by
    simpa [n, m, k] using hdiv
  have hu_dvd_m : u ∣ m := by
    rcases hdivn with ⟨t, ht⟩
    refine ⟨k * t, ?_⟩
    calc
      m = k * n := hm_eq_k_n
      _ = k * (u * t) := by rw [ht]
      _ = u * (k * t) := by ac_rfl
  have hm_eq_u_k : m = u * k :=
    Nat.eq_mul_of_div_eq_right hu_dvd_m (by simpa [m, k] using hcount)
  have hsame : u * k = n * k := by
    calc
      u * k = m := hm_eq_u_k.symm
      _ = k * n := hm_eq_k_n
      _ = n * k := Nat.mul_comm k n
  have hun : u = n := Nat.mul_right_cancel hk_pos hsame
  simpa [n, m, k] using hun

private theorem theorem_9_9_case_b_count_eq_of_le_sec9
    {p q u : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hu : 0 < u)
    (hdiv : u ∣ (p ^ q - 1) / (p - 1))
    (hle : (p ^ q - 1) / u ≤ p - 1) :
    (p ^ q - 1) / u = p - 1 := by
  let m := p ^ q - 1
  let k := p - 1
  let n := m / k
  have hk_pos : 0 < k := by
    dsimp [k]
    exact Nat.sub_pos_of_lt hp.one_lt
  have hk_dvd_m : k ∣ m := by
    dsimp [m, k]
    exact Nat.sub_one_dvd_pow_sub_one p q
  have hm_eq_k_n : m = k * n :=
    Nat.eq_mul_of_div_eq_right hk_dvd_m rfl
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ hp.one_lt hq.ne_zero)
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hm0 : m = 0 := by
      rw [hm_eq_k_n, hn0, mul_zero]
    exact (Nat.ne_of_gt hm_pos) hm0
  rcases hdiv with ⟨t, ht⟩
  have ht_pos : 0 < t := by
    by_contra htpos
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos htpos
    have hn0 : n = 0 := by
      dsimp [n, m, k]
      rw [ht, ht0, mul_zero]
    exact (Nat.ne_of_gt hn_pos) hn0
  have hm_eq_u_kt : m = u * (k * t) := by
    calc
      m = k * n := hm_eq_k_n
      _ = k * (u * t) := by
            simpa [n, m, k] using congrArg (fun x => k * x) ht
      _ = u * (k * t) := by ac_rfl
  have hdiv_eq : m / u = k * t := by
    rw [hm_eq_u_kt]
    exact Nat.mul_div_right (k * t) hu
  have hle_t : k * t ≤ k := by
    rw [← hdiv_eq]
    simpa [m, k] using hle
  have ht_le_one : t ≤ 1 := by
    have hle_left : k * t ≤ k * 1 := by
      simpa using hle_t
    exact Nat.le_of_mul_le_mul_left hle_left hk_pos
  have ht_eq_one : t = 1 := by
    cases t with
    | zero =>
        exact False.elim ((Nat.not_lt_zero 0) ht_pos)
    | succ s =>
        have hs_le_zero : s ≤ 0 := by
          exact Nat.succ_le_succ_iff.mp ht_le_one
        have hs : s = 0 := Nat.eq_zero_of_le_zero hs_le_zero
        simp [hs]
  calc
    (p ^ q - 1) / u = m / u := by rfl
    _ = k * t := hdiv_eq
    _ = p - 1 := by simp [k, ht_eq_one]

private theorem theorem_9_9_SH0C_subset_SH0Cprime_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C Cprime : Subgroup G)
    (SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    Cprime = (_root_.commutator C).map C.subtype →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
          SH0C ⊆ SH0Cprime := by
  intro hCprimeEq hSH0C hSH0Cprime
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  exact kernelInducedFamily_subset_of_le_sec9 M (ambientDerivedSubgroup M) MF
    (H0 ⊔ Cprime) (H0 ⊔ C) SH0Cprime SH0C
    (sup_le_sup_left hCprimeC H0) hSH0Cprime hSH0C

private theorem theorem_9_9_HC_index_eq_q_mul_u_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u := by
  intro hcase
  exact HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u
    (case_9_7_b_hypothesis_9_2_sec9 hcase)
    (case_9_7_b_barU_cardinality_sec9 hcase)

private theorem theorem_9_9_HC_subgroupOf_ambientDerived_index_eq_u_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Subgroup.index
        (((MF ⊔ C).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)) = u := by
  classical
  intro hcase
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  change Subgroup.index ((HC.subgroupOf M).subgroupOf (D.subgroupOf M)) = u
  have hidxHC :
      Subgroup.index (HC.subgroupOf M) = q * u :=
    theorem_9_9_HC_index_eq_q_mul_u_sec9 M MF U W1 W2 H0 C p q u hcase
  rcases hcase with
    ⟨h92, _hH0MF, hCentIn, _hpprime, hqprime, _hpdata, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
  have hDindex_eq_q : (D.subgroupOf M).index = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  rcases hCentIn with ⟨hC_le_U, _hCcentralizer⟩
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hHC_le_D : HC ≤ D := by
    dsimp [HC]
    exact sup_le hMFleD (hC_le_U.trans hUleD)
  have hHCsub_le_Dsub : HC.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    simpa [Subgroup.mem_subgroupOf, HC, D] using
      hHC_le_D (by simpa [Subgroup.mem_subgroupOf, HC] using hx)
  have hrel_eq_u :
      (HC.subgroupOf M).relIndex (D.subgroupOf M) = u := by
    have hmul :
        Subgroup.index (HC.subgroupOf M) =
          (HC.subgroupOf M).relIndex (D.subgroupOf M) *
            (D.subgroupOf M).index := by
      exact (Subgroup.relIndex_mul_index hHCsub_le_Dsub).symm
    have hright :
        (HC.subgroupOf M).relIndex (D.subgroupOf M) * q = u * q := by
      calc
        (HC.subgroupOf M).relIndex (D.subgroupOf M) * q
            = (HC.subgroupOf M).relIndex (D.subgroupOf M) *
                (D.subgroupOf M).index := by rw [hDindex_eq_q]
        _ = Subgroup.index (HC.subgroupOf M) := hmul.symm
        _ = q * u := hidxHC
        _ = u * q := Nat.mul_comm q u
    exact Nat.mul_right_cancel hqprime.pos hright
  change (HC.subgroupOf M).relIndex (D.subgroupOf M) = u
  exact hrel_eq_u

private theorem theorem_9_9_HC_le_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      MF ⊔ C ≤ ambientDerivedSubgroup M := by
  intro hcase
  rcases hcase with
    ⟨h92, _hH0MF, hCentIn, _hpprime, _hqprime, _hpdata, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  rcases hCentIn with ⟨hC_le_U, _hCcentralizer⟩
  exact sup_le hMFleD (hC_le_U.trans hUleD)

private theorem theorem_9_9_HC_le_M_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      MF ⊔ C ≤ M := by
  intro hcase
  exact (theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u
    hcase).trans section12_ambientDerivedSubgroup_le

private theorem theorem_9_9_case_b_U_le_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      U ≤ ambientDerivedSubgroup M := by
  intro hcase
  rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  exact hUleD

private theorem theorem_9_9_case_b_U_le_M_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      U ≤ M := by
  intro hcase
  exact (theorem_9_9_case_b_U_le_ambientDerived_sec9
    M MF U W1 W2 H0 C p q u hcase).trans section12_ambientDerivedSubgroup_le

private theorem theorem_9_9_case_b_U_le_normalizer_MF_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      U ≤ Subgroup.normalizer (MF : Set G) := by
  intro hcase
  rcases hcase with
    ⟨h92, _hH0MF, _hCentIn, _hpprime, _hqprime, _hpdata, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  exact hUleD.trans (section12_ambientDerivedSubgroup_le.trans hM_norm_MF)

private theorem theorem_9_9_case_b_H0_isInvariant_U_MF_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u) :
    let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
      theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    IsInvariant U MF (H0.subgroupOf MF) := by
  dsimp only
  let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have h92 := case_9_7_b_hypothesis_9_2_sec9 hcase
  have hMFleM : MF ≤ M := case_9_7_b_MF_le_M_sec9 hcase
  have hH0normalM : (H0.subgroupOf M).Normal :=
    case_9_7_b_H0_normal_M_sec9 hcase
  have hUleM : U ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hUleD.trans section12_ambientDerivedSubgroup_le
  exact subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF U H0
    hMFleM hUleM hH0normalM hUnormMF


private theorem quotient_image_ne_bot_of_not_le_kernel_sec9
    {L : Type u} [Group L] (A B : Subgroup L) [A.Normal]
    (hnot : ¬ B ≤ A) :
    B.map (QuotientGroup.mk' A) ≠ ⊥ := by
  intro hbot
  apply hnot
  intro b hb
  have hbmap : QuotientGroup.mk' A b ∈ B.map (QuotientGroup.mk' A) :=
    ⟨b, hb, rfl⟩
  have hbmap_bot : QuotientGroup.mk' A b ∈ (⊥ : Subgroup (L ⧸ A)) := by
    simpa [hbot] using hbmap
  have hq_one : QuotientGroup.mk' A b = 1 := by
    simpa using hbmap_bot
  exact (QuotientGroup.eq_one_iff (N := A) (x := b)).mp hq_one

private theorem quotient_internalDirectProduct_top_of_le_inf_mul_surjective_sec9
    {L : Type u} [Group L] (A H K : Subgroup L) [A.Normal]
    [IsMulCommutative (L ⧸ A)]
    (hA_le_K : A ≤ K)
    (hInf_le_A : H ⊓ K ≤ A)
    (hmul : ∀ l : L, ∃ h ∈ H, ∃ k ∈ K, l = h * k) :
    Section2.IsInternalDirectProduct (⊤ : Subgroup (L ⧸ A))
      (H.map (QuotientGroup.mk' A)) (K.map (QuotientGroup.mk' A)) := by
  let q : L →* L ⧸ A := QuotientGroup.mk' A
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x _hx
    trivial
  · intro x _hx
    trivial
  · intro x _hx y _hy
    exact mul_comm x y
  · apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨h, hhH, hhx⟩
      rcases hx.2 with ⟨k, hkK, hkx⟩
      have hkhA : k⁻¹ * h ∈ A :=
        QuotientGroup.eq.mp (hkx.trans hhx.symm)
      have hkhK : k⁻¹ * h ∈ K := hA_le_K hkhA
      have hhK : h ∈ K := by
        have : k * (k⁻¹ * h) ∈ K := K.mul_mem hkK hkhK
        simpa [mul_assoc] using this
      have hhA : h ∈ A := hInf_le_A ⟨hhH, hhK⟩
      have hq_one : q h = 1 :=
        (QuotientGroup.eq_one_iff (N := A) (x := h)).2 hhA
      have hx_one : x = 1 := by
        rw [← hhx, hq_one]
      simp [hx_one]
    · exact bot_le
  · intro x _hx
    rcases QuotientGroup.mk'_surjective (N := A) x with ⟨l, rfl⟩
    rcases hmul l with ⟨h, hhH, k, hkK, hl⟩
    refine ⟨q h, ⟨h, hhH, rfl⟩, q k, ⟨k, hkK, rfl⟩, ?_⟩
    rw [hl]
    exact (q.map_mul h k).symm

private theorem theorem_9_9_MF_normal_HC_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (MF.subgroupOf (MF ⊔ C)).Normal := by
  intro hcase
  have hHC_le_M : MF ⊔ C ≤ M :=
    theorem_9_9_HC_le_M_sec9 M MF U W1 W2 H0 C p q u hcase
  rcases hcase with
    ⟨h92, _hH0MF, _hCentIn, _hpprime, _hqprime, _hpdata, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
  rcases h92.typeP with ⟨hMFtype, _hcommon⟩
  rcases hMFtype.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hHC_le_norm_MF : MF ⊔ C ≤ Subgroup.normalizer (MF : Set G) :=
    hHC_le_M.trans hM_le_norm_MF
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show MF ≤ MF ⊔ C from le_sup_left)).2 hHC_le_norm_MF


private theorem quotientCentralizerIn_le_normalizer_of_le_normalizers_pf99_sec9
    {G : Type u} [Group G]
    {M MF U H0 C N : Subgroup G}
    (hNleM : N ≤ M)
    (hNnormU : N ≤ Subgroup.normalizer (U : Set G))
    (hNnormMF : N ≤ Subgroup.normalizer (MF : Set G))
    (hH0leM : H0 ≤ M)
    (hH0normalM : (H0.subgroupOf M).Normal)
    (hC : quotientCentralizerIn MF H0 U C) :
    N ≤ Subgroup.normalizer (C : Set G) := by
  have hforward :
      ∀ n : G, n ∈ N → ∀ x : G, x ∈ C → n * x * n⁻¹ ∈ C := by
    intro n hn x hxC
    have hxU : x ∈ U := hC.1 hxC
    have hconjU : n * x * n⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hNnormU hn) x).mp hxU
    rw [(hC.2 (n * x * n⁻¹) hconjU)]
    intro h hhMF
    have hninv_normMF : n⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normalizer (MF : Set G)).inv_mem (hNnormMF hn)
    have hh' : n⁻¹ * h * n ∈ MF := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp hninv_normMF h).mp hhMF
    have hcomm : ⁅x, n⁻¹ * h * n⁆ ∈ H0 :=
      (hC.2 x hxU).mp hxC (n⁻¹ * h * n) hh'
    let nM : M := ⟨n, hNleM hn⟩
    let cM : M := ⟨⁅x, n⁻¹ * h * n⁆, hH0leM hcomm⟩
    have hcM : cM ∈ H0.subgroupOf M := by
      simpa [cM, Subgroup.mem_subgroupOf] using hcomm
    have hconjM : nM * cM * nM⁻¹ ∈ H0.subgroupOf M :=
      hH0normalM.conj_mem cM hcM nM
    have hconjH0 : n * ⁅x, n⁻¹ * h * n⁆ * n⁻¹ ∈ H0 := by
      simpa [nM, cM, Subgroup.mem_subgroupOf] using hconjM
    have hcomm_eq :
        ⁅n * x * n⁻¹, h⁆ = n * ⁅x, n⁻¹ * h * n⁆ * n⁻¹ := by
      simp [commutatorElement_def]
      group
    rw [hcomm_eq]
    exact hconjH0
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward n hn x
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have hmem := hforward n⁻¹ hninv (n * x * n⁻¹) hx
    simpa [mul_assoc] using hmem

private theorem theorem_9_9_MF_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  have h92 := case_9_7_b_hypothesis_9_2_sec9 hcase
  rcases h92.mf.1 with ⟨_hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  exact Subgroup.Normal.subgroupOf hMFnormalM ((ambientDerivedSubgroup M).subgroupOf M)

private theorem theorem_9_9_H0_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ((H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  exact Subgroup.Normal.subgroupOf (case_9_7_b_H0_normal_M_sec9 hcase)
    ((ambientDerivedSubgroup M).subgroupOf M)

private theorem theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  rcases case_9_7_b_barU_cardinality_sec9 hcase with
    ⟨hC_le_U_card, hCnormalU, _hcardU⟩
  have h92 := case_9_7_b_hypothesis_9_2_sec9 hcase
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, _hMFUdisj⟩
  have hHC_le_D : HC ≤ D := by
    dsimp [HC, D]
    exact sup_le hMFleD (hC_le_U_card.trans hUleD)
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U_card).1 hCnormalU
  have hU_norm_HC : U ≤ Subgroup.normalizer (HC : Set G) := by
    dsimp [HC]
    exact le_normalizer_sup_of_le_normalizer_sec9 MF C U hU_norm_MF hU_norm_C
  have hMF_norm_HC : MF ≤ Subgroup.normalizer (HC : Set G) :=
    (le_sup_left : MF ≤ HC).trans (Subgroup.le_normalizer (H := HC))
  have hMFU_norm_HC : MF ⊔ U ≤ Subgroup.normalizer (HC : Set G) :=
    sup_le hMF_norm_HC hU_norm_HC
  have hD_norm_HC : D ≤ Subgroup.normalizer (HC : Set G) := by
    simpa [D, hD_eq] using hMFU_norm_HC
  change ((HC.subgroupOf M).subgroupOf (D.subgroupOf M)).Normal
  exact subgroupOf_subgroupOf_normal_of_le_normalizer_sec9 hHC_le_D hD_norm_HC

private theorem theorem_9_9_MF_C_isComplement_HC_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (MF.subgroupOf (MF ⊔ C)).IsComplement' (C.subgroupOf (MF ⊔ C)) := by
  intro hcase
  have hMFnormalHC : (MF.subgroupOf (MF ⊔ C)).Normal :=
    theorem_9_9_MF_normal_HC_sec9 M MF U W1 W2 H0 C p q u hcase
  rcases hcase with
    ⟨h92, _hH0MF, hCentIn, _hpprime, _hqprime, _hpdata, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', _hUleD, _hD_eq, hMFUdisj⟩
  rcases hCentIn with ⟨hC_le_U, _hCcentralizer⟩
  have hdisjMFC : Disjoint MF C := by
    rw [disjoint_iff] at hMFUdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : x ∈ MF ⊓ U := ⟨hx.1, hC_le_U hx.2⟩
      simpa [hMFUdisj] using hxAmb
    · exact bot_le
  have hdisjMFC_sub : Disjoint (MF.subgroupOf (MF ⊔ C)) (C.subgroupOf (MF ⊔ C)) := by
    rw [disjoint_iff] at hdisjMFC ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ C := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisjMFC] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMF_C_supTop : MF.subgroupOf (MF ⊔ C) ⊔ C.subgroupOf (MF ⊔ C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := C) (B := MF ⊔ C)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  letI : (MF.subgroupOf (MF ⊔ C)).Normal := hMFnormalHC
  exact isComplement'_of_disjoint_sup_eq_top_of_normal
    (MF.subgroupOf (MF ⊔ C)) (C.subgroupOf (MF ⊔ C)) hdisjMFC_sub hMF_C_supTop

private theorem theorem_9_9_H0_normal_MF_sup_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (H0.subgroupOf (MF ⊔ U)).Normal := by
  intro hcase
  rcases hcase with
    ⟨h92, _hH0MF, _hCentIn, _hpprime, _hqprime, hpdata, _hcard,
      _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv⟩
  rcases hpdata with ⟨_hp, _hp_eq, hpdata, _h96⟩
  rcases hpdata with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, _hMFder, hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  have hH0_le_M : H0 ≤ M := hH0_le_MF.trans hMF_le_M
  have hM_le_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1 hH0_normal_M
  have hU_le_M : U ≤ M :=
    (complement_le_right_sec9 hcomp).trans section12_ambientDerivedSubgroup_le
  have hMFU_le_M : MF ⊔ U ≤ M := sup_le hMF_le_M hU_le_M
  have hH0_le_MFU : H0 ≤ MF ⊔ U := hH0_le_MF.trans le_sup_left
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_MFU).2
    (hMFU_le_M.trans hM_le_norm_H0)

private theorem theorem_9_9_H0C_normal_MF_sup_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ((H0 ⊔ C).subgroupOf (MF ⊔ U)).Normal := by
  intro hcase
  have hH0C_le_L : H0 ⊔ C ≤ MF ⊔ U := by
    exact sup_le ((case_9_7_b_H0_le_MF_sec9 hcase).trans le_sup_left)
      ((case_9_7_b_quotientCentralizerIn_sec9 hcase).1.trans le_sup_right)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hH0C_le_L).2
  have hH0_le_L : H0 ≤ MF ⊔ U :=
    (case_9_7_b_H0_le_MF_sec9 hcase).trans le_sup_left
  have hH0normalL : (H0.subgroupOf (MF ⊔ U)).Normal :=
    theorem_9_9_H0_normal_MF_sup_U_sec9 M MF U W1 W2 H0 C p q u hcase
  have hL_norm_H0 : MF ⊔ U ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_L).1 hH0normalL
  have hMF_norm_H0C : MF ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact le_sup_left.trans hL_norm_H0
    · intro n hnMF b hbC
      exact case_9_7_b_quotientCentralizedBy_sec9 hcase b hbC n hnMF
  have hU_norm_H0C : U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    have hC_le_U : C ≤ U :=
      (case_9_7_b_quotientCentralizerIn_sec9 hcase).1
    have hCnormalU : (C.subgroupOf U).Normal :=
      (case_9_7_b_barU_cardinality_sec9 hcase).2.1
    have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U).1 hCnormalU
    exact le_normalizer_sup_of_le_normalizer_sec9 H0 C U
      (le_sup_right.trans hL_norm_H0) hU_norm_C
  exact sup_le hMF_norm_H0C hU_norm_H0C

private theorem theorem_9_9_H0C_normal_M_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ((H0 ⊔ C).subgroupOf M).Normal := by
  intro hcase
  rcases hcase with
    ⟨h92, hH0MF, hC, _hpprime, _hqprime, hpData, _hcard, _hcentBy,
      _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv⟩
  rcases hpData with ⟨_hp, _hp_eq, hpDataCore, _h96⟩
  rcases hpDataCore with
    ⟨_hH0MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  rcases h92.mf.1 with ⟨hMFleM92, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, hcompMW1, hUleD,
      _hUnil, hW1normUInM, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hH0_le_M : H0 ≤ M := hH0MF.trans hMF_le_M
  have hC_le_M : C ≤ M := hC.1.trans (hUleD.trans hDleM)
  have hH0C_le_M : H0 ⊔ C ≤ M := sup_le hH0_le_M hC_le_M
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hH0C_le_M).2 ?_
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1 hH0_normal_M
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM92).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_le_M : U ≤ M := hUleD.trans hDleM
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_pf99_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := U)
      hU_le_M Subgroup.le_normalizer hU_norm_MF hH0_le_M hH0_normal_M hC
  have hU_norm_H0C : U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 C U
      (hU_le_M.trans hM_norm_H0) hU_norm_C
  have hMF_norm_H0C :
      MF ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_le_M.trans hM_norm_H0
    · intro n hnMF b hbC
      exact (hC.2 b (hC.1 hbC)).mp hbC n hnMF
  have hMFU_norm_H0C :
      MF ⊔ U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    sup_le hMF_norm_H0C hU_norm_H0C
  have hD_norm_H0C :
      D ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    have hD_eq : D = MF ⊔ U := by
      dsimp [D]
      exact hcompDU.2.2.1
    simpa [hD_eq] using hMFU_norm_H0C
  have hW1_le_M : W1 ≤ M := hW1hall.1
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normUInM hw)).1
  have hW1_norm_C : W1 ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_pf99_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := W1)
      hW1_le_M hW1_norm_U (hW1_le_M.trans hM_norm_MF)
      hH0_le_M hH0_normal_M hC
  have hW1_norm_H0C :
      W1 ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 C W1
      (hW1_le_M.trans hM_norm_H0) hW1_norm_C
  have hDW1_norm_H0C :
      D ⊔ W1 ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    sup_le hD_norm_H0C hW1_norm_H0C
  have hM_eq : M = D ⊔ W1 := by
    dsimp [D]
    exact hcompMW1.2.2.1
  simpa [hM_eq] using hDW1_norm_H0C


private theorem theorem_9_9_MF_U_internalSemidirect_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal :
        ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
        letI : ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
        Section2.IsInternalSemidirectProduct
          (⊤ : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
          ((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M))
          ((U.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) := by
  intro h92 hKnormal
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let W : Subgroup (D.subgroupOf M) := (U.subgroupOf M).subgroupOf (D.subgroupOf M)
  letI : K.Normal := by
    simpa [D, K] using hKnormal
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, hMFUdisj⟩
  have hMFleM : MF ≤ M := hMFleD.trans hDleM
  have hUleM : U ≤ M := hUleD.trans hDleM
  have hMFsubD : MF.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hMFleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hUsubD : U.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hUleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hsupM :
      (MF.subgroupOf M) ⊔ (U.subgroupOf M) = D.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := M) hMFleM hUleM]
    simp [D, hD_eq]
  have hdisj : Disjoint K W := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      have hxMFU : (((x : D.subgroupOf M) : M) : G) ∈ MF ⊓ U := by
        exact ⟨by
            simpa [D, K, Subgroup.mem_subgroupOf] using hx.1,
          by
            simpa [D, W, Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (((x : D.subgroupOf M) : M) : G) ∈ (⊥ : Subgroup G) := by
        exact hMFUdisj.le_bot hxMFU
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : K ⊔ W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF.subgroupOf M) (A' := U.subgroupOf M)
      (B := D.subgroupOf M) hMFsubD hUsubD]
    rw [hsupM]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  exact internalSemidirectProduct_top_of_normal_isComplement'_sec9
    (isComplement'_of_disjoint_sup_eq_top_of_normal K W hdisj hsupTop)

private theorem inertiaSubgroup_eq_of_semidirect_fixed_complement_mem_sec9
    {L : Type u} [Group L] [Finite L]
    (K B W : Subgroup L) [K.Normal]
    (hBK : B ≤ K)
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) B W)
    {X : Section1.ClassFunction K}
    (hXclass : Section1.IsClassFunction X)
    (hfixW :
      ∀ w : L, w ∈ W →
        Section1.conjugateOnNormal K X w = X → w ∈ K) :
    Section1.inertiaSubgroup K X = K := by
  have hKleI : K ≤ Section1.inertiaSubgroup K X := by
    intro x hx
    change Section1.conjugateOnNormal K X x = X
    funext h
    unfold Section1.conjugateOnNormal
    change X ((⟨x, hx⟩ : K) * h * (⟨x, hx⟩ : K)⁻¹) = X h
    exact hXclass ⟨x, hx⟩ h
  apply le_antisymm
  · intro g hgI
    rcases hsemi.mul_surjective g (by trivial) with ⟨b, hbB, w, hwW, hbw⟩
    have hbK : b ∈ K := hBK hbB
    have hfixw :
        Section1.conjugateOnNormal K X w = X := by
      have hfixg :
          Section1.conjugateOnNormal K X g = X := by
        simpa [Section1.inertiaSubgroup] using hgI
      have hfixbw :
          Section1.conjugateOnNormal K X (b * w) = X := by
        simpa [hbw] using hfixg
      have herase :
          Section1.conjugateOnNormal K X (b * w) =
            Section1.conjugateOnNormal K X w :=
        conjugateOnNormal_mul_left_of_mem_sec9 X hXclass hbK
      exact herase.symm.trans hfixbw
    have hwK : w ∈ K := hfixW w hwW hfixw
    rw [hbw]
    exact K.mul_mem hbK hwK
  · exact hKleI

private theorem subgroup_eq_top_of_le_of_prime_index_ne_sec9
    {L : Type u} [Group L] [Finite L]
    {H K : Subgroup L} {q : ℕ}
    (hHK : H ≤ K)
    (hHindex : H.index = q)
    (hq : Nat.Prime q)
    (hne : K ≠ H) :
    K = ⊤ := by
  have hmul : H.relIndex K * K.index = q := by
    simpa [hHindex] using Subgroup.relIndex_mul_index hHK
  have hreldvd : H.relIndex K ∣ q := ⟨K.index, hmul.symm⟩
  rcases hq.eq_one_or_self_of_dvd (H.relIndex K) hreldvd with hrel | hrel
  · have hKH : K ≤ H := Subgroup.relIndex_eq_one.mp hrel
    exact False.elim (hne (le_antisymm hKH hHK))
  · have hmul' : q * K.index = q * 1 := by
      simpa [hrel] using hmul
    have hKindex : K.index = 1 := Nat.mul_left_cancel hq.pos hmul'
    exact Subgroup.index_eq_one.mp hKindex

private theorem inertiaSubgroup_eq_top_of_not_irreducible_induced_prime_index_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] {q : ℕ}
    (hKindex : K.index = q)
    (hq : Nat.Prime q)
    {X : Section1.ClassFunction K}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup X)
    (hIndRed : ¬ Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X)) :
    Section1.inertiaSubgroup K X = ⊤ := by
  have hXclass : Section1.IsClassFunction X :=
    Section1.isCharacter_isClassFunction X
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hXirr)
  have hKleI : K ≤ Section1.inertiaSubgroup K X :=
    Section1.proposition_1_7_inertia_contains_H K X hXclass
  by_cases hIeq : Section1.inertiaSubgroup K X = K
  · exact False.elim
      (hIndRed (inducedCF_isIrreducible_of_inertia_eq_self_sec9 K hXirr hIeq))
  · exact subgroup_eq_top_of_le_of_prime_index_ne_sec9 hKleI hKindex hq hIeq

public theorem induced_eq_imp_conjugateOrbitConj_pf99_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {φ θ : Section1.ClassFunction H}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hInd : Section1.inducedCF H φ = Section1.inducedCF H θ) :
    ∃ i : Section1.conjugateOrbitIndex H θ,
      φ = Section1.conjugateOrbitConj H θ i := by
  classical
  rcases hφ with ⟨nφ, φRep, hφirr, hφeq⟩
  rcases hθ with ⟨nθ, θRep, hθirr, hθeq⟩
  subst φ
  subst θ
  exact Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
    H φRep θRep hφirr hθirr hInd

private theorem conjugateOrbitConj_eq_self_of_inertia_top_pf99_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H)
    (hI : Section1.inertiaSubgroup H θ = ⊤)
    (i : Section1.conjugateOrbitIndex H θ) :
    Section1.conjugateOrbitConj H θ i = θ := by
  refine Quotient.inductionOn i ?_
  intro g
  have hg : g ∈ Section1.inertiaSubgroup H θ := by
    rw [hI]
    trivial
  change Section1.conjugateOnNormal H θ g = θ
  simpa [Section1.inertiaSubgroup] using hg

private theorem subgroupOfClassFunction_injective_pf99_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T) :
    Function.Injective
      (fun θ : Section1.ClassFunction H =>
        Section1.subgroupOfClassFunction (T := T) θ) := by
  intro θ ψ hθψ
  ext h
  have hval := congrFun hθψ ((Subgroup.subgroupOfEquivOfLe hHT).symm h)
  simpa [Section1.subgroupOfClassFunction, Subgroup.subgroupOfEquivOfLe] using hval

private theorem subgroupInKernel'_of_inducedCF_eq_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {θ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hEq : θ = Section1.inducedCF K ψ)
    (hθker : Section1.subgroupInKernel' θ A) :
    Section1.subgroupInKernel' ψ (A.subgroupOf K) := by
  rcases hψirr with ⟨n, ρ, _hρirr, hψeq⟩
  have hIndKer :
      Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) A := by
    simpa [hEq, hψeq] using hθker
  have hρker :
      Section1.subgroupInKernel' ρ.character (A.subgroupOf K) :=
    (Section1.proposition_1_6_a K A hAK ρ).2 hIndKer
  simpa [hψeq] using hρker

private theorem isIrreducible_subgroupOfClassFunction_pf99_sec9
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T)
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.subgroupOfClassFunction (T := T) θ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let e : H.subgroupOf T ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let ρH : Representation ℂ (H.subgroupOf T) (Fin n → ℂ) :=
    ρ.comp e.toMonoidHom
  refine ⟨n, ρH, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective
      ρ e.toMonoidHom e.surjective hρirr
  · ext h
    simp [ρH, e, Section1.subgroupOfClassFunction, hθeq,
      Representation.character, Subgroup.subgroupOfEquivOfLe]

private theorem subgroupInKernel'_subgroupOfClassFunction_pf99_sec9
    {G : Type u} [Group G] {H T A : Subgroup G}
    (_hAT : A ≤ T) (hAH : A ≤ H)
    {θ : Section1.ClassFunction H}
    (hθker : Section1.subgroupInKernel' θ (A.subgroupOf H)) :
    Section1.subgroupInKernel'
      (Section1.subgroupOfClassFunction (T := T) θ)
        ((A.subgroupOf T).subgroupOf (H.subgroupOf T)) := by
  intro a
  have haA : (((a : H.subgroupOf T) : T) : G) ∈ A := by
    have haAT : ((a : H.subgroupOf T) : T) ∈ A.subgroupOf T :=
      (a : (A.subgroupOf T).subgroupOf (H.subgroupOf T)).property
    simpa [Subgroup.mem_subgroupOf] using haAT
  let aH : A.subgroupOf H := ⟨⟨(((a : H.subgroupOf T) : T) : G), hAH haA⟩, by
    simpa [Subgroup.mem_subgroupOf] using haA⟩
  have ha := hθker aH
  simpa [Section1.subgroupOfClassFunction, aH,
    Section1.degree_subgroupOfClassFunction] using ha

private theorem subgroupInKernel'_of_subgroupOfClassFunction_pf99_sec9
    {G : Type u} [Group G] {H T A : Subgroup G}
    (hAT : A ≤ T) (_hAH : A ≤ H)
    {θ : Section1.ClassFunction H}
    (hθker : Section1.subgroupInKernel'
      (Section1.subgroupOfClassFunction (T := T) θ)
        ((A.subgroupOf T).subgroupOf (H.subgroupOf T))) :
    Section1.subgroupInKernel' θ (A.subgroupOf H) := by
  intro a
  have haA : ((a : H) : G) ∈ A := by
    exact (a : A.subgroupOf H).property
  let aT : H.subgroupOf T := ⟨⟨((a : H) : G), hAT haA⟩, by
    exact (a : H).property⟩
  have haT : (aT : T) ∈ A.subgroupOf T := by
    simpa [aT, Subgroup.mem_subgroupOf] using haA
  let aHT : (A.subgroupOf T).subgroupOf (H.subgroupOf T) := ⟨aT, haT⟩
  have ha := hθker aHT
  simpa [aT, aHT, Section1.subgroupOfClassFunction,
    Section1.degree_subgroupOfClassFunction] using ha

private theorem theorem_9_9_exists_HC_restriction_constituent_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Section1.IsIrreducibleCharacterOnGroup θ →
        ¬ Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
          Section1.subgroupInKernel' θ
            ((H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            ∃ ψ : Section1.ClassFunction
                (((MF ⊔ C).subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)),
              Section1.IsIrreducibleCharacterOnGroup ψ ∧
                Section1.scalarProduct
                  (((MF ⊔ C).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M))
                  ψ
                  (Section1.subgroupRestriction
                    (((MF ⊔ C).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) θ) ≠ 0 ∧
                  ¬ Section1.subgroupInKernel' ψ
                    (((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                        (((MF ⊔ C).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M))) ∧
                    Section1.subgroupInKernel' ψ
                      (((H0.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                          (((MF ⊔ C).subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M))) := by
  intro hcase hθirr hθnotMF hθkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) :=
    ((MF ⊔ C).subgroupOf M).subgroupOf (D.subgroupOf M)
  let A : Subgroup (D.subgroupOf M) :=
    (H0.subgroupOf M).subgroupOf (D.subgroupOf M)
  let B : Subgroup (D.subgroupOf M) :=
    (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  change ∃ ψ : Section1.ClassFunction K,
    Section1.IsIrreducibleCharacterOnGroup ψ ∧
      Section1.scalarProduct K ψ (Section1.subgroupRestriction K θ) ≠ 0 ∧
        ¬ Section1.subgroupInKernel' ψ (B.subgroupOf K) ∧
          Section1.subgroupInKernel' ψ (A.subgroupOf K)
  have hKnormal : K.Normal := by
    dsimp [K, D]
    exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q u hcase
  have hBnormal : B.Normal := by
    dsimp [B, D]
    exact theorem_9_9_MF_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q u hcase
  have hBK : B ≤ K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (le_sup_left : MF ≤ MF ⊔ C) hx
  letI : K.Normal := hKnormal
  letI : B.Normal := hBnormal
  exact exists_restriction_constituent_kernelD_sec9 K A B hBK
    hθirr hθnotMF hθkerH0


private theorem theorem_9_9_H0Cprime_le_HC_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        H0 ⊔ Cprime ≤ MF ⊔ C := by
  intro hcase hCprimeEq
  have hH0MF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  exact sup_le_sup hH0MF hCprimeC

private theorem theorem_9_9_H0Cprime_le_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        H0 ⊔ Cprime ≤ ambientDerivedSubgroup M := by
  intro hcase hCprimeEq
  exact (theorem_9_9_H0Cprime_le_HC_sec9 M MF U W1 W2 H0 C Cprime p q u
    hcase hCprimeEq).trans
      (theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u hcase)

private theorem theorem_9_9_H0Cprime_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        (((H0 ⊔ Cprime).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase hCprimeEq
  -- apply `sub_cfker_Ind_irr` to the subgroup `H0C'`.
  let D : Subgroup G := ambientDerivedSubgroup M
  have hH0Cprime_le_D :
      H0 ⊔ Cprime ≤ D := by
    dsimp [D]
    exact theorem_9_9_H0Cprime_le_ambientDerived_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hCprime_comm : Cprime = (⁅C, C⁆ : Subgroup G) := by
    rw [hCprimeEq, Subgroup.map_subtype_commutator]
  have h92 := case_9_7_b_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, _hMFUdisj⟩
  have hH0_le_M : H0 ≤ M :=
    (case_9_7_b_H0_le_MF_sec9 hcase).trans (case_9_7_b_MF_le_M_sec9 hcase)
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1
      (case_9_7_b_H0_normal_M_sec9 hcase)
  have hMF_norm_H0 : MF ≤ Subgroup.normalizer (H0 : Set G) :=
    (case_9_7_b_MF_le_M_sec9 hcase).trans hM_norm_H0
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hU_norm_H0 : U ≤ Subgroup.normalizer (H0 : Set G) :=
    hUleD.trans (hDleM.trans hM_norm_H0)
  have hMF_norm_H0Cprime :
      MF ≤ Subgroup.normalizer ((H0 ⊔ Cprime : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_norm_H0
    · intro n hnMF b hbCprime
      exact case_9_7_b_quotientCentralizedBy_sec9 hcase b
        (hCprimeC hbCprime) n hnMF
  have hU_norm_H0Cprime :
      U ≤ Subgroup.normalizer ((H0 ⊔ Cprime : Subgroup G) : Set G) := by
    rcases case_9_7_b_barU_cardinality_sec9 hcase with
      ⟨hC_le_U, hCnormalU, _hcardU⟩
    have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U).1 hCnormalU
    have hU_norm_Cprime : U ≤ Subgroup.normalizer (Cprime : Set G) := by
      have hU_norm_comm :
          U ≤ Subgroup.normalizer (((⁅C, C⁆ : Subgroup G) : Set G)) :=
        normalizer_le_normalizer_commutator_self_sec9 C U hU_norm_C
      simpa [hCprime_comm] using hU_norm_comm
    exact le_normalizer_sup_of_le_normalizer_sec9 H0 Cprime U
      hU_norm_H0 hU_norm_Cprime
  have hMFU_norm_H0Cprime :
      MF ⊔ U ≤ Subgroup.normalizer ((H0 ⊔ Cprime : Subgroup G) : Set G) :=
    sup_le hMF_norm_H0Cprime hU_norm_H0Cprime
  have hD_norm_H0Cprime :
      D ≤ Subgroup.normalizer ((H0 ⊔ Cprime : Subgroup G) : Set G) := by
    simpa [D, hD_eq] using hMFU_norm_H0Cprime
  exact subgroupOf_subgroupOf_normal_of_le_normalizer_sec9
    hH0Cprime_le_D hD_norm_H0Cprime

private theorem theorem_9_9_HC_commutator_le_H0Cprime_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        _root_.commutator
            (((MF ⊔ C).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)) ≤
          ((((H0 ⊔ Cprime).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              (((MF ⊔ C).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) := by
  intro hcase hCprimeEq
  --   rewrite (norm_joinEr nH0C') -quotientSK ?quotient_der
  --   rewrite -(der_dprod 1 defHCbar) (derG1P abHbar) dprod1g.
  -- This is the derived-subgroup calculation `HC' ≤ H0C'`.
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  let N : Subgroup G := H0 ⊔ Cprime
  have hN_le_HC : N ≤ HC := by
    dsimp [N, HC]
    exact theorem_9_9_H0Cprime_le_HC_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hCprime_comm : Cprime = (⁅C, C⁆ : Subgroup G) := by
    rw [hCprimeEq, Subgroup.map_subtype_commutator]
  have hNnormalHC : (N.subgroupOf HC).Normal := by
    rcases case_9_7_b_barU_cardinality_sec9 hcase with
      ⟨hC_le_U, hCnormalU, _hcardU⟩
    have h92 := case_9_7_b_hypothesis_9_2_sec9 hcase
    rcases h92.typeP with ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
    rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
    have hH0_le_M : H0 ≤ M :=
      (case_9_7_b_H0_le_MF_sec9 hcase).trans (case_9_7_b_MF_le_M_sec9 hcase)
    have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1
        (case_9_7_b_H0_normal_M_sec9 hcase)
    have hMF_norm_H0 : MF ≤ Subgroup.normalizer (H0 : Set G) :=
      (case_9_7_b_MF_le_M_sec9 hcase).trans hM_norm_H0
    have hDleM : D ≤ M := by
      dsimp [D]
      exact section12_ambientDerivedSubgroup_le (E := M)
    have hU_norm_H0 : U ≤ Subgroup.normalizer (H0 : Set G) :=
      hUleD.trans (hDleM.trans hM_norm_H0)
    have hMF_norm_N : MF ≤ Subgroup.normalizer (N : Set G) := by
      dsimp [N]
      apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
      · exact hMF_norm_H0
      · intro n hnMF b hbCprime
        exact case_9_7_b_quotientCentralizedBy_sec9 hcase b
          (hCprimeC hbCprime) n hnMF
    have hU_norm_N : U ≤ Subgroup.normalizer (N : Set G) := by
      have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U).1 hCnormalU
      have hU_norm_Cprime : U ≤ Subgroup.normalizer (Cprime : Set G) := by
        have hU_norm_comm :
            U ≤ Subgroup.normalizer (((⁅C, C⁆ : Subgroup G) : Set G)) :=
          normalizer_le_normalizer_commutator_self_sec9 C U hU_norm_C
        simpa [hCprime_comm] using hU_norm_comm
      dsimp [N]
      exact le_normalizer_sup_of_le_normalizer_sec9 H0 Cprime U
        hU_norm_H0 hU_norm_Cprime
    have hHC_norm_N : HC ≤ Subgroup.normalizer (N : Set G) := by
      dsimp [HC]
      exact sup_le hMF_norm_N (hC_le_U.trans hU_norm_N)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_HC).2 hHC_norm_N
  letI : (N.subgroupOf HC).Normal := hNnormalHC
  have hMFroot_le_H0sub : _root_.commutator MF ≤ H0.subgroupOf MF := by
    rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨hp, _hpval, hpData⟩
    rcases hpData with
      ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem,
        _hrest⟩
    rcases hElem with ⟨hnormal, hbarElem⟩
    letI : (H0.subgroupOf MF).Normal := hnormal
    letI : IsElementaryAbelian hp.val (MF ⧸ H0.subgroupOf MF) := hbarElem
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    infer_instance
  have hAA : ⁅MF, MF⁆ ≤ N := by
    intro x hx
    have hxmap : x ∈ (_root_.commutator MF).map MF.subtype := by
      simpa [Subgroup.map_subtype_commutator] using hx
    rcases hxmap with ⟨y, hy, hyx⟩
    have hyH0 : (y : G) ∈ H0 := hMFroot_le_H0sub hy
    rw [← hyx]
    exact Subgroup.mem_sup_left hyH0
  have hAB : ⁅MF, C⁆ ≤ N := by
    have hCMF_le_H0 : ⁅C, MF⁆ ≤ H0 :=
      (quotientCentralizedBy_iff_commutator_le_sec9).1
        (case_9_7_b_quotientCentralizedBy_sec9 hcase)
    intro x hx
    exact Subgroup.mem_sup_left
      (hCMF_le_H0 ((Subgroup.commutator_comm_le MF C) hx))
  have hBB : ⁅C, C⁆ ≤ N := by
    intro x hx
    exact Subgroup.mem_sup_right (by
      simpa [hCprimeEq, Subgroup.map_subtype_commutator] using hx)
  have hrootHC : _root_.commutator HC ≤ N.subgroupOf HC := by
    exact commutator_le_subgroupOf_of_isComplement'_pairwise_sec9
      (K := HC) (A := MF) (B := C) (N := N)
      le_sup_left le_sup_right hN_le_HC
      (theorem_9_9_MF_C_isComplement_HC_sec9 M MF U W1 W2 H0 C p q u hcase)
      hAA hAB hBB
  let Dm : Subgroup M := D.subgroupOf M
  let K : Subgroup Dm := (HC.subgroupOf M).subgroupOf Dm
  change _root_.commutator K ≤
    (((N.subgroupOf M).subgroupOf Dm).subgroupOf K)
  intro x hx
  let φ : K →* HC :=
    { toFun := fun x =>
        ⟨(((x : Dm) : M) : G), by
          have hxHCm : ((x : Dm) : M) ∈ HC.subgroupOf M := by
            have hxK : (x : Dm) ∈ (HC.subgroupOf M).subgroupOf Dm := by
              exact x.property
            change ((x : Dm) : M) ∈ HC.subgroupOf M at hxK
            exact hxK
          simpa [Subgroup.mem_subgroupOf] using hxHCm⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro a b
        ext
        rfl }
  have hxHC : φ x ∈ _root_.commutator HC :=
    monoidHom_mem_commutator_of_mem_sec9 φ hx
  have hxNsub : φ x ∈ N.subgroupOf HC := hrootHC hxHC
  have hxN : ((φ x : HC) : G) ∈ N := by
    simpa [Subgroup.mem_subgroupOf] using hxNsub
  rw [Subgroup.mem_subgroupOf]
  change (((x : Dm) : M) : G) ∈ N
  simpa [φ] using hxN

private theorem theorem_9_9_U_component_mem_HC_of_mem_C_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    {w : (ambientDerivedSubgroup M).subgroupOf M} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      w ∈ (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M) →
        (((w : (ambientDerivedSubgroup M).subgroupOf M) : M) : G) ∈ C →
          w ∈ ((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M) := by
  intro _hcase _hwU hwC
  change (w : M) ∈ (MF ⊔ C).subgroupOf M
  rw [Subgroup.mem_subgroupOf]
  exact (le_sup_right : C ≤ MF ⊔ C) hwC

private theorem theorem_9_9_HC_MF_commutator_le_H0_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ⁅MF ⊔ C, MF⁆ ≤ H0 := by
  intro hcase
  have hMFroot_le_H0sub : _root_.commutator MF ≤ H0.subgroupOf MF := by
    rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨hp, _hpval, hpData⟩
    rcases hpData with
      ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem,
        _hrest⟩
    rcases hElem with ⟨hnormal, hbarElem⟩
    letI : (H0.subgroupOf MF).Normal := hnormal
    letI : IsElementaryAbelian hp.val (MF ⧸ H0.subgroupOf MF) := hbarElem
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    infer_instance
  have hAA : ⁅MF, MF⁆ ≤ H0 := by
    intro x hx
    have hxmap : x ∈ (_root_.commutator MF).map MF.subtype := by
      simpa [Subgroup.map_subtype_commutator] using hx
    rcases hxmap with ⟨y, hy, hyx⟩
    rw [← hyx]
    exact hMFroot_le_H0sub hy
  have hCMF_le_H0 : ⁅C, MF⁆ ≤ H0 :=
    (quotientCentralizedBy_iff_commutator_le_sec9).1
      (case_9_7_b_quotientCentralizedBy_sec9 hcase)
  rw [Subgroup.commutator_le]
  intro x hxHC y hyMF
  have hC_norm_MF : C ≤ Subgroup.normalizer (MF : Set G) := by
    have hMFnormalHC : (MF.subgroupOf (MF ⊔ C)).Normal :=
      theorem_9_9_MF_normal_HC_sec9 M MF U W1 W2 H0 C p q u hcase
    have hHC_norm_MF : MF ⊔ C ≤ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (show MF ≤ MF ⊔ C from le_sup_left)).1 hMFnormalHC
    exact le_sup_right.trans hHC_norm_MF
  have hxProd : x ∈ (MF : Set G) * (C : Set G) := by
    have hsup := Subgroup.coe_mul_of_right_le_normalizer_left MF C hC_norm_MF
    rw [← hsup]
    exact hxHC
  rcases hxProd with ⟨a, haMF, c, hcC, hacx⟩
  have hH0leMF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hH0normalMF : (H0.subgroupOf MF).Normal :=
    case_9_7_b_H0_normal_MF_sec9 hcase
  have hcy : ⁅c, y⁆ ∈ H0 :=
    hCMF_le_H0 (Subgroup.commutator_mem_commutator hcC hyMF)
  have hay : ⁅a, y⁆ ∈ H0 :=
    hAA (Subgroup.commutator_mem_commutator haMF hyMF)
  have hconj_cy : a * ⁅c, y⁆ * a⁻¹ ∈ H0 := by
    let aMF : MF := ⟨a, haMF⟩
    let cyMF : MF := ⟨⁅c, y⁆, hH0leMF hcy⟩
    let cyH0MF : H0.subgroupOf MF := ⟨cyMF, by
      change (cyMF : G) ∈ H0
      simpa [cyMF] using hcy⟩
    have hconj :
        aMF * cyH0MF * aMF⁻¹ ∈ H0.subgroupOf MF :=
      hH0normalMF.conj_mem cyH0MF cyH0MF.property aMF
    change ((aMF * cyH0MF * aMF⁻¹ : MF) : G) ∈ H0 at hconj
    simpa [aMF, cyH0MF, cyMF, mul_assoc] using hconj
  have hprod : a * ⁅c, y⁆ * a⁻¹ * ⁅a, y⁆ ∈ H0 :=
    H0.mul_mem hconj_cy hay
  rw [← hacx]
  convert hprod using 1
  group

private theorem scalar_smul_one_injective_sec9
    {V : Type v} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {a b : ℂ}
    (h : a • (1 : Module.End ℂ V) = b • (1 : Module.End ℂ V)) :
    a = b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hv' := congrArg (fun f : Module.End ℂ V => f v) h
  have hsub : (a - b) • v = 0 := by
    simpa [sub_smul] using sub_eq_zero.mpr hv'
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hv)

private theorem scalar_smul_one_ne_zero_sec9
    {V : Type v} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {a : ℂ}
    (hunit : ∃ f : Module.End ℂ V,
      (a • (1 : Module.End ℂ V)) * f = 1) :
    a ≠ 0 := by
  intro ha
  rcases hunit with ⟨f, hf⟩
  have hzero : (0 : Module.End ℂ V) = 1 := by
    subst a
    simpa only [zero_smul, zero_mul] using hf
  exact zero_ne_one hzero

private theorem representation_scalar_of_commutator_kernel_sec9
    {L : Type u} {V : Type v} [Group L] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (ρ : Representation ℂ L V)
    (hρirr : Representation.IsIrreducible ρ)
    (A : Subgroup L)
    (hker : Section1.subgroupInRepresentationKernel ρ A)
    {b : L}
    (hcomm : ∀ l : L, ⁅l, b⁆ ∈ A) :
    ∃ a : ℂ, (ρ b : Module.End ℂ V) = a • (1 : Module.End ℂ V) := by
  classical
  letI : Representation.IsIrreducible ρ := hρirr
  have hcommute : ∀ l : L, ρ b * ρ l = ρ l * ρ b := by
    intro l
    have hcommRep : ρ ⁅l, b⁆ = 1 := hker ⟨⁅l, b⁆, hcomm l⟩
    have hcommMap :
        ρ l * ρ b * ρ l⁻¹ * ρ b⁻¹ = 1 := by
      simpa [commutatorElement_def, map_mul, mul_assoc] using hcommRep
    have hb_inv_mul : ρ b⁻¹ * ρ b = 1 := by
      rw [← map_mul]
      simp
    have hl_inv_mul : ρ l⁻¹ * ρ l = 1 := by
      rw [← map_mul]
      simp
    have hconj_eq : ρ l * ρ b * ρ l⁻¹ = ρ b := by
      calc
        ρ l * ρ b * ρ l⁻¹ =
            (ρ l * ρ b * ρ l⁻¹) * 1 := by simp
        _ = (ρ l * ρ b * ρ l⁻¹) * (ρ b⁻¹ * ρ b) := by rw [hb_inv_mul]
        _ = (ρ l * ρ b * ρ l⁻¹ * ρ b⁻¹) * ρ b := by
          simp [mul_assoc]
        _ = 1 * ρ b := by rw [hcommMap]
        _ = ρ b := by simp
    calc
      ρ b * ρ l = (ρ l * ρ b * ρ l⁻¹) * ρ l := by rw [hconj_eq]
      _ = ρ l * ρ b * (ρ l⁻¹ * ρ l) := by rw [mul_assoc]
      _ = ρ l * ρ b := by rw [hl_inv_mul, mul_one]
  let f : Representation.IntertwiningMap ρ ρ :=
    (ρ b).intertwiningMap_of_isIntertwiningMap ρ ρ (by
      intro l v
      exact congrArg (fun F : Module.End ℂ V => F v) (hcommute l))
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  refine ⟨a, ?_⟩
  ext v
  have hv :=
    congrArg (fun F : Representation.IntertwiningMap ρ ρ => F v) ha.symm
  simpa [Representation.IntertwiningMap.algebraMap_apply, f,
    Representation.IntertwiningMap.smul_apply] using hv

private theorem exists_nonprincipal_quotient_linear_character_of_central_subgroup_sec9
    {L : Type u} [Group L] [Finite L]
    (A B : Subgroup L) [A.Normal] [(A.subgroupOf B).Normal]
    {ψ : Section1.ClassFunction L}
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψkerA : Section1.subgroupInKernel' ψ A)
    (hψnotB : ¬ Section1.subgroupInKernel' ψ B)
    (hcentral : ∀ b : B, ∀ l : L, ⁅l, (b : L)⁆ ∈ A) :
    ∃ χ : (B ⧸ A.subgroupOf B) →* ℂˣ,
      χ ≠ 1 ∧
        ∀ b : B,
          ψ (b : L) = Section1.degree ψ *
            (χ (QuotientGroup.mk' (A.subgroupOf B) b) : ℂ) := by
  classical
  rcases hψirr with ⟨n, ρ, hρirr, hψeq⟩
  have hkerRep : Section1.subgroupInRepresentationKernel ρ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρ A).mp (by simpa [hψeq] using hψkerA)
  let scalar : B → ℂ := fun b =>
    Classical.choose
      (representation_scalar_of_commutator_kernel_sec9 ρ hρirr A hkerRep
        (b := (b : L)) (fun l => hcentral b l))
  have hscalar : ∀ b : B,
      (ρ (b : L) : Module.End ℂ (Fin n → ℂ)) =
        scalar b • (1 : Module.End ℂ (Fin n → ℂ)) := fun b =>
    Classical.choose_spec
      (representation_scalar_of_commutator_kernel_sec9 ρ hρirr A hkerRep
        (b := (b : L)) (fun l => hcentral b l))
  haveI : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial ρ
  have hscalar_ne_zero : ∀ b : B, scalar b ≠ 0 := by
    intro b
    refine scalar_smul_one_ne_zero_sec9 (V := Fin n → ℂ) ?_
    refine ⟨ρ ((b : L)⁻¹), ?_⟩
    rw [← hscalar b]
    rw [← map_mul]
    simp
  let lam : B →* ℂˣ :=
    { toFun := fun b => Units.mk0 (scalar b) (hscalar_ne_zero b)
      map_one' := by
        apply Units.ext
        change scalar 1 = 1
        apply scalar_smul_one_injective_sec9 (V := Fin n → ℂ)
        rw [← hscalar 1]
        simp
      map_mul' := by
        intro b c
        apply Units.ext
        change scalar (b * c) = scalar b * scalar c
        apply scalar_smul_one_injective_sec9 (V := Fin n → ℂ)
        calc
          scalar (b * c) • (1 : Module.End ℂ (Fin n → ℂ))
              = ρ (((b * c : B) : L)) := (hscalar (b * c)).symm
          _ = ρ ((b : L) * (c : L)) := by rfl
          _ = ρ (b : L) * ρ (c : L) := by rw [map_mul]
          _ =
              (scalar b • (1 : Module.End ℂ (Fin n → ℂ))) *
                (scalar c • (1 : Module.End ℂ (Fin n → ℂ))) := by
                rw [hscalar b, hscalar c]
          _ = (scalar b * scalar c) • (1 : Module.End ℂ (Fin n → ℂ)) := by
                ext v i
                simp [mul_smul]
                ring }
  have hAker : A.subgroupOf B ≤ lam.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply Units.ext
    change scalar a = 1
    apply scalar_smul_one_injective_sec9 (V := Fin n → ℂ)
    calc
      scalar a • (1 : Module.End ℂ (Fin n → ℂ))
          = ρ ((a : B) : L) := (hscalar a).symm
      _ = 1 := hkerRep ⟨((a : B) : L), by
        simpa [Subgroup.mem_subgroupOf] using ha⟩
      _ = (1 : ℂ) • (1 : Module.End ℂ (Fin n → ℂ)) := by simp
  let χ : (B ⧸ A.subgroupOf B) →* ℂˣ :=
    QuotientGroup.lift (A.subgroupOf B) lam hAker
  have hvalue : ∀ b : B,
      ψ (b : L) = (n : ℂ) *
        (χ (QuotientGroup.mk' (A.subgroupOf B) b) : ℂ) := by
    intro b
    rw [hψeq]
    have hχb :
        (χ (QuotientGroup.mk' (A.subgroupOf B) b) : ℂ) = scalar b := by
      simp [χ, lam]
    rw [hχb]
    simp [Representation.character, hscalar b]
    ring
  refine ⟨χ, ?_, ?_⟩
  · intro hχ
    apply hψnotB
    intro b
    rw [hvalue b, hχ]
    simp [hψeq, Section1.degree]
  · intro b
    rw [hvalue b]
    rw [hψeq]
    simp [Section1.degree, Representation.character]

/-- If a finite abelian group automorphism has only the identity fixed point,
then every linear character fixed by that automorphism is principal. -/
private theorem linearCharacter_eq_one_of_fixed_by_fixedPointFree_sec9
    {A Q : Type*} [Group A] [Group Q] [Finite Q]
    [IsMulCommutative Q] [MulDistribMulAction A Q]
    (a : A)
    (hfree : ∀ q : Q, a • q = q → q = 1)
    (χ : Q →* ℂˣ)
    (hχfix : ∀ q : Q, χ (a • q) = χ q) :
    χ = 1 := by
  classical
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  let φ : Q → Q := fun q => (a • q) * q⁻¹
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : (a • x) * x⁻¹ = (a • y) * y⁻¹ := by
      simpa [φ] using hxy
    have hmul : (a • x) * y = (a • y) * x :=
      (mul_inv_eq_mul_inv_iff_mul_eq_mul).mp hxy'
    have hax : a • x = (a • y) * x * y⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      simpa [mul_assoc] using hmul
    have htmp : (a • x) * (a • y)⁻¹ = x * y⁻¹ := by
      rw [hax]
      simp [mul_assoc, mul_comm]
    have htarget : a • (x * y⁻¹) = x * y⁻¹ := by
      calc
        a • (x * y⁻¹) = (a • x) * (a • y)⁻¹ := by
          simp [smul_mul']
        _ = x * y⁻¹ := htmp
    have hxy1 : x * y⁻¹ = 1 := hfree (x * y⁻¹) htarget
    exact mul_inv_eq_one.mp hxy1
  have hφsurj : Function.Surjective φ := by
    rwa [← Finite.injective_iff_surjective]
  apply MonoidHom.ext
  intro q
  rcases hφsurj q with ⟨r, hr⟩
  rw [← hr]
  simp [φ, hχfix r]

private theorem theorem_9_9_nonprincipal_linear_character_fixed_U_mem_C_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ)
    (w : U) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      χ ≠ 1 →
        (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
          (hH0invU :
            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
            IsInvariant U MF (H0.subgroupOf MF)) →
          (letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
          letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
            quotientMulDistribMulAction (A := U) (G := MF)
              (H0.subgroupOf MF) hH0invU
          ∀ x : MF ⧸ H0.subgroupOf MF, χ (w • x) = χ x) →
            ((w : U) : G) ∈ C := by
  intro hcase hχne hUnormMF hH0invU hχfix
  classical
  by_contra hwC
  rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨hp, hp_eq, hpData⟩
  rcases hpData with
    ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem,
      _htypeData⟩
  rcases hElem with ⟨hnormalElem, hbarElemRaw⟩
  have hpprime : Nat.Prime p := case_9_7_b_p_prime_sec9 hcase
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := by
    simpa [hp_eq] using hbarElemRaw
  letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := inferInstance
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  have hfree : ∀ x : MF ⧸ H0.subgroupOf MF, w • x = x → x = 1 := by
    intro x hx
    rcases case_9_7_b_fieldSemidirectModelData_sec9 hcase with
      ⟨_hnormalH0_field, hnormalC, _hW1normU, _hCinv, F, fieldInst,
        fintypeInst, Ustar, _hFcard, _hUstarcard, _hUstarcyc, _hspan,
        φH, φU, _φW, hactU, _hactW⟩
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    letI : (C.subgroupOf U).Normal := hnormalC
    let CMU : Subgroup U := C.subgroupOf U
    let H0MF : Subgroup MF := H0.subgroupOf MF
    revert hx
    refine QuotientGroup.induction_on x ?_
    intro h hx
    let wbar : U ⧸ CMU := QuotientGroup.mk' CMU w⁻¹
    rcases hactU wbar h with ⟨hconjMF, hφ⟩
    let hout : U := wbar.out
    let c : U := hout / w⁻¹
    have hcCMU : c ∈ CMU := by
      have hout_eq :
          QuotientGroup.mk' CMU hout = QuotientGroup.mk' CMU w⁻¹ := by
        calc
          QuotientGroup.mk' CMU hout = wbar := by
            simpa only [QuotientGroup.mk'_apply, hout] using
              (Quotient.out_eq wbar)
          _ = QuotientGroup.mk' CMU w⁻¹ := rfl
      exact QuotientGroup.eq_iff_div_mem.mp hout_eq
    have hcC : ((c : U) : G) ∈ C := by
      simpa [CMU, Subgroup.mem_subgroupOf] using hcCMU
    have hout_eq_cw : hout = c * w⁻¹ := by
      simp [c, div_eq_mul_inv, mul_assoc]
    have hCcent :
        ∀ z : G, z ∈ MF → ⁅((c⁻¹ : U) : G), z⁆ ∈ H0 := by
      have hcInvC : (((c⁻¹ : U) : U) : G) ∈ C := C.inv_mem hcC
      exact (case_9_7_b_quotientCentralizerIn_sec9 hcase).2
        (((c⁻¹ : U) : U) : G) (U.inv_mem c.property) |>.mp hcInvC
    let hCconj : MF :=
      ⟨((c⁻¹ : U) : G) * (h : G) * ((c : U) : G), by
        have hnorm : (((c⁻¹ : U) • h : MF) : G) ∈ MF :=
          ((c⁻¹ : U) • h : MF).property
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          mul_assoc] using hnorm⟩
    have hCconj_q :
        QuotientGroup.mk' H0MF hCconj = QuotientGroup.mk' H0MF h := by
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (hCconj / h : MF) ∈ H0MF
      have hcomm : ⁅((c⁻¹ : U) : G), (h : G)⁆ ∈ H0 :=
        hCcent (h : G) h.property
      have hval : ((hCconj / h : MF) : G) =
          ⁅((c⁻¹ : U) : G), (h : G)⁆ := by
        simp [hCconj, div_eq_mul_inv, commutatorElement_def, mul_assoc]
      simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcomm
    let houtConj : MF :=
      ⟨(hout : G)⁻¹ * (h : G) * (hout : G), hconjMF h⟩
    have houtConj_q :
        QuotientGroup.mk' H0MF houtConj =
          w • QuotientGroup.mk' H0MF h := by
      have hsmul_mk :
          w • QuotientGroup.mk' H0MF h =
            QuotientGroup.mk' H0MF (w • h : MF) := by
        simpa only [QuotientGroup.mk'_apply] using
          (MulAction.Quotient.smul_mk (H := H0MF) w h)
      rw [hsmul_mk]
      have htarget :
          QuotientGroup.mk' H0MF houtConj =
            QuotientGroup.mk' H0MF (w • h : MF) := by
        calc
          QuotientGroup.mk' H0MF houtConj =
              QuotientGroup.mk' H0MF (w • hCconj : MF) := by
                apply congrArg (QuotientGroup.mk' H0MF)
                apply Subtype.ext
                simp [houtConj, hCconj, hout_eq_cw,
                  Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
                  mul_assoc]
          _ = w • QuotientGroup.mk' H0MF hCconj := by
                symm
                simpa only [QuotientGroup.mk'_apply] using
                  (MulAction.Quotient.smul_mk (H := H0MF) w hCconj)
          _ = w • QuotientGroup.mk' H0MF h := by rw [hCconj_q]
          _ = QuotientGroup.mk' H0MF (w • h : MF) := hsmul_mk
      exact htarget
    have hqfixed :
        QuotientGroup.mk' H0MF houtConj = QuotientGroup.mk' H0MF h := by
      rw [houtConj_q]
      exact hx
    have hφ' :
        φH (QuotientGroup.mk' H0MF houtConj) =
          Multiplicative.ofAdd
            ((((φU wbar : Ustar) : Fˣ) : F) *
              Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h))) := by
      simpa [H0MF, CMU, hout, houtConj] using hφ
    have hscalar_eq :
        Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h)) =
          (((φU wbar : Ustar) : Fˣ) : F) *
            Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h)) := by
      have hφfixed := hφ'
      rw [hqfixed] at hφfixed
      exact congrArg Multiplicative.toAdd hφfixed
    have hαne :
        (((φU wbar : Ustar) : Fˣ) : F) ≠ 1 := by
      intro hα
      apply hwC
      have hφU_one : φU wbar = 1 := by
        apply Subtype.ext
        apply Units.ext
        simpa using hα
      have hwbar_one : wbar = 1 := by
        exact φU.injective (by simpa using hφU_one)
      have hwinvC : (w⁻¹ : U) ∈ CMU := by
        exact (QuotientGroup.eq_one_iff (N := CMU) (x := w⁻¹)).1
          (by simpa [wbar] using hwbar_one)
      have hwC' : ((w⁻¹ : U) : G) ∈ C := by
        simpa [CMU, Subgroup.mem_subgroupOf] using hwinvC
      simpa using C.inv_mem hwC'
    have hz0 :
        Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h)) = 0 := by
      let z : F := Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h))
      let α : F := (((φU wbar : Ustar) : Fˣ) : F)
      have hαz : z = α * z := by
        simpa [z, α] using hscalar_eq
      have hmul0 : (α - 1) * z = 0 := by
        calc
          (α - 1) * z = α * z - z := by ring
          _ = 0 := by rw [← hαz]; ring
      have hαsub : α - 1 ≠ 0 := sub_ne_zero.mpr (by
        simpa [α] using hαne)
      exact (mul_eq_zero.mp hmul0).resolve_left hαsub
    have hφ_one : φH (QuotientGroup.mk' H0MF h) = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hz0
    exact φH.injective (by simpa using hφ_one)
  have hχone :
      χ = 1 :=
    linearCharacter_eq_one_of_fixed_by_fixedPointFree_sec9
      (A := U) (Q := MF ⧸ H0.subgroupOf MF) w hfree χ hχfix
  exact hχne hχone

set_option maxHeartbeats 800000 in
private theorem theorem_9_9_fixed_nonMF_HC_constituent_U_component_mem_C_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (ψ : Section1.ClassFunction
      (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)))
    [(((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal] :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Section1.IsIrreducibleCharacterOnGroup ψ →
        ¬ Section1.subgroupInKernel' ψ
          (((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              (((MF ⊔ C).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) →
        Section1.subgroupInKernel' ψ
          (((H0.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              (((MF ⊔ C).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) →
        ∀ w : (ambientDerivedSubgroup M).subgroupOf M,
          w ∈ (U.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M) →
          Section1.conjugateOnNormal
              (((MF ⊔ C).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) ψ w = ψ →
            (((w : (ambientDerivedSubgroup M).subgroupOf M) : M) : G) ∈ C := by
  intro hcase hψirr hψnotMF hψkerH0 w hwW hfixw
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let K : Subgroup Dm := ((MF ⊔ C).subgroupOf M).subgroupOf Dm
  have hKnormal : K.Normal := by
    dsimp [K, Dm, D]
    infer_instance
  letI : K.Normal := hKnormal
  let B0 : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let A0 : Subgroup Dm := (H0.subgroupOf M).subgroupOf Dm
  let B : Subgroup K := B0.subgroupOf K
  let A : Subgroup K := A0.subgroupOf K
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_b_hypothesis_9_2_sec9 hcase
  have hMFleM : MF ≤ M := case_9_7_b_MF_le_M_sec9 hcase
  have hH0leMF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hH0leM : H0 ≤ M := hH0leMF.trans hMFleM
  have hH0normalM : (H0.subgroupOf M).Normal :=
    case_9_7_b_H0_normal_M_sec9 hcase
  have hMFleD : MF ≤ D := by
    dsimp [D]
    exact MF_le_ambientDerived_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have hMFm_le_Dm : MF.subgroupOf M ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ D
    exact hMFleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hB0leK : B0 ≤ K := by
    intro x hx
    change (x : Dm) ∈ ((MF ⊔ C).subgroupOf M).subgroupOf Dm
    rw [Subgroup.mem_subgroupOf]
    exact (le_sup_left : MF ≤ MF ⊔ C)
      (by simpa [B0, Subgroup.mem_subgroupOf] using hx)
  have hA_normal : A.Normal := by
    dsimp [A, A0, K]
    exact Subgroup.Normal.subgroupOf
      (theorem_9_9_H0_normal_ambientDerived_subgroupOf_sec9
        M MF U W1 W2 H0 C p q u hcase)
      K
  letI : A.Normal := hA_normal
  have hA_subgroupOf_B_normal : (A.subgroupOf B).Normal := by
    exact Subgroup.Normal.subgroupOf hA_normal B
  letI : (A.subgroupOf B).Normal := hA_subgroupOf_B_normal
  letI : Group (B ⧸ A.subgroupOf B) :=
    @QuotientGroup.Quotient.group B _ (A.subgroupOf B)
      hA_subgroupOf_B_normal
  have hcentral : ∀ b : B, ∀ l : K, ⁅l, (b : K)⁆ ∈ A := by
    intro b l
    have hlHC : ((((l : K) : Dm) : M) : G) ∈ MF ⊔ C := by
      have hlK : ((l : K) : Dm) ∈ K := l.property
      change (((l : K) : Dm) : M) ∈ (MF ⊔ C).subgroupOf M at hlK
      simpa [Subgroup.mem_subgroupOf] using hlK
    have hbMF : (((((b : B) : K) : Dm) : M) : G) ∈ MF := by
      have hbB0 : (((b : B) : K) : Dm) ∈ B0 := by
        change ((b : B) : K) ∈ B
        exact b.property
      change ((((b : B) : K) : Dm) : M) ∈ MF.subgroupOf M at hbB0
      simpa [Subgroup.mem_subgroupOf] using hbB0
    have hcommG :
        ⁅((((l : K) : Dm) : M) : G),
            (((((b : B) : K) : Dm) : M) : G)⁆ ∈ H0 :=
      theorem_9_9_HC_MF_commutator_le_H0_sec9
        M MF U W1 W2 H0 C p q u hcase
        (Subgroup.commutator_mem_commutator hlHC hbMF)
    change
      ⁅((((l : K) : Dm) : M) : G),
        (((((b : B) : K) : Dm) : M) : G)⁆ ∈ H0
    exact hcommG
  have hψkerA : Section1.subgroupInKernel' ψ A := by
    simpa [A, A0, K, Dm, D] using hψkerH0
  have hψnotB : ¬ Section1.subgroupInKernel' ψ B := by
    simpa [B, B0, K, Dm, D] using hψnotMF
  rcases exists_nonprincipal_quotient_linear_character_of_central_subgroup_sec9
      A B hψirr hψkerA hψnotB hcentral with
    ⟨χ, hχne, hχvalue⟩
  let qB : B →* B ⧸ A.subgroupOf B :=
    @QuotientGroup.mk' B _ (A.subgroupOf B) hA_subgroupOf_B_normal
  let eBMF : B ≃* MF :=
    (Subgroup.subgroupOfEquivOfLe hB0leK).trans
      ((Subgroup.subgroupOfEquivOfLe hMFm_le_Dm).trans
        (Subgroup.subgroupOfEquivOfLe hMFleM))
  let H0MF : Subgroup MF := H0.subgroupOf MF
  letI : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : Group (MF ⧸ H0MF) :=
    @QuotientGroup.Quotient.group MF _ H0MF (inferInstance : H0MF.Normal)
  have hkerLamMF :
      H0MF ≤
        (χ.comp (qB.comp eBMF.symm.toMonoidHom)).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change χ ((@QuotientGroup.mk' B _ (A.subgroupOf B)
      hA_subgroupOf_B_normal) (eBMF.symm x)) = 1
    have hxA : eBMF.symm x ∈ A.subgroupOf B := by
      change ((eBMF.symm x : B) : K) ∈ A
      have hxH0 : (x : G) ∈ H0 := by
        change (x : G) ∈ H0 at hx
        exact hx
      simpa [eBMF, A, A0, B, B0, K, Dm, D, Subgroup.mem_subgroupOf]
        using hxH0
    have hmk_one_raw :
        ((eBMF.symm x : B) : B ⧸ A.subgroupOf B) =
          ((1 : B) : B ⧸ A.subgroupOf B) := by
      exact (QuotientGroup.eq).2 (by
        simpa using (A.subgroupOf B).inv_mem hxA)
    have hχmk :
        χ (((eBMF.symm x : B) : B ⧸ A.subgroupOf B)) =
          χ (((1 : B) : B ⧸ A.subgroupOf B)) :=
      congrArg χ hmk_one_raw
    calc
      χ ((@QuotientGroup.mk' B _ (A.subgroupOf B)
          hA_subgroupOf_B_normal) (eBMF.symm x)) =
          χ ((@QuotientGroup.mk' B _ (A.subgroupOf B)
            hA_subgroupOf_B_normal) 1) := by
            simpa only [QuotientGroup.mk'_apply] using hχmk
      _ = 1 := (χ.comp qB).map_one
  let χMF : (MF ⧸ H0MF) →* ℂˣ :=
    QuotientGroup.lift H0MF
      (χ.comp (qB.comp eBMF.symm.toMonoidHom))
      hkerLamMF
  have hχMF_mk : ∀ h : MF,
      χMF (QuotientGroup.mk' H0MF h) =
        χ (qB (eBMF.symm h)) := by
    intro h
    simp [χMF]
  have hχMFne : χMF ≠ 1 := by
    intro hχMFone
    apply hχne
    apply MonoidHom.ext
    intro y
    refine QuotientGroup.induction_on y ?_
    intro b
    change χ (qB b) = 1
    have hval := hχMF_mk (eBMF b)
    have hpre : eBMF.symm (eBMF b) = b := by simp
    have hval' : χ (qB b) =
        χMF (QuotientGroup.mk' H0MF (eBMF b)) := by
      simpa [hpre] using hval.symm
    rw [hval', hχMFone]
    simp
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    by
      rcases h92.mf.1 with ⟨hMFleM', hMFnormalM, _hMFnil, _hMFhall⟩
      rcases h92.typeP with ⟨_hMFtype, hcommon⟩
      rcases hcommon with
        ⟨_hDhall, _hMFleD', hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
          _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
          _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
      rcases hcompD with ⟨_hMFleD_comp, hUleD, _hD_eq, _hMFUdisj⟩
      have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM').1 hMFnormalM
      exact hUleD.trans (section12_ambientDerivedSubgroup_le.trans hM_norm_MF)
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hUleM : U ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hUleD.trans section12_ambientDerivedSubgroup_le
  have hH0invU : IsInvariant U MF H0MF := by
    dsimp [H0MF]
    exact subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF U H0
      hMFleM hUleM hH0normalM hUnormMF
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      H0MF hH0invU
  let wU : U := ⟨(((w : Dm) : M) : G), by
    simpa [Dm, D, Subgroup.mem_subgroupOf] using hwW⟩
  have hχfixMF : ∀ x : MF ⧸ H0MF, χMF (wU • x) = χMF x := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro h
    have hsmul_mk :
        wU • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF (wU • h : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) wU h)
    calc
      χMF (wU • QuotientGroup.mk' H0MF h) =
          χMF (QuotientGroup.mk' H0MF (wU • h : MF)) := by
            rw [hsmul_mk]
      _ = χMF (QuotientGroup.mk' H0MF h) := by
        rw [hχMF_mk, hχMF_mk]
        let b : B := eBMF.symm h
        let bconj : B := eBMF.symm (wU • h : MF)
        have hbconj_eq :
            (bconj : K) =
              ⟨(w : Dm) * (b : K) * (w : Dm)⁻¹,
                (show K.Normal from by simpa [K] using hKnormal).conj_mem
                  (b : K) (b : K).property w⟩ := by
          ext
          change ((wU • h : MF) : G) =
            ((wU : U) : G) * (h : G) * ((wU : U) : G)⁻¹
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
            wU, mul_assoc]
        have hfix_eval :
            ψ bconj = ψ b := by
          have hraw := congrFun hfixw b
          simpa [Section1.conjugateOnNormal, hbconj_eq] using hraw
        have hdeg_ne : Section1.degree ψ ≠ 0 :=
          Section1.degree_ne_zero_of_isBookIrreducibleCharacter ψ
            (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hψirr)
        have hmul :
            Section1.degree ψ *
                (χ (QuotientGroup.mk' (A.subgroupOf B) bconj) : ℂ) =
              Section1.degree ψ *
                (χ (QuotientGroup.mk' (A.subgroupOf B) b) : ℂ) := by
          rw [← hχvalue bconj, ← hχvalue b, hfix_eval]
        apply Units.ext
        exact mul_left_cancel₀ hdeg_ne hmul
  have hwC :
      ((wU : U) : G) ∈ C :=
    theorem_9_9_nonprincipal_linear_character_fixed_U_mem_C_sec9
      M MF U W1 W2 H0 C p q u χMF wU hcase hχMFne hUnormMF hH0invU
      hχfixMF
  simpa [wU, Dm, D] using hwC

private theorem theorem_9_9_case_b_clifford_part_a_package_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ∀ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
        Section1.IsIrreducibleCharacterOnGroup θ →
          ¬ Section1.subgroupInKernel' θ
            ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
          Section1.subgroupInKernel' θ
            ((H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            ∃ ψ : Section1.ClassFunction
                (((MF ⊔ C).subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)),
              Section1.IsIrreducibleCharacterOnGroup ψ ∧
                Section1.scalarProduct
                  (((MF ⊔ C).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M))
                  ψ
                  (Section1.subgroupRestriction
                    (((MF ⊔ C).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) θ) ≠ 0 ∧
                ¬ Section1.subgroupInKernel' ψ
                  (((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                      (((MF ⊔ C).subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M))) ∧
                Section1.subgroupInKernel' ψ
                  (((H0.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                      (((MF ⊔ C).subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M))) ∧
                θ = Section1.inducedCF
                  (((MF ⊔ C).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ψ := by
  intro hcase θ hθirr hθnotMF hθkerH0
  rcases theorem_9_9_exists_HC_restriction_constituent_sec9
      M MF U W1 W2 H0 C p q u θ hcase hθirr hθnotMF hθkerH0 with
    ⟨ψ, hψirr, hψinner, hψnotMF, hψkerH0⟩
  have hKnormal :
      (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal :=
    theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q u hcase
  letI :
      (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
  have hIeq :
      Section1.inertiaSubgroup
          (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) ψ =
        (((MF ⊔ C).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)) := by
    classical
    let D : Subgroup G := ambientDerivedSubgroup M
    let Dm : Subgroup M := D.subgroupOf M
    let K : Subgroup Dm := ((MF ⊔ C).subgroupOf M).subgroupOf Dm
    let B : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    have hBnormal : B.Normal := by
      dsimp [B, Dm, D]
      exact theorem_9_9_MF_normal_ambientDerived_subgroupOf_sec9
        M MF U W1 W2 H0 C p q u hcase
    have hsemi :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) B W := by
      dsimp [B, W, Dm, D]
      exact theorem_9_9_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q (case_9_7_b_hypothesis_9_2_sec9 hcase) hBnormal
    have hBK : B ≤ K := by
      intro x hx
      change ((x : Dm) : M) ∈ (MF ⊔ C).subgroupOf M
      change ((x : Dm) : M) ∈ MF.subgroupOf M at hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (le_sup_left : MF ≤ MF ⊔ C) hx
    have hψclass : Section1.IsClassFunction ψ := by
      rcases hψirr with ⟨_n, ρ, _hρirr, hψeq⟩
      intro x g
      rw [hψeq]
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    refine inertiaSubgroup_eq_of_semidirect_fixed_complement_mem_sec9
      K B W hBK hsemi hψclass ?_
    intro w hwW hfixw
    have hwC :
        (((w : Dm) : M) : G) ∈ C :=
      theorem_9_9_fixed_nonMF_HC_constituent_U_component_mem_C_sec9
        M MF U W1 W2 H0 C p q u ψ hcase hψirr hψnotMF hψkerH0
        w hwW hfixw
    exact theorem_9_9_U_component_mem_HC_of_mem_C_sec9
      M MF U W1 W2 H0 C p q u hcase hwW hwC
  have hIndψ :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF
          (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) ψ) :=
    inducedCF_isIrreducible_of_inertia_eq_self_sec9
      (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)) hψirr hIeq
  exact ⟨ψ, hψirr, hψinner, hψnotMF, hψkerH0,
    inducedCF_eq_of_irreducible_constituent_sec9
      (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))
      hθirr hIndψ hψinner⟩

private theorem theorem_9_9_inducedCF_HC_irreducible_of_kernel_H0_not_MF_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (ψ : Section1.ClassFunction ((MF ⊔ C).subgroupOf M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Section1.IsIrreducibleCharacterOnGroup ψ →
        ¬ Section1.subgroupInKernel' ψ
          ((MF.subgroupOf M).subgroupOf ((MF ⊔ C).subgroupOf M)) →
        Section1.subgroupInKernel' ψ
          ((H0.subgroupOf M).subgroupOf ((MF ⊔ C).subgroupOf M)) →
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF
            (((MF ⊔ C).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M))
            (Section1.subgroupOfClassFunction
              (T := (ambientDerivedSubgroup M).subgroupOf M) ψ)) := by
  intro hcase hψirr hψnotMF hψkerH0
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let K : Subgroup Dm := HCm.subgroupOf Dm
  let ψD : Section1.ClassFunction K :=
    Section1.subgroupOfClassFunction (T := Dm) ψ
  have hHC_le_Dm : HCm ≤ Dm := by
    have hHC_le_D :
        MF ⊔ C ≤ D :=
      theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u hcase
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHC_le_D hx
  have hMFm_le_Dm : MF.subgroupOf M ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ D
    exact (theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u
      hcase) ((le_sup_left : MF ≤ MF ⊔ C)
        (by simpa [Subgroup.mem_subgroupOf] using hx))
  have hH0m_le_Dm : H0.subgroupOf M ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ D
    exact (theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u
      hcase) ((le_sup_left : MF ≤ MF ⊔ C)
        ((case_9_7_b_H0_le_MF_sec9 hcase)
          (by simpa [Subgroup.mem_subgroupOf] using hx)))
  have hMFm_le_HCm : MF.subgroupOf M ≤ HCm := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (le_sup_left : MF ≤ MF ⊔ C) hx
  have hH0m_le_HCm : H0.subgroupOf M ≤ HCm := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (le_sup_left : MF ≤ MF ⊔ C)
      ((case_9_7_b_H0_le_MF_sec9 hcase) hx)
  have hψDirr : Section1.IsIrreducibleCharacterOnGroup ψD := by
    dsimp [ψD, K, HCm, Dm]
    exact isIrreducible_subgroupOfClassFunction_pf99_sec9 hHC_le_Dm hψirr
  have hψDnotMF :
      ¬ Section1.subgroupInKernel' ψD
        (((MF.subgroupOf M).subgroupOf Dm).subgroupOf K) := by
    intro hker
    exact hψnotMF
      (subgroupInKernel'_of_subgroupOfClassFunction_pf99_sec9
        (H := HCm) (T := Dm) (A := MF.subgroupOf M)
        hMFm_le_Dm hMFm_le_HCm (by simpa [ψD, K, HCm, Dm] using hker))
  have hψDkerH0 :
      Section1.subgroupInKernel' ψD
        (((H0.subgroupOf M).subgroupOf Dm).subgroupOf K) := by
    exact subgroupInKernel'_subgroupOfClassFunction_pf99_sec9
      (H := HCm) (T := Dm) (A := H0.subgroupOf M)
      hH0m_le_Dm hH0m_le_HCm hψkerH0
  have hKnormal : K.Normal := by
    dsimp [K, HCm, Dm, D]
    exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q u hcase
  letI : K.Normal := hKnormal
  have hIeq : Section1.inertiaSubgroup K ψD = K := by
    let B : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    have hBnormal : B.Normal := by
      dsimp [B, Dm, D]
      exact theorem_9_9_MF_normal_ambientDerived_subgroupOf_sec9
        M MF U W1 W2 H0 C p q u hcase
    have hsemi :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) B W := by
      dsimp [B, W, Dm, D]
      exact theorem_9_9_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q (case_9_7_b_hypothesis_9_2_sec9 hcase) hBnormal
    have hBK : B ≤ K := by
      intro x hx
      change ((x : Dm) : M) ∈ HCm
      change ((x : Dm) : M) ∈ MF.subgroupOf M at hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (le_sup_left : MF ≤ MF ⊔ C) hx
    have hψDclass : Section1.IsClassFunction ψD := by
      rcases hψDirr with ⟨_n, ρ, _hρirr, hψeq⟩
      intro x g
      rw [hψeq]
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    refine inertiaSubgroup_eq_of_semidirect_fixed_complement_mem_sec9
      K B W hBK hsemi hψDclass ?_
    intro w hwW hfixw
    have hwC :
        (((w : Dm) : M) : G) ∈ C :=
      theorem_9_9_fixed_nonMF_HC_constituent_U_component_mem_C_sec9
        M MF U W1 W2 H0 C p q u ψD hcase hψDirr hψDnotMF hψDkerH0
        w hwW hfixw
    exact theorem_9_9_U_component_mem_HC_of_mem_C_sec9
      M MF U W1 W2 H0 C p q u hcase hwW hwC
  simpa [D, Dm, HCm, K, ψD] using
    inducedCF_isIrreducible_of_inertia_eq_self_sec9 K hψDirr hIeq

private theorem theorem_9_9_degree_eq_q_mul_u_of_linear_HC_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF C : Subgroup G) (q u : ℕ)
    (χ : Section1.ClassFunction M) :
    Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u →
      inducedFromLinearCharacterOfHC M MF C χ →
        Section1.degree χ = (q * u : ℂ) := by
  intro hidx hlin
  rcases hlin with ⟨θ, _hθirr, hθdeg, hχeq⟩
  rw [hχeq, Section1.degree_inducedClassFunction, hθdeg, hidx]
  simp

/-- The contragredient action on multiplicative linear characters. -/
@[reducible] private noncomputable def characterGroupContragredientMulDistribMulAction_sec9
    (A Q : Type*) [Group A] [Group Q] [MulDistribMulAction A Q] :
    MulDistribMulAction A (Q →* ℂˣ) where
  smul a χ :=
    { toFun := fun q => χ (a⁻¹ • q)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [smul_mul'] }
  one_smul χ := by
    ext q
    change (((χ ((1 : A)⁻¹ • q)) : ℂˣ) : ℂ) = ((χ q : ℂˣ) : ℂ)
    simp
  mul_smul a b χ := by
    ext q
    change (((χ (((a * b)⁻¹) • q)) : ℂˣ) : ℂ) =
      (((χ (b⁻¹ • (a⁻¹ • q))) : ℂˣ) : ℂ)
    rw [mul_inv_rev, mul_smul]
  smul_one a := by
    ext q
    change (((1 : Q →* ℂˣ) (a⁻¹ • q) : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ)
    rfl
  smul_mul a χ η := by
    ext q
    change ((((χ * η) (a⁻¹ • q)) : ℂˣ) : ℂ) =
      ((((χ (a⁻¹ • q)) * (η (a⁻¹ • q))) : ℂˣ) : ℂ)
    rfl

@[reducible] private def nonidentitySubMulAction_sec9
    (A : Type u) (Q : Type v) [Group A] [Group Q] [MulDistribMulAction A Q] :
    MulAction A {q : Q // q ≠ 1} where
  smul a q := ⟨a • (q : Q), by
    intro h
    apply q.2
    have h' := congrArg (fun y : Q => a⁻¹ • y) h
    simpa using h'⟩
  one_smul := by
    intro q
    apply Subtype.ext
    change (1 : A) • (q : Q) = (q : Q)
    simp
  mul_smul := by
    intro a b q
    apply Subtype.ext
    change (a * b) • (q : Q) = a • (b • (q : Q))
    rw [mul_smul]

private noncomputable def nonidentityOrbitQuotient_sec9
    (A : Type u) (Q : Type v) [Group A] [Group Q] [MulDistribMulAction A Q] :
    Type v := by
  letI : MulAction A {q : Q // q ≠ 1} := nonidentitySubMulAction_sec9 A Q
  exact Quotient (MulAction.orbitRel A {q : Q // q ≠ 1})

private theorem nonidentityOrbitQuotient_card_eq_div_sec9
    {A : Type u} {Q : Type v} [Group A] [Finite A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q]
    (hfree : ∀ a : A, a ≠ 1 → ∀ q : Q, a • q = q → q = 1) :
    Nat.card (nonidentityOrbitQuotient_sec9 A Q) =
      (Nat.card Q - 1) / Nat.card A := by
  classical
  let α := {q : Q // q ≠ 1}
  letI : MulAction A α := nonidentitySubMulAction_sec9 A Q
  have hstab : ∀ q : α, MulAction.stabilizer A q = ⊥ := by
    intro q
    rw [eq_bot_iff]
    intro a ha
    have haq : a • q = q := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (q : Q) = (q : Q) := congrArg Subtype.val haq
    exact q.2 (hfree a ha_ne (q : Q) hfix)
  let Ω := Quotient (MulAction.orbitRel A α)
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardα : Nat.card α = Nat.card Q - 1 := by
    letI : Fintype Q := Fintype.ofFinite Q
    letI : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {q : Q // q ≠ 1} = Fintype.card Q - 1
    simp
  have hmul : Nat.card A * Nat.card Ω = Nat.card Q - 1 := by
    rw [← hcardα]
    simpa [Nat.card_prod, mul_comm, Ω, α] using hcard_equiv.symm
  have hΩ : Nat.card (nonidentityOrbitQuotient_sec9 A Q) = Nat.card Ω := by
    rfl
  rw [hΩ]
  exact (Nat.div_eq_of_eq_mul_right (Nat.card_pos (α := A)) hmul.symm).symm

private theorem theorem_9_9_C_bot_nonprincipalLinearCharacter_orbit_count_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
      theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    let hH0invU : IsInvariant U MF H0MF := by
      simpa [H0MF] using
        theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : MulDistribMulAction U (MF ⧸ H0MF) :=
      quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
    letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
    Nat.card (nonidentityOrbitQuotient_sec9 U ((MF ⧸ H0MF) →* ℂˣ)) =
      (p ^ q - 1) / u := by
  classical
  dsimp only
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF H0MF := by
    simpa [H0MF] using
      theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
  have hcomm : IsMulCommutative (MF ⧸ H0MF) := by
    rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨hp, hp_eq, hpData⟩
    rcases hpData with
      ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem,
        _htypeData⟩
    rcases hElem with ⟨_hnormalElem, hbarElemRaw⟩
    have hpprime : Nat.Prime p := case_9_7_b_p_prime_sec9 hcase
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p (MF ⧸ H0MF) := by
      simpa [H0MF, hp_eq] using hbarElemRaw
    infer_instance
  letI : IsMulCommutative (MF ⧸ H0MF) := hcomm
  have hfree :
      ∀ a : U, a ≠ 1 → ∀ χ : (MF ⧸ H0MF) →* ℂˣ,
        a • χ = χ → χ = 1 := by
    intro a ha χ hfix
    by_contra hχne
    have hfix_inv :
        ∀ x : MF ⧸ H0MF, χ ((a⁻¹ : U) • x) = χ x := by
      intro x
      have h := congrFun (congrArg DFunLike.coe hfix) x
      change χ ((a⁻¹ : U) • x) = χ x at h
      exact h
    have hmemC : (((a⁻¹ : U) : U) : G) ∈ C :=
      theorem_9_9_nonprincipal_linear_character_fixed_U_mem_C_sec9
        M MF U W1 W2 H0 C p q u χ a⁻¹ hcase hχne hUnormMF hH0invU
        hfix_inv
    have hmemBot : (((a⁻¹ : U) : U) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hCbot] using hmemC
    have hainv_one_G : (((a⁻¹ : U) : U) : G) = 1 := by
      simpa using hmemBot
    have hainv_one : a⁻¹ = 1 := by
      apply Subtype.ext
      exact hainv_one_G
    exact (inv_ne_one.mpr ha) hainv_one
  have horbit :=
    nonidentityOrbitQuotient_card_eq_div_sec9
      (A := U) (Q := ((MF ⧸ H0MF) →* ℂˣ)) hfree
  have hQcard : Nat.card (MF ⧸ H0MF) = p ^ q := by
    rcases case_9_7_b_quotient_card_sec9 hcase with ⟨_hnormalQ, hcardQ⟩
    simpa [H0MF] using hcardQ
  have hcharCard : Nat.card ((MF ⧸ H0MF) →* ℂˣ) = p ^ q := by
    let Q := MF ⧸ H0MF
    letI : CommGroup Q := IsMulCommutative.instCommGroup
    haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
      Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
    have hchars : Nat.card (Q →* ℂˣ) = Nat.card Q :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
    simpa [Q, hQcard] using hchars
  have hUcard : Nat.card U = u := by
    rcases case_9_7_b_barU_cardinality_sec9 hcase with
      ⟨_hCU, hnormalC, hcardQuot⟩
    letI : (C.subgroupOf U).Normal := hnormalC
    have hCsub : C.subgroupOf U = ⊥ := by
      rw [hCbot]
      ext x
      simp
    let e1 : U ⧸ C.subgroupOf U ≃* U ⧸ (⊥ : Subgroup U) :=
      QuotientGroup.quotientMulEquivOfEq hCsub
    let e : U ⧸ C.subgroupOf U ≃* U :=
      e1.trans (QuotientGroup.quotientBot (G := U))
    exact (Nat.card_congr e.toEquiv).symm.trans hcardQuot
  calc
    Nat.card (nonidentityOrbitQuotient_sec9 U ((MF ⧸ H0MF) →* ℂˣ)) =
        (Nat.card ((MF ⧸ H0MF) →* ℂˣ) - 1) / Nat.card U := horbit
    _ = (p ^ q - 1) / u := by rw [hcharCard, hUcard]


private theorem theorem_9_9_case_b_clifford_induction_package_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (∀ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
        Section1.IsIrreducibleCharacterOnGroup θ →
          ¬ Section1.subgroupInKernel' θ
            ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
          Section1.subgroupInKernel' θ
            ((H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            ∃ ψ : Section1.ClassFunction
                (((MF ⊔ C).subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)),
              Section1.IsIrreducibleCharacterOnGroup ψ ∧
                θ = Section1.inducedCF
                  (((MF ⊔ C).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ψ) ∧
      ∀ Cprime : Subgroup G,
        Cprime = (_root_.commutator C).map C.subtype →
          ∀ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
            Section1.IsIrreducibleCharacterOnGroup θ →
              ¬ Section1.subgroupInKernel' θ
                ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
              Section1.subgroupInKernel' θ
                (((H0 ⊔ Cprime).subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)) →
                ∃ ψ : Section1.ClassFunction ((MF ⊔ C).subgroupOf M),
                  Section1.IsIrreducibleCharacterOnGroup ψ ∧
                    Section1.degree ψ = (1 : ℂ) ∧
                      θ = Section1.inducedCF
                        (((MF ⊔ C).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M))
                        (Section1.subgroupOfClassFunction ψ) := by
  intro hcase
  constructor
  · intro θ hθirr hθnotMF hθkerH0
    rcases theorem_9_9_case_b_clifford_part_a_package_source_bridge_sec9
        M MF U W1 W2 H0 C p q u hcase θ hθirr hθnotMF hθkerH0 with
      ⟨ψ, hψirr, _hψinner, _hψnotMF, _hψkerH0, hθeq⟩
    exact ⟨ψ, hψirr, hθeq⟩
  · intro Cprime hCprimeEq θ hθirr hθnotMF hθkerH0Cprime
    let D : Subgroup G := ambientDerivedSubgroup M
    let Dm : Subgroup M := D.subgroupOf M
    let K : Subgroup Dm := ((MF ⊔ C).subgroupOf M).subgroupOf Dm
    let A : Subgroup Dm := ((H0 ⊔ Cprime).subgroupOf M).subgroupOf Dm
    let H0D : Subgroup Dm := (H0.subgroupOf M).subgroupOf Dm
    have hH0D_le_A : H0D ≤ A := by
      intro x hx
      change ((x : Dm) : M) ∈ (H0 ⊔ Cprime).subgroupOf M
      change ((x : Dm) : M) ∈ H0.subgroupOf M at hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (le_sup_left : H0 ≤ H0 ⊔ Cprime) hx
    have hθkerH0 : Section1.subgroupInKernel' θ H0D := by
      intro x
      exact hθkerH0Cprime ⟨x.1, hH0D_le_A x.2⟩
    rcases theorem_9_9_case_b_clifford_part_a_package_source_bridge_sec9
        M MF U W1 W2 H0 C p q u hcase θ hθirr hθnotMF hθkerH0 with
      ⟨ψD, hψDirr, _hψDinner, _hψDnotMF, _hψDkerH0, hθeq⟩
    have hKnormal : K.Normal := by
      dsimp [K, Dm, D]
      exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
        M MF U W1 W2 H0 C p q u hcase
    have hAnormal : A.Normal := by
      dsimp [A, Dm, D]
      exact theorem_9_9_H0Cprime_normal_ambientDerived_subgroupOf_sec9
        M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
    have hAK : A ≤ K := by
      have hA_le_HC :
          H0 ⊔ Cprime ≤ MF ⊔ C :=
        theorem_9_9_H0Cprime_le_HC_sec9 M MF U W1 W2 H0 C Cprime
          p q u hcase hCprimeEq
      intro x hx
      change ((x : Dm) : M) ∈ (MF ⊔ C).subgroupOf M
      change ((x : Dm) : M) ∈ (H0 ⊔ Cprime).subgroupOf M at hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hA_le_HC hx
    letI : K.Normal := hKnormal
    letI : A.Normal := hAnormal
    have hψDkerA : Section1.subgroupInKernel' ψD (A.subgroupOf K) :=
      subgroupInKernel'_of_inducedCF_eq_sec9 K A hAK hψDirr hθeq hθkerH0Cprime
    have hcomm_le :
        _root_.commutator K ≤ A.subgroupOf K := by
      dsimp [K, A, Dm, D]
      exact theorem_9_9_HC_commutator_le_H0Cprime_subgroupOf_sec9
        M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
    have hψDkerComm :
        Section1.subgroupInKernel' ψD (_root_.commutator K) := by
      intro x
      exact hψDkerA ⟨x.1, hcomm_le x.2⟩
    have hψDdeg : Section1.degree ψD = (1 : ℂ) :=
      degree_eq_one_of_irreducible_subgroupInKernel_commutator_sec9
        hψDirr hψDkerComm
    have hHC_le_Dm :
        (MF ⊔ C).subgroupOf M ≤ Dm := by
      have hHC_le_D :
          MF ⊔ C ≤ D :=
        theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u hcase
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hHC_le_D hx
    let ψ : Section1.ClassFunction ((MF ⊔ C).subgroupOf M) :=
      pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHC_le_Dm ψD
    refine ⟨ψ, ?_, ?_, ?_⟩
    · exact isIrreducible_pullbackClassFunctionOfSubgroupOfEquiv_sec9
        hHC_le_Dm hψDirr
    · rw [degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHC_le_Dm ψD,
        hψDdeg]
    · have hsub :
          Section1.subgroupOfClassFunction (T := Dm) ψ = ψD :=
        subgroupOfClassFunction_pullbackClassFunctionOfSubgroupOfEquiv_sec9
          hHC_le_Dm ψD
      calc
        θ = Section1.inducedCF K ψD := hθeq
        _ = Section1.inducedCF K (Section1.subgroupOfClassFunction (T := Dm) ψ) := by
          rw [hsub]

private theorem theorem_9_9_SH0_witness_HC_induction_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Section1.IsIrreducibleCharacterOnGroup θ →
        ¬ Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
          Section1.subgroupInKernel' θ
            ((H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            ∃ ψ : Section1.ClassFunction
                (((MF ⊔ C).subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)),
              Section1.IsIrreducibleCharacterOnGroup ψ ∧
                θ = Section1.inducedCF
                  (((MF ⊔ C).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ψ := by
  intro hcase hθirr hθnot hθker
  exact (theorem_9_9_case_b_clifford_induction_package_source_bridge_sec9
    M MF U W1 W2 H0 C p q u hcase).1 θ hθirr hθnot hθker

private theorem theorem_9_9_SH0_witness_constituent_degree_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Section1.IsIrreducibleCharacterOnGroup θ →
        ¬ Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              ((H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            characterDegreeDivisibleBy u θ := by
  intro hcase hθirr hθnot hθker
  rcases theorem_9_9_SH0_witness_HC_induction_source_bridge_sec9
      M MF U W1 W2 H0 C p q u θ hcase hθirr hθnot hθker with
    ⟨ψ, hψirr, hθeq⟩
  have hidx :
      Subgroup.index
        (((MF ⊔ C).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)) = u :=
    theorem_9_9_HC_subgroupOf_ambientDerived_index_eq_u_sec9
      M MF U W1 W2 H0 C p q u hcase
  rcases hψirr with ⟨n, ρ, _hρirr, hψeq⟩
  refine ⟨u * n, ?_, Nat.dvd_mul_right u n⟩
  rw [hθeq, Section1.degree_inducedClassFunction, hidx, hψeq,
    Section1.degree_representation_character]
  simp [Nat.cast_mul]

private theorem theorem_9_9_SH0_witness_degree_divisibility_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (χ : Section1.ClassFunction M)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Section1.IsIrreducibleCharacterOnGroup θ →
        ¬ Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
          Section1.subgroupInKernel' θ
            ((H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ →
              characterDegreeDivisibleBy u χ := by
  intro hcase hθirr hθnot hθker hχeq
  exact characterDegreeDivisibleBy_inducedCF_of_constituent_sec9
    ((ambientDerivedSubgroup M).subgroupOf M) u χ θ
    (theorem_9_9_SH0_witness_constituent_degree_source_bridge_sec9
      M MF U W1 W2 H0 C p q u θ hcase hθirr hθnot hθker)
    hχeq

private theorem theorem_9_9_SH0_degree_divisibility_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
        ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
          characterDegreeDivisibleBy u χ := by
  intro hcase hSH0 χ hχ
  rcases hSH0 with ⟨_hH0le, _hMFle, hmem⟩
  rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
  exact theorem_9_9_SH0_witness_degree_divisibility_source_bridge_sec9
    M MF U W1 W2 H0 C p q u χ θ hcase hθirr hθnot hθker hχeq

private theorem theorem_9_9_SH0Cprime_derived_witness_linear_induction_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        Section1.IsIrreducibleCharacterOnGroup θ →
          ¬ Section1.subgroupInKernel' θ
            ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              (((H0 ⊔ Cprime).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
              ∃ ψ : Section1.ClassFunction ((MF ⊔ C).subgroupOf M),
                Section1.IsIrreducibleCharacterOnGroup ψ ∧
                  Section1.degree ψ = (1 : ℂ) ∧
                    θ = Section1.inducedCF
                      (((MF ⊔ C).subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M))
                      (Section1.subgroupOfClassFunction ψ) := by
  intro hcase hCprimeEq hθirr hθnot hθker
  exact (theorem_9_9_case_b_clifford_induction_package_source_bridge_sec9
    M MF U W1 W2 H0 C p q u hcase).2 Cprime hCprimeEq θ hθirr hθnot hθker

private theorem theorem_9_9_SH0Cprime_kernel_witness_linear_induction_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (χ : Section1.ClassFunction M)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        Section1.IsIrreducibleCharacterOnGroup θ →
          ¬ Section1.subgroupInKernel' θ
            ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              (((H0 ⊔ Cprime).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
              χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ →
                inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hCprimeEq hθirr hθnot hθker hχeq
  rcases theorem_9_9_SH0Cprime_derived_witness_linear_induction_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime p q u θ hcase hCprimeEq hθirr hθnot hθker with
    ⟨ψ, hψirr, hψdeg, hθeq⟩
  refine ⟨ψ, hψirr, hψdeg, ?_⟩
  have hHC_le_D :
      (MF ⊔ C).subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    rcases hcase with
      ⟨h92, _hH0MF, hCentIn, _hpprime, _hqprime, _hpdata, _hcard,
        _hcentBy, _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
    rcases h92.typeP with ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
    rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
    rcases hCentIn with ⟨hC_le_U, _hCcentralizer⟩
    intro x hx
    change ((x : M) : G) ∈ ambientDerivedSubgroup M
    have hxHC : ((x : M) : G) ∈ MF ⊔ C := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact (sup_le hMFleD (hC_le_U.trans hUleD)) hxHC
  calc
    χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ := hχeq
    _ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
          (Section1.inducedCF
            (((MF ⊔ C).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M))
            (Section1.subgroupOfClassFunction ψ)) := by rw [hθeq]
    _ = Section1.inducedCF ((MF ⊔ C).subgroupOf M) ψ :=
      Section1.inducedCF_trans ((MF ⊔ C).subgroupOf M)
        ((ambientDerivedSubgroup M).subgroupOf M) hHC_le_D ψ

private theorem theorem_9_9_SH0Cprime_linear_induction_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
          ∀ χ : Section1.ClassFunction M, χ ∈ SH0Cprime →
            inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hCprimeEq hSH0Cprime χ hχ
  rcases hSH0Cprime with ⟨_hYle, _hMFle, hmem⟩
  rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
  exact theorem_9_9_SH0Cprime_kernel_witness_linear_induction_source_bridge_sec9
    M MF U W1 W2 H0 C Cprime p q u χ θ hcase hCprimeEq hθirr hθnot
      hθker hχeq

private theorem theorem_9_9_SH0Cprime_degree_induction_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
          ∀ χ : Section1.ClassFunction M, χ ∈ SH0Cprime →
            Section1.degree χ = (q * u : ℂ) ∧
              inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hCprimeEq hSH0Cprime χ hχ
  have hidx : Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u :=
    theorem_9_9_HC_index_eq_q_mul_u_sec9 M MF U W1 W2 H0 C p q u hcase
  have hlin : inducedFromLinearCharacterOfHC M MF C χ :=
    theorem_9_9_SH0Cprime_linear_induction_source_bridge_sec9 M MF U W1 W2
      H0 C Cprime p q u SH0Cprime hcase hCprimeEq hSH0Cprime χ hχ
  exact ⟨theorem_9_9_degree_eq_q_mul_u_of_linear_HC_sec9 M MF C q u χ
    hidx hlin, hlin⟩

private theorem theorem_9_9_degree_induction_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              (∀ χ : Section1.ClassFunction M, χ ∈ SH0 → characterDegreeDivisibleBy u χ) ∧
                ∀ χ : Section1.ClassFunction M, χ ∈ SH0Cprime →
                  Section1.degree χ = (q * u : ℂ) ∧
                    inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hCprimeEq hSH0 _hSH0C hSH0Cprime
  constructor
  · exact theorem_9_9_SH0_degree_divisibility_source_bridge_sec9
      M MF U W1 W2 H0 C p q u SH0 hcase hSH0
  · exact theorem_9_9_SH0Cprime_degree_induction_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime p q u SH0Cprime hcase hCprimeEq hSH0Cprime

private theorem theorem_9_9_reducible_filter_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
                ∃ R0 RC : Finset (Section1.ClassFunction M),
                  R0.card = p - 1 ∧
                    RC.card = p - 1 ∧
                    (∀ χ : Section1.ClassFunction M,
                      χ ∈ R0 ↔
                        χ ∈ SH0 ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    ∀ χ : Section1.ClassFunction M,
                      χ ∈ RC ↔
                        χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
  intro hcase _hCprimeEq hSH0 hSH0C _hSH0Cprime
  rcases hcase with
    ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hcard, _hcentBy, _hcyclic,
      _hirr, _hfield, _hcop, _hdiv⟩
  exact theorem_9_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C p q SH0 SH0C h92 hH0MF hC hpprime hpData
      hSH0 hSH0C

private theorem theorem_9_9_reducible_subfamily_degree_free_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              ∃ R : Finset (Section1.ClassFunction M),
                R.card = p - 1 ∧
                  R ⊆ SH0 ∧
                  (∀ χ : Section1.ClassFunction M, χ ∈ R →
                    ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                  (∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
                    ¬ Section1.IsIrreducibleCharacterOnGroup χ → χ ∈ R) ∧
                  R ⊆ SH0C := by
  intro hcase hCprimeEq hSH0 hSH0C hSH0Cprime
  rcases theorem_9_9_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime p q u SH0 SH0C SH0Cprime hcase hCprimeEq
      hSH0 hSH0C hSH0Cprime with
    ⟨R0, RC, hR0card, hRCcard, hR0mem, hRCmem⟩
  have hSH0CsubSH0 : SH0C ⊆ SH0 :=
    kernelInducedFamily_subset_of_le_sec9 M (ambientDerivedSubgroup M) MF
      H0 (H0 ⊔ C) SH0 SH0C le_sup_left hSH0 hSH0C
  have hRCsubR0 : RC ⊆ R0 := by
    intro χ hχRC
    rcases (hRCmem χ).1 hχRC with ⟨hχSH0C, hχred⟩
    exact (hR0mem χ).2 ⟨hSH0CsubSH0 hχSH0C, hχred⟩
  have hRCeqR0 : RC = R0 :=
    Finset.eq_of_subset_of_card_le hRCsubR0 (by rw [hR0card, hRCcard])
  have hR0subSH0 : R0 ⊆ SH0 := by
    intro χ hχR0
    exact ((hR0mem χ).1 hχR0).1
  have hR0nonirr :
      ∀ χ : Section1.ClassFunction M, χ ∈ R0 →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro χ hχR0
    exact ((hR0mem χ).1 hχR0).2
  have hR0all :
      ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ → χ ∈ R0 := by
    intro χ hχSH0 hχred
    exact (hR0mem χ).2 ⟨hχSH0, hχred⟩
  have hR0subSH0C : R0 ⊆ SH0C := by
    intro χ hχR0
    have hχRC : χ ∈ RC := by
      rw [hRCeqR0]
      exact hχR0
    exact ((hRCmem χ).1 hχRC).1
  exact ⟨R0, hR0card, hR0subSH0, hR0nonirr, hR0all, hR0subSH0C⟩

private theorem theorem_9_9_reducible_subfamily_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              ∃ R : Finset (Section1.ClassFunction M),
                R.card = p - 1 ∧
                  reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
                  R ⊆ SH0C := by
  intro hcase hCprimeEq hSH0 hSH0C hSH0Cprime
  rcases theorem_9_9_reducible_subfamily_degree_free_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime p q u SH0 SH0C SH0Cprime hcase hCprimeEq
      hSH0 hSH0C hSH0Cprime with
    ⟨R, hRcard, hRsubSH0, hRnonirr, hRall, hRsubSH0C⟩
  have hSH0Csubset : SH0C ⊆ SH0Cprime :=
    theorem_9_9_SH0C_subset_SH0Cprime_sec9 M MF H0 C Cprime SH0C
      SH0Cprime hCprimeEq hSH0C hSH0Cprime
  have hdegreeInduced :
      ∀ χ : Section1.ClassFunction M, χ ∈ SH0Cprime →
        Section1.degree χ = (q * u : ℂ) ∧
          inducedFromLinearCharacterOfHC M MF C χ :=
    theorem_9_9_SH0Cprime_degree_induction_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime p q u SH0Cprime hcase hCprimeEq
      hSH0Cprime
  have hRdata : reducibleCharacterSubfamilyData M SH0 R (q * u) := by
    refine ⟨hRsubSH0, ?_, hRall⟩
    intro χ hχR
    have hdeg : Section1.degree χ = (q * u : ℂ) :=
      (hdegreeInduced χ (hSH0Csubset (hRsubSH0C hχR))).1
    exact ⟨hRnonirr χ hχR, by simpa [Nat.cast_mul] using hdeg⟩
  exact ⟨R, hRcard, hRdata, hRsubSH0C⟩

private theorem theorem_9_9_H0C_le_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      H0 ⊔ C ≤ ambientDerivedSubgroup M := by
  intro hcase
  have hH0C_le_HC : H0 ⊔ C ≤ MF ⊔ C :=
    sup_le_sup (case_9_7_b_H0_le_MF_sec9 hcase) le_rfl
  exact hH0C_le_HC.trans
    (theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u hcase)

private theorem theorem_9_9_H0C_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (((H0 ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  let D : Subgroup G := ambientDerivedSubgroup M
  have hH0C_le_D : H0 ⊔ C ≤ D := by
    dsimp [D]
    exact theorem_9_9_H0C_le_ambientDerived_sec9
      M MF U W1 W2 H0 C p q u hcase
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_b_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', _hUleD, hD_eq, _hMFUdisj⟩
  have hH0C_le_MFU : H0 ⊔ C ≤ MF ⊔ U := by
    exact sup_le ((case_9_7_b_H0_le_MF_sec9 hcase).trans le_sup_left)
      ((case_9_7_b_quotientCentralizerIn_sec9 hcase).1.trans le_sup_right)
  have hH0CnormalMFU :
      ((H0 ⊔ C).subgroupOf (MF ⊔ U)).Normal :=
    theorem_9_9_H0C_normal_MF_sup_U_sec9 M MF U W1 W2 H0 C p q u hcase
  have hMFU_norm_H0C :
      MF ⊔ U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0C_le_MFU).1
      hH0CnormalMFU
  have hD_norm_H0C : D ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    intro d hdD
    exact hMFU_norm_H0C (by
      rw [← hD_eq]
      simpa [D] using hdD)
  exact subgroupOf_subgroupOf_normal_of_le_normalizer_sec9
    (M := M) (D := D) (H := H0 ⊔ C) hH0C_le_D hD_norm_H0C

private theorem theorem_9_9_MF_inf_H0Cprime_eq_H0_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        MF ⊓ (H0 ⊔ Cprime) = H0 := by
  intro hcase hCprimeEq
  have hH0MF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hC_le_U : C ≤ U := (case_9_7_b_quotientCentralizerIn_sec9 hcase).1
  have hCprimeU : Cprime ≤ U := hCprimeC.trans hC_le_U
  have hMFU :
      Disjoint MF U := by
    rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typeP with
      ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
    exact hcompD.2.2.2
  have hCprime_norm_H0 :
      Cprime ≤ Subgroup.normalizer (H0 : Set G) := by
    have hH0_le_M : H0 ≤ M :=
      (case_9_7_b_H0_le_MF_sec9 hcase).trans (case_9_7_b_MF_le_M_sec9 hcase)
    have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1
        (case_9_7_b_H0_normal_M_sec9 hcase)
    have hU_le_D : U ≤ ambientDerivedSubgroup M := by
      rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typePDefinitionData with
        ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
          _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
          _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
      exact hUleD
    have hCprimeM : Cprime ≤ M :=
      hCprimeU.trans (hU_le_D.trans section12_ambientDerivedSubgroup_le)
    exact hCprimeM.trans hM_norm_H0
  apply le_antisymm
  · intro x hx
    have hxProd : x ∈ (H0 : Set G) * (Cprime : Set G) := by
      have hsup := Subgroup.coe_mul_of_right_le_normalizer_left H0 Cprime
        hCprime_norm_H0
      rw [← hsup]
      exact hx.2
    rcases hxProd with ⟨h, hhH0, c, hcCprime, hcx⟩
    have hx_eq : x = h * c := hcx.symm
    have hcMF : c ∈ MF := by
      have hhMF : h ∈ MF := hH0MF hhH0
      have hhcMF : h * c ∈ MF := by simpa [← hx_eq] using hx.1
      have hc_eq : c = h⁻¹ * (h * c) := by group
      rw [hc_eq]
      exact MF.mul_mem (MF.inv_mem hhMF) hhcMF
    have hcU : c ∈ U := hCprimeU hcCprime
    have hc_bot : c ∈ (⊥ : Subgroup G) := by
      have hc_inf : c ∈ MF ⊓ U := ⟨hcMF, hcU⟩
      simpa [disjoint_iff.mp hMFU] using hc_inf
    have hc_one : c = 1 := by simpa using hc_bot
    simpa [hx_eq, hc_one] using hhH0
  · intro x hx
    exact ⟨hH0MF hx, Subgroup.mem_sup_left hx⟩

private theorem theorem_9_9_MF_inf_H0C_eq_H0_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      MF ⊓ (H0 ⊔ C) = H0 := by
  intro hcase
  have hH0MF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hC_le_U : C ≤ U := (case_9_7_b_quotientCentralizerIn_sec9 hcase).1
  have hMFU :
      Disjoint MF U := by
    rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typeP with
      ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
    exact hcompD.2.2.2
  have hC_norm_H0 :
      C ≤ Subgroup.normalizer (H0 : Set G) := by
    have hH0_le_M : H0 ≤ M :=
      (case_9_7_b_H0_le_MF_sec9 hcase).trans (case_9_7_b_MF_le_M_sec9 hcase)
    have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1
        (case_9_7_b_H0_normal_M_sec9 hcase)
    have hU_le_D : U ≤ ambientDerivedSubgroup M := by
      rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typePDefinitionData with
        ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
          _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
          _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
      exact hUleD
    have hCM : C ≤ M := hC_le_U.trans
      (hU_le_D.trans section12_ambientDerivedSubgroup_le)
    exact hCM.trans hM_norm_H0
  apply le_antisymm
  · intro x hx
    have hxProd : x ∈ (H0 : Set G) * (C : Set G) := by
      have hsup := Subgroup.coe_mul_of_right_le_normalizer_left H0 C
        hC_norm_H0
      rw [← hsup]
      exact hx.2
    rcases hxProd with ⟨h, hhH0, c, hcC, hcx⟩
    have hx_eq : x = h * c := hcx.symm
    have hcMF : c ∈ MF := by
      have hhMF : h ∈ MF := hH0MF hhH0
      have hhcMF : h * c ∈ MF := by simpa [← hx_eq] using hx.1
      have hc_eq : c = h⁻¹ * (h * c) := by group
      rw [hc_eq]
      exact MF.mul_mem (MF.inv_mem hhMF) hhcMF
    have hcU : c ∈ U := hC_le_U hcC
    have hc_bot : c ∈ (⊥ : Subgroup G) := by
      have hc_inf : c ∈ MF ⊓ U := ⟨hcMF, hcU⟩
      simpa [disjoint_iff.mp hMFU] using hc_inf
    have hc_one : c = 1 := by simpa using hc_bot
    simpa [hx_eq, hc_one] using hhH0
  · intro x hx
    exact ⟨hH0MF hx, Subgroup.mem_sup_left hx⟩

private theorem theorem_9_9_C_inf_H0Cprime_eq_Cprime_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        C ⊓ (H0 ⊔ Cprime) = Cprime := by
  intro hcase hCprimeEq
  have hH0MF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hC_le_U : C ≤ U := (case_9_7_b_quotientCentralizerIn_sec9 hcase).1
  have hMFU :
      Disjoint MF U := by
    rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typeP with
      ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
    exact hcompD.2.2.2
  have hCprime_norm_H0 :
      Cprime ≤ Subgroup.normalizer (H0 : Set G) := by
    have hH0_le_M : H0 ≤ M :=
      (case_9_7_b_H0_le_MF_sec9 hcase).trans (case_9_7_b_MF_le_M_sec9 hcase)
    have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1
        (case_9_7_b_H0_normal_M_sec9 hcase)
    have hU_le_D : U ≤ ambientDerivedSubgroup M := by
      rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typePDefinitionData with
        ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
          _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
          _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
      exact hUleD
    have hCprimeM : Cprime ≤ M :=
      hCprimeC.trans (hC_le_U.trans
        (hU_le_D.trans section12_ambientDerivedSubgroup_le))
    exact hCprimeM.trans hM_norm_H0
  apply le_antisymm
  · intro x hx
    have hxProd : x ∈ (H0 : Set G) * (Cprime : Set G) := by
      have hsup := Subgroup.coe_mul_of_right_le_normalizer_left H0 Cprime
        hCprime_norm_H0
      rw [← hsup]
      exact hx.2
    rcases hxProd with ⟨h, hhH0, c, hcCprime, hcx⟩
    have hx_eq : x = h * c := hcx.symm
    have hhC : h ∈ C := by
      have hcC : c ∈ C := hCprimeC hcCprime
      have hhcC : h * c ∈ C := by simpa [← hx_eq] using hx.1
      have hh_eq : h = (h * c) * c⁻¹ := by group
      rw [hh_eq]
      exact C.mul_mem hhcC (C.inv_mem hcC)
    have hhMF : h ∈ MF := hH0MF hhH0
    have hhU : h ∈ U := hC_le_U hhC
    have hh_bot : h ∈ (⊥ : Subgroup G) := by
      have hh_inf : h ∈ MF ⊓ U := ⟨hhMF, hhU⟩
      simpa [disjoint_iff.mp hMFU] using hh_inf
    have hh_one : h = 1 := by simpa using hh_bot
    simpa [hx_eq, hh_one] using hcCprime
  · intro x hx
    exact ⟨hCprimeC hx, Subgroup.mem_sup_right hx⟩

private theorem theorem_9_9_nontrivial_C_exists_HC_character_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        C ≠ ⊥ →
          ∃ ψ : Section1.ClassFunction ((MF ⊔ C).subgroupOf M),
            Section1.IsIrreducibleCharacterOnGroup ψ ∧
              Section1.subgroupInKernel' ψ
                (((H0 ⊔ Cprime).subgroupOf M).subgroupOf
                  ((MF ⊔ C).subgroupOf M)) ∧
              ¬ Section1.subgroupInKernel' ψ
                ((MF.subgroupOf M).subgroupOf ((MF ⊔ C).subgroupOf M)) ∧
              ¬ Section1.subgroupInKernel' ψ
                (((H0 ⊔ C).subgroupOf M).subgroupOf
                  ((MF ⊔ C).subgroupOf M)) := by
  intro hcase hCprimeEq hCne
  classical
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let A0 : Subgroup M := (H0 ⊔ Cprime).subgroupOf M
  let A : Subgroup HCm := A0.subgroupOf HCm
  have hA0_le_HCm : A0 ≤ HCm := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact theorem_9_9_H0Cprime_le_HC_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq hx
  have hHC_le_D :
      MF ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u hcase
  have hH0Cprime_le_D :
      H0 ⊔ Cprime ≤ ambientDerivedSubgroup M :=
    theorem_9_9_H0Cprime_le_ambientDerived_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  have hHCm_le_Dm : HCm ≤ Dm := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHC_le_D hx
  have hA0_le_Dm : A0 ≤ Dm := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hH0Cprime_le_D hx
  have hA0_normal_Dm :
      (A0.subgroupOf Dm).Normal := by
    dsimp [A0, Dm, D]
    exact theorem_9_9_H0Cprime_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
  have hDm_norm_A0 :
      Dm ≤ Subgroup.normalizer (A0 : Set M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA0_le_Dm).1 hA0_normal_Dm
  have hA_normal : A.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hA0_le_HCm).2
      (hHCm_le_Dm.trans hDm_norm_A0)
  letI : A.Normal := hA_normal
  let qHC : HCm →* HCm ⧸ A := QuotientGroup.mk' A
  let MFHC : Subgroup HCm := (MF.subgroupOf M).subgroupOf HCm
  let H0CHC : Subgroup HCm := ((H0 ⊔ C).subgroupOf M).subgroupOf HCm
  let QMF : Subgroup (HCm ⧸ A) := MFHC.map qHC
  let QH0C : Subgroup (HCm ⧸ A) := H0CHC.map qHC
  have hcomm_le_A : _root_.commutator HCm ≤ A := by
    let incl : HCm →* HCm.subgroupOf Dm :=
      { toFun := fun x => ⟨⟨(x : M), hHCm_le_Dm x.2⟩, x.2⟩
        map_one' := by
          ext
          rfl
        map_mul' := by
          intro x y
          ext
          rfl }
    have hcommD :=
      theorem_9_9_HC_commutator_le_H0Cprime_subgroupOf_sec9
        M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
    intro x hx
    have hxD : incl x ∈ _root_.commutator (HCm.subgroupOf Dm) :=
      monoidHom_mem_commutator_of_mem_sec9 incl hx
    have hmem := hcommD (by
      simpa [HCm, Dm, D, incl] using hxD)
    change ((x : HCm) : M) ∈ A0
    simpa [A0, HCm, Dm, D, incl, Subgroup.mem_subgroupOf] using hmem
  have hQcomm : IsMulCommutative (HCm ⧸ A) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le_A
  letI : IsMulCommutative (HCm ⧸ A) := hQcomm
  have hQprod :
      Section2.IsInternalDirectProduct
        (⊤ : Subgroup (HCm ⧸ A)) QMF QH0C := by
    have hCprimeC : Cprime ≤ C := by
      rw [hCprimeEq]
      rintro x ⟨y, _hy, rfl⟩
      exact y.property
    have hA_le_H0CHC : A ≤ H0CHC := by
      intro x hx
      have hxG : (((x : HCm) : M) : G) ∈ H0 ⊔ Cprime := by
        simpa [A, A0, Subgroup.mem_subgroupOf] using hx
      change (((x : HCm) : M) : G) ∈ H0 ⊔ C
      exact (sup_le_sup le_rfl hCprimeC) hxG
    have hInf_le_A : MFHC ⊓ H0CHC ≤ A := by
      intro x hx
      have hxG : (((x : HCm) : M) : G) ∈ MF ⊓ (H0 ⊔ C) := by
        exact ⟨by simpa [MFHC, Subgroup.mem_subgroupOf] using hx.1,
          by simpa [H0CHC, Subgroup.mem_subgroupOf] using hx.2⟩
      have hxH0 : (((x : HCm) : M) : G) ∈ H0 := by
        simpa [theorem_9_9_MF_inf_H0C_eq_H0_sec9
          M MF U W1 W2 H0 C p q u hcase] using hxG
      change (((x : HCm) : M) : G) ∈ H0 ⊔ Cprime
      exact (le_sup_left : H0 ≤ H0 ⊔ Cprime) hxH0
    have hmul : ∀ l : HCm, ∃ h ∈ MFHC, ∃ k ∈ H0CHC, l = h * k := by
      intro l
      let lHC : (MF ⊔ C : Subgroup G) := ⟨((l : M) : G), l.2⟩
      rcases (theorem_9_9_MF_C_isComplement_HC_sec9
          M MF U W1 W2 H0 C p q u hcase).2 lHC with
        ⟨⟨⟨m, hmMF⟩, ⟨c, hcC⟩⟩, hlHC⟩
      have hHC_le_M' : MF ⊔ C ≤ M :=
        theorem_9_9_HC_le_M_sec9 M MF U W1 W2 H0 C p q u hcase
      let h : HCm :=
        ⟨⟨m, hHC_le_M' ((le_sup_left : MF ≤ MF ⊔ C) hmMF)⟩,
          (le_sup_left : MF ≤ MF ⊔ C) hmMF⟩
      let k : HCm :=
        ⟨⟨c, hHC_le_M' ((le_sup_right : C ≤ MF ⊔ C) hcC)⟩,
          (le_sup_right : C ≤ MF ⊔ C) hcC⟩
      refine ⟨h, ?_, k, ?_, ?_⟩
      · exact hmMF
      · exact (le_sup_right : C ≤ H0 ⊔ C) hcC
      · ext
        exact (congrArg Subtype.val hlHC).symm
    simpa [QMF, QH0C, qHC] using
      quotient_internalDirectProduct_top_of_le_inf_mul_surjective_sec9
        A MFHC H0CHC hA_le_H0CHC hInf_le_A hmul
  have hQMFne : QMF ≠ ⊥ := by
    apply quotient_image_ne_bot_of_not_le_kernel_sec9
    intro hle
    have hMF_le_H0 : MF ≤ H0 := by
      intro m hm
      have hmM : m ∈ M := case_9_7_b_MF_le_M_sec9 hcase hm
      let x : HCm := ⟨⟨m, hmM⟩, (le_sup_left : MF ≤ MF ⊔ C) hm⟩
      have hxA : x ∈ A := hle (by exact hm)
      have hxG : m ∈ H0 ⊔ Cprime := by
        simpa [A, A0, Subgroup.mem_subgroupOf, x] using hxA
      have hxInf : m ∈ MF ⊓ (H0 ⊔ Cprime) := ⟨hm, hxG⟩
      simpa [theorem_9_9_MF_inf_H0Cprime_eq_H0_sec9
        M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq] using hxInf
    exact (case_9_7_b_H0_lt_MF_sec9 hcase).not_ge hMF_le_H0
  have hCprime_lt_C : Cprime < C := by
    have hMsolv : Group.IsSolvable M :=
      section9_solvable_of_proper_subgroup
        (case_9_7_b_hypothesis_9_2_sec9 hcase).maximal.1
    have hC_le_M : C ≤ M :=
      (le_sup_right : C ≤ MF ⊔ C).trans
        (theorem_9_9_HC_le_M_sec9 M MF U W1 W2 H0 C p q u hcase)
    have hCsub_solv : Group.IsSolvable (C.subgroupOf M) := by
      let _ : Group.IsSolvable M := hMsolv
      infer_instance
    have hCsolv : Group.IsSolvable C := by
      let _ : Group.IsSolvable (C.subgroupOf M) := hCsub_solv
      let e : C.subgroupOf M ≃* C := Subgroup.subgroupOfEquivOfLe hC_le_M
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    let _ : Group.IsSolvable C := hCsolv
    letI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot (H := C)).2 hCne
    have hlt : ⁅C, C⁆ < C := commutator_lt_self_of_isSolvable_local C
    simpa [hCprimeEq, Subgroup.map_subtype_commutator] using hlt
  have hQH0Cne : QH0C ≠ ⊥ := by
    apply quotient_image_ne_bot_of_not_le_kernel_sec9
    intro hle
    have hC_le_Cprime : C ≤ Cprime := by
      intro c hc
      have hcM : c ∈ M :=
        (theorem_9_9_HC_le_M_sec9 M MF U W1 W2 H0 C p q u hcase)
          ((le_sup_right : C ≤ MF ⊔ C) hc)
      let x : HCm := ⟨⟨c, hcM⟩, (le_sup_right : C ≤ MF ⊔ C) hc⟩
      have hxH0C : x ∈ H0CHC := by
        exact (le_sup_right : C ≤ H0 ⊔ C) hc
      have hxA : x ∈ A := hle hxH0C
      have hxG : c ∈ H0 ⊔ Cprime := by
        simpa [A, A0, Subgroup.mem_subgroupOf, x] using hxA
      have hxInf : c ∈ C ⊓ (H0 ⊔ Cprime) := ⟨hc, hxG⟩
      simpa [theorem_9_9_C_inf_H0Cprime_eq_Cprime_sec9
        M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq] using hxInf
    exact hCprime_lt_C.not_ge hC_le_Cprime
  have hMsolv : Group.IsSolvable M :=
    section9_solvable_of_proper_subgroup
      (case_9_7_b_hypothesis_9_2_sec9 hcase).maximal.1
  have hHCsolv : Group.IsSolvable HCm := by
    let _ : Group.IsSolvable M := hMsolv
    infer_instance
  have hQsolv : Group.IsSolvable (HCm ⧸ A) := by
    let _ : Group.IsSolvable HCm := hHCsolv
    infer_instance
  have hQMFsolv : Group.IsSolvable QMF := by
    let _ : Group.IsSolvable (HCm ⧸ A) := hQsolv
    infer_instance
  have hQH0Csolv : Group.IsSolvable QH0C := by
    let _ : Group.IsSolvable (HCm ⧸ A) := hQsolv
    infer_instance
  let _ : Group.IsSolvable QMF := hQMFsolv
  let _ : Group.IsSolvable QH0C := hQH0Csolv
  letI : Nontrivial QMF := (Subgroup.nontrivial_iff_ne_bot (H := QMF)).2 hQMFne
  letI : Nontrivial QH0C :=
    (Subgroup.nontrivial_iff_ne_bot (H := QH0C)).2 hQH0Cne
  rcases Section6.exists_nontrivial_linear_character_of_solvable QMF with
    ⟨χMF, hχMFne⟩
  rcases Section6.exists_nontrivial_linear_character_of_solvable QH0C with
    ⟨χC, hχCne⟩
  let lamTop : (⊤ : Subgroup (HCm ⧸ A)) →* ℂˣ :=
    Section3.internalDirectProductLinearCharacter hQprod χMF χC
  let lam : (HCm ⧸ A) →* ℂˣ :=
    lamTop.comp (Subgroup.topEquiv.symm.toMonoidHom)
  let ψ : Section1.ClassFunction HCm :=
    Section1.characterInflationByHom qHC lam
  have hψirr : Section1.IsIrreducibleCharacterOnGroup ψ := by
    simpa [ψ] using
      Section1.characterInflationByHom_isIrreducibleCharacterOnGroup qHC lam
  have hψkerA : Section1.subgroupInKernel' ψ A := by
    intro a
    have hdeg : Section1.degree ψ = 1 := by
      simp [ψ, Section1.degree, Section1.characterInflationByHom]
    rw [hdeg]
    have hqa : qHC a = 1 :=
      (QuotientGroup.eq_one_iff (N := A) (x := (a : HCm))).2 a.2
    simp [ψ, Section1.characterInflationByHom, hqa]
  have hψnotMF : ¬ Section1.subgroupInKernel' ψ MFHC := by
    intro hkerMF
    have hprodKerMF :
        Section1.subgroupInKernel'
          (Section3.linearCharacterProductOverInternalDirectProduct hQprod χMF χC)
          (QMF.subgroupOf (⊤ : Subgroup (HCm ⧸ A))) := by
      intro y
      have hdegProd :=
        Section3.linearCharacterProductOverInternalDirectProduct_degree hQprod χMF χC
      rw [hdegProd]
      rcases y.2 with ⟨m, hmMF, hmq⟩
      have hmker := hkerMF ⟨m, hmMF⟩
      have hψdeg : Section1.degree ψ = 1 := by
        simp [ψ, Section1.degree, Section1.characterInflationByHom]
      rw [hψdeg] at hmker
      have hval : (lam (qHC m) : ℂ) = 1 := by
        simpa [ψ, Section1.characterInflationByHom] using hmker
      have htop :
          ((Section3.internalDirectProductLinearCharacter hQprod χMF χC)
            (Subgroup.topEquiv.symm (qHC m)) : ℂ) = 1 := by
        simpa [lam, lamTop] using hval
      have hy :
          (y : (⊤ : Subgroup (HCm ⧸ A))) =
            Subgroup.topEquiv.symm (qHC m) := by
        apply Subtype.ext
        exact hmq.symm
      change
        ((Section3.internalDirectProductLinearCharacter hQprod χMF χC)
          (y : (⊤ : Subgroup (HCm ⧸ A))) : ℂ) = 1
      rw [hy]
      exact htop
    have hχone :=
      (Section3.linearCharacterProductOverInternalDirectProduct_rightKernel_iff
        hQprod χMF χC).1 hprodKerMF
    exact hχMFne hχone
  have hψnotH0C : ¬ Section1.subgroupInKernel' ψ H0CHC := by
    intro hkerH0C
    have hprodKerH0C :
        Section1.subgroupInKernel'
          (Section3.linearCharacterProductOverInternalDirectProduct hQprod χMF χC)
          (QH0C.subgroupOf (⊤ : Subgroup (HCm ⧸ A))) := by
      intro y
      have hdegProd :=
        Section3.linearCharacterProductOverInternalDirectProduct_degree hQprod χMF χC
      rw [hdegProd]
      rcases y.2 with ⟨m, hmH0C, hmq⟩
      have hmker := hkerH0C ⟨m, hmH0C⟩
      have hψdeg : Section1.degree ψ = 1 := by
        simp [ψ, Section1.degree, Section1.characterInflationByHom]
      rw [hψdeg] at hmker
      have hval : (lam (qHC m) : ℂ) = 1 := by
        simpa [ψ, Section1.characterInflationByHom] using hmker
      have htop :
          ((Section3.internalDirectProductLinearCharacter hQprod χMF χC)
            (Subgroup.topEquiv.symm (qHC m)) : ℂ) = 1 := by
        simpa [lam, lamTop] using hval
      have hy :
          (y : (⊤ : Subgroup (HCm ⧸ A))) =
            Subgroup.topEquiv.symm (qHC m) := by
        apply Subtype.ext
        exact hmq.symm
      change
        ((Section3.internalDirectProductLinearCharacter hQprod χMF χC)
          (y : (⊤ : Subgroup (HCm ⧸ A))) : ℂ) = 1
      rw [hy]
      exact htop
    have hχone :=
      (Section3.linearCharacterProductOverInternalDirectProduct_leftKernel_iff
        hQprod χMF χC).1 hprodKerH0C
    exact hχCne hχone
  exact ⟨ψ, hψirr, hψkerA, hψnotMF, hψnotH0C⟩

private theorem theorem_9_9_nontrivial_C_outside_SH0C_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
                C ≠ ⊥ →
                  ∃ χ : Section1.ClassFunction M,
                    χ ∈ SH0Cprime ∧ χ ∉ SH0C := by
  intro hcase hCprimeEq _hSH0 hSH0C hSH0Cprime hCne
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let K : Subgroup Dm := HCm.subgroupOf Dm
  let A : Subgroup Dm := ((H0 ⊔ Cprime).subgroupOf M).subgroupOf Dm
  let B : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
  rcases theorem_9_9_nontrivial_C_exists_HC_character_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq hCne with
    ⟨ψ, hψirr, hψkerA_HC, hψnotMF_HC, hψnotB_HC⟩
  have hHC_le_Dm : HCm ≤ Dm := by
    have hHC_le_D :
        MF ⊔ C ≤ D :=
      theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u hcase
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHC_le_D hx
  have hH0_le_HC : H0 ≤ MF ⊔ C :=
    (case_9_7_b_H0_le_MF_sec9 hcase).trans le_sup_left
  have hH0_le_D : H0 ≤ D := by
    exact hH0_le_HC.trans
      (theorem_9_9_HC_le_ambientDerived_sec9 M MF U W1 W2 H0 C p q u hcase)
  have hH0_le_H0Cprime : H0 ≤ H0 ⊔ Cprime := le_sup_left
  have hH0m_le_HCm : H0.subgroupOf M ≤ HCm := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hH0_le_HC hx
  have hψkerH0_HC :
      Section1.subgroupInKernel' ψ
        ((H0.subgroupOf M).subgroupOf HCm) := by
    refine subgroupInKernel'_mono_sec9 ?_ hψkerA_HC
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hH0_le_H0Cprime hx
  let ψD : Section1.ClassFunction K :=
    Section1.subgroupOfClassFunction (T := Dm) ψ
  have hψDirr : Section1.IsIrreducibleCharacterOnGroup ψD := by
    dsimp [ψD, K, HCm, Dm, D]
    exact isIrreducible_subgroupOfClassFunction_pf99_sec9 hHC_le_Dm hψirr
  have hψDkerA : Section1.subgroupInKernel' ψD (A.subgroupOf K) := by
    have hA_le_Dm : (H0 ⊔ Cprime).subgroupOf M ≤ Dm := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact theorem_9_9_H0Cprime_le_ambientDerived_sec9
        M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq hx
    have hA_le_HCm : (H0 ⊔ Cprime).subgroupOf M ≤ HCm := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact theorem_9_9_H0Cprime_le_HC_sec9
        M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq hx
    dsimp [ψD, A, K]
    exact subgroupInKernel'_subgroupOfClassFunction_pf99_sec9
      (G := M) (H := HCm) (T := Dm)
      (A := (H0 ⊔ Cprime).subgroupOf M)
      hA_le_Dm hA_le_HCm hψkerA_HC
  have hψDnotMF :
      ¬ Section1.subgroupInKernel' ψD
        (((MF.subgroupOf M).subgroupOf Dm).subgroupOf K) := by
    intro hker
    exact hψnotMF_HC
      (subgroupInKernel'_of_subgroupOfClassFunction_pf99_sec9
        (show MF.subgroupOf M ≤ Dm by
          intro x hx
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact (theorem_9_9_HC_le_ambientDerived_sec9
            M MF U W1 W2 H0 C p q u hcase)
            ((le_sup_left : MF ≤ MF ⊔ C) hx))
        (show MF.subgroupOf M ≤ HCm by
          intro x hx
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact (le_sup_left : MF ≤ MF ⊔ C) hx)
        hker)
  have hKnormal : K.Normal := by
    dsimp [K, HCm, Dm, D]
    exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q u hcase
  have hAnormal : A.Normal := by
    dsimp [A, Dm, D]
    exact theorem_9_9_H0Cprime_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq
  have hBnormal : B.Normal := by
    dsimp [B, Dm, D]
    exact theorem_9_9_H0C_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q u hcase
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_9_H0C_normal_M_sec9 M MF U W1 W2 H0 C p q u hcase
  have hDmnormal : Dm.Normal := by
    dsimp [Dm, D]
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hMFnormalDm : ((MF.subgroupOf M).subgroupOf Dm).Normal := by
    dsimp [Dm, D]
    exact theorem_9_9_MF_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q u hcase
  letI : K.Normal := hKnormal
  letI : A.Normal := hAnormal
  letI : B.Normal := hBnormal
  letI : ((H0 ⊔ C).subgroupOf M).Normal := hH0CnormalM
  letI : Dm.Normal := hDmnormal
  letI : ((MF.subgroupOf M).subgroupOf Dm).Normal := hMFnormalDm
  have hAK : A ≤ K := by
    intro x hx
    change ((x : Dm) : M) ∈ HCm
    change ((x : Dm) : M) ∈ (H0 ⊔ Cprime).subgroupOf M at hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (theorem_9_9_H0Cprime_le_HC_sec9
      M MF U W1 W2 H0 C Cprime p q u hcase hCprimeEq) hx
  have hBK : B ≤ K := by
    intro x hx
    change ((x : Dm) : M) ∈ HCm
    change ((x : Dm) : M) ∈ (H0 ⊔ C).subgroupOf M at hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (sup_le_sup (case_9_7_b_H0_le_MF_sec9 hcase) le_rfl) hx
  let θ : Section1.ClassFunction Dm := Section1.inducedCF K ψD
  have hθirr : Section1.IsIrreducibleCharacterOnGroup θ := by
    dsimp [θ, ψD, K, HCm, Dm, D]
    exact theorem_9_9_inducedCF_HC_irreducible_of_kernel_H0_not_MF_sec9
      M MF U W1 W2 H0 C p q u ψ hcase hψirr hψnotMF_HC hψkerH0_HC
  have hθkerA : Section1.subgroupInKernel' θ A := by
    dsimp [θ]
    exact subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
      K A hAK hψDirr hψDkerA
  have hθnotMF :
      ¬ Section1.subgroupInKernel' θ ((MF.subgroupOf M).subgroupOf Dm) := by
    intro hθkerMF
    exact hψDnotMF
      (subgroupInKernel'_of_inducedCF_eq_sec9 K ((MF.subgroupOf M).subgroupOf Dm)
        (by
          intro x hx
          change ((x : Dm) : M) ∈ HCm
          change ((x : Dm) : M) ∈ MF.subgroupOf M at hx
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact (le_sup_left : MF ≤ MF ⊔ C) hx)
        hψDirr rfl hθkerMF)
  let χ : Section1.ClassFunction M := Section1.inducedCF Dm θ
  refine ⟨χ, ?_, ?_⟩
  · rcases hSH0Cprime with ⟨_hYle, _hMFle, hmem⟩
    exact (hmem χ).2 ⟨θ, hθirr, hθnotMF, hθkerA, rfl⟩
  · intro hχSH0C
    rcases hSH0C with ⟨_hYle, _hMFle, hmem⟩
    rcases (hmem χ).1 hχSH0C with
      ⟨θC, hθCirr, _hθCnotMF, hθCkerB, hχeqC⟩
    have hχkerB : Section1.subgroupInKernel' χ ((H0 ⊔ C).subgroupOf M) := by
      rw [hχeqC]
      exact subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
        Dm ((H0 ⊔ C).subgroupOf M)
        (by
          intro x hx
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact theorem_9_9_H0C_le_ambientDerived_sec9
            M MF U W1 W2 H0 C p q u hcase hx)
        hθCirr hθCkerB
    have hθkerB : Section1.subgroupInKernel' θ B :=
      subgroupInKernel'_of_inducedCF_eq_sec9 Dm ((H0 ⊔ C).subgroupOf M)
        (by
          intro x hx
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact theorem_9_9_H0C_le_ambientDerived_sec9
            M MF U W1 W2 H0 C p q u hcase hx)
        hθirr rfl hχkerB
    have hψDkerB : Section1.subgroupInKernel' ψD (B.subgroupOf K) :=
      subgroupInKernel'_of_inducedCF_eq_sec9 K B hBK hψDirr rfl hθkerB
    have hψkerB :
        Section1.subgroupInKernel' ψ (((H0 ⊔ C).subgroupOf M).subgroupOf HCm) :=
      by
        have hB_le_Dm : (H0 ⊔ C).subgroupOf M ≤ Dm := by
          intro x hx
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact theorem_9_9_H0C_le_ambientDerived_sec9
            M MF U W1 W2 H0 C p q u hcase hx
        have hB_le_HCm : (H0 ⊔ C).subgroupOf M ≤ HCm := by
          intro x hx
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact (sup_le_sup (case_9_7_b_H0_le_MF_sec9 hcase) le_rfl) hx
        exact subgroupInKernel'_of_subgroupOfClassFunction_pf99_sec9
          (G := M) (H := HCm) (T := Dm)
          (A := (H0 ⊔ C).subgroupOf M)
          hB_le_Dm hB_le_HCm
          (by simpa [ψD, B, K] using hψDkerB)
    exact hψnotB_HC hψkerB

private theorem theorem_9_9_nontrivial_C_irreducible_member_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              (∃ R : Finset (Section1.ClassFunction M),
                R.card = p - 1 ∧
                  reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
                  R ⊆ SH0C) →
                C ≠ ⊥ →
                  ∃ χ : Section1.ClassFunction M,
                    χ ∈ SH0Cprime ∧ Section1.IsIrreducibleCharacterOnGroup χ := by
  intro hcase hCprimeEq hSH0 hSH0C hSH0Cprime hreducibles hCne
  rcases theorem_9_9_nontrivial_C_outside_SH0C_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime p q u SH0 SH0C SH0Cprime hcase hCprimeEq
      hSH0 hSH0C hSH0Cprime hCne with
    ⟨χ, hχCprime, hχnotC⟩
  rcases hreducibles with ⟨R, _hRcard, hRdata, hRsubSH0C⟩
  rcases hRdata with ⟨_hRsubSH0, _hRred, hRall⟩
  have hSH0Cprime_sub_SH0 : SH0Cprime ⊆ SH0 :=
    kernelInducedFamily_subset_of_le_sec9 M (ambientDerivedSubgroup M) MF
      H0 (H0 ⊔ Cprime) SH0 SH0Cprime le_sup_left hSH0 hSH0Cprime
  have hχSH0 : χ ∈ SH0 := hSH0Cprime_sub_SH0 hχCprime
  refine ⟨χ, hχCprime, ?_⟩
  by_contra hnotirr
  have hχR : χ ∈ R := hRall χ hχSH0 hnotirr
  exact hχnotC (hRsubSH0C hχR)

private theorem isIrreducible_pullback_mulEquiv_sec9
    {H K : Type u} [Group H] [Finite H] [Group K] [Finite K]
    (e : H ≃* K)
    {θ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup (fun h : H => θ (e h)) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let ρH : Representation ℂ H (Fin n → ℂ) := ρ.comp e.toMonoidHom
  refine ⟨n, ρH, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective
      ρ e.toMonoidHom e.surjective hρirr
  · ext h
    simp [ρH, hθeq, Representation.character]

private noncomputable def theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hCbot : C = ⊥)
    (ψ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ) :
    Section1.ClassFunction ((MF ⊔ C).subgroupOf M) := by
  let ψMF : Section1.ClassFunction (MF.subgroupOf M) :=
    Section1.subgroupOfClassFunction (T := M)
      (Section1.quotientCharacterInflation H0 MF ψ)
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let hHCeq : HCm = MF.subgroupOf M := by
    dsimp [HCm]
    rw [hCbot]
    simp
  let eHC : HCm ≃* MF.subgroupOf M := MulEquiv.subgroupCongr hHCeq
  exact fun x => ψMF (eHC x)

private noncomputable def theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hCbot : C = ⊥)
    (ψ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ) :
    Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M) := by
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let K : Subgroup Dm := HCm.subgroupOf Dm
  exact Section1.inducedCF K
    (Section1.subgroupOfClassFunction (T := Dm)
      (theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9 M MF H0 C hCbot ψ))

private noncomputable def theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hCbot : C = ⊥)
    (ψ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ) :
    Section1.ClassFunction M := by
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let θ : Section1.ClassFunction Dm :=
    theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
      M MF H0 C hCbot ψ
  exact Section1.inducedCF Dm θ

private theorem theorem_9_9_C_bot_quotientLinearCharacter_induced_mem_SH0C_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hSH0C : kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    ∀ ψ : (MF ⧸ H0MF) →* ℂˣ,
      ψ ≠ 1 →
        let ψMF : Section1.ClassFunction (MF.subgroupOf M) :=
          Section1.subgroupOfClassFunction (T := M)
            (Section1.quotientCharacterInflation H0 MF ψ)
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let hHCeq : HCm = MF.subgroupOf M := by
          dsimp [HCm]
          rw [hCbot]
          simp
        let eHC : HCm ≃* MF.subgroupOf M := MulEquiv.subgroupCongr hHCeq
        let ψHC : Section1.ClassFunction HCm := fun x => ψMF (eHC x)
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let K : Subgroup Dm := HCm.subgroupOf Dm
        let θ : Section1.ClassFunction Dm :=
          Section1.inducedCF K (Section1.subgroupOfClassFunction (T := Dm) ψHC)
        Section1.inducedCF Dm θ ∈ SH0C := by
  classical
  subst C
  have hnormalH0MF : (H0.subgroupOf MF).Normal :=
    case_9_7_b_H0_normal_MF_sec9 hcase
  letI : (H0.subgroupOf MF).Normal := hnormalH0MF
  dsimp only
  intro ψ hψne
  let ψG : Section1.ClassFunction MF :=
    Section1.quotientCharacterInflation H0 MF ψ
  let ψMF : Section1.ClassFunction (MF.subgroupOf M) :=
    Section1.subgroupOfClassFunction (T := M) ψG
  let HCm : Subgroup M := (MF ⊔ (⊥ : Subgroup G)).subgroupOf M
  have hHCeq : HCm = MF.subgroupOf M := by
    dsimp [HCm]
    simp
  let eHC : HCm ≃* MF.subgroupOf M := MulEquiv.subgroupCongr hHCeq
  let ψHC : Section1.ClassFunction HCm := fun x => ψMF (eHC x)
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let K : Subgroup Dm := HCm.subgroupOf Dm
  let θ : Section1.ClassFunction Dm :=
    Section1.inducedCF K (Section1.subgroupOfClassFunction (T := Dm) ψHC)
  have hKnormal : K.Normal := by
    dsimp [K, HCm, Dm]
    exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : K.Normal := hKnormal
  have hMFmDnormal : ((MF.subgroupOf M).subgroupOf Dm).Normal := by
    dsimp [Dm]
    exact theorem_9_9_MF_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  have hH0mDnormal : ((H0.subgroupOf M).subgroupOf Dm).Normal := by
    dsimp [Dm]
    exact theorem_9_9_H0_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : ((MF.subgroupOf M).subgroupOf Dm).Normal := hMFmDnormal
  letI : ((H0.subgroupOf M).subgroupOf Dm).Normal := hH0mDnormal
  have hSH0 :
      kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0C := by
    simpa using hSH0C
  rcases hSH0 with ⟨_hH0leD, hMFleD_family, hmem⟩
  have hH0leMF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hMFleM : MF ≤ M := case_9_7_b_MF_le_M_sec9 hcase
  have hH0leM : H0 ≤ M := hH0leMF.trans hMFleM
  have hMFm_le_Dm : MF.subgroupOf M ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ ambientDerivedSubgroup M
    exact hMFleD_family (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hHCm_le_Dm : HCm ≤ Dm := by
    intro x hx
    rw [hHCeq] at hx
    exact hMFm_le_Dm hx
  have hH0m_le_Dm : H0.subgroupOf M ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ ambientDerivedSubgroup M
    exact hMFleD_family (hH0leMF (by simpa [Subgroup.mem_subgroupOf] using hx))
  have hH0m_le_MFm : H0.subgroupOf M ≤ MF.subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hH0leMF hx
  have hMFm_le_HCm : MF.subgroupOf M ≤ HCm := by
    rw [hHCeq]
  have hH0m_le_HCm : H0.subgroupOf M ≤ HCm := hH0m_le_MFm.trans hMFm_le_HCm
  have hψGirr : Section1.IsIrreducibleCharacterOnGroup ψG := by
    dsimp [ψG]
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup H0 MF ψ
  have hψMFirr : Section1.IsIrreducibleCharacterOnGroup ψMF := by
    dsimp [ψMF]
    exact isIrreducible_subgroupOfClassFunction_pf99_sec9 hMFleM hψGirr
  have hψMFkerH0 :
      Section1.subgroupInKernel' ψMF
        ((H0.subgroupOf M).subgroupOf (MF.subgroupOf M)) := by
    dsimp [ψMF, ψG]
    exact subgroupInKernel'_subgroupOfClassFunction_pf99_sec9
      hH0leM hH0leMF
      (Section1.subgroupInKernel'_quotientCharacterInflation H0 MF ψ)
  have hψMFnotMF :
      ¬ Section1.subgroupInKernel' ψMF
        ((MF.subgroupOf M).subgroupOf (MF.subgroupOf M)) := by
    intro hkerMF
    apply hψne
    apply MonoidHom.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    apply Units.ext
    let xM : MF.subgroupOf M := ⟨⟨(x : G), hMFleM x.2⟩, by
      simp [Subgroup.mem_subgroupOf]⟩
    let xTop : (MF.subgroupOf M).subgroupOf (MF.subgroupOf M) := ⟨xM, by
      simp [xM]⟩
    have hval := hkerMF xTop
    have hdeg : Section1.degree ψMF = 1 := by
      dsimp [ψMF, ψG]
      rw [Section1.degree_subgroupOfClassFunction]
      exact Section1.quotientCharacterInflation_degree H0 MF ψ
    rw [hdeg] at hval
    simpa [ψMF, ψG, xM, xTop, Section1.subgroupOfClassFunction,
      Section1.quotientCharacterInflation] using hval
  have hψHCirr : Section1.IsIrreducibleCharacterOnGroup ψHC := by
    dsimp [ψHC]
    exact isIrreducible_pullback_mulEquiv_sec9 eHC hψMFirr
  have hψHCnotMF :
      ¬ Section1.subgroupInKernel' ψHC ((MF.subgroupOf M).subgroupOf HCm) := by
    intro hkerHC
    apply hψMFnotMF
    intro x
    let yHC : HCm := eHC.symm (x : MF.subgroupOf M)
    have hyMF : (yHC : M) ∈ MF.subgroupOf M := by
      have hyHC : ((yHC : M) : G) ∈ MF ⊔ (⊥ : Subgroup G) := by
        simpa [HCm, Subgroup.mem_subgroupOf] using yHC.property
      have hyG : ((yHC : M) : G) ∈ MF := by
        simpa using hyHC
      simpa [Subgroup.mem_subgroupOf] using hyG
    let yA : (MF.subgroupOf M).subgroupOf HCm := ⟨yHC, hyMF⟩
    have hval := hkerHC yA
    have hdeg : Section1.degree ψHC = Section1.degree ψMF := by
      change ψHC 1 = ψMF 1
      simp [ψHC, eHC]
    have hy : eHC yHC = (x : MF.subgroupOf M) := by
      simp [yHC]
    rw [hdeg] at hval
    simpa [ψHC, yA, yHC, hy] using hval
  have hψHCkerH0 :
      Section1.subgroupInKernel' ψHC ((H0.subgroupOf M).subgroupOf HCm) := by
    intro x
    have hxH0 : ((eHC (x : HCm) : MF.subgroupOf M) : M) ∈ H0.subgroupOf M := by
      have hx : ((x : HCm) : M) ∈ H0.subgroupOf M :=
        (x : (H0.subgroupOf M).subgroupOf HCm).property
      simpa [eHC, MulEquiv.subgroupCongr_apply] using hx
    let xMF : (H0.subgroupOf M).subgroupOf (MF.subgroupOf M) :=
      ⟨eHC (x : HCm), hxH0⟩
    have hval := hψMFkerH0 xMF
    have hdeg : Section1.degree ψHC = Section1.degree ψMF := by
      change ψHC 1 = ψMF 1
      simp [ψHC, eHC]
    rw [hdeg]
    simpa [ψHC, xMF] using hval
  have hθirr : Section1.IsIrreducibleCharacterOnGroup θ := by
    dsimp [θ, K, Dm, HCm, ψHC]
    simpa [HCm, ψHC, hHCeq] using
      theorem_9_9_inducedCF_HC_irreducible_of_kernel_H0_not_MF_sec9
        M MF U W1 W2 H0 (⊥ : Subgroup G) p q u ψHC
        hcase hψHCirr hψHCnotMF hψHCkerH0
  have hψHCDirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.subgroupOfClassFunction (T := Dm) ψHC) := by
    dsimp [Dm]
    exact isIrreducible_subgroupOfClassFunction_pf99_sec9 hHCm_le_Dm hψHCirr
  have hθnotMF :
      ¬ Section1.subgroupInKernel' θ ((MF.subgroupOf M).subgroupOf Dm) := by
    intro hθkerMF
    have hkerD :
        Section1.subgroupInKernel' (Section1.subgroupOfClassFunction (T := Dm) ψHC)
          (((MF.subgroupOf M).subgroupOf Dm).subgroupOf K) :=
      subgroupInKernel'_of_inducedCF_eq_sec9 K ((MF.subgroupOf M).subgroupOf Dm)
        (by
          intro x hx
          change ((x : Dm) : M) ∈ HCm
          exact hMFm_le_HCm hx)
        hψHCDirr rfl hθkerMF
    exact hψHCnotMF
      (subgroupInKernel'_of_subgroupOfClassFunction_pf99_sec9
        hMFm_le_Dm hMFm_le_HCm hkerD)
  have hψHCDkerH0 :
      Section1.subgroupInKernel'
        (Section1.subgroupOfClassFunction (T := Dm) ψHC)
        (((H0.subgroupOf M).subgroupOf Dm).subgroupOf K) := by
    dsimp [K, Dm]
    exact subgroupInKernel'_subgroupOfClassFunction_pf99_sec9
      hH0m_le_Dm hH0m_le_HCm hψHCkerH0
  have hθkerH0 :
      Section1.subgroupInKernel' θ ((H0.subgroupOf M).subgroupOf Dm) := by
    dsimp [θ, K]
    exact subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
      K ((H0.subgroupOf M).subgroupOf Dm)
      (by
        intro x hx
        change ((x : Dm) : M) ∈ HCm
        change ((x : Dm) : M) ∈ H0.subgroupOf M at hx
        exact hH0m_le_HCm hx)
      hψHCDirr hψHCDkerH0
  exact (hmem (Section1.inducedCF Dm θ)).2
    ⟨θ, hθirr, hθnotMF, hθkerH0, rfl⟩

private theorem theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_data_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hCbot : C = ⊥)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (ψ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ)
    (hψne : ψ ≠ 1) :
    let ψHC : Section1.ClassFunction ((MF ⊔ C).subgroupOf M) :=
      theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9 M MF H0 C hCbot ψ
    Section1.IsIrreducibleCharacterOnGroup ψHC ∧
      ¬ Section1.subgroupInKernel' ψHC
        ((MF.subgroupOf M).subgroupOf ((MF ⊔ C).subgroupOf M)) ∧
      Section1.subgroupInKernel' ψHC
        ((H0.subgroupOf M).subgroupOf ((MF ⊔ C).subgroupOf M)) := by
  classical
  subst C
  dsimp only
  have hnormalH0MF : (H0.subgroupOf MF).Normal :=
    case_9_7_b_H0_normal_MF_sec9 hcase
  letI : (H0.subgroupOf MF).Normal := hnormalH0MF
  let ψG : Section1.ClassFunction MF :=
    Section1.quotientCharacterInflation H0 MF ψ
  let ψMF : Section1.ClassFunction (MF.subgroupOf M) :=
    Section1.subgroupOfClassFunction (T := M) ψG
  let HCm : Subgroup M := (MF ⊔ (⊥ : Subgroup G)).subgroupOf M
  have hHCeq : HCm = MF.subgroupOf M := by
    dsimp [HCm]
    simp
  let eHC : HCm ≃* MF.subgroupOf M := MulEquiv.subgroupCongr hHCeq
  let ψHC : Section1.ClassFunction HCm := fun x => ψMF (eHC x)
  have hMFleM : MF ≤ M := case_9_7_b_MF_le_M_sec9 hcase
  have hH0leMF : H0 ≤ MF := case_9_7_b_H0_le_MF_sec9 hcase
  have hH0leM : H0 ≤ M := hH0leMF.trans hMFleM
  have hH0m_le_MFm : H0.subgroupOf M ≤ MF.subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hH0leMF hx
  have hMFm_le_HCm : MF.subgroupOf M ≤ HCm := by
    rw [hHCeq]
  have hH0m_le_HCm : H0.subgroupOf M ≤ HCm := hH0m_le_MFm.trans hMFm_le_HCm
  have hψGirr : Section1.IsIrreducibleCharacterOnGroup ψG := by
    dsimp [ψG]
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup H0 MF ψ
  have hψMFirr : Section1.IsIrreducibleCharacterOnGroup ψMF := by
    dsimp [ψMF]
    exact isIrreducible_subgroupOfClassFunction_pf99_sec9 hMFleM hψGirr
  have hψHCirr : Section1.IsIrreducibleCharacterOnGroup ψHC := by
    dsimp [ψHC]
    exact isIrreducible_pullback_mulEquiv_sec9 eHC hψMFirr
  have hψMFkerH0 :
      Section1.subgroupInKernel' ψMF
        ((H0.subgroupOf M).subgroupOf (MF.subgroupOf M)) := by
    dsimp [ψMF, ψG]
    exact subgroupInKernel'_subgroupOfClassFunction_pf99_sec9
      hH0leM hH0leMF
      (Section1.subgroupInKernel'_quotientCharacterInflation H0 MF ψ)
  have hψMFnotMF :
      ¬ Section1.subgroupInKernel' ψMF
        ((MF.subgroupOf M).subgroupOf (MF.subgroupOf M)) := by
    intro hkerMF
    apply hψne
    apply MonoidHom.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    apply Units.ext
    let xM : MF.subgroupOf M := ⟨⟨(x : G), hMFleM x.2⟩, by
      simp [Subgroup.mem_subgroupOf]⟩
    let xTop : (MF.subgroupOf M).subgroupOf (MF.subgroupOf M) := ⟨xM, by
      simp [xM]⟩
    have hval := hkerMF xTop
    have hdeg : Section1.degree ψMF = 1 := by
      dsimp [ψMF, ψG]
      rw [Section1.degree_subgroupOfClassFunction]
      exact Section1.quotientCharacterInflation_degree H0 MF ψ
    rw [hdeg] at hval
    simpa [ψMF, ψG, xM, xTop, Section1.subgroupOfClassFunction,
      Section1.quotientCharacterInflation] using hval
  have hψHCnotMF :
      ¬ Section1.subgroupInKernel' ψHC ((MF.subgroupOf M).subgroupOf HCm) := by
    intro hkerHC
    apply hψMFnotMF
    intro x
    let yHC : HCm := eHC.symm (x : MF.subgroupOf M)
    have hyMF : (yHC : M) ∈ MF.subgroupOf M := by
      have hyHC : ((yHC : M) : G) ∈ MF ⊔ (⊥ : Subgroup G) := by
        simpa [HCm, Subgroup.mem_subgroupOf] using yHC.property
      have hyG : ((yHC : M) : G) ∈ MF := by
        simpa using hyHC
      simpa [Subgroup.mem_subgroupOf] using hyG
    let yA : (MF.subgroupOf M).subgroupOf HCm := ⟨yHC, hyMF⟩
    have hval := hkerHC yA
    have hdeg : Section1.degree ψHC = Section1.degree ψMF := by
      change ψHC 1 = ψMF 1
      simp [ψHC, eHC]
    have hy : eHC yHC = (x : MF.subgroupOf M) := by
      simp [yHC]
    rw [hdeg] at hval
    simpa [ψHC, yA, yHC, hy] using hval
  have hψHCkerH0 :
      Section1.subgroupInKernel' ψHC ((H0.subgroupOf M).subgroupOf HCm) := by
    intro x
    have hxH0 : ((eHC (x : HCm) : MF.subgroupOf M) : M) ∈ H0.subgroupOf M := by
      have hx : ((x : HCm) : M) ∈ H0.subgroupOf M :=
        (x : (H0.subgroupOf M).subgroupOf HCm).property
      simpa [eHC, MulEquiv.subgroupCongr_apply] using hx
    let xMF : (H0.subgroupOf M).subgroupOf (MF.subgroupOf M) :=
      ⟨eHC (x : HCm), hxH0⟩
    have hval := hψMFkerH0 xMF
    have hdeg : Section1.degree ψHC = Section1.degree ψMF := by
      change ψHC 1 = ψMF 1
      simp [ψHC, eHC]
    rw [hdeg]
    simpa [ψHC, xMF] using hval
  simpa [theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9,
    ψG, ψMF, HCm, hHCeq, eHC, ψHC] using
    ⟨hψHCirr, hψHCnotMF, hψHCkerH0⟩

private theorem theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_injective_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hMFleM : MF ≤ M)
    (hCbot : C = ⊥) :
    Function.Injective
      (fun ψ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ =>
        theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
          M MF H0 C hCbot ψ) := by
  classical
  subst C
  intro ψ η hψη
  apply Section1.quotientCharacterInflation_injective H0 MF
  ext x
  let HCm : Subgroup M := (MF ⊔ (⊥ : Subgroup G)).subgroupOf M
  have hHCeq : HCm = MF.subgroupOf M := by
    dsimp [HCm]
    simp
  let eHC : HCm ≃* MF.subgroupOf M := MulEquiv.subgroupCongr hHCeq
  let xM : MF.subgroupOf M := ⟨⟨(x : G), hMFleM x.2⟩, by
    simp [Subgroup.mem_subgroupOf]⟩
  let xHC : HCm := eHC.symm xM
  have hx : eHC xHC = xM := by
    simp [xHC]
  have hval := congrFun hψη xHC
  change Section1.quotientCharacterInflation H0 MF ψ x =
    Section1.quotientCharacterInflation H0 MF η x
  simpa [theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9,
    HCm, hHCeq, eHC, xHC, xM, hx, Section1.subgroupOfClassFunction] using hval

private theorem theorem_9_9_C_bot_quotientLinearCharacter_intermediate_isIrreducible_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hCbot : C = ⊥)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (ψ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ)
    (hψne : ψ ≠ 1) :
    Section1.IsIrreducibleCharacterOnGroup
      (theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
        M MF H0 C hCbot ψ) := by
  classical
  subst C
  have hnormalH0MF : (H0.subgroupOf MF).Normal :=
    case_9_7_b_H0_normal_MF_sec9 hcase
  letI : (H0.subgroupOf MF).Normal := hnormalH0MF
  let ψHC : Section1.ClassFunction ((MF ⊔ (⊥ : Subgroup G)).subgroupOf M) :=
    theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
      M MF H0 (⊥ : Subgroup G) rfl ψ
  rcases theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_data_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase rfl ψ hψne with
    ⟨hψHCirr, hψHCnotMF, hψHCkerH0⟩
  simpa [theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9,
    ψHC] using
    theorem_9_9_inducedCF_HC_irreducible_of_kernel_H0_not_MF_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u ψHC
      hcase hψHCirr hψHCnotMF hψHCkerH0

private theorem theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_smul_eq_conjugateOnNormal_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
      theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    let hH0invU : IsInvariant U MF H0MF := by
      simpa [H0MF] using
        theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : MulDistribMulAction U (MF ⧸ H0MF) :=
      quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
    letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
    ∀ a : U,
    ∀ ψ : (MF ⧸ H0MF) →* ℂˣ,
      let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
      let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
      let K : Subgroup Dm := HCm.subgroupOf Dm
      let hKnormal : K.Normal := by
        dsimp [K, HCm, Dm]
        exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
          M MF U W1 W2 H0 C p q u hcase
      letI : K.Normal := hKnormal
      let aD : Dm := ⟨⟨((a⁻¹ : U) : G), by
        exact (theorem_9_9_case_b_U_le_M_sec9 M MF U W1 W2 H0 C p q u hcase)
          (a⁻¹).property⟩, by
        change ((a⁻¹ : U) : G) ∈ ambientDerivedSubgroup M
        exact theorem_9_9_case_b_U_le_ambientDerived_sec9
          M MF U W1 W2 H0 C p q u hcase (a⁻¹).property⟩
      Section1.subgroupOfClassFunction (T := Dm)
          (theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
            M MF H0 C hCbot (a • ψ)) =
        Section1.conjugateOnNormal K
          (Section1.subgroupOfClassFunction (T := Dm)
            (theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
              M MF H0 C hCbot ψ)) aD := by
  classical
  subst C
  dsimp only
  intro a ψ
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF H0MF := by
    simpa [H0MF] using
      theorem_9_9_case_b_H0_isInvariant_U_MF_sec9
        M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
  let ψG : Section1.ClassFunction MF :=
    Section1.quotientCharacterInflation H0 MF ψ
  let ψGsmul : Section1.ClassFunction MF :=
    Section1.quotientCharacterInflation H0 MF (a • ψ)
  let ψMF : Section1.ClassFunction (MF.subgroupOf M) :=
    Section1.subgroupOfClassFunction (T := M) ψG
  let ψMFsmul : Section1.ClassFunction (MF.subgroupOf M) :=
    Section1.subgroupOfClassFunction (T := M) ψGsmul
  let HCm : Subgroup M := (MF ⊔ (⊥ : Subgroup G)).subgroupOf M
  have hHCeq : HCm = MF.subgroupOf M := by
    dsimp [HCm]
    simp
  let eHC : HCm ≃* MF.subgroupOf M := MulEquiv.subgroupCongr hHCeq
  let ψHC : Section1.ClassFunction HCm := fun x => ψMF (eHC x)
  let ψHCsmul : Section1.ClassFunction HCm := fun x => ψMFsmul (eHC x)
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let K : Subgroup Dm := HCm.subgroupOf Dm
  have hKnormal : K.Normal := by
    dsimp [K, HCm, Dm]
    exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : K.Normal := hKnormal
  have hUleD : U ≤ ambientDerivedSubgroup M := by
    exact theorem_9_9_case_b_U_le_ambientDerived_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  have hUleM : U ≤ M :=
    hUleD.trans section12_ambientDerivedSubgroup_le
  let aD : Dm := ⟨⟨((a⁻¹ : U) : G), hUleM (a⁻¹).property⟩,
    by
      change ((a⁻¹ : U) : G) ∈ ambientDerivedSubgroup M
      exact hUleD (a⁻¹).property⟩
  have hsrc :
      Section1.subgroupOfClassFunction (T := Dm) ψHCsmul =
        Section1.conjugateOnNormal K
          (Section1.subgroupOfClassFunction (T := Dm) ψHC) aD := by
    ext x
    let xHC : HCm := ⟨(x : Dm), x.property⟩
    let yHC : HCm := ⟨aD * (x : Dm) * aD⁻¹,
      (show K.Normal from by simpa [K] using hKnormal).conj_mem
        (x : Dm) x.property aD⟩
    let xMF : MF := ⟨(((eHC xHC : MF.subgroupOf M) : M) : G), by
      exact (eHC xHC : MF.subgroupOf M).property⟩
    let yMF : MF := ⟨(((eHC yHC : MF.subgroupOf M) : M) : G), by
      exact (eHC yHC : MF.subgroupOf M).property⟩
    have hyMF : yMF = ((a⁻¹ : U) • xMF : MF) := by
      apply Subtype.ext
      change (((eHC yHC : MF.subgroupOf M) : M) : G) =
        (((a⁻¹ : U) • xMF : MF) : G)
      simp [xMF, xHC, yHC, eHC, aD, HCm,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
    have hsmul_mk :
        (a⁻¹ : U) • QuotientGroup.mk' H0MF xMF =
          QuotientGroup.mk' H0MF ((a⁻¹ : U) • xMF : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) (a⁻¹ : U) xMF)
    change (((ψ ((a⁻¹ : U) • QuotientGroup.mk' H0MF xMF)) : ℂˣ) : ℂ) =
      ((ψ (QuotientGroup.mk' H0MF yMF) : ℂˣ) : ℂ)
    rw [hsmul_mk, ← hyMF]
  simpa [theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9,
    ψG, ψGsmul, ψMF, ψMFsmul, HCm, hHCeq, eHC, ψHC, ψHCsmul, Dm, K,
    aD] using hsrc

private theorem theorem_9_9_C_bot_intermediate_eq_of_induced_eq_of_no_irreducible_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hSH0C : kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    ∀ ψ η : {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1},
      (¬ ∃ χ : Section1.ClassFunction M,
        χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
      theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot ψ.1 =
        theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot η.1 →
      theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
          M MF H0 C hCbot ψ.1 =
        theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
          M MF H0 C hCbot η.1 := by
  classical
  dsimp only
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  intro ψ η hnoSH0C hIndFinal
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  have hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let θψ : Section1.ClassFunction Dm :=
    theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
      M MF H0 C hCbot ψ.1
  let θη : Section1.ClassFunction Dm :=
    theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
      M MF H0 C hCbot η.1
  have hθψirr : Section1.IsIrreducibleCharacterOnGroup θψ := by
    dsimp [θψ, H0MF]
    exact theorem_9_9_C_bot_quotientLinearCharacter_intermediate_isIrreducible_sec9
      M MF U W1 W2 H0 C p q u hcase hCbot ψ.1 ψ.2
  have hθηirr : Section1.IsIrreducibleCharacterOnGroup θη := by
    dsimp [θη, H0MF]
    exact theorem_9_9_C_bot_quotientLinearCharacter_intermediate_isIrreducible_sec9
      M MF U W1 W2 H0 C p q u hcase hCbot η.1 η.2
  have hηmem :
      theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot η.1 ∈ SH0C := by
    simpa [theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9,
      theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9,
      theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9, H0MF] using
      theorem_9_9_C_bot_quotientLinearCharacter_induced_mem_SH0C_sec9
        M MF U W1 W2 H0 C p q u SH0C hcase hSH0C hCbot η.1 η.2
  have hηred :
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF Dm θη) := by
    intro hηfinalIrr
    apply hnoSH0C
    refine ⟨Section1.inducedCF Dm θη, ?_, hηfinalIrr⟩
    simpa [θη, theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9,
      Dm] using hηmem
  have hDindex : Dm.index = q := by
    simpa [Dm] using
      ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
        M MF U W1 W2 q (case_9_7_b_hypothesis_9_2_sec9 hcase)
  have hqprime : Nat.Prime q := case_9_7_b_q_prime_sec9 hcase
  have hηinertiaTop :
      Section1.inertiaSubgroup Dm θη = ⊤ :=
    inertiaSubgroup_eq_top_of_not_irreducible_induced_prime_index_sec9
      Dm hDindex hqprime hθηirr hηred
  have hInd :
      Section1.inducedCF Dm θψ = Section1.inducedCF Dm θη := by
    simpa [θψ, θη, Dm,
      theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9] using hIndFinal
  rcases induced_eq_imp_conjugateOrbitConj_pf99_sec9 Dm hθψirr hθηirr hInd with
    ⟨i, hi⟩
  have hself :
      Section1.conjugateOrbitConj Dm θη i = θη :=
    conjugateOrbitConj_eq_self_of_inertia_top_pf99_sec9 Dm θη hηinertiaTop i
  simpa [θψ, θη] using hi.trans hself

private theorem theorem_9_9_C_bot_orbitRel_of_intermediate_eq_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
      theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    let hH0invU : IsInvariant U MF H0MF := by
      simpa [H0MF] using
        theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : MulDistribMulAction U (MF ⧸ H0MF) :=
      quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
    letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
    letI : MulAction U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} :=
      nonidentitySubMulAction_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
    ∀ ψ η : {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1},
      theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
          M MF H0 C hCbot ψ.1 =
        theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
          M MF H0 C hCbot η.1 →
      MulAction.orbitRel U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} ψ η := by
  classical
  subst C
  dsimp only
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF H0MF := by
    simpa [H0MF] using
      theorem_9_9_case_b_H0_isInvariant_U_MF_sec9
        M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
  letI : MulAction U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
  intro ψ η hθeq
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ (⊥ : Subgroup G)).subgroupOf M
  let K : Subgroup Dm := HCm.subgroupOf Dm
  have hKnormal : K.Normal := by
    dsimp [K, HCm, Dm]
    exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : K.Normal := hKnormal
  let ψHC : Section1.ClassFunction HCm :=
    theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
      M MF H0 (⊥ : Subgroup G) rfl ψ.1
  let ηHC : Section1.ClassFunction HCm :=
    theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
      M MF H0 (⊥ : Subgroup G) rfl η.1
  let ψD : Section1.ClassFunction K :=
    Section1.subgroupOfClassFunction (T := Dm) ψHC
  let ηD : Section1.ClassFunction K :=
    Section1.subgroupOfClassFunction (T := Dm) ηHC
  have hHC_le_D :
      MF ⊔ (⊥ : Subgroup G) ≤ ambientDerivedSubgroup M :=
    theorem_9_9_HC_le_ambientDerived_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  have hHCm_le_Dm : HCm ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ ambientDerivedSubgroup M
    exact hHC_le_D (by simpa [HCm, Subgroup.mem_subgroupOf] using hx)
  rcases theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_data_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase rfl ψ.1 ψ.2 with
    ⟨hψHCirr, _hψHCnotMF, _hψHCkerH0⟩
  rcases theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_data_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase rfl η.1 η.2 with
    ⟨hηHCirr, _hηHCnotMF, _hηHCkerH0⟩
  have hψDirr : Section1.IsIrreducibleCharacterOnGroup ψD := by
    dsimp [ψD]
    exact isIrreducible_subgroupOfClassFunction_pf99_sec9 hHCm_le_Dm hψHCirr
  have hηDirr : Section1.IsIrreducibleCharacterOnGroup ηD := by
    dsimp [ηD]
    exact isIrreducible_subgroupOfClassFunction_pf99_sec9 hHCm_le_Dm hηHCirr
  have hIndInner :
      Section1.inducedCF K ψD = Section1.inducedCF K ηD := by
    simpa [theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9,
      ψHC, ηHC, ψD, ηD, HCm, Dm, K] using hθeq
  rcases induced_eq_imp_conjugateOrbitConj_pf99_sec9 K hψDirr hηDirr hIndInner with
    ⟨i, hi⟩
  revert hi
  refine Quotient.inductionOn i ?_
  intro g hi
  have hconjG :
      ψD = Section1.conjugateOnNormal K ηD g := by
    simpa [Section1.conjugateOrbitConj] using hi
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let UD : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  have hMFDnormal : MFD.Normal := by
    dsimp [MFD, Dm]
    exact theorem_9_9_MF_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  have hsemi :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD UD := by
    dsimp [MFD, UD, Dm]
    exact theorem_9_9_MF_U_internalSemidirect_ambientDerived_sec9
      M MF U W1 W2 q (case_9_7_b_hypothesis_9_2_sec9 hcase) hMFDnormal
  rcases hsemi.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
  have hmK : m0 ∈ K := by
    have hmMF : ((m0 : Dm) : M) ∈ MF.subgroupOf M := by
      simpa [MFD, Dm, Subgroup.mem_subgroupOf] using hm0
    have hmHC : (((m0 : Dm) : M) : G) ∈ MF ⊔ (⊥ : Subgroup G) := by
      exact (le_sup_left : MF ≤ MF ⊔ (⊥ : Subgroup G))
        (by simpa [Subgroup.mem_subgroupOf] using hmMF)
    simpa [K, HCm, Dm, Subgroup.mem_subgroupOf] using hmHC
  have hηDclass : Section1.IsClassFunction ηD :=
    Section1.isCharacter_isClassFunction ηD
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hηDirr)
  have hconjU :
      ψD = Section1.conjugateOnNormal K ηD u0 := by
    have hconjMU :
        ψD = Section1.conjugateOnNormal K ηD (m0 * u0) := by
      simpa [hg] using hconjG
    have herase :
        Section1.conjugateOnNormal K ηD (m0 * u0) =
          Section1.conjugateOnNormal K ηD u0 :=
      conjugateOnNormal_mul_left_of_mem_sec9 ηD hηDclass hmK
    exact hconjMU.trans herase
  let uU : U := ⟨(((u0 : Dm) : M) : G), by
    have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
      simpa [UD, Dm, Subgroup.mem_subgroupOf] using hu0
    simpa [Subgroup.mem_subgroupOf] using huUM⟩
  let a : U := uU⁻¹
  let aD : Dm := ⟨⟨((a⁻¹ : U) : G),
      theorem_9_9_case_b_U_le_M_sec9
        M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase (a⁻¹).property⟩,
    by
      change ((a⁻¹ : U) : G) ∈ ambientDerivedSubgroup M
      exact theorem_9_9_case_b_U_le_ambientDerived_sec9
        M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase (a⁻¹).property⟩
  have haD_eq : aD = u0 := by
    ext
    change (((a⁻¹ : U) : U) : G) = (((u0 : Dm) : M) : G)
    simp [a, uU]
  have hconjU_aD :
      ψD = Section1.conjugateOnNormal K ηD aD := by
    simpa [haD_eq] using hconjU
  have hsmulConj :
      Section1.subgroupOfClassFunction (T := Dm)
          (theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
            M MF H0 (⊥ : Subgroup G) rfl (a • η.1)) =
        Section1.conjugateOnNormal K ηD aD := by
    simpa [aD, a, ηD, HCm, Dm, K] using
      theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_smul_eq_conjugateOnNormal_sec9
        M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase rfl a η.1
  have hsourceD :
      ψD =
        Section1.subgroupOfClassFunction (T := Dm)
          (theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
            M MF H0 (⊥ : Subgroup G) rfl (a • η.1)) :=
    hconjU_aD.trans hsmulConj.symm
  have hHCsource :
      ψHC =
        theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9
          M MF H0 (⊥ : Subgroup G) rfl (a • η.1) := by
    exact subgroupOfClassFunction_injective_pf99_sec9 hHCm_le_Dm hsourceD
  have hMFleM : MF ≤ M := case_9_7_b_MF_le_M_sec9 hcase
  have hψeq : ψ.1 = a • η.1 :=
    theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_injective_sec9
      M MF H0 (⊥ : Subgroup G) hMFleM rfl hHCsource
  rw [MulAction.orbitRel_apply]
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact hψeq.symm

private theorem theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_smul_eq_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
      theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    let hH0invU : IsInvariant U MF H0MF := by
      simpa [H0MF] using
        theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : MulDistribMulAction U (MF ⧸ H0MF) :=
      quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
    letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
    ∀ a : U,
    ∀ ψ : (MF ⧸ H0MF) →* ℂˣ,
      theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot (a • ψ) =
        theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot ψ := by
  classical
  subst C
  dsimp only
  intro a ψ
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF H0MF := by
    simpa [H0MF] using
      theorem_9_9_case_b_H0_isInvariant_U_MF_sec9
        M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
  let ψG : Section1.ClassFunction MF :=
    Section1.quotientCharacterInflation H0 MF ψ
  let ψGsmul : Section1.ClassFunction MF :=
    Section1.quotientCharacterInflation H0 MF (a • ψ)
  let ψMF : Section1.ClassFunction (MF.subgroupOf M) :=
    Section1.subgroupOfClassFunction (T := M) ψG
  let ψMFsmul : Section1.ClassFunction (MF.subgroupOf M) :=
    Section1.subgroupOfClassFunction (T := M) ψGsmul
  let HCm : Subgroup M := (MF ⊔ (⊥ : Subgroup G)).subgroupOf M
  have hHCeq : HCm = MF.subgroupOf M := by
    dsimp [HCm]
    simp
  let eHC : HCm ≃* MF.subgroupOf M := MulEquiv.subgroupCongr hHCeq
  let ψHC : Section1.ClassFunction HCm := fun x => ψMF (eHC x)
  let ψHCsmul : Section1.ClassFunction HCm := fun x => ψMFsmul (eHC x)
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let K : Subgroup Dm := HCm.subgroupOf Dm
  have hKnormal : K.Normal := by
    dsimp [K, HCm, Dm]
    exact theorem_9_9_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 (⊥ : Subgroup G) p q u hcase
  letI : K.Normal := hKnormal
  have hUleD : U ≤ ambientDerivedSubgroup M := by
    rcases (case_9_7_b_hypothesis_9_2_sec9 hcase).typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hUleD
  have hUleM : U ≤ M :=
    hUleD.trans section12_ambientDerivedSubgroup_le
  let aD : Dm := ⟨⟨((a⁻¹ : U) : G), hUleM (a⁻¹).property⟩,
    by
      change ((a⁻¹ : U) : G) ∈ ambientDerivedSubgroup M
      exact hUleD (a⁻¹).property⟩
  have hsrc :
      Section1.subgroupOfClassFunction (T := Dm) ψHCsmul =
        Section1.conjugateOnNormal K
          (Section1.subgroupOfClassFunction (T := Dm) ψHC) aD := by
    ext x
    let xHC : HCm := ⟨(x : Dm), x.property⟩
    let yHC : HCm := ⟨aD * (x : Dm) * aD⁻¹,
      (show K.Normal from by simpa [K] using hKnormal).conj_mem
        (x : Dm) x.property aD⟩
    let xMF : MF := ⟨(((eHC xHC : MF.subgroupOf M) : M) : G), by
      exact (eHC xHC : MF.subgroupOf M).property⟩
    let yMF : MF := ⟨(((eHC yHC : MF.subgroupOf M) : M) : G), by
      exact (eHC yHC : MF.subgroupOf M).property⟩
    have hyMF : yMF = ((a⁻¹ : U) • xMF : MF) := by
      apply Subtype.ext
      change (((eHC yHC : MF.subgroupOf M) : M) : G) =
        (((a⁻¹ : U) • xMF : MF) : G)
      simp [xMF, xHC, yHC, eHC, aD, HCm,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
    have hsmul_mk :
        (a⁻¹ : U) • QuotientGroup.mk' H0MF xMF =
          QuotientGroup.mk' H0MF ((a⁻¹ : U) • xMF : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) (a⁻¹ : U) xMF)
    change (((ψ ((a⁻¹ : U) • QuotientGroup.mk' H0MF xMF)) : ℂˣ) : ℂ) =
      ((ψ (QuotientGroup.mk' H0MF yMF) : ℂˣ) : ℂ)
    rw [hsmul_mk, ← hyMF]
  have hind :
      Section1.inducedCF K (Section1.subgroupOfClassFunction (T := Dm) ψHCsmul) =
        Section1.inducedCF K (Section1.subgroupOfClassFunction (T := Dm) ψHC) := by
    rw [hsrc]
    exact inducedCF_conjugateOnNormal_sec9 K
      (Section1.subgroupOfClassFunction (T := Dm) ψHC) aD
  change Section1.inducedCF Dm
      (Section1.inducedCF K (Section1.subgroupOfClassFunction (T := Dm) ψHCsmul)) =
    Section1.inducedCF Dm
      (Section1.inducedCF K (Section1.subgroupOfClassFunction (T := Dm) ψHC))
  rw [hind]

private theorem theorem_9_9_C_bot_quotientLinearCharacter_induced_eq_of_orbitRel_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
      theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    let hH0invU : IsInvariant U MF H0MF := by
      simpa [H0MF] using
        theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : MulDistribMulAction U (MF ⧸ H0MF) :=
      quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
    letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
    letI : MulAction U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} :=
      nonidentitySubMulAction_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
    ∀ ψ η : {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1},
      MulAction.orbitRel U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} ψ η →
      theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot ψ.1 =
        theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot η.1 := by
  classical
  dsimp only
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF H0MF := by
    simpa [H0MF] using
      theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
  letI : MulAction U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
  intro ψ η hrel
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨a, ha⟩
  rw [← ha]
  exact theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_smul_eq_sec9
    M MF U W1 W2 H0 C p q u hcase hCbot a η.1

private theorem theorem_9_9_C_bot_orbitRel_of_quotientLinearCharacter_induced_eq_of_no_irreducible_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (hcase : case_9_7_b_data M MF U W1 W2 H0 C p q u)
    (hSH0C : kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C)
    (hCbot : C = ⊥) :
    let H0MF : Subgroup MF := H0.subgroupOf MF
    letI : H0MF.Normal := case_9_7_b_H0_normal_MF_sec9 hcase
    let hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
      theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    let hH0invU : IsInvariant U MF H0MF := by
      simpa [H0MF] using
        theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
    letI : MulDistribMulAction U (MF ⧸ H0MF) :=
      quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
    letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
    letI : MulAction U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} :=
      nonidentitySubMulAction_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
    ∀ ψ η : {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1},
      (¬ ∃ χ : Section1.ClassFunction M,
        χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
      theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot ψ.1 =
        theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
          M MF H0 C hCbot η.1 →
      MulAction.orbitRel U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} ψ η := by
  classical
  dsimp only
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF H0MF := by
    simpa [H0MF] using
      theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
  letI : MulAction U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
  intro ψ η hnoSH0C hInd
  have hθeq :
      theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
          M MF H0 C hCbot ψ.1 =
        theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9
          M MF H0 C hCbot η.1 :=
    theorem_9_9_C_bot_intermediate_eq_of_induced_eq_of_no_irreducible_sec9
      M MF U W1 W2 H0 C p q u SH0C hcase hSH0C hCbot ψ η hnoSH0C hInd
  exact theorem_9_9_C_bot_orbitRel_of_intermediate_eq_sec9
    M MF U W1 W2 H0 C p q u hcase hCbot ψ η hθeq

private theorem theorem_9_9_C_bot_nonprincipalLinearCharacter_orbit_count_le_SH0C_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
        C = ⊥ →
          (¬ ∃ χ : Section1.ClassFunction M,
            χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
            (p ^ q - 1) / u ≤ SH0C.card := by
  intro hcase hSH0C hCbot hnoSH0C
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  have hnormalH0 : H0MF.Normal := by
    dsimp [H0MF]
    exact case_9_7_b_H0_normal_MF_sec9 hcase
  letI : H0MF.Normal := hnormalH0
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_9_case_b_U_le_normalizer_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF H0MF := by
    simpa [H0MF] using
      theorem_9_9_case_b_H0_isInvariant_U_MF_sec9 M MF U W1 W2 H0 C p q u hcase
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U ((MF ⧸ H0MF) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction_sec9 U (MF ⧸ H0MF)
  letI : MulAction U {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
  let Ω := nonidentityOrbitQuotient_sec9 U ((MF ⧸ H0MF) →* ℂˣ)
  let β : Type u := {χ : Section1.ClassFunction M // χ ∈ SH0C}
  let f : Ω → β :=
    Quotient.lift
      (fun ψ : {ψ : (MF ⧸ H0MF) →* ℂˣ // ψ ≠ 1} =>
        (⟨theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9
            M MF H0 C hCbot ψ.1, by
          simpa [theorem_9_9_C_bot_quotientLinearCharacter_inducedCharacter_sec9,
            theorem_9_9_C_bot_quotientLinearCharacter_intermediateCharacter_sec9,
            theorem_9_9_C_bot_quotientLinearCharacter_HCCharacter_sec9, H0MF] using
            theorem_9_9_C_bot_quotientLinearCharacter_induced_mem_SH0C_sec9
              M MF U W1 W2 H0 C p q u SH0C hcase hSH0C hCbot ψ.1 ψ.2⟩ : β))
      (by
        intro ψ η hrel
        apply Subtype.ext
        dsimp
        exact theorem_9_9_C_bot_quotientLinearCharacter_induced_eq_of_orbitRel_sec9
          M MF U W1 W2 H0 C p q u hcase hCbot ψ η hrel)
  have hf_inj : Function.Injective f := by
    intro ω₁ ω₂ hω
    revert hω
    refine Quotient.inductionOn₂ ω₁ ω₂ ?_
    intro ψ η hψη
    apply Quotient.sound
    apply theorem_9_9_C_bot_orbitRel_of_quotientLinearCharacter_induced_eq_of_no_irreducible_sec9
      M MF U W1 W2 H0 C p q u SH0C hcase hSH0C hCbot
    · exact hnoSH0C
    exact congrArg Subtype.val hψη
  have hcard_le : Nat.card Ω ≤ Nat.card β := by
    haveI : Finite Ω := by
      dsimp [Ω, nonidentityOrbitQuotient_sec9]
      infer_instance
    letI : Fintype Ω := Fintype.ofFinite Ω
    letI : Fintype β := Fintype.ofFinite β
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective f hf_inj)
  have hβcard : Nat.card β = SH0C.card := by
    dsimp [β]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe SH0C
  have horbit :=
    theorem_9_9_C_bot_nonprincipalLinearCharacter_orbit_count_sec9
      M MF U W1 W2 H0 C p q u hcase hCbot
  dsimp only at horbit
  calc
    (p ^ q - 1) / u =
        Nat.card (nonidentityOrbitQuotient_sec9 U ((MF ⧸ H0MF) →* ℂˣ)) := horbit.symm
    _ = Nat.card Ω := rfl
    _ ≤ Nat.card β := hcard_le
    _ = SH0C.card := hβcard

private theorem theorem_9_9_C_bot_no_irreducible_numeric_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
        C = ⊥ →
          (¬ ∃ χ : Section1.ClassFunction M,
            χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
            (p ^ q - 1) / u = p - 1 := by
  intro hcase hSH0C hCbot hnoSH0C
  have hsource_le :
      (p ^ q - 1) / u ≤ SH0C.card :=
    theorem_9_9_C_bot_nonprincipalLinearCharacter_orbit_count_le_SH0C_sec9
      M MF U W1 W2 H0 C p q u SH0C hcase hSH0C hCbot hnoSH0C
  have hSH0 :
      kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0C := by
    simpa [hCbot] using hSH0C
  rcases hcase with
    ⟨h92, hH0MF, hC, hpprime, hqprime, hpData, _hcard, _hcentBy, hcyclic,
      _hirr, _hfield, _hcop, hdiv, _hprimeField⟩
  rcases theorem_9_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C p q SH0C SH0C h92 hH0MF hC hpprime hpData hSH0
      hSH0C with
    ⟨_R0, RC, _hR0card, hRCcard, _hR0mem, hRCmem⟩
  have hRC_eq_SH0C : RC = SH0C := by
    apply Finset.ext
    intro χ
    constructor
    · intro hχRC
      exact ((hRCmem χ).1 hχRC).1
    · intro hχSH0C
      have hχreducible : ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
        intro hχirr
        exact hnoSH0C ⟨χ, hχSH0C, hχirr⟩
      exact (hRCmem χ).2 ⟨hχSH0C, hχreducible⟩
  have hSH0Ccard : SH0C.card = p - 1 := by
    rw [← hRC_eq_SH0C, hRCcard]
  have hle : (p ^ q - 1) / u ≤ p - 1 := by
    simpa [hSH0Ccard] using hsource_le
  have hu : 0 < u := by
    rcases hcyclic with ⟨_hCU, _hnormal, _hcyc, hcardU⟩
    rw [← hcardU]
    exact Nat.card_pos
  exact theorem_9_9_case_b_count_eq_of_le_sec9 hpprime hqprime hu hdiv hle

private theorem theorem_9_9_C_bot_irreducible_count_eq_reducible_card_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
        C = ⊥ →
          (¬ ∃ χ : Section1.ClassFunction M,
            χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
            (p ^ q - 1) / u = SH0C.card := by
  intro hcase hSH0C hCbot hnoSH0C
  have hnumeric :
      (p ^ q - 1) / u = p - 1 :=
    theorem_9_9_C_bot_no_irreducible_numeric_count_source_bridge_sec9
      M MF U W1 W2 H0 C p q u SH0C hcase hSH0C hCbot hnoSH0C
  have hSH0 :
      kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0C := by
    simpa [hCbot] using hSH0C
  rcases hcase with
    ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hcard, _hcentBy, _hcyclic,
      _hirr, _hfield, _hcop, _hdiv⟩
  rcases theorem_9_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C p q SH0C SH0C h92 hH0MF hC hpprime hpData hSH0
      hSH0C with
    ⟨_R0, RC, _hR0card, hRCcard, _hR0mem, hRCmem⟩
  have hRC_eq_SH0C : RC = SH0C := by
    apply Finset.ext
    intro χ
    constructor
    · intro hχRC
      exact ((hRCmem χ).1 hχRC).1
    · intro hχSH0C
      have hχreducible : ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
        intro hχirr
        exact hnoSH0C ⟨χ, hχSH0C, hχirr⟩
      exact (hRCmem χ).2 ⟨hχSH0C, hχreducible⟩
  calc
    (p ^ q - 1) / u = p - 1 := hnumeric
    _ = RC.card := hRCcard.symm
    _ = SH0C.card := by rw [hRC_eq_SH0C]

private theorem theorem_9_9_C_bot_irreducible_count_eq_reducible_card_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime R : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              reducibleCharacterSubfamilyData M SH0 R (q * u) →
                R ⊆ SH0C →
                  C = ⊥ →
                    (¬ ∃ χ : Section1.ClassFunction M,
                      χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
                      (p ^ q - 1) / u = R.card := by
  intro hcase _hCprimeEq hSH0 hSH0C _hSH0Cprime hRdata hRsubSH0C hCbot hnoSH0C
  rcases hRdata with ⟨_hRsubSH0, _hRred, hRall⟩
  have hSH0CsubSH0 : SH0C ⊆ SH0 :=
    kernelInducedFamily_subset_of_le_sec9 M (ambientDerivedSubgroup M) MF
      H0 (H0 ⊔ C) SH0 SH0C le_sup_left hSH0 hSH0C
  have hSH0CsubR : SH0C ⊆ R := by
    intro χ hχSH0C
    have hχSH0 : χ ∈ SH0 := hSH0CsubSH0 hχSH0C
    have hχreducible : ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
      intro hχirr
      exact hnoSH0C ⟨χ, hχSH0C, hχirr⟩
    exact hRall χ hχSH0 hχreducible
  have hR_eq_SH0C : R = SH0C := by
    apply Finset.ext
    intro χ
    constructor
    · intro hχR
      exact hRsubSH0C hχR
    · intro hχSH0C
      exact hSH0CsubR hχSH0C
  have hcountSH0C :
      (p ^ q - 1) / u = SH0C.card :=
    theorem_9_9_C_bot_irreducible_count_eq_reducible_card_source_bridge_sec9
      M MF U W1 W2 H0 C p q u SH0C hcase hSH0C hCbot hnoSH0C
  simpa [hR_eq_SH0C] using hcountSH0C

private theorem theorem_9_9_no_irreducible_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              (∀ χ : Section1.ClassFunction M, χ ∈ SH0Cprime →
                Section1.degree χ = (q * u : ℂ) ∧
                  inducedFromLinearCharacterOfHC M MF C χ) →
                (∃ R : Finset (Section1.ClassFunction M),
                  R.card = p - 1 ∧
                    reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
                    R ⊆ SH0C) →
                  (¬ ∃ χ : Section1.ClassFunction M,
                    χ ∈ SH0Cprime ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
                    (¬ ∃ χ : Section1.ClassFunction M,
                      χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
                    C = ⊥ ∧ (p ^ q - 1) / u = p - 1 := by
  intro hcase hCprimeEq hSH0 hSH0C hSH0Cprime _hdegreeInduced hreducibles
    hno hnoSH0C
  have hCbot : C = ⊥ := by
    by_contra hCne
    rcases theorem_9_9_nontrivial_C_irreducible_member_source_bridge_sec9
        M MF U W1 W2 H0 C Cprime p q u SH0 SH0C SH0Cprime hcase hCprimeEq
        hSH0 hSH0C hSH0Cprime hreducibles hCne with
      ⟨χ, hχmem, hχirr⟩
    exact hno ⟨χ, hχmem, hχirr⟩
  rcases hreducibles with ⟨R, hRcard, hRdata, hRsubSH0C⟩
  have hcount :
      (p ^ q - 1) / u = R.card :=
    theorem_9_9_C_bot_irreducible_count_eq_reducible_card_sec9
      M MF U W1 W2 H0 C Cprime p q u SH0 SH0C SH0Cprime R hcase
      hCprimeEq hSH0 hSH0C hSH0Cprime hRdata hRsubSH0C hCbot hnoSH0C
  exact ⟨hCbot, hcount.trans hRcard⟩

public theorem theorem_9_9_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime := by
  intro hcase hCprimeEq hSH0 hSH0C hSH0Cprime
  rcases theorem_9_9_degree_induction_source_bridge_sec9 M MF U W1 W2 H0 C
      Cprime p q u SH0 SH0C SH0Cprime hcase hCprimeEq hSH0 hSH0C
      hSH0Cprime with
    ⟨hdegreeDiv, hdegreeInduced⟩
  have hreducibles :
      ∃ R : Finset (Section1.ClassFunction M),
        R.card = p - 1 ∧
          reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
          R ⊆ SH0C :=
    theorem_9_9_reducible_subfamily_source_bridge_sec9 M MF U W1 W2 H0 C
      Cprime p q u SH0 SH0C SH0Cprime hcase hCprimeEq hSH0 hSH0C
      hSH0Cprime
  have hnoirreducible :
      (¬ ∃ χ : Section1.ClassFunction M,
        χ ∈ SH0Cprime ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
          C = ⊥ ∧ u = (p ^ q - 1) / (p - 1) := by
    intro hno
    have hSH0Csubset : SH0C ⊆ SH0Cprime :=
      theorem_9_9_SH0C_subset_SH0Cprime_sec9 M MF H0 C Cprime SH0C
        SH0Cprime hCprimeEq hSH0C hSH0Cprime
    have hnoSH0C :
        ¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0C ∧ Section1.IsIrreducibleCharacterOnGroup χ := by
      rintro ⟨χ, hχ, hχirr⟩
      exact hno ⟨χ, hSH0Csubset hχ, hχirr⟩
    rcases theorem_9_9_no_irreducible_count_source_bridge_sec9 M MF U W1 W2 H0 C
        Cprime p q u SH0 SH0C SH0Cprime hcase hCprimeEq hSH0 hSH0C
        hSH0Cprime hdegreeInduced hreducibles hno hnoSH0C with
      ⟨hCbot, hcount⟩
    rcases hcase with
      ⟨_h92, _hH0MF, _hCentIn, hpprime, _hqprime, _hpdata, _hcard,
        _hcentBy, _hcyclic, _hirr, _hfield, _hcop, hdiv, _hprimeField⟩
    exact ⟨hCbot, theorem_9_9_case_b_count_arithmetic_sec9 hpprime hdiv hcount⟩
  exact ⟨hdegreeDiv, hdegreeInduced, hreducibles, hnoirreducible⟩

public theorem theorem_9_9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Cprime = (_root_.commutator C).map C.subtype →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) SH0Cprime →
              (∀ χ : Section1.ClassFunction M, χ ∈ SH0 → characterDegreeDivisibleBy u χ) ∧
              case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime := by
  intro hcase hCprimeEq hSH0 hSH0C hSH0Cprime
  have hchar :
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime :=
    theorem_9_9_source_core_sec9 M MF U W1 W2 H0 C Cprime p q u
      SH0 SH0C SH0Cprime hcase hCprimeEq hSH0 hSH0C hSH0Cprime
  exact ⟨hchar.1, hchar⟩

end CFSG.Section9
