module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rG
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rH
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rM
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rN
public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Quasithin (IsSylowIn)
open scoped Pointwise

section Abstract

variable {K : Type*} [Group K]

theorem uc22s21rs1_le_normalizer_sSup (S : Subgroup K) (𝓢 : Set (Subgroup K))
    (h : ∀ R ∈ 𝓢, S ≤ normalizer (R : Set K)) : S ≤ normalizer ((sSup 𝓢 : Subgroup K) : Set K) := by
  rw [sSup_eq_iSup']
  have h1 : S ≤ ⨅ R : ↥𝓢, normalizer ((R : Subgroup K) : Set K) := le_iInf fun R => h R.1 R.2
  exact h1.trans (Subgroup.iInf_normalizer_le_normalizer_iSup fun R : ↥𝓢 => (R : Subgroup K))

end Abstract

section Transport

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rs1_barPreimage_sSup_le (M H : Subgroup G) (𝓢 : Set (Subgroup (Bar2 M)))
    (hne : 𝓢.Nonempty) (h : ∀ R ∈ 𝓢, barPreimage M R ≤ H) : barPreimage M (sSup 𝓢) ≤ H := by
  obtain ⟨R₀, hR₀⟩ := hne
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hker : ∀ m : ↥M, π m = 1 → (m : G) ∈ H := fun m hm =>
    h R₀ hR₀ ⟨m, by change π m ∈ R₀; rw [hm]; exact R₀.one_mem, rfl⟩
  have hY : sSup 𝓢 ≤ (H.subgroupOf M).map π := by
    refine sSup_le fun R hR y hy => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) y
    exact ⟨m, h R hR ⟨m, hy, rfl⟩, rfl⟩
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨a, ha, hax⟩ := hY hm
  have h1 : π (a⁻¹ * m) = 1 := by rw [map_mul, map_inv, hax, inv_mul_cancel]
  have h2 : (m : G) = (a : G) * ((a⁻¹ * m : ↥M) : G) := by simp
  change (m : G) ∈ H
  rw [h2]
  exact H.mul_mem ha (hker _ h1)

end Transport

section Step1

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rs1_hinf_commutator_le (D : Data G) (st : Standing22 D) (hr77 : F07.R77E4 D)
    (h4 : 3 < CFSG.Open.evenRank G) {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M)
    (hH : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) :
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M := by
  classical
  rw [uc22p21c_commutator_bar_eq_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_contra hKF
  haveI hKperf : Group.IsPerfect ↥(CFSG.perfectResidual (Bar2 D.M)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  have hK : ⁅CFSG.perfectResidual (Bar2 D.M), CFSG.perfectResidual (Bar2 D.M)⁆ =
      CFSG.perfectResidual (Bar2 D.M) := Subgroup.isPerfect_iff.mp hKperf
  have h2 : CFSG.pCore 2 (Bar2 D.M) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥D.M) (p := 2)
  obtain ⟨q, hq, hq2, X, hXq, hXn, -, hXexp, hXcl, hnt, hXnc⟩ :=
    uc22s21rh_exists_supercritical_of_fitting h2 hK hKF
  haveI : X.Normal := hXn
  have hXp : IsPGroup q ↥X := CFSG.pCore_isPGroup.to_le hXq
  have hns : ¬ Group.IsSolvable ↥D.M := by
    intro hs
    haveI : Group.IsSolvable (Bar2 D.M) := inferInstance
    apply hKF
    have hbot : CFSG.perfectResidual (Bar2 D.M) = ⊥ :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.2 this
    rw [hbot]
    exact bot_le
  have hσ1 : D.sig ⊆ D.sig1 := UC6S846.sig_subset_sig1 st.sigmaStd hns
  obtain ⟨p, hpσ⟩ := st.dataExt.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hsp := UC6S846.sp_of_mem_sig st.sigmaStd hns hpσ
  have hrk : 3 < CFSG.Open.pRank p D.M :=
    lt_of_lt_of_le (by norm_num) (st.dataExt.four_le h4 p hpσ)
  have hTM : IsSylowIn 2 D.T D.M := uc22p22ta_isSylowIn D D.sylowM.le
  have hTX : barImage D.M D.T ≤ normalizer (X : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨𝓡, hsup, hpieces⟩ := uc22s21rg_pieces_le_or_le hq hq2 hTM hH₁.1 hH₂.1 hH hXp hTX
  have hcyc : ∀ H ∈ hSet D.T D.M, ∀ 𝓢 : Set (Subgroup (Bar2 D.M)),
      (∀ R ∈ 𝓢, R ≤ X ∧ barPreimage D.M R ≤ H) → IsCyclic ↥(sSup 𝓢) := by
    intro H hH 𝓢 h𝓢
    rcases 𝓢.eq_empty_or_nonempty with rfl | hne
    · rw [sSup_empty]
      infer_instance
    · exact uc22s21rn_piece_cyclic_of_r77 D st.r6_1 st.r6_3 hr77 hσ1 hp hp2 hpσ hq hq2 hsp hrk
        hXp hXnc hXexp hXcl (sSup_le fun R hR => (h𝓢 R hR).1) hH
        (uc22s21rs1_barPreimage_sSup_le D.M H 𝓢 hne fun R hR => (h𝓢 R hR).2)
  set 𝓢₁ : Set (Subgroup (Bar2 D.M)) :=
    {R | R ∈ 𝓡 ∧ barPreimage D.M (R ⊔ barImage D.M D.T) ≤ H₁} with h𝓢₁
  set 𝓢₂ : Set (Subgroup (Bar2 D.M)) :=
    {R | R ∈ 𝓡 ∧ barPreimage D.M (R ⊔ barImage D.M D.T) ≤ H₂} with h𝓢₂
  have hle : ∀ R : Subgroup (Bar2 D.M),
      barPreimage D.M R ≤ barPreimage D.M (R ⊔ barImage D.M D.T) := fun R =>
    Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
  have hX₁ : sSup 𝓢₁ ≤ X := sSup_le fun R hR => (hpieces R hR.1).1
  have hX₂ : sSup 𝓢₂ ≤ X := sSup_le fun R hR => (hpieces R hR.1).1
  have hX12 : sSup 𝓢₁ ⊔ sSup 𝓢₂ = X := by
    refine le_antisymm (sup_le hX₁ hX₂) ?_
    rw [← hsup]
    refine sSup_le fun R hRmem => ?_
    rcases (hpieces R hRmem).2.2 with h | h
    · exact le_sup_of_le_left (le_sSup ⟨hRmem, h⟩)
    · exact le_sup_of_le_right (le_sSup ⟨hRmem, h⟩)
  have hc₁ : IsCyclic ↥(sSup 𝓢₁) := hcyc H₁ hH₁ 𝓢₁ fun R hR =>
    ⟨(hpieces R hR.1).1, (hle R).trans hR.2⟩
  have hc₂ : IsCyclic ↥(sSup 𝓢₂) := hcyc H₂ hH₂ 𝓢₂ fun R hR =>
    ⟨(hpieces R hR.1).1, (hle R).trans hR.2⟩
  have hn₁ : barImage D.M D.T ≤ normalizer ((sSup 𝓢₁ : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
    uc22s21rs1_le_normalizer_sSup _ _ fun R hR => (hpieces R hR.1).2.1.2.2.1
  have hn₂ : barImage D.M D.T ≤ normalizer ((sSup 𝓢₂ : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
    uc22s21rs1_le_normalizer_sSup _ _ fun R hR => (hpieces R hR.1).2.1.2.2.1
  have hS : IsPGroup 2 ↥(barImage D.M D.T) :=
    isPGroup_map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
      (uc22s21rd_isSylowIn_subgroupOf hTM).isPGroup
  have hSi : ¬ 2 ∣ (barImage D.M D.T).index := fun h =>
    hTM.not_dvd_relIndex (h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hfin := uc22s21rm_commutator_mem_frattini hq hq2 hXexp hXnc hS hSi hc₁ hc₂ hX₁ hX₂ hX12
    hn₁ hn₂ hK
  obtain ⟨k, hk, x, hx, hne⟩ := hnt
  exact hne (hfin k hk x hx)

end Step1

end CFSG.LocalAnalysis.UniquenessCase.UC22
