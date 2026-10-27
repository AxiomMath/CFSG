module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rS1
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Eq
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rQ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin (IsSylowIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rq_gamma_le_eq (D : Data G) (hr77 : F07.R77Eq D) (hσ1 : D.sig ⊆ D.sig1) {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) (hq : q.Prime) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hqσ : q ∉ D.sig) (hsp : IsStronglyPEmbedded p D.M) (hrk : 2 < CFSG.Open.pRank p D.M)
    {X : Subgroup (Bar2 D.M)} [X.Normal] (hXq : IsPGroup q X) (hXnc : ¬ IsCyclic X)
    (hXexp : ∀ x ∈ X, x ^ q = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) {Q : Subgroup G}
    (hQ : IsSylowOf q Q (barPreimage D.M X)) : rankThreeGamma 1 q Q ≤ D.M := by
  haveI := Fact.mk hq
  obtain ⟨hQM, hXQ, hdisj⟩ := uc22s21rq_barImage_sylow D.M hq hq2 hXq hQ
  have hle := uc22s21rq_pRank_le D.M hp hp2 hq hpq hXq hQ
  have heq : CFSG.Open.pRank p D.M = CFSG.Open.pRank p (D.M ⊓ normalizer (Q : Set G)) :=
    le_antisymm hle (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_left)
  refine hr77 hσ1 p hpσ hp2 hsp q hq hq2 hqσ Q hQM hQ.isPGroup
    (fun hc => hXnc (uc22s21rn_isCyclic_of_barImage_eq hQM hXQ hc)) ?_ ?_ (hrk.trans_le hle) heq
  · intro x hx
    have hx1 : (⟨x, hQM hx⟩ : ↥D.M) ∈ Q.subgroupOf D.M := hx
    have hy : (⟨x, hQM hx⟩ : ↥D.M) ^ q ∈ Q.subgroupOf D.M := (Q.subgroupOf D.M).pow_mem hx1 q
    have hker : (⟨x, hQM hx⟩ : ↥D.M) ^ q ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hXexp _ (hXQ ▸ ⟨_, hx1, rfl⟩)
    have := Subgroup.disjoint_def.1 hdisj hy hker
    simpa using congrArg Subtype.val this
  · have hQ' : (Q.subgroupOf D.M).map D.M.subtype = Q := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQM]
    have hle' : ∀ A B : Subgroup ↥D.M, A ≤ Q.subgroupOf D.M → B ≤ Q.subgroupOf D.M →
        ⁅A, B⁆ ≤ Q.subgroupOf D.M := by
      intro A B hA hB
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (Q.subgroupOf D.M).mul_mem ((Q.subgroupOf D.M).mul_mem
        ((Q.subgroupOf D.M).mul_mem (hA ha) (hB hb)) ((Q.subgroupOf D.M).inv_mem (hA ha)))
        ((Q.subgroupOf D.M).inv_mem (hB hb))
    have h1 : ⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆ ≤ Q.subgroupOf D.M := hle' _ _ le_rfl le_rfl
    have h2 : ⁅⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆, Q.subgroupOf D.M⁆ ≤ Q.subgroupOf D.M :=
      hle' _ _ h1 le_rfl
    have h3 : ⁅⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆, Q.subgroupOf D.M⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      have hmap : (⁅⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆, Q.subgroupOf D.M⁆).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) = ⊥ := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator]
        change ⁅⁅barImage D.M Q, barImage D.M Q⁆, barImage D.M Q⁆ = ⊥
        rw [hXQ]
        exact hXcl
      exact Subgroup.mem_bot.2 (Subgroup.disjoint_def.1 hdisj (h2 hc)
        ((Subgroup.map_eq_bot_iff _).1 hmap hc))
    rw [← hQ', ← Subgroup.map_commutator, ← Subgroup.map_commutator, h3, Subgroup.map_bot]

theorem uc22s21rn_hGamma_eq (D : Data G) (hr77 : F07.R77Eq D) (hσ1 : D.sig ⊆ D.sig1) {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) (hq : q.Prime) (hq2 : q ≠ 2)
    (hsp : IsStronglyPEmbedded p D.M) (hrk : 2 < CFSG.Open.pRank p D.M)
    {X : Subgroup (Bar2 D.M)} [X.Normal] (hXq : IsPGroup q X) (hXnc : ¬ IsCyclic X)
    (hXexp : ∀ x ∈ X, x ^ q = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) :
    q ∈ D.sig ∨ ∀ Q : Subgroup G, IsSylowOf q Q (barPreimage D.M X) →
      rankThreeGamma 1 q Q ≤ D.M := by
  by_cases hqσ : q ∈ D.sig
  · exact Or.inl hqσ
  · exact Or.inr fun Q hQ => uc22s21rq_gamma_le_eq D hr77 hσ1 hp hp2 hpσ hq hq2
      (fun h => hqσ (h ▸ hpσ)) hqσ hsp hrk hXq hXnc hXexp hXcl hQ

theorem uc22s21rn_piece_cyclic_of_r77Eq (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (hr77 : F07.R77Eq D) (hσ1 : D.sig ⊆ D.sig1) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpσ : p ∈ D.sig) (hq : q.Prime) (hq2 : q ≠ 2) (hsp : IsStronglyPEmbedded p D.M)
    (hrk : 2 < CFSG.Open.pRank p D.M) {X : Subgroup (Bar2 D.M)} [X.Normal] (hXq : IsPGroup q X)
    (hXnc : ¬ IsCyclic X) (hXexp : ∀ x ∈ X, x ^ q = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    {R : Subgroup (Bar2 D.M)} (hRX : R ≤ X) {H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hRH : barPreimage D.M R ≤ H) : IsCyclic R :=
  uc22s21rn_piece_cyclic D h61 h63 hq hq2
    (uc22s21rn_hGamma_eq D hr77 hσ1 hp hp2 hpσ hq hq2 hsp hrk hXq hXnc hXexp hXcl) hRX
    (hXq.to_le hRX) hH hRH

theorem uc22s21rs1_hinf_commutator_le_eq (D : Data G) (st : Standing22 D) (hr77 : F07.R77Eq D)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
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
  have hrk : 2 < CFSG.Open.pRank p D.M :=
    lt_of_lt_of_le (by norm_num) (st.sigmaStd.three_le p hpσ)
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
    · exact uc22s21rn_piece_cyclic_of_r77Eq D st.r6_1 st.r6_3 hr77 hσ1 hp hp2 hpσ hq hq2 hsp hrk
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

end CFSG.LocalAnalysis.UniquenessCase.UC22
