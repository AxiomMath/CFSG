module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5StepC
public import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem odd_relIndex_sup {M H I N : Subgroup G} (hIH : I ≤ H) (hHI : H ≤ normalizer (I : Set G))
    (hNH : N ≤ H) (hNM : N ≤ M) (hodd : Odd (M.relIndex H)) : Odd (M.relIndex (I ⊔ N)) := by
  have hIodd : Odd (M.relIndex I) := by
    have hI'norm : (I.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2 hHI
    haveI : (I.subgroupOf H).Normal := hI'norm
    have hdvd : (M.subgroupOf H).relIndex ((I.subgroupOf H) ⊔ (M.subgroupOf H)) ∣
        M.relIndex H := by
      have := Subgroup.relIndex_dvd_index_of_le (H := M.subgroupOf H)
        (K := (I.subgroupOf H) ⊔ (M.subgroupOf H)) le_sup_right
      rwa [show (M.subgroupOf H).index = M.relIndex H from rfl] at this
    have heq : M.relIndex I =
        (M.subgroupOf H).relIndex ((I.subgroupOf H) ⊔ (M.subgroupOf H)) := by
      rw [← Subgroup.relIndex_subgroupOf hIH]
      exact (CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (I.subgroupOf H)
        (M.subgroupOf H)).symm
    rw [heq]
    exact Odd.of_dvd_nat hodd hdvd
  have hH₁ : I ⊔ N ≤ normalizer (I : Set G) :=
    sup_le Subgroup.le_normalizer (hNH.trans hHI)
  have hInorm : (I.subgroupOf (I ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hH₁
  haveI : (I.subgroupOf (I ⊔ N)).Normal := hInorm
  have hsupIN : (I.subgroupOf (I ⊔ N)) ⊔ (N.subgroupOf (I ⊔ N)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hsup : (I.subgroupOf (I ⊔ N)) ⊔ (M.subgroupOf (I ⊔ N)) = ⊤ := by
    apply top_le_iff.1
    rw [← hsupIN]
    exact sup_le le_sup_left
      ((Subgroup.subgroupOf_mono (I ⊔ N) hNM).trans le_sup_right)
  have hMeq : M.relIndex (I ⊔ N) = M.relIndex I := by
    calc M.relIndex (I ⊔ N) = (M.subgroupOf (I ⊔ N)).index := rfl
      _ = (M.subgroupOf (I ⊔ N)).relIndex ⊤ := by rw [Subgroup.relIndex_top_right]
      _ = (M.subgroupOf (I ⊔ N)).relIndex
            ((I.subgroupOf (I ⊔ N)) ⊔ (M.subgroupOf (I ⊔ N))) := by rw [hsup]
      _ = (M.subgroupOf (I ⊔ N)).relIndex (I.subgroupOf (I ⊔ N)) :=
            CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal _ _
      _ = M.relIndex I := Subgroup.relIndex_subgroupOf le_sup_left
  rw [hMeq]
  exact hIodd

theorem not_seven_dvd_card_of_le {M H I : Subgroup G} (hM : IsStronglyPEmbedded 7 M)
    (hIH : I ≤ H) (hHI : H ≤ normalizer (I : Set G)) (hIM : I ≤ M) (hHM : ¬ H ≤ M) :
    ¬ 7 ∣ Nat.card I := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rintro h7
  obtain ⟨W, hW⟩ := CFSG.ABGLocalTools.exists_isSylowOf 7 I
  have hWI : W ≤ I := hW.le
  have hWM : W ≤ M := hWI.trans hIM
  have hW7 : IsPGroup 7 W := hW.isPGroup
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card W = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hW.card_eq] at hcard
    have hpos : 0 < (Nat.card I).factorization 7 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_seven
        (Nat.card_ne_zero.mpr ⟨⟨1, I.one_mem⟩, inferInstance⟩) h7
    have hlt : 1 < 7 ^ ((Nat.card I).factorization 7) :=
      Nat.one_lt_pow (Nat.ne_of_gt hpos) (by norm_num)
    omega
  have hNW : normalizer (W : Set G) ≤ M := hM.normalizer_le hWne hW7 hWM
  have hHeq : H = I ⊔ (H ⊓ normalizer (W : Set G)) := by
    let N : Subgroup ↥H := I.subgroupOf H
    have hNnorm : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2 hHI
    haveI : N.Normal := hNnorm
    have hWsyl : CFSG.ABGLocalTools.IsSylowOf 7 (W.subgroupOf H) N := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨Subgroup.subgroupOf_mono H hWI, hW7.comap_subtype, ?_⟩
      rw [Subgroup.relIndex_subgroupOf hIH]
      exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hW).2.2
    obtain ⟨Q, hQ⟩ := hWsyl
    have htop : Subgroup.normalizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔ N = ⊤ := by
      rw [← hQ]
      exact Sylow.normalizer_sup_eq_top Q
    apply le_antisymm
    · intro h hh
      have hmem : (⟨h, hh⟩ : ↥H) ∈
          Subgroup.normalizer (W.subgroupOf H : Subgroup ↥H) ⊔ N := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 hmem
      have hyNormG : (y : G) ∈ normalizer (W : Set G) := by
        have hy' : y ∈ (normalizer (W : Set G)).subgroupOf H := by
          rw [Subgroup.subgroupOf_normalizer_eq (hWI.trans hIH)]
          exact hy
        exact Subgroup.mem_subgroupOf.mp hy'
      have hzI : (z : G) ∈ I := Subgroup.mem_subgroupOf.mp hz
      have hh_eq : h = (y : G) * (z : G) := by
        have := congrArg Subtype.val hyz
        simpa using this.symm
      rw [hh_eq]
      simpa [sup_comm] using
        (Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨y.2, hyNormG⟩) hzI)
    · exact sup_le hIH inf_le_left
  exact hHM (hHeq.le.trans (sup_le hIM (inf_le_right.trans hNW)))

theorem isCyclic_of_le_of_pRank_le_one {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 7 P)
    (hr : Open.pRank 7 K ≤ 1) : IsCyclic ↥P := by
  refine CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one (p := 7) (by norm_num) (by norm_num)
    hPK hP ?_
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank 7 K]
  exact hr

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem isSylowOf_three_of_eq_opp (h : Hyp141 D L₁ L₂ X) (h1421 : Thm1421 D)
    (hL : L₁ ⊔ L₂ = Opp 3 D.M) {H : Subgroup G} (hXH : X ≤ H) :
    CFSG.ABGLocalTools.IsSylowOf 3 X H := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hX3 : IsPGroup 3 X := h.sylow.isPGroup
  obtain ⟨S, hS, hXS⟩ := exists_isSylowOf_ge_of_isPGroup hX3 h.X_le_M
  have hSleL : S ≤ L₁ ⊔ L₂ := by
    rw [hL]
    intro s hs
    obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hs⟩
    have hk' : s ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk')
    exact Subgroup.subset_closure ⟨hS.le hs, j, hj⟩
  have hSeq : S = X := h.sylow.eq_of_le hXS hSleL hS.isPGroup
  have hXsylM : CFSG.ABGLocalTools.IsSylowOf 3 X D.M := hSeq ▸ hS
  obtain ⟨S', hS', hXS'⟩ := exists_isSylowOf_ge_of_isPGroup hX3 hXH
  have hS'eq : S' = X := by
    by_contra hne
    have hlt : X < S' := lt_of_le_of_ne hXS' (Ne.symm hne)
    have hlt' := lt_inf_normalizer Nat.prime_three hS'.isPGroup hlt
    have hQleM : S' ⊓ normalizer (X : Set G) ≤ D.M :=
      inf_le_right.trans (h.normalizer_X_le h1421)
    have hQp : IsPGroup 3 (S' ⊓ normalizer (X : Set G) : Subgroup G) :=
      hS'.isPGroup.to_inf_left
    have hQeq : S' ⊓ normalizer (X : Set G) = X := hXsylM.eq_of_le hlt'.le hQleM hQp
    have hcontr : X < X := by
      have := hlt'
      rwa [hQeq] at this
    exact absurd hcontr (lt_irrefl X)
  exact hS'eq ▸ hS'

theorem primeCore_le (h : Hyp141 D L₁ L₂ X) (hSg : UC6S846.SigmaStd D) (h1421 : Thm1421 D)
    (h1422 : Thm1422 D) (hperm : PermutesPair D.M L₁ L₂) {H : Subgroup G} (hXH : X ≤ H)
    (hF : Fstar H = pCoreOf 2 H) (hodd : Odd (D.M.relIndex H))
    (hAut : ∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (H ⊓ (L₁ ⊔ L₂)) ⊓ normalizer (X : Set G), ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹) :
    rankThreePrimeCore 3 H ≤ D.M := by
  obtain ⟨hIH₀, hHI₀, hI3₀⟩ := rankThreePrimeCore_facts H
  set I : Subgroup G := rankThreePrimeCore 3 H with hI
  have hIH : I ≤ H := by rw [hI]; exact hIH₀
  have hHI : H ≤ normalizer (I : Set G) := by rw [hI]; exact hHI₀
  have hI3 : ¬ 3 ∣ Nat.card I := by rw [hI]; exact hI3₀
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hXbot : X = ⊥ := le_bot_iff.1 (hbot ▸ hXH)
    have h9 := h.card_X
    rw [hXbot, Subgroup.card_bot] at h9
    norm_num at h9
  have hNX : H ⊓ normalizer (X : Set G) ≤ D.M :=
    inf_le_right.trans (h.normalizer_X_le h1421)
  have hH₁H : I ⊔ (H ⊓ normalizer (X : Set G)) ≤ H := sup_le hIH inf_le_left
  have hodd₁ : Odd (D.M.relIndex (I ⊔ (H ⊓ normalizer (X : Set G)))) :=
    odd_relIndex_sup hIH hHI inf_le_left hNX hodd
  have hinf : (I ⊔ (H ⊓ normalizer (X : Set G))) ⊓ normalizer (X : Set G) =
      H ⊓ normalizer (X : Set G) := by
    apply le_antisymm
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hH₁H (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hx, (Subgroup.mem_inf.1 hx).2⟩
  have hHeq : I ⊔ (H ⊓ normalizer (X : Set G)) =
      I ⊔ ((I ⊔ (H ⊓ normalizer (X : Set G))) ⊓ normalizer (X : Set G)) := by
    rw [hinf]
  have hXH₁ : X ≤ I ⊔ (H ⊓ normalizer (X : Set G)) :=
    (le_inf hXH Subgroup.le_normalizer).trans le_sup_right
  have hH₁I : I ⊔ (H ⊓ normalizer (X : Set G)) ≤ normalizer (I : Set G) :=
    sup_le Subgroup.le_normalizer (inf_le_left.trans hHI)
  have hrank₁ : ∀ q : ℕ, q.Prime → q ≠ 2 →
      ∀ V : Subgroup G, V ≤ I ⊔ (H ⊓ normalizer (X : Set G)) →
        IsElemAbelian q V → Nat.card V ≤ q ^ 3 := by
    intro q hq hq2 V hV hVe
    exact card_le_pow_of_pRank_le hq hVe (hV.trans hH₁H)
      (h.pRank_le_three_of_fstar hF hHne hq hq2)
  have hAut₁ : ∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (I ⊔ (H ⊓ normalizer (X : Set G))) ⊓ normalizer (X : Set G),
        ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹ := by
    intro n hn
    obtain ⟨m, hm, hmx⟩ := hAut n hn
    refine ⟨m, Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.1 hm).2⟩, hmx⟩
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hm).1).1, (Subgroup.mem_inf.1 hm).2⟩)
  have hH₁M : I ⊔ (H ⊓ normalizer (X : Set G)) ≤ D.M :=
    h.le_of_eq_sup_inf_normalizer hSg h1421 h1422 hperm
      (H := I ⊔ (H ⊓ normalizer (X : Set G))) (I := I)
      hXH₁ le_sup_left hH₁I hI3 hHeq hodd₁ hrank₁ hAut₁
  exact hI ▸ (le_sup_left.trans hH₁M)

theorem pRank_seven_le_one (h : Hyp141 D L₁ L₂ X) (hSg : UC6S846.SigmaStd D) (h71 : F07.R71 D)
    {H : Subgroup G} (hXH : X ≤ H) (hF : Fstar H = pCoreOf 2 H) (hHM : ¬ H ≤ D.M) :
    Open.pRank 7 (H ⊓ D.M) ≤ 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  by_contra hle
  rw [not_le] at hle
  have hsec : F07.Sec7Hyp D 7 H :=
    ⟨by norm_num, by norm_num, h.isStronglyPEmbedded_seven hSg,
      h.ne_top_of_fstar hXH hF, hHM, hle⟩
  have hoddPP : Odd (Nat.card (F07.PPrimeCoreIn 7 H)) := (h71 7 H hsec).1
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hXbot : X = ⊥ := le_bot_iff.1 (hbot ▸ hXH)
    have h9 := h.card_X
    rw [hXbot, Subgroup.card_bot] at h9
    norm_num at h9
  have hPne : pCoreOf 2 H ≠ ⊥ := pCoreOf_ne_bot_of_fstar hF hHne
  have hcore_le : CFSG.pCore 2 ↥H ≤ CFSG.pPrimeCore 7 ↥H := by
    refine le_sSup ?_
    refine ⟨CFSG.pCore_normal, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥H) (p := 2))
    rw [hk]
    exact (show Nat.Coprime 7 2 by norm_num).pow_right k
  have hmap_le : pCoreOf 2 H ≤ F07.PPrimeCoreIn 7 H := by
    rw [show pCoreOf 2 H = (CFSG.pCore 2 ↥H).map H.subtype from
      CFSG.openPCoreOf_eq_map_pCore 2 H]
    exact Subgroup.map_mono hcore_le
  have h2dvd : 2 ∣ Nat.card (pCoreOf 2 H) := by
    rcases (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) hPne
    · exact h2
  have h2dvdPP : 2 ∣ Nat.card (F07.PPrimeCoreIn 7 H) :=
    h2dvd.trans (Subgroup.card_dvd_of_le hmap_le)
  obtain ⟨j, hj⟩ := hoddPP
  obtain ⟨k, hk⟩ := h2dvdPP
  omega

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
