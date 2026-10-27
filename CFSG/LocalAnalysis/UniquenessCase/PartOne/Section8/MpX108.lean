module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Theorem8108
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC1K31
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four)

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_isSL3Four
    {X : Type} [Group X] [Finite X]
    (h : IsSL3Four X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    nonempty_mulEquiv_statedSL_of_isSL3Four h
  letI := hKfield
  letI := hKfin
  have hcard : Nat.card X = 60480 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL,
      CFSG.RankThree.PartTwo.KFacts.L34.card_specialLinearGroup hKcard]
  refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hp ?_
  rw [hcard]
  intro hsq
  have hfac : (60480 : ℕ) = 2 ^ 6 * 3 ^ 3 * 5 * 7 := by norm_num
  rw [hfac] at hsq
  have hp_dvd : p ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7 := by
    have h1 : p ∣ p ^ 2 := ⟨p, by ring⟩
    simpa using h1.trans hsq
  have hpcase : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have h1 : p ∣ 2 ^ 6 * (3 ^ 3 * (5 * 7)) := by
      simpa [mul_assoc] using hp_dvd
    rcases hp.dvd_mul.mp h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h2))
    · rcases hp.dvd_mul.mp h2 with h3 | h3
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h3)))
      · rcases hp.dvd_mul.mp h3 with h5 | h7
        · exact Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5)))
        · exact Or.inr (Or.inr (Or.inr
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7)))
  rcases hpcase with rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at hsq
  · norm_num at hsq

theorem pRank_X_le_two
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    {L L' : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf S.M L = {L, L'})
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) :
    CFSG.Open.pRank S.p (CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure S.M L) ≤ 2 := by
  classical
  haveI : Fact S.p.Prime := ⟨S.hp.1.1⟩
  have h3β : 3 ∉ CFSG.Open.uniqueFourBeta G :=
    three_not_mem_uniqueFourBeta_of_not_strong hU S hMS hnot
  have hp5 : 5 ≤ S.p := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.five_le_of_mem_uniqueFourSigma S.hp h3β
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  have hLM : L ≤ S.M := hL.1.le
  have hXeq : conjClosure S.M L = L ⊔ L' := by
    unfold conjClosure
    rw [hset]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun X => iSup_le fun hX => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup₂_of_le L (by simp) le_rfl)
        (le_iSup₂_of_le L' (by simp) le_rfl)
  by_cases hL'eq : L' = L
  ·
    rw [hXeq, hL'eq, sup_idem]
    rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd
      (Y := L) (p := S.p) S.hp.1.1 hp2]
    exact (pRank_le_one_of_isSL3Four hSL S.hp.1.1 hp5).trans (by norm_num)
  ·
    have hL'conj : L' ∈ conjSetOf S.M L := by
      rw [hset]
      simp
    obtain ⟨g, hgM, hL'map⟩ := hL'conj
    have hL'calC : L' ∈ calC S.M := by
      rw [hL'map]
      exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map S.M (MulAut.conj g)
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.1
          (Subgroup.le_normalizer hgM)) hL
    have hL'LM : L' ≤ S.M := hL'calC.1.le
    have hSL' : IsSL3Four (Bar2 L') := by
      obtain ⟨eBar⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20d_bar2_conj g L
      have hL'map' : L' = CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20bCj g L := by
        simpa [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20bCj] using hL'map
      have e : Bar2 L ≃* Bar2 L' := by
        rw [hL'map']
        exact eBar
      obtain ⟨hSL3, hcenter⟩ := hSL
      let ec : (Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
          (Bar2 L' ⧸ Subgroup.center (Bar2 L')) :=
        QuotientGroup.congr (Subgroup.center (Bar2 L)) (Subgroup.center (Bar2 L'))
          e (Subgroup.map_center_eq e)
      refine ⟨⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hSL3.1,
        CFSG.Blueprint.LieModel.of_mulEquiv ec hSL3.2⟩, ?_⟩
      rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact hcenter
    set A : Subgroup (Bar2 S.M) := barImage S.M L with hAdef
    set B : Subgroup (Bar2 S.M) := barImage S.M L' with hBdef
    set Kbar : Subgroup (Bar2 S.M) := barImage S.M (L ⊔ L') with hKdef
    have hK_eq : Kbar = A ⊔ B := by
      rw [hKdef, hAdef, hBdef]
      show barImage S.M (L ⊔ L') = barImage S.M L ⊔ barImage S.M L'
      simp only [barImage, Subgroup.subgroupOf_sup hLM hL'LM, Subgroup.map_sup]
    have hAK : A ≤ Kbar := by rw [hK_eq]; exact le_sup_left
    have hBK : B ≤ Kbar := by rw [hK_eq]; exact le_sup_right
    have hne : L ≠ L' := fun h => hL'eq h.symm
    have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
      uc22p22l_barImage_commute hL hL'calC hne
    have hA_NB : A ≤ Subgroup.normalizer (B : Set (Bar2 S.M)) := by
      rw [Subgroup.le_normalizer_iff]
      intro a ha b hb
      have hcommab : a * b = b * a := hcomm a ha b hb
      have hval : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [hcommab]
          _ = b := by group
      rwa [hval]
    have hB_NB : B ≤ Subgroup.normalizer (B : Set (Bar2 S.M)) := Subgroup.le_normalizer
    have hKN : Kbar ≤ Subgroup.normalizer (B : Set (Bar2 S.M)) := by
      rw [hK_eq]
      exact sup_le hA_NB hB_NB
    haveI : (B.subgroupOf Kbar).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hKN
    have hAcenter : Nat.card (Subgroup.center ↥A) = 3 := by
      obtain ⟨eA⟩ := uc22p22l_barImage_equiv hL
      exact (Nat.card_congr (Subgroup.centerCongr eA).toEquiv).symm.trans hSL.2
    have hcent : A ⊓ B ≤ (Subgroup.center ↥A).map A.subtype := by
      rintro x ⟨hxA, hxB⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro a
      apply Subtype.ext
      exact hcomm a a.2 x hxB
    have hinf_card : Nat.card ↥(A ⊓ B) ≤ 3 := by
      have hle := Subgroup.card_le_of_le hcent
      rwa [Subgroup.card_map_of_injective A.subtype_injective, hAcenter] at hle
    have hp_not_dvd_inf : ¬ S.p ∣ Nat.card ↥(A ⊓ B) := by
      intro hdvd
      have hle : S.p ≤ Nat.card ↥(A ⊓ B) := Nat.le_of_dvd Nat.card_pos hdvd
      omega
    have hKmul : (Kbar : Set (Bar2 S.M)) = (A : Set (Bar2 S.M)) * (B : Set (Bar2 S.M)) := by
      rw [hK_eq, Subgroup.coe_mul_of_left_le_normalizer_right A B hA_NB]
    have hNC : ∀ k : ↥Kbar, ∃ c ∈ A.subgroupOf Kbar, c * k⁻¹ ∈ B.subgroupOf Kbar := by
      intro k
      have hk : (k : Bar2 S.M) ∈ (A : Set (Bar2 S.M)) * (B : Set (Bar2 S.M)) := by
        rw [← hKmul]
        exact k.2
      obtain ⟨a, ha, b, hb, hkab⟩ := hk
      refine ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
      have hval : ((⟨a, hAK ha⟩ : ↥Kbar) * k⁻¹ : ↥Kbar) =
          ⟨b⁻¹, hBK (B.inv_mem hb)⟩ := by
        apply Subtype.ext
        have hkcoe : (k : Bar2 S.M) = a * b := hkab.symm
        have hcommab : a * b = b * a := hcomm a ha b hb
        have hcommab' : a * b⁻¹ = b⁻¹ * a := (show Commute a b from hcommab).inv_right.eq
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
        rw [hkcoe]
        calc a * (a * b)⁻¹ = a * (b⁻¹ * a⁻¹) := by group
          _ = (a * b⁻¹) * a⁻¹ := by group
          _ = (b⁻¹ * a) * a⁻¹ := by rw [hcommab']
          _ = b⁻¹ := by group
      rw [hval]
      exact Subgroup.mem_subgroupOf.mpr (B.inv_mem hb)
    have hcop : ∀ c ∈ A.subgroupOf Kbar, c ∈ B.subgroupOf Kbar → c ^ S.p = 1 → c = 1 := by
      intro c hcA hcB hcp
      have hxA : (c : Bar2 S.M) ∈ A := Subgroup.mem_subgroupOf.mp hcA
      have hxB : (c : Bar2 S.M) ∈ B := Subgroup.mem_subgroupOf.mp hcB
      have hmem : (c : Bar2 S.M) ∈ A ⊓ B := ⟨hxA, hxB⟩
      have hcp' : (c : Bar2 S.M) ^ S.p = 1 := by
        have h := congrArg Subtype.val hcp
        simpa using h
      have hdvd : orderOf (c : Bar2 S.M) ∣ S.p := orderOf_dvd_of_pow_eq_one hcp'
      have hc1 : (c : Bar2 S.M) = 1 := by
        by_contra hne
        have hord_ne : orderOf (c : Bar2 S.M) ≠ 1 := fun h =>
          hne (orderOf_eq_one_iff.mp h)
        have hord : orderOf (c : Bar2 S.M) = S.p := by
          rcases (Nat.dvd_prime S.hp.1.1).mp hdvd with h | h
          · exact absurd h hord_ne
          · exact h
        have hpcard : S.p ∣ Nat.card ↥(A ⊓ B) := by
          have h := Subgroup.orderOf_dvd_natCard (A ⊓ B) hmem
          rwa [hord] at h
        exact hp_not_dvd_inf hpcard
      exact Subtype.ext hc1
    have hmain := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p218s_pRank_top_le_add
      (K := ↥Kbar) (p := S.p) S.hp.1.1 (B.subgroupOf Kbar) (A.subgroupOf Kbar) hNC hcop
    have hleft : CFSG.Open.pRank S.p (⊤ : Subgroup ↥Kbar) =
        CFSG.Open.pRank S.p (L ⊔ L') := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := S.p) Kbar, hKdef]
      simpa [barImage, CFSG.AGLEmbedding.barM] using
        CFSG.AGLEmbedding.pRank_barM_eq S.hp.1.1 hp2 S.M (L ⊔ L') (sup_le hLM hL'LM)
    have hCrank : CFSG.Open.pRank S.p (A.subgroupOf Kbar) =
        CFSG.Open.pRank S.p (⊤ : Subgroup (Bar2 L)) := by
      rw [CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_subgroupOf_eq (p := S.p)
        S.hp.1.1.one_lt hAK]
      rw [show A = CFSG.AGLEmbedding.barM S.M L by
          rw [hAdef, barImage, CFSG.AGLEmbedding.barM],
        CFSG.AGLEmbedding.pRank_barM_eq S.hp.1.1 hp2 S.M L hLM,
        ← CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd (Y := L) (p := S.p)
          S.hp.1.1 hp2]
    have hNrank : CFSG.Open.pRank S.p (B.subgroupOf Kbar) =
        CFSG.Open.pRank S.p (⊤ : Subgroup (Bar2 L')) := by
      rw [CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_subgroupOf_eq (p := S.p)
        S.hp.1.1.one_lt hBK]
      rw [show B = CFSG.AGLEmbedding.barM S.M L' by
          rw [hBdef, barImage, CFSG.AGLEmbedding.barM],
        CFSG.AGLEmbedding.pRank_barM_eq S.hp.1.1 hp2 S.M L' hL'LM,
        ← CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd (Y := L') (p := S.p)
          S.hp.1.1 hp2]
    rw [hleft, hCrank, hNrank] at hmain
    have hLbar : CFSG.Open.pRank S.p (⊤ : Subgroup (Bar2 L)) ≤ 1 :=
      pRank_le_one_of_isSL3Four hSL S.hp.1.1 hp5
    have hL'bar : CFSG.Open.pRank S.p (⊤ : Subgroup (Bar2 L')) ≤ 1 :=
      pRank_le_one_of_isSL3Four hSL' S.hp.1.1 hp5
    rw [hXeq]
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
