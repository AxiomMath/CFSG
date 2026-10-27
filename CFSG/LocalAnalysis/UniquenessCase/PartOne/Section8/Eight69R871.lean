module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R873
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Ident
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Replace
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Pair108
import CFSG.LocalAnalysis.UniquenessCase.UC22S213CovFacts
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.GroupTheory.SylowNormalElements
import CFSG.GroupTheory.MulAutTrivialOnSubgroup
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OmegaOneNormalCyclic
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.GroupTheory.PRankCommutingSup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (barImage)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (Thin8 IsProdOfCalC Hyp81 R82)
open scoped Pointwise

theorem r871_sylow_of_sup {G : Type} [Group G] [Finite G] {L X P : Subgroup G}
    (hXL : X ≤ L) (hsup : X ⊔ pCoreOf 2 L = L) (hP : IsSylowOf 3 P X) : IsSylowOf 3 P L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPX, hPg, hrel⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPX.trans hXL, hPg, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P X L hPX hXL]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h | h
  · exact hrel h
  · have hO_le_L : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
    have hO : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
      change (pCoreOf 2 L).comap L.subtype = CFSG.pCore 2 ↥L
      rw [CFSG.Open.pCoreOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    have hsup_l : CFSG.pCore 2 ↥L ⊔ X.subgroupOf L = ⊤ := by
      rw [sup_comm, ← hO, ← Subgroup.subgroupOf_sup hXL hO_le_L, hsup, Subgroup.subgroupOf_self]
    have h2 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (CFSG.pCore 2 ↥L)
      (X.subgroupOf L)
    rw [hsup_l, Subgroup.relIndex_top_right] at h2
    have h3 : 3 ∣ (X.subgroupOf L).relIndex (CFSG.pCore 2 ↥L) := by
      rw [← h2]
      exact h
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    have h4 := Subgroup.relIndex_dvd_card (X.subgroupOf L) (CFSG.pCore 2 ↥L)
    rw [hk] at h4
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans h4)) (by norm_num)

theorem r871_isSL3PiType_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : IsSL3PiType K) : IsSL3PiType K' := by
  have hcen : (Subgroup.center K).map (e : K →* K') = Subgroup.center K' :=
    Subgroup.map_center_eq e
  have hcard : Nat.card (Subgroup.center K') = Nat.card (Subgroup.center K) := by
    rw [← hcen]
    exact Subgroup.card_map_of_injective e.injective
  let q : K ⧸ Subgroup.center K ≃* K' ⧸ Subgroup.center K' :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center K') e hcen
  rcases h with ⟨p, f, hp, hl⟩ | ⟨p, f, hp, hl⟩ | ⟨p, f, hp, hq, hc, hl⟩ | ⟨p, f, hp, hq, hc, hl⟩
  · exact Or.inl ⟨p, f, hp, CFSG.Blueprint.LieModel.of_mulEquiv e hl⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, CFSG.Blueprint.LieModel.of_mulEquiv e hl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq,
      hcard.trans hc, CFSG.Blueprint.LieModel.of_mulEquiv q hl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, f, hp, CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq,
      hcard.trans hc, CFSG.Blueprint.LieModel.of_mulEquiv q hl⟩))

private theorem r871r3p_factor_setup {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) :
    (∀ A ∈ List.ofFn S, ∀ B ∈ List.ofFn S, A ≤ Subgroup.normalizer (B : Set G)) ∧
      L = ⨆ i, S i ∧
      (∀ i, S i ≤ L ∧ L ≤ Subgroup.normalizer (S i : Set G) ∧ S i ∈ calC L) := by
  have hpair : ∀ A ∈ List.ofFn S, ∀ B ∈ List.ofFn S, A ≤ Subgroup.normalizer (B : Set G) := by
    intro A hA B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hB
    by_cases hij : S j = S i
    · rw [hij]; exact Subgroup.le_normalizer
    · exact UC22.uc22p22u_calC_normalizes (hS j) (hS i) hij
  have hLeq : L = ⨆ A ∈ List.ofFn S, A := by
    apply SetLike.coe_injective
    rw [hLset, ← UC22.uc22p22u_prod_list_eq_iSup (List.ofFn S) hpair, List.map_ofFn]
    rfl
  have hLeq' : L = ⨆ i, S i := by
    rw [hLeq]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun A hA => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      exact le_iSup (fun i => S i) i
    · exact iSup_le fun i => le_iSup₂ (f := fun A (_ : A ∈ List.ofFn S) => A) (S i)
        (List.mem_ofFn.2 ⟨i, rfl⟩)
  refine ⟨hpair, hLeq', fun i => ?_⟩
  have hmem : S i ∈ List.ofFn S := List.mem_ofFn.2 ⟨i, rfl⟩
  have hSL : S i ≤ L := by
    rw [hLeq']
    exact le_iSup (fun i => S i) i
  have hLN : L ≤ Subgroup.normalizer (S i : Set G) := by
    rw [hLeq']
    exact iSup_le fun j => hpair (S j) (List.mem_ofFn.2 ⟨j, rfl⟩) (S i) hmem
  exact ⟨hSL, hLN, UC22.P22fin3.mem_calC_of_le_normalizer (hS i) hSL hLN⟩

private theorem r871r3p_one_le_pRank_of_dvd_card {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H : Subgroup G} (h : p ∣ Nat.card H) : 1 ≤ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p h
  have hcard : Nat.card (Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe x, hx]
  have hle : Subgroup.zpowers (x : G) ≤ H := Subgroup.zpowers_le.mpr x.2
  have hEel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers (x : G)) :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime hcard
  have := CFSG.SectionRank.le_pRank hp.one_lt hle hEel (k := 1) (by rw [hcard]; norm_num)
  simpa using this

private theorem r871r3p_hZ {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    (hT : T ∈ calC L) (hTle : T ≤ L) (hT1 : CFSG.Open.pRank 3 T ≤ 1) :
    ¬ 3 ∣ Nat.card ↥(barImage L T ⊓
      Subgroup.centralizer (barImage L T : Set (Bar2 L))) := by
  by_cases h3T : 3 ∣ Nat.card T
  · have hpos : 1 ≤ CFSG.Open.pRank 3 T :=
      r871r3p_one_le_pRank_of_dvd_card Nat.prime_three h3T
    have h1 : CFSG.Open.pRank 3 T = 1 := by omega
    have hnc := UC22.R8107Odd.not_three_dvd_card_center hT h1
    rw [← CFSG.center_map_subtype_eq_inf_centralizer,
      Subgroup.card_map_of_injective (barImage L T).subtype_injective]
    obtain ⟨e, -⟩ := UC22.uc22p22l_barImage_equiv hT
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
    exact hnc
  · intro hd
    have hJdvd : Nat.card ↥(barImage L T ⊓
        Subgroup.centralizer (barImage L T : Set (Bar2 L))) ∣ Nat.card ↥(barImage L T) :=
      Subgroup.card_dvd_of_le inf_le_left
    have hJT : Nat.card ↥(barImage L T) ∣ Nat.card T := by
      unfold barImage
      have h := (T.subgroupOf L).card_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      rwa [CFSG.natCard_subgroupOf_eq T L hTle] at h
    exact h3T (hd.trans (hJdvd.trans hJT))

private theorem r871r3p_first_alt {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (hmin : MinCex869 D L X H) (hL : L ∉ calC D.M) {k : ℕ} {S : Fin k → Subgroup G}
    (hS : ∀ i, S i ∈ calC D.M) (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod)
    (i : Fin k) (hnt : ¬ Thin8 (S i)) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ K ≤ L ∧ L ≤ Subgroup.normalizer (K : Set G) ∧
      ¬ Thin8 K ∧ ¬ L ≤ K ⊔ pCoreOf 2 L := by
  obtain ⟨-, -, hfact⟩ := r871r3p_factor_setup hS hLset
  refine ⟨S i, hS i, (hfact i).1, (hfact i).2.1, hnt, ?_⟩
  intro hle
  have hsup : S i ⊔ pCoreOf 2 L = L :=
    le_antisymm (sup_le (hfact i).1 (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hle
  obtain ⟨e⟩ := nonempty_bar2_equiv_of_sup_pCore L (S i) hsup
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e.symm (hS i).2.2
  exact hL (r873_calC_of_quasisimple hmin.hyp hq)

private theorem r871r3p_hyp81 {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (hmin : MinCex869 D L X H) (h3 : CFSG.Open.pRank 3 X = 3) {k : ℕ} {S : Fin k → Subgroup G}
    (hS : ∀ i, S i ∈ calC D.M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod)
    (hthin : ∀ i, Thin8 (S i)) :
    ∃ T : Subgroup G, Hyp81 D.M T := by
  classical
  obtain ⟨-, hLeq', hfact⟩ := r871r3p_factor_setup hS hLset
  have hLrank : CFSG.Open.pRank 3 L = 3 := by
    rw [← r873_pRank_X hmin.hyp.2.2.1 Nat.prime_three (by norm_num)]
    exact h3
  let s : Finset (Subgroup G) := Finset.univ.image S
  let J : Subgroup G → Subgroup (Bar2 L) := fun A => barImage L A
  have hs_le : ∀ A ∈ s, A ≤ L := by
    intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
    exact (hfact i).1
  have hs_calCL : ∀ A ∈ s, A ∈ calC L := by
    intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
    exact (hfact i).2.2
  have hs_calC : ∀ A ∈ s, A ∈ calC D.M := by
    intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
    exact hS i
  have hs_rank : ∀ A ∈ s, CFSG.Open.pRank 3 A ≤ 1 := by
    intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
    exact hthin i 3 Nat.prime_three (by norm_num)
  have hs_hZ : ∀ A ∈ s, ¬ 3 ∣ Nat.card ↥(J A ⊓
      Subgroup.centralizer (J A : Set (Bar2 L))) := by
    intro A hA
    exact r871r3p_hZ (hs_calCL A hA) (hs_le A hA) (hs_rank A hA)
  have hs_hcomm : ∀ A ∈ s, ∀ B ∈ s, A ≠ B →
      J A ≤ Subgroup.centralizer (J B : Set (Bar2 L)) := by
    intro A hA B hB hAB a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (UC22.uc22p22l_barImage_commute (hs_calCL A hA) (hs_calCL B hB) hAB a ha b hb).symm
  have hJ : (⨆ i, J (S i)) = ⊤ := by
    have h1 : (⨆ i, J (S i)) = J (⨆ i, S i) := by
      dsimp [J]
      unfold barImage
      rw [CFSG.LieType.Steinberg.iSup_subgroupOf (F := L) (T := fun i => S i)
        (fun i => (hfact i).1), Subgroup.map_iSup]
    rw [h1, ← hLeq']
    change barImage L L = ⊤
    unfold barImage
    rw [Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hjoin_s : (⨆ A ∈ s, J A) = ⊤ := by
    have h2 : (⨆ A ∈ s, J A) = ⨆ i, J (S i) := by
      dsimp [s]
      rw [Finset.iSup_finset_image]
      simp
    rw [h2, hJ]
  have hrank := CFSG.GroupTheory.pRank_iSup_eq_sum_of_commute_of_not_dvd
    (p := 3) (s := s) (J := J) Nat.prime_three hs_hcomm hs_hZ
  have hJA : ∀ A ∈ s, CFSG.Open.pRank 3 (J A) = CFSG.Open.pRank 3 A := by
    intro A hA
    obtain ⟨e, -⟩ := UC22.uc22p22l_barImage_equiv (hs_calCL A hA)
    dsimp [J]
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage L A),
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) Nat.prime_three.one_lt e]
    exact r873_pRank_bar2 A Nat.prime_three (by norm_num)
  have hsumJ : (∑ A ∈ s, CFSG.Open.pRank 3 (J A)) = 3 := by
    rw [← hrank, hjoin_s, r873_pRank_bar2 L Nat.prime_three (by norm_num), hLrank]
  have hsum : (∑ A ∈ s, CFSG.Open.pRank 3 A) = 3 :=
    ((Finset.sum_congr rfl (fun A hA => hJA A hA)).symm).trans hsumJ
  let s1 : Finset (Subgroup G) := s.filter (fun A => CFSG.Open.pRank 3 A = 1)
  have hs1card : s1.card = 3 := by
    have h01 : ∀ A ∈ s,
        CFSG.Open.pRank 3 A = if CFSG.Open.pRank 3 A = 1 then 1 else 0 := by
      intro A hA
      have := hs_rank A hA
      split <;> omega
    have h : (∑ A ∈ s, CFSG.Open.pRank 3 A) = s1.card := by
      rw [Finset.sum_congr rfl (fun A hA => h01 A hA), Finset.sum_boole]
      rfl
    omega
  obtain ⟨a, b, c, hab, hac, hbc, hs1eq⟩ := Finset.card_eq_three.mp hs1card
  have ha1 : a ∈ s1 := by rw [hs1eq]; simp
  have hb1 : b ∈ s1 := by rw [hs1eq]; simp
  have hc1 : c ∈ s1 := by rw [hs1eq]; simp
  exact ⟨a ⊔ b ⊔ c, UC22.R8107Odd.hyp81_of_three_rankOne
    (hs_calC a (Finset.mem_filter.mp ha1).1) (hs_calC b (Finset.mem_filter.mp hb1).1)
    (hs_calC c (Finset.mem_filter.mp hc1).1) hab hac hbc
    (Finset.mem_filter.mp ha1).2 (Finset.mem_filter.mp hb1).2 (Finset.mem_filter.mp hc1).2⟩

theorem r871_rank_three_prod {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (hmin : MinCex869 D L X H) (h3 : CFSG.Open.pRank 3 X = 3) (hL : L ∉ calC D.M)
    (hLM : L ≤ D.M) (hML : D.M ≤ Subgroup.normalizer (L : Set G))
    (hprod : IsProdOfCalC D.M L) :
    (∃ K : Subgroup G, K ∈ calC D.M ∧ K ≤ L ∧ L ≤ Subgroup.normalizer (K : Set G) ∧
        ¬ Thin8 K ∧ ¬ L ≤ K ⊔ pCoreOf 2 L) ∨
      ∃ T : Subgroup G, Hyp81 D.M T := by
  classical
  have _hLM := hLM
  have _hML := hML
  obtain ⟨k, S, hS, hLset⟩ := hprod
  by_cases hnt : ∃ i, ¬ Thin8 (S i)
  · obtain ⟨i, hi⟩ := hnt
    exact Or.inl (r871r3p_first_alt hmin hL hS hLset i hi)
  · push Not at hnt
    exact Or.inr (r871r3p_hyp81 hmin h3 hS hLset hnt)

private theorem r871gap_e9_contain {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 3 P) (hP2 : 2 ≤ CFSG.Open.pRank 3 P)
    {x : G} (hxP : x ∈ P) (hxord : orderOf x = 3) :
    ∃ E : Subgroup G, x ∈ E ∧ E ≤ P ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hxord]
  obtain ⟨E, hXE, hEP, hEel, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime (r := 3)
      hP hP2 (Subgroup.zpowers_le.mpr hxP) hXcard
  exact ⟨E, Subgroup.zpowers_le.mp hXE, hEP, hEel, by rw [hEcard]; norm_num⟩

private theorem r871gap_normalizer_le_M_cyclic {G : Type} [Group G] [Finite G] {D : Data G}
    {P Q' : Subgroup G} (hP : IsPGroup 3 P) (hP2 : 2 ≤ CFSG.Open.pRank 3 P)
    (hE9 : ∀ E : Subgroup G, E ≤ P → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      CFSG.Open.rankThreeGamma 1 3 E ≤ D.M)
    (hcyc : IsCyclic Q') (hQ'P : Q' ≤ P) (hQ'rank : 1 ≤ CFSG.Open.pRank 3 Q') :
    Subgroup.normalizer (Q' : Set G) ≤ D.M := by
  obtain ⟨x, hxQ', hxord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three hQ'rank
  have hXQ' : Subgroup.zpowers x ≤ Q' := Subgroup.zpowers_le.mpr hxQ'
  have hN : Subgroup.normalizer (Q' : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    CFSG.GorensteinWalter.normalizer_le_normalizer_of_le_cyclic hcyc hXQ'
  obtain ⟨E, hxE, hEP, hEel, hEcard⟩ := r871gap_e9_contain hP hP2 (hQ'P hxQ') hxord
  have hXE : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.mpr hxE
  have hXrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hXcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
    have hea : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
      CFSG.Open.isElemAbelian_zpowers (by rw [← hxord]; exact pow_orderOf_eq_one x)
    exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl hea (by rw [hXcard]; norm_num)
  have hglb : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤
      CFSG.Open.rankThreeGamma 1 3 E :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hXE hXrank
  exact hN.trans (hglb.trans (hE9 E hEP hEel hEcard))

private theorem r871gap_normalizer_le_M_noncyclic {G : Type} [Group G] [Finite G] {D : Data G}
    {P Q' : Subgroup G} (hP : IsPGroup 3 P) (hPM : P ≤ D.M)
    (hE9 : ∀ E : Subgroup G, E ≤ P → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      CFSG.Open.rankThreeGamma 1 3 E ≤ D.M)
    (h63 : ∀ E : Subgroup G, E ≤ D.M → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      CFSG.Open.rankThreeGamma 1 3 E ≤ D.M →
      CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax D.M E)
    (hcyc : ¬ IsCyclic Q') (hQ'P : Q' ≤ P) :
    Subgroup.normalizer (Q' : Set G) ≤ D.M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ'p : IsPGroup 3 Q' := hP.to_le hQ'P
  have : Fact (IsPGroup 3 Q') := ⟨hQ'p⟩
  obtain ⟨E₀, -, hE₀card, hE₀el⟩ :=
    CFSG.lemma_4_5_a (R := Q') (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hcyc
  let E : Subgroup G := E₀.map Q'.subtype
  have hEQ' : E ≤ Q' := Subgroup.map_subtype_le E₀
  have hEel : CFSG.Open.IsElemAbelian 3 E :=
    CFSG.SectionRank.isElemAbelian_map
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hE₀el) Q'.subtype
  have hEcard : Nat.card E = 9 := by
    change Nat.card (E₀.map Q'.subtype) = 9
    rw [Subgroup.card_map_of_injective Q'.subtype_injective, hE₀card]
    norm_num
  have hE9M : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M := hE9 E (hEQ'.trans hQ'P) hEel hEcard
  have hEM : E ≤ D.M := (hEQ'.trans hQ'P).trans hPM
  have hU : CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E = {D.M} :=
    h63 E hEM hEel hEcard hE9M
  have hMmax : CFSG.Open.rankThreeIsMaxTwoLocal D.M := by
    have hmem : D.M ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := by
      rw [hU]
      exact Set.mem_singleton D.M
    exact hmem.1
  have hEunique : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
    refine CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall hMmax hEM ?_
    intro H hH hEH
    have hmem : H ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := ⟨hH, hEH⟩
    rw [hU] at hmem
    simpa using hmem
  have hQ'min : Q' ≤ D.M := hQ'P.trans hPM
  have hQ'unique : Q' ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hEunique hEQ' hQ'min
  exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hMmax hQ'unique

theorem r871_gamma_sylow {G : Type} [Group G] [Finite G] {D : Data G} (h63 : UC6.R6_3 D)
    {P : Subgroup G} (hP : IsPGroup 3 P) (hPM : P ≤ D.M) (hP2 : 2 ≤ CFSG.Open.pRank 3 P)
    (hE9 : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ D.M) :
    rankThreeGamma 1 3 P ≤ D.M := by
  have h63' : ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ D.M →
      CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax D.M E :=
    fun E hEM hEel hEcard hE9M =>
      h63 3 Nat.prime_three (by norm_num) E hEM hEel (by rw [hEcard]; norm_num) hE9M
  unfold CFSG.Open.rankThreeGamma
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q' hQ'P hQ'rank
  by_cases hcyc : IsCyclic Q'
  · exact r871gap_normalizer_le_M_cyclic hP hP2 hE9 hcyc hQ'P hQ'rank
  · exact r871gap_normalizer_le_M_noncyclic hP hPM hE9 h63' hcyc hQ'P

theorem r871_nonnormal_gamma
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hGA : GriessAllModelsStatement)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hM22 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
      (TauCeti.CFSGIndex.sporadic .M22).Group))
    (hSg : UC6S846.SigmaStd D) (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D) (h870 : R870 D)
    (h76 : UC22.F07.R76 D) (_h638 : UC6.R6_38 D) (_hOut : OutPComplement)
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) (hLc : L ∈ calC D.M)
    (h2 : CFSG.Open.pRank 3 X = 2) (hnn : ¬ D.M ≤ Subgroup.normalizer (L : Set G))
    {E : Subgroup G} (_hEL : E ≤ L) (_hEel : IsElemAbelian 3 E) (_hEc : Nat.card E = 9) :
    rankThreeGamma 1 3 E ≤ D.M := by
  exfalso
  have hsup : X ⊔ pCoreOf 2 L = L := hmin.hyp.2.2.1
  have hq : ∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L →
      q ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    intro q hq hq2 hqk
    by_contra hZq
    exact hnn (r873_normal hSg h870 hmin hq hq2
      (by rw [r873_pRank_X hsup hq hq2]; exact hqk) hZq)
  have hr3 : CFSG.Open.pRank 3 L = 2 := by
    rw [← r873_pRank_X hsup Nat.prime_three (by norm_num)]
    exact h2
  have hZ3 : 3 ∣ Nat.card (Subgroup.center (Bar2 L)) :=
    hq 3 Nat.prime_three (by norm_num) (by omega)
  have hFive : UC22.FiveCovers (Bar2 L) :=
    UC22.uc22s213_fiveCovers_of_three_dvd hGA
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput hSpor
      hM22 hLc hq hZ3 (by omega)
  obtain ⟨hZ, hZS, hAut, hm3⟩ := UC22.uc22s213_typeFacts_of_five hFive
  have hSP : IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_three_of_not_le_normalizer hSg h63 h69
      (UC22.F07.R76Sig_of_R76 D h76) hLc hnn (by omega) hZ hZS hAut hm3
  exact h870 L X H hmin 3 Nat.prime_three (by norm_num) (by omega) hSP

private theorem r871shp_join {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) :
    L = ⨆ i, S i := by
  have hpair : ∀ A ∈ List.ofFn S, ∀ B ∈ List.ofFn S, A ≤ normalizer (B : Set G) := by
    intro A hA B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hB
    by_cases hij : S j = S i
    · rw [hij]
      exact Subgroup.le_normalizer
    · exact UC22.uc22p22u_calC_normalizes (hS j) (hS i) hij
  have h1 := UC22.uc22p22u_prod_list_eq_iSup (List.ofFn S) hpair
  have h1' : (List.ofFn fun i => (S i : Set G)).prod =
      ((⨆ A ∈ List.ofFn S, A : Subgroup G) : Set G) := by
    simpa [Function.comp_def] using h1
  have h2 : (L : Set G) = ((⨆ A ∈ List.ofFn S, A : Subgroup G) : Set G) := by
    rw [hLset, h1']
  apply SetLike.coe_injective
  rw [h2]
  congr 1
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
    exact le_iSup S i
  · refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun A (_ : A ∈ List.ofFn S) => A) (S i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

private theorem r871shp_barImage_top {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) :
    (⨆ i, UC22.barImage L (S i)) = ⊤ := by
  have hjoin : L = ⨆ i, S i := r871shp_join hS hLset
  have hSL : ∀ i, S i ≤ L := fun i => by rw [hjoin]; exact le_iSup S i
  calc (⨆ i, UC22.barImage L (S i))
      = ⨆ i, ((S i).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := rfl
    _ = ((⨆ i, (S i).subgroupOf L)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
          rw [Subgroup.map_iSup]
    _ = ((⨆ i, S i).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
          rw [CFSG.subgroupOf_iSup S hSL]
    _ = UC22.barImage L (⨆ i, S i) := rfl
    _ = UC22.barImage L L := by rw [hjoin]
    _ = ⊤ := by
          rw [UC22.barImage, Subgroup.subgroupOf_self,
            Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem r871shp_calC_L {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) (hLM : L ≤ M)
    (i : Fin k) : S i ∈ UC22.calC L := by
  have hjoin : L = ⨆ j, S j := r871shp_join hS hLset
  have hSL : S i ≤ L := by rw [hjoin]; exact le_iSup S i
  exact ⟨CFSG.Quasithin.A3.subnormal_of_le_of_le (hS i).1 hSL hLM, (hS i).2.1, (hS i).2.2⟩

private theorem r871shp_calC_L_eq_range {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) (hLM : L ≤ M) :
    ∀ C ∈ UC22.calC L, ∃ i, C = S i := by
  intro C hC
  by_contra hcon
  push Not at hcon
  have hCbar : CFSG.IsComponent (UC22.barImage L C) := UC22.uc22p22l_barImage_isComponent hC
  have hSbar : ∀ i, CFSG.IsComponent (UC22.barImage L (S i)) :=
    fun i => UC22.uc22p22l_barImage_isComponent (r871shp_calC_L hS hLset hLM i)
  have hne : ∀ i, UC22.barImage L C ≠ UC22.barImage L (S i) := by
    intro i h
    exact hcon i (UC22.uc22p22u_calC_ext hC (r871shp_calC_L hS hLset hLM i) h)
  have hcomm : ∀ i, UC22.barImage L C ≤
      Subgroup.centralizer (UC22.barImage L (S i) : Set (Bar2 L)) := by
    intro i
    rcases CFSG.LocalCores.distinct_components_commute hCbar (hSbar i) with h | h
    · exact absurd h (hne i)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hle := CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    (fun i => UC22.barImage L (S i)) hcomm
  rw [r871shp_barImage_top hS hLset] at hle
  rw [Subgroup.coe_top] at hle
  have hle_self : UC22.barImage L C ≤ Subgroup.centralizer (UC22.barImage L C : Set (Bar2 L)) :=
    hle.trans (Subgroup.centralizer_le (Set.subset_univ _))
  have hbot_comm : ⁅UC22.barImage L C, UC22.barImage L C⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle_self
  have hne_bot : UC22.barImage L C ≠ ⊥ :=
    CFSG.Quasithin.ne_bot_of_mem_cComp
      (CFSG.Quasithin.mem_cComp_top_of_isComponent hCbar)
  exact hne_bot (((Subgroup.isPerfect_iff).mp hCbar.1.1).symm.trans hbot_comm)

private theorem r871shp_conj_mem_range {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) {m : G} (hm : m ∈ M) (i : Fin k) :
    ∃ j, uniqueFourConj m (S i) = S j := by
  have hSLi : S i ≤ L := by
    rw [r871shp_join hS hLset]; exact le_iSup S i
  have hconj : uniqueFourConj m (S i) ∈ UC22.calC M :=
    UC22.uc22p22u_calC_conj (Subgroup.le_normalizer) (hS i) hm
  have hminv : m⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).inv_mem (hML hm)
  have hLmap : L.map (MulAut.conj m⁻¹).toMonoidHom = L :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hminv
  have hle : uniqueFourConj m (S i) ≤ L := by
    rw [uniqueFourConj, ← hLmap]
    exact Subgroup.map_mono hSLi
  exact r871shp_calC_L_eq_range hS hLset hLM _
    ⟨CFSG.Quasithin.A3.subnormal_of_le_of_le hconj.1 hle hLM, hconj.2.1, hconj.2.2⟩

private theorem r871shp_inf_centralizer_eq_center_map {X : Type} [Group X] (H : Subgroup X) :
    H ⊓ Subgroup.centralizer (H : Set X) = (Subgroup.center ↥H).map H.subtype := by
  ext x
  constructor
  · rintro ⟨hxH, hc⟩
    exact ⟨⟨x, hxH⟩,
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hc (g : X) g.2),
      rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_iff.2 fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨g, hg⟩)⟩

private theorem r871shp_card_inf_centralizer {X : Type} [Group X] (H : Subgroup X) :
    Nat.card ↥(H ⊓ Subgroup.centralizer (H : Set X)) = Nat.card (Subgroup.center ↥H) := by
  rw [r871shp_inf_centralizer_eq_center_map, Subgroup.card_map_of_injective H.subtype_injective]

private theorem r871shp_pRank_barImage {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    (hK : K ∈ UC22.calC L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (UC22.barImage L K) = CFSG.Open.pRank q K := by
  obtain ⟨e, -⟩ := UC22.uc22p22l_barImage_equiv hK
  have h1 : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K)) =
      CFSG.Open.pRank q (UC22.barImage L K) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt e,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (UC22.barImage L K)]
  exact h1.symm.trans (r873_pRank_bar2 K hq hq2)

private theorem r871shp_not_dvd_center {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Subgroup G} (hK : K ∈ UC22.calC L) (hthin : Thin8 K) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card ↥(UC22.barImage L K ⊓
      Subgroup.centralizer (UC22.barImage L K : Set (Bar2 L))) := by
  rw [r871shp_card_inf_centralizer]
  have hqFact : Fact q.Prime := ⟨hq⟩
  have hJq : CFSG.Open.pRank q (UC22.barImage L K) ≤ 1 := by
    rw [r871shp_pRank_barImage hK hq hq2]
    exact hthin q hq hq2
  by_cases hdvd : q ∣ Nat.card ↥(UC22.barImage L K)
  · have hperfect : Group.IsPerfect ↥(UC22.barImage L K) :=
      (UC22.uc22p22l_barImage_isComponent hK).1.1
    have h1 : 1 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥(UC22.barImage L K)) := by
      obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' q hdvd
      have hxq : x ^ q = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      have hcard : Nat.card ↥(Subgroup.zpowers x) = q ^ 1 := by
        rw [Nat.card_zpowers, hxord, pow_one]
      exact CFSG.SectionRank.le_pRank hq.one_lt (H := (⊤ : Subgroup ↥(UC22.barImage L K)))
        (E := Subgroup.zpowers x) le_top (CFSG.Open.isElemAbelian_zpowers hxq) hcard
    have hrank1 : CFSG.Open.pRank q (⊤ : Subgroup ↥(UC22.barImage L K)) = 1 := by
      refine le_antisymm ?_ h1
      rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hJq
    exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one
      hq2 hrank1
  · exact fun h => hdvd (h.trans (Subgroup.card_subgroup_dvd_card _))

private theorem r871shp_pRank_conj {G : Type} [Group G] [Finite G] {A : Subgroup G} (m : G)
    {q : ℕ} (hq1 : 1 < q) :
    CFSG.Open.pRank q (uniqueFourConj m A) = CFSG.Open.pRank q A := by
  have e : A ≃* uniqueFourConj m A :=
    Subgroup.equivMapOfInjective A (MulAut.conj m⁻¹).toMonoidHom
      (MulAut.conj m⁻¹).injective
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (uniqueFourConj m A),
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq1 e,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup A]

private theorem r871shp_barImage_sup_pair {G : Type} [Group G] [Finite G] {L A B : Subgroup G}
    (hAL : A ≤ L) (hBL : B ≤ L) :
    UC22.barImage L (A ⊔ B) = UC22.barImage L A ⊔ UC22.barImage L B := by
  rw [UC22.barImage, UC22.barImage, UC22.barImage, Subgroup.subgroupOf_sup hAL hBL,
    Subgroup.map_sup]

private theorem r871shp_pRank_top_sum {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) (hLM : L ≤ M)
    (hthin : ∀ i, Thin8 (S i)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    [DecidableEq (Subgroup G)] :
    CFSG.Open.pRank q (⊤ : Subgroup (Bar2 L)) =
      ∑ A ∈ (List.ofFn S).toFinset, CFSG.Open.pRank q A := by
  have htop : (⨆ A ∈ (List.ofFn S).toFinset, UC22.barImage L A) = ⊤ := by
    have h1 : (⨆ A ∈ (List.ofFn S).toFinset, UC22.barImage L A) =
        (⨆ A ∈ List.ofFn S, UC22.barImage L A) := by
      refine le_antisymm ?_ ?_
      · refine iSup₂_le fun A hA => ?_
        exact le_iSup₂ (f := fun A (_ : A ∈ List.ofFn S) => UC22.barImage L A) A
          (List.mem_toFinset.mp hA)
      · refine iSup₂_le fun A hA => ?_
        exact le_iSup₂ (f := fun A (_ : A ∈ (List.ofFn S).toFinset) => UC22.barImage L A) A
          (List.mem_toFinset.mpr hA)
    rw [h1]
    have h2 : (⨆ A ∈ List.ofFn S, UC22.barImage L A) = ⨆ i, UC22.barImage L (S i) := by
      refine le_antisymm ?_ ?_
      · refine iSup₂_le fun A hA => ?_
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
        exact le_iSup (fun i => UC22.barImage L (S i)) i
      · refine iSup_le fun i => ?_
        exact le_iSup₂ (f := fun A (_ : A ∈ List.ofFn S) => UC22.barImage L A) (S i)
          (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [h2, r871shp_barImage_top hS hLset]
  have hmem : ∀ A ∈ (List.ofFn S).toFinset, A ∈ UC22.calC L := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hA)
    exact hi ▸ r871shp_calC_L hS hLset hLM i
  have hcomm : ∀ A ∈ (List.ofFn S).toFinset, ∀ B ∈ (List.ofFn S).toFinset, A ≠ B →
      UC22.barImage L A ≤ Subgroup.centralizer (UC22.barImage L B : Set (Bar2 L)) := by
    intro A hA B hB hAB
    rcases CFSG.LocalCores.distinct_components_commute
      (UC22.uc22p22l_barImage_isComponent (hmem A hA))
      (UC22.uc22p22l_barImage_isComponent (hmem B hB)) with h | h
    · exfalso
      exact hAB (UC22.uc22p22u_calC_ext (hmem A hA) (hmem B hB) h)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hZ : ∀ A ∈ (List.ofFn S).toFinset, ¬ q ∣ Nat.card ↥(UC22.barImage L A ⊓
      Subgroup.centralizer (UC22.barImage L A : Set (Bar2 L))) := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hA)
    exact hi ▸ r871shp_not_dvd_center (r871shp_calC_L hS hLset hLM i) (hthin i) hq hq2
  have hsum := CFSG.GroupTheory.pRank_iSup_eq_sum_of_commute_of_not_dvd hq
    (List.ofFn S).toFinset (fun A => UC22.barImage L A) hcomm hZ
  rw [htop] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun A hA => ?_
  exact r871shp_pRank_barImage (hmem A hA) hq hq2

private theorem r871shp_card_filter_of_sum {ι : Type} (t : Finset ι) (f : ι → ℕ)
    (hf : ∀ A ∈ t, f A ≤ 1) (h2 : 2 ≤ ∑ A ∈ t, f A) :
    2 ≤ (t.filter fun A => 1 ≤ f A).card := by
  have hb : (∑ A ∈ t, if 1 ≤ f A then 1 else 0) =
      (t.filter fun A => 1 ≤ f A).card := by
    simp
  rw [← hb]
  refine h2.trans ?_
  refine Finset.sum_le_sum fun A hA => ?_
  have := hf A hA
  by_cases h : 1 ≤ f A
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

private theorem r871shp_card_filter_eq_one {ι : Type} (t : Finset ι) (f : ι → ℕ)
    (hf : ∀ A ∈ t, f A ≤ 1) (h1 : ∑ A ∈ t, f A = 1) :
    (t.filter fun A => 1 ≤ f A).card = 1 := by
  have hb : (∑ A ∈ t, if 1 ≤ f A then 1 else 0) =
      (t.filter fun A => 1 ≤ f A).card := by
    simp
  rw [← hb]
  trans ∑ A ∈ t, f A
  · refine Finset.sum_congr rfl fun A hA => ?_
    have := hf A hA
    by_cases h : 1 ≤ f A
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  · exact h1

private theorem r871shp_pRank_sum {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) (hLM : L ≤ M)
    (hthin : ∀ i, Thin8 (S i)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    [DecidableEq (Subgroup G)] :
    CFSG.Open.pRank q L = ∑ A ∈ (List.ofFn S).toFinset, CFSG.Open.pRank q A := by
  rw [← r873_pRank_bar2 L hq hq2]
  exact r871shp_pRank_top_sum hS hLset hLM hthin hq hq2

private theorem r871shp_subgroupOf_pCoreOf {G : Type} [Group G] (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  rw [pCoreOf]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

private theorem r871shp_barImage_sup_pCore {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hPL : P ≤ L) :
    UC22.barImage L (P ⊔ pCoreOf 2 L) = UC22.barImage L P := by
  rw [UC22.barImage, UC22.barImage, Subgroup.subgroupOf_sup hPL (UC22.uc22p21c_pCoreOf_le L),
    Subgroup.map_sup, r871shp_subgroupOf_pCoreOf L]
  have hbot : (CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact (QuotientGroup.ker_mk' _).ge
  rw [hbot, sup_bot_eq]

private theorem r871shp_barImage_iSup_finset {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (s : Finset (Subgroup G)) (hs : ∀ A ∈ s, A ≤ L) :
    UC22.barImage L (⨆ A ∈ s, A) = ⨆ A ∈ s, UC22.barImage L A := by
  have h1 : (⨆ A ∈ s, A) = ⨆ A : {A // A ∈ s}, A.1 := iSup_subtype'
  have h2 : (⨆ A ∈ s, UC22.barImage L A) =
      ⨆ A : {A // A ∈ s}, UC22.barImage L A.1 := iSup_subtype'
  rw [h1, h2, UC22.barImage,
    CFSG.subgroupOf_iSup (fun A : {A // A ∈ s} => A.1) (fun A => hs A.1 A.2),
    Subgroup.map_iSup]
  rfl

private theorem r871shp_not_le_sup {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) (hLM : L ≤ M)
    [DecidableEq (Subgroup G)]
    (s : Finset (Subgroup G)) (hs : ∀ A ∈ s, A ∈ (List.ofFn S).toFinset)
    (hproper : ∃ C ∈ (List.ofFn S).toFinset, C ∉ s) :
    ¬ L ≤ (⨆ A ∈ s, A) ⊔ pCoreOf 2 L := by
  have hmemL : ∀ A ∈ (List.ofFn S).toFinset, A ∈ UC22.calC L := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hA)
    exact hi ▸ r871shp_calC_L hS hLset hLM i
  intro hle
  obtain ⟨C, hCt, hCs⟩ := hproper
  have hCL : C ∈ UC22.calC L := hmemL C hCt
  have hCLle : C ≤ L := CFSG.Quasithin.A3.subnormal_le hCL.1
  have hsL : ∀ A ∈ s, A ≤ L := fun A hA =>
    CFSG.Quasithin.A3.subnormal_le (hmemL A (hs A hA)).1
  have hsLt : (⨆ A ∈ s, A) ≤ L := iSup₂_le hsL
  have hOC : C ≤ (⨆ A ∈ s, A) ⊔ pCoreOf 2 L := hCLle.trans hle
  have hLeq : L = (⨆ A ∈ s, A) ⊔ pCoreOf 2 L :=
    le_antisymm hle (sup_le hsLt (UC22.uc22p21c_pCoreOf_le L))
  have hcenter : UC22.barImage L C ≤
      Subgroup.centralizer (Set.univ : Set (Bar2 L)) := by
    have hcomm : ∀ A ∈ s, UC22.barImage L C ≤
        Subgroup.centralizer (UC22.barImage L A : Set (Bar2 L)) := by
      intro A hA
      have hAL : A ∈ UC22.calC L := hmemL A (hs A hA)
      have hne : C ≠ A := fun h => hCs (h ▸ hA)
      rcases CFSG.LocalCores.distinct_components_commute
        (UC22.uc22p22l_barImage_isComponent hCL)
        (UC22.uc22p22l_barImage_isComponent hAL) with h | h
      · exfalso
        exact hne (UC22.uc22p22u_calC_ext hCL hAL h)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hle' := CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (fun A : {A // A ∈ s} => UC22.barImage L A.1)
      (fun A => hcomm A.1 A.2)
    have hsup_eq : (⨆ A : {A // A ∈ s}, UC22.barImage L A.1) =
        ⨆ A ∈ s, UC22.barImage L A := by
      refine le_antisymm ?_ ?_
      · refine iSup_le fun A => ?_
        exact le_iSup₂ (f := fun A (_ : A ∈ s) => UC22.barImage L A) A.1 A.2
      · refine iSup₂_le fun A hA => ?_
        exact le_iSup (fun A : {A // A ∈ s} => UC22.barImage L A.1) ⟨A, hA⟩
    rw [hsup_eq] at hle'
    have htop : (⨆ A ∈ s, UC22.barImage L A) = ⊤ := by
      rw [← r871shp_barImage_iSup_finset s hsL, ← r871shp_barImage_sup_pCore hsLt, ← hLeq,
        UC22.barImage, Subgroup.subgroupOf_self,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [htop, Subgroup.coe_top] at hle'
    exact hle'
  have hbot_comm : ⁅UC22.barImage L C, UC22.barImage L C⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcenter.trans (Subgroup.centralizer_le (Set.subset_univ _)))
  have hne_bot : UC22.barImage L C ≠ ⊥ :=
    CFSG.Quasithin.ne_bot_of_mem_cComp
      (CFSG.Quasithin.mem_cComp_top_of_isComponent (UC22.uc22p22l_barImage_isComponent hCL))
  exact hne_bot (((Subgroup.isPerfect_iff).mp
    (UC22.uc22p22l_barImage_isComponent hCL).1.1).symm.trans hbot_comm)

private theorem r871shp_barImage_iSup_set {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (s : Set (Subgroup G)) (hs : ∀ A ∈ s, A ≤ L) :
    UC22.barImage L (⨆ A ∈ s, A) = ⨆ A ∈ s, UC22.barImage L A := by
  have h1 : (⨆ A ∈ s, A) = ⨆ A : s, A.1 := iSup_subtype'
  have h2 : (⨆ A ∈ s, UC22.barImage L A) = ⨆ A : s, UC22.barImage L A.1 := iSup_subtype'
  rw [h1, h2, UC22.barImage,
    CFSG.subgroupOf_iSup (fun A : s => A.1) (fun A => hs A.1 A.2),
    Subgroup.map_iSup]
  rfl

private theorem r871shp_conjClosure_cover {G : Type} [Group G] [Finite G] {M L : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ UC22.calC M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod) (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) [DecidableEq (Subgroup G)] (B : Subgroup G)
    (hB : B ∈ (List.ofFn S).toFinset)
    (hcover : L ≤ UC22.conjClosure M B ⊔ pCoreOf 2 L) :
    ∀ C ∈ (List.ofFn S).toFinset, ∃ m ∈ M, uniqueFourConj m B = C := by
  have hmemL : ∀ A ∈ (List.ofFn S).toFinset, A ∈ UC22.calC L := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hA)
    exact hi ▸ r871shp_calC_L hS hLset hLM i
  have hCL : ∀ A ∈ (List.ofFn S).toFinset, A ≤ L := fun A hA =>
    CFSG.Quasithin.A3.subnormal_le (hmemL A hA).1
  have hmemM : ∀ A ∈ (List.ofFn S).toFinset, A ∈ UC22.calC M := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hA)
    exact hi ▸ hS i
  have hconjL : ∀ K ∈ UC22.conjSetOf M B, K ∈ UC22.calC L := by
    rintro K ⟨g, hg, rfl⟩
    have hK : B.map (MulAut.conj g).toMonoidHom ∈ UC22.calC M := by
      have h := UC22.uc22p22u_calC_conj (Subgroup.le_normalizer) (hmemM B hB)
        (M.inv_mem hg)
      simpa only [uniqueFourConj, inv_inv] using h
    have hKL : B.map (MulAut.conj g).toMonoidHom ≤ L := by
      have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hML hg)
      calc B.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_mono (hCL B hB)
        _ = L := hLmap
    exact ⟨CFSG.Quasithin.A3.subnormal_of_le_of_le hK.1 hKL hLM, hK.2.1, hK.2.2⟩
  have hcoverL : L = UC22.conjClosure M B ⊔ pCoreOf 2 L :=
    le_antisymm hcover
      (sup_le (UC22.uc22p22u_conjClosure_isProd hLM hML (hmemL B hB)).1
        (UC22.uc22p21c_pCoreOf_le L))
  intro C hC
  by_contra hcon
  push Not at hcon
  have hCL' : C ∈ UC22.calC L := hmemL C hC
  have hnotmem : C ∉ UC22.conjSetOf M B := by
    rintro ⟨g, hg, hgC⟩
    exact hcon g⁻¹ (M.inv_mem hg) (by
      rw [uniqueFourConj, hgC]; simp [inv_inv])
  have hbar_top : UC22.barImage L (UC22.conjClosure M B) = ⊤ := by
    rw [← r871shp_barImage_sup_pCore
        (UC22.uc22p22u_conjClosure_isProd hLM hML (hmemL B hB)).1,
      ← hcoverL, UC22.barImage, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hcomm : ∀ K ∈ UC22.conjSetOf M B, UC22.barImage L C ≤
      Subgroup.centralizer (UC22.barImage L K : Set (Bar2 L)) := by
    intro K hK
    have hKL : K ∈ UC22.calC L := hconjL K hK
    have hne : C ≠ K := fun h => hnotmem (h ▸ hK)
    rcases CFSG.LocalCores.distinct_components_commute
      (UC22.uc22p22l_barImage_isComponent hCL')
      (UC22.uc22p22l_barImage_isComponent hKL) with h | h
    · exact absurd (UC22.uc22p22u_calC_ext hCL' hKL h) hne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hle' := CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    (fun K : UC22.conjSetOf M B => UC22.barImage L K.1) (fun K => hcomm K.1 K.2)
  have hsup_eq : (⨆ K : UC22.conjSetOf M B, UC22.barImage L K.1) =
      ⨆ K ∈ UC22.conjSetOf M B, UC22.barImage L K := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun K => ?_
      exact le_iSup₂ (f := fun K (_ : K ∈ UC22.conjSetOf M B) => UC22.barImage L K) K.1 K.2
    · refine iSup₂_le fun K hK => ?_
      exact le_iSup (fun K : UC22.conjSetOf M B => UC22.barImage L K.1) ⟨K, hK⟩
  rw [hsup_eq] at hle'
  have hbar_conj : (⨆ K ∈ UC22.conjSetOf M B, UC22.barImage L K) =
      UC22.barImage L (UC22.conjClosure M B) := by
    rw [UC22.conjClosure]
    exact (r871shp_barImage_iSup_set (UC22.conjSetOf M B)
      (fun K hK => (hconjL K hK).1.le)).symm
  rw [hbar_conj, hbar_top, Subgroup.coe_top] at hle'
  have hbot_comm : ⁅UC22.barImage L C, UC22.barImage L C⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hle'.trans (Subgroup.centralizer_le (Set.subset_univ _)))
  have hne_bot : UC22.barImage L C ≠ ⊥ :=
    CFSG.Quasithin.ne_bot_of_mem_cComp
      (CFSG.Quasithin.mem_cComp_top_of_isComponent (UC22.uc22p22l_barImage_isComponent hCL'))
  exact hne_bot (((Subgroup.isPerfect_iff).mp
    (UC22.uc22p22l_barImage_isComponent hCL').1.1).symm.trans hbot_comm)

private theorem r871shp_le_normalizer_sup {G : Type} [Group G] {A B H : Subgroup G}
    (hA : H ≤ Subgroup.normalizer (A : Set G)) (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)]

private theorem r871shp_ofFn_pair {G : Type} [Group G] (A B : Subgroup G) :
    (List.ofFn fun i : Fin 2 => ((if i = 0 then A else B : Subgroup G) : Set G)) =
      [(A : Set G), (B : Set G)] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]; simp

private theorem r871shp_isProdOfCalC_sup {G : Type} [Group G] [Finite G] {M A B : Subgroup G}
    (hA : A ∈ calC M) (hB : B ∈ calC M) (hne : A ≠ B) :
    IsProdOfCalC M (A ⊔ B) := by
  have hN : B ≤ Subgroup.normalizer (A : Set G) := UC22.uc22p22u_calC_normalizes hA hB hne
  refine ⟨2, fun i : Fin 2 => if i = 0 then A else B, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
  · rw [r871shp_ofFn_pair A B, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
    exact Subgroup.coe_mul_of_right_le_normalizer_left A B hN

private theorem r871shp_filter_two {ι : Type} [DecidableEq ι] (t : Finset ι) (f : ι → ℕ)
    (hf : ∀ A ∈ t, f A ≤ 1) (h2 : ∑ A ∈ t, f A = 2) :
    ∃ A B, A ≠ B ∧ A ∈ t ∧ B ∈ t ∧ f A = 1 ∧ f B = 1 ∧
      (t.filter fun C => 1 ≤ f C) = {A, B} := by
  classical
  have hsum : (∑ A ∈ t, f A) = (t.filter fun C => 1 ≤ f C).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun A hA => ?_
    have := hf A hA
    by_cases h : 1 ≤ f A
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  have hcard : (t.filter fun C => 1 ≤ f C).card = 2 := by rw [← hsum]; exact h2
  obtain ⟨A, B, hAB, hABeq⟩ := Finset.card_eq_two.mp hcard
  have hA' : A ∈ t.filter (fun C => 1 ≤ f C) := by rw [hABeq]; simp
  have hB' : B ∈ t.filter (fun C => 1 ≤ f C) := by rw [hABeq]; simp
  rw [Finset.mem_filter] at hA' hB'
  exact ⟨A, B, hAB, hA'.1, hB'.1, le_antisymm (hf A hA'.1) hA'.2,
    le_antisymm (hf B hB'.1) hB'.2, hABeq⟩

private theorem r871shp_pRank_sup_pair {G : Type} [Group G] [Finite G] {M A B : Subgroup G}
    (hA : A ∈ calC M) (hB : B ∈ calC M) (hne : A ≠ B)
    (hthinA : Thin8 A) (hthinB : Thin8 B)
    (hABM : A ⊔ B ≤ M) (hmul : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G)) :
    CFSG.Open.pRank 3 (A ⊔ B) = CFSG.Open.pRank 3 A + CFSG.Open.pRank 3 B := by
  classical
  have hsum := r871shp_pRank_sum (M := M) (L := A ⊔ B) (k := 2)
    (S := fun i : Fin 2 => if i = 0 then A else B)
    (by intro i
        fin_cases i
        · simpa using hA
        · simpa using hB)
    (by rw [r871shp_ofFn_pair A B, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
        exact hmul)
    hABM
    (by intro i
        fin_cases i
        · simpa using hthinA
        · simpa using hthinB)
    Nat.prime_three (by norm_num)
  rw [hsum]
  have hfin : (List.ofFn fun i : Fin 2 => (if i = 0 then A else B : Subgroup G)).toFinset =
      {A, B} := by
    rw [show (List.ofFn fun i : Fin 2 => (if i = 0 then A else B : Subgroup G)) = [A, B] by
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]; simp]
    simp
  rw [hfin, Finset.sum_pair hne]

private theorem r871shp_barImage_commutator_mem {G : Type} [Group G] [Finite G]
    {L K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ calC L) (hK₂ : K₂ ∈ calC L) (hne : K₁ ≠ K₂) :
    ∀ a ∈ K₁, ∀ b ∈ K₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L := by
  have hK₁L : K₁ ≤ L := CFSG.Quasithin.A3.subnormal_le hK₁.1
  have hK₂L : K₂ ≤ L := CFSG.Quasithin.A3.subnormal_le hK₂.1
  have hcomm := UC22.uc22p22l_barImage_commute hK₁ hK₂ hne
  intro a ha b hb
  let x : ↥L := ⟨a, hK₁L ha⟩
  let y : ↥L := ⟨b, hK₂L hb⟩
  have hx : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) ∈ UC22.barImage L K₁ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  have hy : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) y) ∈ UC22.barImage L K₂ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
  have h := hcomm _ hx _ hy
  have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (x * y * x⁻¹ * y⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h3 : (x * y * x⁻¹ * y⁻¹) ∈ CFSG.pCore 2 ↥L :=
    (QuotientGroup.eq_one_iff _).mp h2
  have hcoe : ((x * y * x⁻¹ * y⁻¹ : ↥L) : G) = a * b * a⁻¹ * b⁻¹ := by
    simp [x, y]
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L := by
    rw [← hcoe]
    exact (CFSG.mem_openPCoreOf_iff (H := L) _).mpr h3
  exact hmem

private theorem r871shp_conj_mem_pair {G : Type} [Group G] [Finite G] [DecidableEq (Subgroup G)]
    {D : Data G} {L X H : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (hmin : MinCex869 D L X H) (hL : L ∉ calC D.M)
    (hS : ∀ i, S i ∈ calC D.M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod)
    {S₁ S₂ A : Subgroup G}
    (hpairset : (List.ofFn S).toFinset.filter (fun C => 1 ≤ CFSG.Open.pRank 3 C) = {S₁, S₂})
    (hAt : A ∈ (List.ofFn S).toFinset) (hpA : CFSG.Open.pRank 3 A = 1) :
    ∀ m ∈ D.M, uniqueFourConj m A ∈ ({S₁, S₂} : Finset (Subgroup G)) := by
  classical
  have hdata := hmin.hyp.1.resolve_left hL
  have hLM : L ≤ D.M := hdata.1
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) := hdata.2.1
  intro m hm
  obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hAt)
  obtain ⟨j, hj⟩ := r871shp_conj_mem_range hS hLset hLM hML hm i
  have hpj : CFSG.Open.pRank 3 (S j) = 1 := by
    rw [← hj, r871shp_pRank_conj m (by norm_num : 1 < 3)]
    simpa [← hi] using hpA
  have hjt : S j ∈ (List.ofFn S).toFinset := by
    rw [List.mem_toFinset, List.mem_ofFn]; exact ⟨j, rfl⟩
  have hmem : S j ∈ (List.ofFn S).toFinset.filter (fun C => 1 ≤ CFSG.Open.pRank 3 C) :=
    Finset.mem_filter.mpr ⟨hjt, by omega⟩
  rw [hpairset] at hmem
  have hji : uniqueFourConj m A = S j := by rw [← hi]; exact hj
  rw [hji]
  exact hmem

private theorem r871shp_sup_pair_false {G : Type} [Group G] [Finite G] [DecidableEq (Subgroup G)]
    {D : Data G} {L X H : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (hmin : MinCex869 D L X H) (hL : L ∉ calC D.M)
    (hS : ∀ i, S i ∈ calC D.M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod)
    (_hthin : ∀ i, Thin8 (S i)) {S₁ S₂ A : Subgroup G}
    (hS₁ : S₁ ∈ calC D.M) (hS₂ : S₂ ∈ calC D.M) (hS₁ne₂ : S₁ ≠ S₂)
    (hpS₁ : CFSG.Open.pRank 3 S₁ = 1) (hpS₂ : CFSG.Open.pRank 3 S₂ = 1)
    (hthinS₁ : Thin8 S₁) (hthinS₂ : Thin8 S₂)
    (hpairset : (List.ofFn S).toFinset.filter (fun C => 1 ≤ CFSG.Open.pRank 3 C) = {S₁, S₂})
    (hAin : A ∈ (List.ofFn S).toFinset) (hAne₁ : A ≠ S₁) (hAne₂ : A ≠ S₂) :
    False := by
  classical
  have hdata := hmin.hyp.1.resolve_left hL
  have hLM : L ≤ D.M := hdata.1
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) := hdata.2.1
  have hjoin : L = ⨆ i, S i := r871shp_join hS hLset
  have hSL : ∀ i, S i ≤ L := fun i => by rw [hjoin]; exact le_iSup S i
  have hS₁t : S₁ ∈ (List.ofFn S).toFinset := by
    have : S₁ ∈ (List.ofFn S).toFinset.filter (fun C => 1 ≤ CFSG.Open.pRank 3 C) := by
      rw [hpairset]; simp
    exact (Finset.mem_filter.mp this).1
  have hS₂t : S₂ ∈ (List.ofFn S).toFinset := by
    have : S₂ ∈ (List.ofFn S).toFinset.filter (fun C => 1 ≤ CFSG.Open.pRank 3 C) := by
      rw [hpairset]; simp
    exact (Finset.mem_filter.mp this).1
  have hS₁L : S₁ ≤ L := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₁t)
    rw [← hi]; exact hSL i
  have hS₂L : S₂ ≤ L := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₂t)
    rw [← hi]; exact hSL i
  have hconj₁ := r871shp_conj_mem_pair hmin hL hS hLset hpairset hS₁t hpS₁
  have hconj₂ := r871shp_conj_mem_pair hmin hL hS hLset hpairset hS₂t hpS₂
  have hL'L : S₁ ⊔ S₂ ≤ L := sup_le hS₁L hS₂L
  have hbmul : ((S₁ ⊔ S₂ : Subgroup G) : Set G) = (S₁ : Set G) * (S₂ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S₁ S₂
      (UC22.uc22p22u_calC_normalizes hS₁ hS₂ hS₁ne₂)
  have hnorm : L ≤ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup G) : Set G) := by
    rw [hjoin]
    refine iSup_le fun i => r871shp_le_normalizer_sup ?_ ?_
    · by_cases h : S i = S₁
      · rw [h]; exact Subgroup.le_normalizer
      · exact UC22.uc22p22u_calC_normalizes hS₁ (hS i) (Ne.symm h)
    · by_cases h : S i = S₂
      · rw [h]; exact Subgroup.le_normalizer
      · exact UC22.uc22p22u_calC_normalizes hS₂ (hS i) (Ne.symm h)
  have hMN : D.M ≤ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    have e₁mem := hconj₁ m⁻¹ (D.M.inv_mem hm)
    have e₂mem := hconj₂ m⁻¹ (D.M.inv_mem hm)
    simp only [Finset.mem_insert, Finset.mem_singleton] at e₁mem e₂mem
    have e₁ : Subgroup.map (MulAut.conj m) S₁ = S₁ ∨
        Subgroup.map (MulAut.conj m) S₁ = S₂ := by
      simpa [uniqueFourConj, inv_inv] using e₁mem
    have e₂ : Subgroup.map (MulAut.conj m) S₂ = S₁ ∨
        Subgroup.map (MulAut.conj m) S₂ = S₂ := by
      simpa [uniqueFourConj, inv_inv] using e₂mem
    rcases e₁ with e₁ | e₁ <;> rcases e₂ with e₂ | e₂
    · exfalso
      exact hS₁ne₂ (Subgroup.map_injective (MulAut.conj m).injective (e₁.trans e₂.symm))
    · rw [e₁, e₂]
    · rw [e₁, e₂, sup_comm]
    · exfalso
      exact hS₁ne₂ (Subgroup.map_injective (MulAut.conj m).injective (e₁.trans e₂.symm))
  have hsh : S₁ ⊔ S₂ ∈ calC D.M ∨
      (S₁ ⊔ S₂ ≤ D.M ∧ D.M ≤ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup G) : Set G) ∧
        IsProdOfCalC D.M (S₁ ⊔ S₂)) :=
    Or.inr ⟨sup_le hS₁.1.le hS₂.1.le, hMN, r871shp_isProdOfCalC_sup hS₁ hS₂ hS₁ne₂⟩
  have hnt : ¬ Thin8 (S₁ ⊔ S₂) := by
    intro hth
    have hrank := r871shp_pRank_sup_pair hS₁ hS₂ hS₁ne₂ hthinS₁ hthinS₂
      (sup_le hS₁.1.le hS₂.1.le) hbmul
    have := hth 3 Nat.prime_three (by norm_num)
    omega
  have hne : ¬ L ≤ (S₁ ⊔ S₂) ⊔ pCoreOf 2 L := by
    have hsup : (⨆ C ∈ ({S₁, S₂} : Finset (Subgroup G)), C) = S₁ ⊔ S₂ := by
      apply le_antisymm
      · refine iSup₂_le fun C hC => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC
        rcases hC with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      · refine sup_le ?_ ?_
        · exact le_iSup₂ (f := fun C (_ : C ∈ ({S₁, S₂} : Finset (Subgroup G))) => C) S₁ (by simp)
        · exact le_iSup₂ (f := fun C (_ : C ∈ ({S₁, S₂} : Finset (Subgroup G))) => C) S₂ (by simp)
    have h := r871shp_not_le_sup (M := D.M) (L := L) (S := S) hS hLset hLM
      ({S₁, S₂} : Finset (Subgroup G))
      (by
        intro C hC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC
        rcases hC with rfl | rfl
        exacts [hS₁t, hS₂t])
      ⟨A, hAin, by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hAne₁, hAne₂⟩⟩
    intro hle
    exact h (by rwa [← hsup] at hle)
  exact r869_replace_false hmin hL'L hnorm hsh hnt hne

private theorem r871shp_all_mem_pair {G : Type} [Group G] [Finite G] [DecidableEq (Subgroup G)]
    {D : Data G} {L X H : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (hmin : MinCex869 D L X H) (hL : L ∉ calC D.M)
    (hS : ∀ i, S i ∈ calC D.M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod)
    (hthin : ∀ i, Thin8 (S i)) {S₁ S₂ : Subgroup G}
    (hS₁ : S₁ ∈ calC D.M) (hS₂ : S₂ ∈ calC D.M) (hS₁ne₂ : S₁ ≠ S₂)
    (hpS₁ : CFSG.Open.pRank 3 S₁ = 1) (hpS₂ : CFSG.Open.pRank 3 S₂ = 1)
    (hthinS₁ : Thin8 S₁) (hthinS₂ : Thin8 S₂)
    (hpairset : (List.ofFn S).toFinset.filter (fun C => 1 ≤ CFSG.Open.pRank 3 C) = {S₁, S₂}) :
    ∀ A ∈ (List.ofFn S).toFinset, A = S₁ ∨ A = S₂ := by
  intro A hA
  by_contra hcon
  push Not at hcon
  have hAthin : Thin8 A := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hA)
    rw [← hi]; exact hthin i
  have hA0 : CFSG.Open.pRank 3 A = 0 := by
    have hAle : CFSG.Open.pRank 3 A ≤ 1 := hAthin 3 Nat.prime_three (by norm_num)
    have hAne : A ∉ (List.ofFn S).toFinset.filter (fun C => 1 ≤ CFSG.Open.pRank 3 C) := by
      rw [hpairset]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hcon.1, hcon.2⟩
    have : ¬ (1 ≤ CFSG.Open.pRank 3 A) := fun h => hAne (Finset.mem_filter.mpr ⟨hA, h⟩)
    omega
  exact r871shp_sup_pair_false hmin hL hS hLset hthin hS₁ hS₂ hS₁ne₂ hpS₁ hpS₂
    hthinS₁ hthinS₂ hpairset hA hcon.1 hcon.2

theorem r871_prod_shape {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (hmin : MinCex869 D L X H) (h2 : CFSG.Open.pRank 3 X = 2) (hL : L ∉ calC D.M) {k : ℕ}
    {S : Fin k → Subgroup G} (hS : ∀ i, S i ∈ calC D.M)
    (hLset : (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod)
    (hthin : ∀ i, Thin8 (S i)) :
    ∃ S₁ S₂ : Subgroup G, S₁ ∈ calC D.M ∧ S₂ ∈ calC D.M ∧ Thin8 S₁ ∧ Thin8 S₂ ∧
      (L : Set G) = (S₁ : Set G) * (S₂ : Set G) ∧
      (∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L) ∧
      CFSG.Open.pRank 3 S₁ = 1 ∧ CFSG.Open.pRank 3 S₂ = 1 ∧
      ((D.M ≤ Subgroup.normalizer (S₁ : Set G) ∧ D.M ≤ Subgroup.normalizer (S₂ : Set G)) ∨
        (S₁ ≠ S₂ ∧ UC22.conjSetOf D.M S₁ = {S₁, S₂})) := by
  classical
  have hdata := hmin.hyp.1.resolve_left hL
  have hLM : L ≤ D.M := hdata.1
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) := hdata.2.1
  have hsup := hmin.hyp.2.2.1
  have hrankL : CFSG.Open.pRank 3 L = 2 := by
    rw [← r873_pRank_X hsup Nat.prime_three (by norm_num)]
    exact h2
  have hsum := r871shp_pRank_sum hS hLset hLM hthin Nat.prime_three (by norm_num)
  have hsum2 : ∑ A ∈ (List.ofFn S).toFinset, CFSG.Open.pRank 3 A = 2 := by
    rw [← hsum]; exact hrankL
  have hf : ∀ A ∈ (List.ofFn S).toFinset, CFSG.Open.pRank 3 A ≤ 1 := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hA)
    rw [← hi]; exact hthin i 3 Nat.prime_three (by norm_num)
  obtain ⟨S₁, S₂, hS₁ne₂, hS₁t, hS₂t, hpS₁, hpS₂, hpairset⟩ :=
    r871shp_filter_two (List.ofFn S).toFinset (fun A => CFSG.Open.pRank 3 A) hf hsum2
  have hS₁ : S₁ ∈ calC D.M := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₁t)
    rw [← hi]; exact hS i
  have hS₂ : S₂ ∈ calC D.M := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₂t)
    rw [← hi]; exact hS i
  have hthinS₁ : Thin8 S₁ := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₁t)
    rw [← hi]; exact hthin i
  have hthinS₂ : Thin8 S₂ := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₂t)
    rw [← hi]; exact hthin i
  have hpair : ∀ A ∈ (List.ofFn S).toFinset, A = S₁ ∨ A = S₂ :=
    r871shp_all_mem_pair hmin hL hS hLset hthin hS₁ hS₂ hS₁ne₂ hpS₁ hpS₂ hthinS₁ hthinS₂ hpairset
  have hjoin : L = ⨆ i, S i := r871shp_join hS hLset
  have hS₁L : S₁ ≤ L := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₁t)
    rw [← hi]; rw [hjoin]; exact le_iSup S i
  have hS₂L : S₂ ≤ L := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₂t)
    rw [← hi]; rw [hjoin]; exact le_iSup S i
  have hLsup : L = S₁ ⊔ S₂ := by
    apply le_antisymm
    · rw [hjoin]
      refine iSup_le fun i => ?_
      have hmem : S i ∈ (List.ofFn S).toFinset := by
        rw [List.mem_toFinset, List.mem_ofFn]; exact ⟨i, rfl⟩
      rcases hpair (S i) hmem with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    · exact sup_le hS₁L hS₂L
  have hLset' : (L : Set G) = (S₁ : Set G) * (S₂ : Set G) := by
    rw [hLsup, Subgroup.coe_mul_of_right_le_normalizer_left S₁ S₂
      (UC22.uc22p22u_calC_normalizes hS₁ hS₂ hS₁ne₂)]
  have hS₁calC_L : S₁ ∈ calC L := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₁t)
    rw [← hi]; exact r871shp_calC_L hS hLset hLM i
  have hS₂calC_L : S₂ ∈ calC L := by
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 (List.mem_toFinset.mp hS₂t)
    rw [← hi]; exact r871shp_calC_L hS hLset hLM i
  have hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L :=
    r871shp_barImage_commutator_mem hS₁calC_L hS₂calC_L hS₁ne₂
  refine ⟨S₁, S₂, hS₁, hS₂, hthinS₁, hthinS₂, hLset', hcomm, hpS₁, hpS₂, ?_⟩
  have hconj₁ := r871shp_conj_mem_pair hmin hL hS hLset hpairset hS₁t hpS₁
  have hconj₂ := r871shp_conj_mem_pair hmin hL hS hLset hpairset hS₂t hpS₂
  by_cases hfix : ∀ m ∈ D.M, uniqueFourConj m S₁ = S₁
  · left
    refine ⟨?_, ?_⟩
    · intro m hm
      exact CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_eq_self_iff.mp (hfix m hm)
    · intro m hm
      have h2mem := hconj₂ m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2mem
      rcases h2mem with h2mem | h2mem
      · exfalso
        have hmap : S₁.map (MulAut.conj m⁻¹).toMonoidHom =
            S₂.map (MulAut.conj m⁻¹).toMonoidHom := (hfix m hm).trans h2mem.symm
        exact hS₁ne₂ (Subgroup.map_injective (MulAut.conj m⁻¹).injective hmap)
      · exact CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_eq_self_iff.mp h2mem
  · right
    push Not at hfix
    obtain ⟨m₀, hm₀, hne₀⟩ := hfix
    have hmem₀ := hconj₁ m₀ hm₀
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₀
    have hswap : uniqueFourConj m₀ S₁ = S₂ := by
      rcases hmem₀ with h | h
      · exact absurd h hne₀
      · exact h
    refine ⟨hS₁ne₂, ?_⟩
    apply Set.Subset.antisymm
    · intro K hK
      obtain ⟨g, hg, rfl⟩ := hK
      have hg' := hconj₁ g⁻¹ (D.M.inv_mem hg)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg'
      have hmap : S₁.map (MulAut.conj g).toMonoidHom = uniqueFourConj g⁻¹ S₁ := by
        simp [uniqueFourConj]
      rw [hmap]
      rcases hg' with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl
      · exact ⟨1, D.M.one_mem, by ext x; simp⟩
      · exact ⟨m₀⁻¹, D.M.inv_mem hm₀, by simpa [uniqueFourConj] using hswap.symm⟩

section r871swp

open CFSG.RankThree.PartOne (omegaOne)
open scoped commutatorElement

private theorem r871swp_map_pow_eq_self {G : Type} [Group G] {S : Subgroup G} {g : MulAut G}
    (h : S.map g.toMonoidHom = S) (n : ℕ) : S.map (g ^ n).toMonoidHom = S := by
  induction n with
  | zero =>
    change S.map (MonoidHom.id G) = S
    exact Subgroup.map_id S
  | succ m ih =>
    rw [pow_succ]
    rw [show (g ^ m * g).toMonoidHom = (g ^ m).toMonoidHom.comp g.toMonoidHom from rfl]
    rw [← Subgroup.map_map, h, ih]

private theorem r871swp_fix₁ {G : Type} [Group G] [Finite G] {D : Data G} {q : ℕ} (hq : Odd q)
    {S₁ S₂ R : Subgroup G} (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) (hne : S₁ ≠ S₂)
    (hRM : R ≤ D.M) (hRp : IsPGroup q R) : R ≤ Subgroup.normalizer (S₁ : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  set f : MulAut G := MulAut.conj r with hf
  have hmem : S₁.map f.toMonoidHom ∈ ({S₁, S₂} : Set (Subgroup G)) := by
    rw [← hset]
    exact ⟨r, hRM hr, by simp [hf]⟩
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exact h
  · exfalso
    have hS₂ : S₂ ∈ UC22.conjSetOf D.M S₁ := by rw [hset]; simp
    obtain ⟨m, hmM, hm⟩ := hS₂
    have h2mem : S₂.map f.toMonoidHom ∈ UC22.conjSetOf D.M S₁ := by
      refine ⟨r * m, D.M.mul_mem (hRM hr) hmM, ?_⟩
      rw [hm]
      rw [Subgroup.map_map]
      congr 1
      rw [hf]
      ext x
      simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    have h2 : S₂.map f.toMonoidHom = S₁ := by
      have h2' := h2mem
      rw [hset] at h2'
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h2'
      rcases h2' with h' | h'
      · exact h'
      · exact absurd (Subgroup.map_injective f.injective (by rw [h, h'])) hne
    have hf2 : S₂.map (f ^ 2).toMonoidHom = S₂ := by
      have hcomp : (f ^ 2).toMonoidHom = f.toMonoidHom.comp f.toMonoidHom := by
        rw [sq]; rfl
      rw [hcomp, ← Subgroup.map_map, h2, h]
    obtain ⟨k, hk⟩ := hRp (⟨r, hr⟩ : ↥R)
    have hrk : r ^ (q ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hf3 : f ^ (q ^ k) = 1 := by
      rw [hf, ← map_pow, hrk, map_one]
    have hodd : Odd (q ^ k) := hq.pow
    obtain ⟨m, hm'⟩ := hodd
    have hkey : S₂.map ((f ^ 2) ^ m).toMonoidHom = S₂ := r871swp_map_pow_eq_self hf2 m
    have h1 : S₁.map (f ^ (q ^ k)).toMonoidHom = S₁ := by
      rw [hf3]; exact Subgroup.map_id S₁
    have h2' : S₁.map (f ^ (q ^ k)).toMonoidHom = S₂ := by
      rw [hm', pow_succ, pow_mul]
      rw [show ((f ^ 2) ^ m * f).toMonoidHom =
        ((f ^ 2) ^ m).toMonoidHom.comp f.toMonoidHom from rfl]
      rw [← Subgroup.map_map, h, hkey]
    rw [h2'] at h1
    exact hne h1.symm

private theorem r871swp_conj_mem {G : Type} [Group G] [Finite G] {D : Data G} {S₁ S₂ : Subgroup G}
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) {m : G} (hmM : m ∈ D.M)
    (hm : S₂ = S₁.map (MulAut.conj m).toMonoidHom) {r : G} (hr : r ∈ D.M) :
    S₂.map (MulAut.conj r).toMonoidHom ∈ ({S₁, S₂} : Set (Subgroup G)) := by
  rw [← hset]
  refine ⟨r * m, D.M.mul_mem hr hmM, ?_⟩
  rw [hm, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]

private theorem r871swp_fix₂ {G : Type} [Group G] [Finite G] {D : Data G} {q : ℕ} (hq : Odd q)
    {S₁ S₂ R : Subgroup G} (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) (hne : S₁ ≠ S₂)
    (hRM : R ≤ D.M) (hRp : IsPGroup q R) : R ≤ Subgroup.normalizer (S₂ : Set G) := by
  have hfix₁ : R ≤ Subgroup.normalizer (S₁ : Set G) := r871swp_fix₁ hq hset hne hRM hRp
  have hS₂ : S₂ ∈ UC22.conjSetOf D.M S₁ := by rw [hset]; simp
  obtain ⟨m, hmM, hm⟩ := hS₂
  intro r hr
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmem := r871swp_conj_mem hset hmM hm (hRM hr)
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exfalso
    have h1 : S₁.map (MulAut.conj r).toMonoidHom = S₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hfix₁ hr)
    exact hne (Subgroup.map_injective (MulAut.conj r).injective (by rw [h, h1]))
  · exact h

private theorem r871swp_card_eq {G : Type} [Group G] [Finite G] {D : Data G} {S₁ S₂ : Subgroup G}
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) : Nat.card S₂ = Nat.card S₁ := by
  have hS₂ : S₂ ∈ UC22.conjSetOf D.M S₁ := by rw [hset]; simp
  obtain ⟨m, -, hm⟩ := hS₂
  rw [hm]
  exact Subgroup.card_map_of_injective (MulAut.conj m).injective

private theorem r871swp_inf_normal {G : Type} [Group G] {R S : Subgroup G}
    (hRS : R ≤ Subgroup.normalizer (S : Set G)) :
    R ≤ Subgroup.normalizer ((R ⊓ S : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hRS hr) h).mp hh.2⟩
    exact R.mul_mem (R.mul_mem hr hh.1) (R.inv_mem hr)
  · intro hh
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hRS hr) h).mpr hh.2⟩
    have h2 : r⁻¹ * (r * h * r⁻¹) * r ∈ R :=
      R.mul_mem (R.mul_mem (R.inv_mem hr) hh.1) hr
    have h3 : r⁻¹ * (r * h * r⁻¹) * r = h := by group
    rwa [h3] at h2

private theorem r871swp_le_L {G : Type} [Group G] {S₁ S₂ L : Subgroup G}
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G)) : S₁ ≤ L ∧ S₂ ≤ L := by
  constructor
  · intro y hy
    change y ∈ (L : Set G)
    rw [hLset]
    exact ⟨y, hy, 1, S₂.one_mem, by simp⟩
  · intro y hy
    change y ∈ (L : Set G)
    rw [hLset]
    exact ⟨1, S₁.one_mem, y, hy, by simp⟩

private theorem r871swp_le_M {G : Type} [Group G] [Finite G] {D : Data G} {S₁ S₂ L : Subgroup G}
    (hS₁ : S₁ ∈ calC D.M) (hS₂ : S₂ ∈ calC D.M)
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G)) : L ≤ D.M := by
  intro l hl
  have hl' : l ∈ (L : Set G) := hl
  rw [hLset] at hl'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hl'
  exact D.M.mul_mem (hS₁.1.le ha) (hS₂.1.le hb)

private theorem r871swp_sylow_inf {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {M R S : Subgroup G} (hR : IsSylowOf q R M) (hSM : S ≤ M)
    (hRS : R ≤ Subgroup.normalizer (S : Set G)) : IsSylowOf q (R ⊓ S) S := by
  have hK : R ⊔ S ≤ Subgroup.normalizer (S : Set G) := sup_le hRS Subgroup.le_normalizer
  have hKM : R ⊔ S ≤ M := sup_le hR.le hSM
  exact (hR.of_le le_sup_left hKM).inf_of_le_normalizer le_sup_right hK

private theorem r871swp_dvd_card {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {Q S : Subgroup G} (hQ : IsSylowOf q Q S) (hS : q ∣ Nat.card S) : q ∣ Nat.card Q := by
  obtain ⟨-, -, hrel⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hQ
  have h := Subgroup.relIndex_mul_card (H := Q) (K := S)
  rw [inf_eq_left.mpr hQ.le] at h
  rw [← h] at hS
  exact ((Fact.out : q.Prime).dvd_mul.mp hS).resolve_left hrel

private theorem r871swp_inf_bot {G : Type} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hpq : p ≠ q) {P Q : Subgroup G} (hP : IsPGroup p P) (hQ : IsPGroup q Q) :
    P ⊓ Q = ⊥ := by
  have hc := IsPGroup.coprime_card_of_ne p q hpq (P ⊓ Q) (P ⊓ Q) hP.to_inf_left hQ.to_inf_right
  rw [Nat.coprime_self] at hc
  exact Subgroup.eq_bot_of_card_eq _ hc

private theorem r871swp_commute_normalizer {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (h a ha b hb).symm

private theorem r871swp_sup_card {G : Type} [Group G] [Finite G] {q : ℕ} {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hinf : A ⊓ B = ⊥) (hA : Nat.card A = q)
    (hB : Nat.card B = q) : Nat.card (A ⊔ B : Subgroup G) = q ^ 2 := by
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hAB
  rw [hinf, Subgroup.card_bot, mul_one, hA, hB] at h
  rw [h, sq]

private theorem r871swp_zpowers_elem {G : Type} [Group G] {q : ℕ} {x : G} (hx : x ^ q = 1) :
    IsElemAbelian q (Subgroup.zpowers x) := by
  rw [Subgroup.zpowers_eq_closure]
  refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_)
  · rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  · rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hx

private theorem r871swp_pow_of_mem_zpowers {G : Type} [Group G] {q : ℕ} {x y : G}
    (hy : y ∈ Subgroup.zpowers x) (hx : x ^ q = 1) : y ^ q = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private theorem r871swp_normalizer_omegaOne {G : Type} [Group G] {q : ℕ} {Q : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (Q : Set G)) :
    s ∈ Subgroup.normalizer ((omegaOne q Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hs ⊢
  exact (CFSG.RankThree.PartOne.Sec9B.map_omegaOne (f := (MulAut.conj s).toMonoidHom)
    (MulAut.conj s).injective q Q).trans (congrArg (omegaOne q) hs)

private theorem r871swp_centralizes {G : Type} [Group G] [Finite G] {S₀ C : Subgroup G}
    (hodd : Odd (Nat.card S₀)) (hC : Nat.card C = 3)
    (hN : S₀ ≤ Subgroup.normalizer (C : Set G)) : C ≤ Subgroup.centralizer (S₀ : Set G) := by
  have h := CFSG.MulAut.act_trivial_of_preserves_card_three (B := G)
    (Y := S₀.map (MulAut.conj : G →* MulAut G))
    (Odd.of_dvd_nat hodd (Subgroup.card_map_dvd S₀ _)) hC (by
      rintro y ⟨s, hs, rfl⟩
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hs))
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 := h (MulAut.conj s) ⟨s, hs, rfl⟩ c hc
  rw [MulAut.conj_apply] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

private theorem r871swp_map_omegaOne_subtype {G : Type} [Group G] {Q R : Subgroup G}
    (hQR : Q ≤ R) : (omegaOne 3 (Q.subgroupOf R)).map R.subtype = omegaOne 3 Q := by
  rw [CFSG.RankThree.PartOne.Sec9B.map_omegaOne R.subtype_injective 3 (Q.subgroupOf R)]
  congr 1
  exact Subgroup.map_subgroupOf_eq_of_le hQR

private theorem r871swp_map_center_subtype {G : Type} [Group G] (R : Subgroup G) :
    (Subgroup.center ↥R).map R.subtype = R ⊓ Subgroup.centralizer (R : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)
  · rintro ⟨hxR, hxC⟩
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (y : G) y.2)

private theorem r871swp_Ei_center {G : Type} [Group G] [Finite G] {R Q : Subgroup G}
    (hRp : IsPGroup 3 R) (hQR : Q ≤ R) (hQnorm : R ≤ Subgroup.normalizer (Q : Set G))
    (hQcyc : IsCyclic Q) : omegaOne 3 Q ≤ Subgroup.centralizer (R : Set G) := by
  have hN : (Q.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQR]
    exact hQnorm
  have hcyc : IsCyclic (Q.subgroupOf R) := by
    have e : ↥(Q.subgroupOf R) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQR
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have h := omegaOne_le_center_of_normal_cyclic hRp hN hcyc
  have hmap : (omegaOne 3 (Q.subgroupOf R)).map R.subtype ≤
      (Subgroup.center ↥R).map R.subtype := Subgroup.map_mono h
  rw [r871swp_map_omegaOne_subtype hQR, r871swp_map_center_subtype R] at hmap
  exact hmap.trans inf_le_right

private theorem r871swp_mem_pCore_of_commutator {G : Type} [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) {L : Subgroup G} (hZ : ¬ q ∣ Nat.card (Subgroup.center (Bar2 L)))
    {z : G} (hzL : z ∈ L) (hzq : z ^ q = 1) (hcomm : ∀ y ∈ L, ⁅z, y⁆ ∈ pCoreOf 2 L) :
    z ∈ pCoreOf 2 L := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hcen : π (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ r
    have hcommL : ⁅(⟨z, hzL⟩ : ↥L), l⁆ ∈ CFSG.pCore 2 ↥L := by
      rw [← CFSG.mem_openPCoreOf_iff]
      exact hcomm (l : G) l.2
    have hcomm' : ⁅π (⟨z, hzL⟩ : ↥L), π l⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hcommL
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm').symm
  have hzqL : (⟨z, hzL⟩ : ↥L) ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hzq
  have hzq' : (π (⟨z, hzL⟩ : ↥L)) ^ q = 1 := by
    rw [← map_pow, hzqL, map_one]
  have hle : Subgroup.zpowers (π (⟨z, hzL⟩ : ↥L)) ≤ Subgroup.center (Bar2 L) :=
    Subgroup.zpowers_le.mpr hcen
  have hdvd : Nat.card (Subgroup.zpowers (π (⟨z, hzL⟩ : ↥L))) ∣ q := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hzq'
  have hcard : Nat.card (Subgroup.zpowers (π (⟨z, hzL⟩ : ↥L))) = 1 := by
    rcases (Nat.dvd_prime hq).mp hdvd with h | h
    · exact h
    · exfalso
      exact hZ (h ▸ Subgroup.card_dvd_of_le hle)
  have hone : π (⟨z, hzL⟩ : ↥L) = 1 := by
    have hbot : Subgroup.zpowers (π (⟨z, hzL⟩ : ↥L)) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ hcard
    have := Subgroup.mem_zpowers (π (⟨z, hzL⟩ : ↥L))
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact (CFSG.mem_openPCoreOf_iff (⟨z, hzL⟩ : ↥L)).mpr
    ((QuotientGroup.eq_one_iff _).mp hone)

private theorem r871swp_inter {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {S₁ S₂ L : Subgroup G} (hZ : ¬ q ∣ Nat.card (Subgroup.center (Bar2 S₁)))
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L) {x : G} (hx₁ : x ∈ S₁)
    (hx₂ : x ∈ S₂) (hxq : x ^ q = 1) : x = 1 := by
  have hS₁L : S₁ ≤ L := (r871swp_le_L hLset).1
  have hO_le : pCoreOf 2 L ⊓ S₁ ≤ pCoreOf 2 S₁ := by
    have h2 : IsPGroup 2 ↥(pCoreOf 2 L ⊓ S₁) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
    have hnorm : S₁ ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ S₁ : Subgroup G) : Set G) := by
      intro s hs
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hS₁L hs),
          Subgroup.le_normalizer (H := S₁) hs⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm h2
  have hcomm' : ∀ y ∈ S₁, ⁅x, y⁆ ∈ pCoreOf 2 S₁ := by
    intro y hy
    have h := hcomm y hy x hx₂
    have hmem : ⁅x, y⁆ ∈ pCoreOf 2 L ⊓ S₁ := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def,
          show x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ from by group]
        exact Subgroup.inv_mem _ h
      · rw [commutatorElement_def]
        exact S₁.mul_mem (S₁.mul_mem (S₁.mul_mem hx₁ hy) (S₁.inv_mem hx₁)) (S₁.inv_mem hy)
    exact hO_le hmem
  have hxO : x ∈ pCoreOf 2 S₁ := r871swp_mem_pCore_of_commutator hq hZ hx₁ hxq hcomm'
  have hx2p : IsPGroup 2 (pCoreOf 2 S₁) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S₁
  obtain ⟨k, hk⟩ := hx2p.exists_orderOf_eq_pow (⟨x, hxO⟩ : pCoreOf 2 S₁)
  have hk' : orderOf x = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe ⟨x, hxO⟩
  have hxqdvd : orderOf x ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hxq
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp (h2dvd.trans (hk' ▸ hxqdvd))).symm
  exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])

private theorem r871swp_cyclic_comm {G : Type} [Group G] {H : Subgroup G} (hH : IsCyclic H) :
    ∀ a b : H, a * b = b * a := by
  have : IsCyclic H := hH
  let : CommGroup H := IsCyclic.commGroup
  exact fun a b => mul_comm a b

private theorem r871swp_omegaOne_elemAbelian {G : Type} [Group G] {Q : Subgroup G}
    (hQcomm : ∀ a b : Q, a * b = b * a) : IsElemAbelian 3 (omegaOne 3 Q) := by
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · intro a ha b hb
    exact congrArg Subtype.val (hQcomm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
  · intro a ha
    exact ha.2

private theorem r871swp_omegaOne_card {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQcyc : IsCyclic Q) : Nat.card (omegaOne 3 Q) = (Nat.card Q).gcd 3 := by
  have : IsCyclic ↥Q := hQcyc
  have htop : (CFSG.omega₁ (G := Q) (p := 3)) = omegaOne 3 (⊤ : Subgroup Q) := by
    ext x; simp [CFSG.omega₁, CFSG.omega, omegaOne]
  have hmap : (omegaOne 3 (⊤ : Subgroup Q)).map Q.subtype = omegaOne 3 Q := by
    have h := CFSG.RankThree.PartOne.Sec9B.map_omegaOne (f := Q.subtype) Q.subtype_injective 3
      (⊤ : Subgroup Q)
    simpa [Subgroup.map_top, Subgroup.range_subtype] using h
  have hΩeq : omegaOne 3 Q = (CFSG.omega₁ (G := Q) (p := 3)).map Q.subtype := by
    rw [htop]; exact hmap.symm
  rw [hΩeq, Subgroup.card_map_of_injective Q.subtype_injective]
  exact CFSG.card_omega₁_of_isCyclic (X := Q) (p := 3)

private theorem r871swp_omegaOne_card_three {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQcyc : IsCyclic Q) (hQ3 : 3 ∣ Nat.card Q) : Nat.card (omegaOne 3 Q) = 3 := by
  rw [r871swp_omegaOne_card hQcyc]
  exact Nat.gcd_eq_right hQ3

private theorem r871swp_not_dvd_center {G : Type} [Group G] [Finite G] {M S : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hS : S ∈ calC M) (h : CFSG.Open.pRank q S = 1) :
    ¬ q ∣ Nat.card (Subgroup.center (Bar2 S)) := by
  have : Group.IsPerfect (Bar2 S) := ⟨hS.2.2.1⟩
  have : Fact q.Prime := ⟨hq⟩
  exact PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one hq2
    ((UC22.pRank_bar2_eq_of_odd hq hq2).trans h)

private theorem r871swp_Ei {G : Type} [Group G] [Finite G] {M R S : Subgroup G}
    (hR : IsSylowOf 3 R M) (hSM : S ≤ M) (hRS : R ≤ Subgroup.normalizer (S : Set G))
    (hr : CFSG.Open.pRank 3 S = 1) :
    Nat.card (omegaOne 3 (R ⊓ S)) = 3 ∧ omegaOne 3 (R ⊓ S) ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
      omegaOne 3 (R ⊓ S) ≤ S ∧ IsElemAbelian 3 (omegaOne 3 (R ⊓ S)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : IsSylowOf 3 (R ⊓ S) S := r871swp_sylow_inf hR hSM hRS
  have hcyc : IsCyclic ↥(R ⊓ S) :=
    CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hQ.isPGroup inf_le_right
      hr.le
  have hdvd : 3 ∣ Nat.card ↥(R ⊓ S) :=
    r871swp_dvd_card hQ (UC22.R8107Odd.three_dvd_card_of_pRank_eq_one hr)
  have hle : omegaOne 3 (R ⊓ S) ≤ R ⊓ S := (Subgroup.closure_le (R ⊓ S)).2 fun y hy => hy.1
  have hcen := r871swp_Ei_center hR.isPGroup inf_le_left (r871swp_inf_normal hRS) hcyc
  exact ⟨r871swp_omegaOne_card_three hcyc hdvd, le_inf (hle.trans inf_le_left) hcen,
    hle.trans inf_le_right, r871swp_omegaOne_elemAbelian (r871swp_cyclic_comm hcyc)⟩

private theorem r871swp_E {G : Type} [Group G] [Finite G] {D : Data G} {S₁ S₂ L R : Subgroup G}
    (hS₁ : S₁ ∈ calC D.M) (hS₂ : S₂ ∈ calC D.M)
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L)
    (hr₁ : CFSG.Open.pRank 3 S₁ = 1) (hr₂ : CFSG.Open.pRank 3 S₂ = 1) (hne : S₁ ≠ S₂)
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) (hR : IsSylowOf 3 R D.M) :
    Nat.card (omegaOne 3 (R ⊓ S₁)) = 3 ∧ Nat.card (omegaOne 3 (R ⊓ S₂)) = 3 ∧
      omegaOne 3 (R ⊓ S₁) ⊔ omegaOne 3 (R ⊓ S₂) ≤ L ∧
      omegaOne 3 (R ⊓ S₁) ⊔ omegaOne 3 (R ⊓ S₂) ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
      IsElemAbelian 3 (omegaOne 3 (R ⊓ S₁) ⊔ omegaOne 3 (R ⊓ S₂)) ∧
      Nat.card (omegaOne 3 (R ⊓ S₁) ⊔ omegaOne 3 (R ⊓ S₂) : Subgroup G) = 9 := by
  have hp3 := hR.isPGroup
  obtain ⟨hc₁, hcen₁, hE₁S, hel₁⟩ :=
    r871swp_Ei hR hS₁.1.le (r871swp_fix₁ (by decide) hset hne hR.le hp3) hr₁
  obtain ⟨hc₂, hcen₂, hE₂S, hel₂⟩ :=
    r871swp_Ei hR hS₂.1.le (r871swp_fix₂ (by decide) hset hne hR.le hp3) hr₂
  obtain ⟨hS₁L, hS₂L⟩ := r871swp_le_L hLset
  have hZ := r871swp_not_dvd_center Nat.prime_three (by norm_num) hS₁ hr₁
  have hc12 : ∀ a ∈ omegaOne 3 (R ⊓ S₁), ∀ b ∈ omegaOne 3 (R ⊓ S₂), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hcen₁ ha).2 b (hcen₂ hb).1).symm
  have hinf : omegaOne 3 (R ⊓ S₁) ⊓ omegaOne 3 (R ⊓ S₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_bot.mpr (r871swp_inter Nat.prime_three (by norm_num) hZ hLset hcomm
      (hE₁S hx₁) (hE₂S hx₂) (hel₁.2 x hx₁))
  refine ⟨hc₁, hc₂, sup_le (hE₁S.trans hS₁L) (hE₂S.trans hS₂L), sup_le hcen₁ hcen₂,
    hel₁.sup_of_commute hel₂ hc12, ?_⟩
  have h := r871swp_sup_card (r871swp_commute_normalizer hc12) hinf hc₁ hc₂
  rw [h]
  norm_num

private theorem r871swp_two_le_pRank {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {S₁ S₂ L : Subgroup G} (hZ : ¬ q ∣ Nat.card (Subgroup.center (Bar2 S₁)))
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L) {x₁ x₂ : G}
    (hx₁S : x₁ ∈ S₁) (hx₂S : x₂ ∈ S₂) (hx₁ : orderOf x₁ = q) (hx₂ : orderOf x₂ = q)
    (hc : x₁ * x₂ = x₂ * x₁) : 2 ≤ CFSG.Open.pRank q L := by
  have hq₁ : x₁ ^ q = 1 := hx₁ ▸ pow_orderOf_eq_one x₁
  have hq₂ : x₂ ^ q = 1 := hx₂ ▸ pow_orderOf_eq_one x₂
  obtain ⟨hS₁L, hS₂L⟩ := r871swp_le_L hLset
  have hcz : ∀ a ∈ Subgroup.zpowers x₁, ∀ b ∈ Subgroup.zpowers x₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute x₁ x₂ from hc) i j).eq
  have hinf : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_bot.mpr (r871swp_inter hq hq2 hZ hLset hcomm
      (Subgroup.zpowers_le.mpr hx₁S hy₁) (Subgroup.zpowers_le.mpr hx₂S hy₂)
      (r871swp_pow_of_mem_zpowers hy₁ hq₁))
  have hcard := r871swp_sup_card (r871swp_commute_normalizer hcz) hinf
    (by rw [Nat.card_zpowers, hx₁]) (by rw [Nat.card_zpowers, hx₂])
  exact UC6S846.le_pRank' hq
    (sup_le ((Subgroup.zpowers_le.mpr hx₁S).trans hS₁L)
      ((Subgroup.zpowers_le.mpr hx₂S).trans hS₂L))
    ((r871swp_zpowers_elem hq₁).sup_of_commute (r871swp_zpowers_elem hq₂) hcz) hcard

private theorem r871swp_not_dvd {G : Type} [Group G] [Finite G] {D : Data G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {S₁ S₂ L : Subgroup G} (hS₁ : S₁ ∈ calC D.M)
    (hS₂ : S₂ ∈ calC D.M) (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L) (hne : S₁ ≠ S₂)
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) (h1 : CFSG.Open.pRank p L ≤ 1) :
    ¬ p ∣ Nat.card S₁ := by
  intro hdiv
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf p D.M
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' p (r871swp_dvd_card
    (r871swp_sylow_inf hR hS₁.1.le (r871swp_fix₁ hodd hset hne hR.le hR.isPGroup)) hdiv)
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' p (r871swp_dvd_card
    (r871swp_sylow_inf hR hS₂.1.le (r871swp_fix₂ hodd hset hne hR.le hR.isPGroup))
    ((r871swp_card_eq hset).symm ▸ hdiv))
  have hx₁G : orderOf (x₁ : G) = p := by rw [Subgroup.orderOf_coe]; exact hx₁
  have hx₂G : orderOf (x₂ : G) = p := by rw [Subgroup.orderOf_coe]; exact hx₂
  have hbot : R ⊓ pCoreOf 2 L = ⊥ := r871swp_inf_bot (p := p) (q := 2) hp2 hR.isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hc : (x₁ : G) * x₂ = x₂ * x₁ := by
    have hmem : (x₁ : G) * x₂ * (x₁ : G)⁻¹ * (x₂ : G)⁻¹ ∈ R ⊓ pCoreOf 2 L :=
      ⟨R.mul_mem (R.mul_mem (R.mul_mem x₁.2.1 x₂.2.1) (R.inv_mem x₁.2.1)) (R.inv_mem x₂.2.1),
        hcomm x₁ x₁.2.2 x₂ x₂.2.2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hmem)
  have hge : 1 ≤ CFSG.Open.pRank p S₁ :=
    UC6S846.le_pRank' hp (Subgroup.zpowers_le.mpr x₁.2.2)
      (r871swp_zpowers_elem (hx₁G ▸ pow_orderOf_eq_one (x₁ : G))) (k := 1)
      (by rw [Nat.card_zpowers, hx₁G, pow_one])
  have hle : CFSG.Open.pRank p S₁ ≤ CFSG.Open.pRank p L :=
    CFSG.SectionRank.pRank_mono hp.one_lt (r871swp_le_L hLset).1
  have hZ := r871swp_not_dvd_center hp hp2 hS₁ (by omega)
  have h2 := r871swp_two_le_pRank hp hp2 hZ hLset hcomm x₁.2.2 x₂.2.2 hx₁G hx₂G hc
  omega

private theorem r871swp_not_dvd_card {G : Type} [Group G] [Finite G] {D : Data G} {p : ℕ}
    (hp : p.Prime) {S₁ S₂ L : Subgroup G} (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) (hnd : ¬ p ∣ Nat.card S₁) :
    ¬ p ∣ Nat.card L := by
  have h : Nat.card L * Nat.card ↥(S₁ ⊓ S₂) = Nat.card S₁ * Nat.card S₂ := by
    have h0 := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf S₁ S₂
    rw [← hLset] at h0
    exact h0
  intro hpL
  rcases hp.dvd_mul.mp (hpL.trans (Dvd.intro _ h)) with h' | h'
  · exact hnd h'
  · exact hnd ((r871swp_card_eq hset) ▸ h')

private theorem r871swp_sylow_inv {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M L S₀ : Subgroup G} (hLM : L ≤ M) (hS₀p : IsPGroup p S₀)
    (hS₀L : S₀ ≤ Subgroup.normalizer (L : Set G)) (hpL : ¬ p ∣ Nat.card L) :
    ∃ R : Subgroup G, IsSylowOf 3 R M ∧
      S₀ ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := CFSG.GroupTheory.FT63ChII.exists_sylow_normalized hS₀p hS₀L hpL 3
  obtain ⟨R, hR, hRL⟩ := CFSG.GroupTheory.exists_isSylowOf_inf_eq_of_le (p := 3) hLM
    (⟨Q, rfl⟩ : IsSylowOf 3 ((Q : Subgroup L).map L.subtype) L)
  exact ⟨R, hR, by rw [hRL]; exact hQ⟩

private theorem r871swp_Ei_cent {G : Type} [Group G] [Finite G] {R S₀ S L : Subgroup G}
    (hSL : S ≤ L) (hodd : Odd (Nat.card S₀))
    (hN₀ : S₀ ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G))
    (hNS : S₀ ≤ Subgroup.normalizer (S : Set G)) (hc : Nat.card (omegaOne 3 (R ⊓ S)) = 3) :
    omegaOne 3 (R ⊓ S) ≤ Subgroup.centralizer (S₀ : Set G) := by
  have hQ : S₀ ≤ Subgroup.normalizer ((R ⊓ S : Subgroup G) : Set G) := by
    intro s hs
    have h := Subgroup.inf_normalizer_le_normalizer_inf ⟨hN₀ hs, hNS hs⟩
    rwa [inf_assoc, inf_eq_right.mpr hSL] at h
  exact r871swp_centralizes hodd hc fun s hs => r871swp_normalizer_omegaOne (hQ hs)

private theorem r871swp_apply76 {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hns : ¬ Group.IsSolvable ↥D.M) (h76 : UC22.F07.R76 D) {p : ℕ}
    (hp : p ∈ D.sig) {E S₀ : Subgroup G} (hEM : E ≤ D.M) (hEel : IsElemAbelian 3 E)
    (hEc : Nat.card E = 9) (hS₀M : S₀ ≤ D.M) (hS₀el : IsElemAbelian p S₀)
    (hS₀c : Nat.card S₀ = p ^ 3) (hcen : E ≤ Subgroup.centralizer (S₀ : Set G)) :
    rankThreeGamma 1 3 E ≤ D.M := by
  have hσ := D.sig_prime p hp
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hp
  have hS₀C : S₀ ≤ Subgroup.centralizer (E : Set G) := Subgroup.le_centralizer_iff.mp hcen
  have h3 : 3 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) :=
    UC6S846.le_pRank' hσ.1 (le_inf hS₀M hS₀C) hS₀el hS₀c
  refine h76 p hσ.1 hσ.2 hsp 3 Nat.prime_three E hEM hEel (by rw [hEc]; norm_num) (by omega) ?_
  intro X hXE _
  refine lt_of_lt_of_le (by norm_num) (h3.trans (CFSG.SectionRank.pRank_mono hσ.1.one_lt ?_))
  exact inf_le_inf_left _ ((Subgroup.centralizer_le hXE).trans
    (Subgroup.centralizer_le_normalizer _))

private theorem r871swp_gamma {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h76 : UC22.F07.R76 D) {S₁ S₂ L : Subgroup G}
    (hS₁ : S₁ ∈ calC D.M) (hS₂ : S₂ ∈ calC D.M)
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L)
    (hr₁ : CFSG.Open.pRank 3 S₁ = 1) (hr₂ : CFSG.Open.pRank 3 S₂ = 1)
    (hML : D.M ≤ Subgroup.normalizer (L : Set G)) (hne : S₁ ≠ S₂)
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) {p : ℕ} (hp : p ∈ D.sig)
    (hpL : ¬ p ∣ Nat.card L) :
    ∃ R E : Subgroup G, IsSylowOf 3 R D.M ∧ E ≤ L ∧
      E ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      rankThreeGamma 1 3 E ≤ D.M := by
  have hσ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hσ.1⟩
  have hodd₀ : Odd p := hσ.1.odd_of_ne_two hσ.2
  obtain ⟨S₀, hS₀M, hS₀el, hS₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hσ.1 (k := 3) (hSg.three_le p hp)
  have hodd : Odd (Nat.card S₀) := by rw [hS₀c]; exact hodd₀.pow
  obtain ⟨R, hR, hN₀⟩ := r871swp_sylow_inv (r871swp_le_M hS₁ hS₂ hLset) hS₀el.isPGroup
    (hS₀M.trans hML) hpL
  obtain ⟨hc₁, hc₂, hEL, hEcen, hEel, hEc⟩ := r871swp_E hS₁ hS₂ hLset hcomm hr₁ hr₂ hne hset hR
  obtain ⟨hS₁L, hS₂L⟩ := r871swp_le_L hLset
  have hcen : omegaOne 3 (R ⊓ S₁) ⊔ omegaOne 3 (R ⊓ S₂) ≤ Subgroup.centralizer (S₀ : Set G) :=
    sup_le (r871swp_Ei_cent hS₁L hodd hN₀ (r871swp_fix₁ hodd₀ hset hne hS₀M hS₀el.isPGroup) hc₁)
      (r871swp_Ei_cent hS₂L hodd hN₀ (r871swp_fix₂ hodd₀ hset hne hS₀M hS₀el.isPGroup) hc₂)
  exact ⟨R, _, hR, hEL, hEcen, hEel, hEc, r871swp_apply76 hSg
    (UC6S846.not_solvable_of_mem_calC hS₁) h76 hp (hEL.trans (r871swp_le_M hS₁ hS₂ hLset)) hEel
    hEc hS₀M hS₀el hS₀c hcen⟩


end r871swp

theorem isStronglyPEmbedded_three_of_conjSetOf_eq_pair
    {G : Type} [Group G] [Finite G] {D : Data G} {S₁ S₂ L : Subgroup G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : UC22.F07.R76 D)
    (h1 : ∀ p ∈ D.sig, CFSG.Open.pRank p L ≤ 1)
    (hS₁ : S₁ ∈ calC D.M) (hS₂ : S₂ ∈ calC D.M)
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L)
    (hr₁ : CFSG.Open.pRank 3 S₁ = 1) (hr₂ : CFSG.Open.pRank 3 S₂ = 1)
    (hML : D.M ≤ Subgroup.normalizer (L : Set G)) (hne : S₁ ≠ S₂)
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) : IsStronglyPEmbedded 3 D.M := by
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hS₁
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hσ := D.sig_prime p hp
  have hpL : ¬ p ∣ Nat.card L := r871swp_not_dvd_card hσ.1 hLset hset
    (r871swp_not_dvd hσ.1 hσ.2 hS₁ hS₂ hLset hcomm hne hset (h1 p hp))
  obtain ⟨R, E, hR, _, hEcen, hEel, hEc, hΓ⟩ :=
    r871swp_gamma hSg h76 hS₁ hS₂ hLset hcomm hr₁ hr₂ hML hne hset hp hpL
  by_cases h3 : 3 ∈ D.sig
  · exact UC6S846.sp_of_mem_sig hSg hns h3
  · exact h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3
      R hR E hEcen hEel hEc hΓ


theorem r871_swap_false {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h870 : R870 D) (h614 : UC6.R6_14 D) (h76 : UC22.F07.R76 D)
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) {S₁ S₂ : Subgroup G}
    (hS₁ : S₁ ∈ calC D.M) (hS₂ : S₂ ∈ calC D.M) (_hT₁ : Thin8 S₁) (_hT₂ : Thin8 S₂)
    (hLset : (L : Set G) = (S₁ : Set G) * (S₂ : Set G))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L)
    (hr₁ : CFSG.Open.pRank 3 S₁ = 1) (hr₂ : CFSG.Open.pRank 3 S₂ = 1)
    (hML : D.M ≤ Subgroup.normalizer (L : Set G)) (hne : S₁ ≠ S₂)
    (hset : UC22.conjSetOf D.M S₁ = {S₁, S₂}) : False := by
  have h1 : ∀ p ∈ D.sig, CFSG.Open.pRank p L ≤ 1 := by
    intro p hp
    have hσ := D.sig_prime p hp
    by_contra h
    have hX : 1 < CFSG.Open.pRank p X := by
      rw [r873_pRank_X hmin.hyp.2.2.1 hσ.1 hσ.2]
      omega
    exact h870 L X H hmin p hσ.1 hσ.2 hX
      (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hS₁) hp)
  have hsp := isStronglyPEmbedded_three_of_conjSetOf_eq_pair hSg h614 h76 h1
    hS₁ hS₂ hLset hcomm hr₁ hr₂ hML hne hset
  have hjoin_set : ((S₁ ⊔ S₂ : Subgroup G) : Set G) = (S₁ : Set G) * (S₂ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S₁ S₂ (UC22.uc22p22u_calC_normalizes hS₁ hS₂ hne)
  have hjoin : S₁ ⊔ S₂ = L := SetLike.coe_injective (hjoin_set.trans hLset.symm)
  have hrank := r871shp_pRank_sup_pair hS₁ hS₂ hne _hT₁ _hT₂
    (sup_le hS₁.1.le hS₂.1.le) hjoin_set
  rw [hjoin, hr₁, hr₂] at hrank
  have hX : 1 < CFSG.Open.pRank 3 X := by
    rw [r873_pRank_X hmin.hyp.2.2.1 Nat.prime_three (by norm_num), hrank]
    norm_num
  exact h870 L X H hmin 3 Nat.prime_three (by norm_num) hX hsp

private theorem r871_qs_of_open {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    CFSG.IsQuasisimple X := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hperf, hsimple, ?_⟩
  by_contra hcomm
  have hc : ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := fun a b =>
    by_contra fun hne => hcomm ⟨a, b, hne⟩
  have hle : commutator X ≤ Subgroup.center X := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center X)) x y
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hc _ _)] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have := hsimple
  obtain ⟨a, ha⟩ := exists_ne (1 : X ⧸ Subgroup.center X)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  have hx : x ∈ commutator X := by
    rw [hperf]
    exact Subgroup.mem_top x
  exact ha ((QuotientGroup.eq_one_iff x).2 (hle hx))

theorem r871_of_inputs
    {G : Type} [Group G] [Finite G] (D : Data G)
    (hGA : GriessAllModelsStatement)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hM22 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
      (TauCeti.CFSGIndex.sporadic .M22).Group))
    (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D) (h614 : UC6.R6_14 D)
    (h638 : UC6.R6_38 D) (h76 : UC22.F07.R76 D) (hSg : UC6S846.SigmaStd D) (h870 : R870 D)
    (hOut : OutPComplement) (h82 : R82 D) (h856 : R856 D) : R871 D := by
  intro L X H hmin P hP
  by_cases h1 : CFSG.Open.pRank 3 X ≤ 1
  · exact Or.inl h1
  refine Or.inr ?_
  have hX1 : 1 < CFSG.Open.pRank 3 X := by omega
  obtain ⟨hcase, hXL, hsup, hnt⟩ := hmin.hyp
  have hLM : L ≤ D.M :=
    hcase.elim (fun hL => UC22.uc22p22a_le_of_isSubnormal hL.1) (fun h => h.1)
  have hSP : ¬ IsStronglyPEmbedded 3 D.M :=
    h870 L X H hmin 3 Nat.prime_three (by norm_num) hX1
  have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
    pRank_le_three_of_minCex hSg h870 hmin Nat.prime_three (by norm_num) hX1
  have hX3 : CFSG.Open.pRank 3 X ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (hXL.trans hLM)).trans hM3
  have hrL : CFSG.Open.pRank 3 X = CFSG.Open.pRank 3 L :=
    r873_pRank_X hsup Nat.prime_three (by norm_num)
  have hrank : CFSG.Open.pRank 3 X = 2 ∨ CFSG.Open.pRank 3 X = 3 := by omega
  by_cases hLc : L ∈ calC D.M
  · rcases hrank with h2 | h3
    ·
      have hPX : P ≤ X := hP.le
      have hPL : IsSylowOf 3 P L := r871_sylow_of_sup hXL hsup hP
      have hrL2 : CFSG.Open.pRank 3 L = 2 := by omega
      have hPr : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 P :=
        CFSG.pRank_le_of_isSylowOf_le Nat.prime_three (hPX.trans hXL) hPL le_rfl
      have hγ : ∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 9 →
          rankThreeGamma 1 3 E ≤ D.M := by
        intro E hEL hEel hEc
        by_cases hML : D.M ≤ Subgroup.normalizer (L : Set G)
        · exact r873_gamma_all hSg h870 h76 h638 hOut hmin hLc hML Nat.prime_three
            (by norm_num) hEL hEel (by rw [hEc]; norm_num)
        · exact r871_nonnormal_gamma hGA hSpor hM22 hSg h63 h69 h870 h76 h638 hOut hmin hLc h2 hML hEL
            hEel hEc
      have hΓ : rankThreeGamma 1 3 P ≤ D.M :=
        r871_gamma_sylow h63 hP.isPGroup (hPX.trans (hXL.trans hLM)) (by omega)
          fun E hEP hEel hEc => hγ E (hEP.trans (hPX.trans hXL)) hEel hEc
      refine ⟨?_, hΓ⟩
      rcases h856 L hLc hrL2 P hPL hΓ with hsp | hsl
      · exact absurd hsp hSP
      · obtain ⟨e⟩ := nonempty_bar2_equiv_of_sup_pCore L X hsup
        exact r871_isSL3PiType_of_mulEquiv e.symm hsl
    ·
      exfalso
      exact hSP (h82 L ⟨hLc.1, hLc.2.1, by omega, Or.inl (r871_qs_of_open hLc.2.2)⟩)
  · exfalso
    obtain ⟨hLM', hML, hprod⟩ := hcase.resolve_left hLc
    rcases hrank with h2 | h3
    ·
      obtain ⟨k, S, hS, hLset⟩ := hprod
      by_cases hnt' : ∃ i, ¬ Thin8 (S i)
      · obtain ⟨i, hi⟩ := hnt'
        exact r873_prod_nonthin_false hmin hLc hS hLset i hi
      · push Not at hnt'
        obtain ⟨S₁, S₂, hS₁, hS₂, hT₁, hT₂, hLset', hcomm, hr₁, hr₂, hperm⟩ :=
          r871_prod_shape hmin h2 hLc hS hLset hnt'
        rcases hperm with ⟨hN₁, hN₂⟩ | ⟨hne, hset⟩
        · exact r873_prod_two_false hSg h870 h614 h76 h638 hOut hmin hS₁ hS₂ hT₁ hT₂ hLset' hN₁
            hN₂ hcomm Nat.prime_three (by norm_num) (by omega) (by omega)
        · exact r871_swap_false hSg h870 h614 h76 hmin hS₁ hS₂ hT₁ hT₂ hLset' hcomm hr₁ hr₂ hML
            hne hset
    ·
      rcases r871_rank_three_prod hmin h3 hLc hLM' hML hprod with
        ⟨K, hK, hKL, hLK, hKnt, hKne⟩ | ⟨T, hT⟩
      · exact r869_replace_false hmin hKL hLK (Or.inl hK) hKnt hKne
      · exact hSP (h82 T hT)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
