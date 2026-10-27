module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddChain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddKFactDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgFrat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (xbar9 wbar9)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

private theorem r920l2_isCyclic_sylow_of_oddPrime {D : Data G} {L D₃ A : Subgroup G} {n : ℕ}
    (c : R920CfgL2 D L D₃ A n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (T : Sylow p ↥L) :
    IsCyclic ↥(T : Subgroup ↥L) := by
  have h1 : CFSG.Open.pRank p L ≤ 1 := by
    rw [← pRank_bar2_eq_of_odd (Y := L) hp hp2]
    exact pRank_le_one_of_isL2_or_isSz (Or.inl c.isL2) hp hp2
  have htop : CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) L]
    exact h1
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one hp hp2
    T.isPGroup' ((CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono p hp.one_lt le_top).trans htop)

private theorem r920l2_mem_uniqueSet_of_card_eq_prime {D : Data G} {L D₃ A : Subgroup G} {n : ℕ}
    (c : R920CfgL2 D L D₃ A n) {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hXL : X ≤ L)
    (hXc : Nat.card X = p) (hXmem : X ∈ uniqueSet D.M)
    (hcyc : ∀ T : Sylow p ↥L, IsCyclic T) (hEL : E ≤ L) (hE : Nat.card E = p) :
    E ∈ uniqueSet D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := CFSG.AGLEmbeddingD2.exists_eq_map_conj_of_isCyclic (J := ↥L) (p := p)
    hcyc (Y₀ := X.subgroupOf L) (Y₁ := E.subgroupOf L)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv, hXc])
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE])
  have heq : E = X.map (MulAut.conj (j : G)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hy' : (⟨y, hEL hy⟩ : ↥L) ∈ E.subgroupOf L := hy
      rw [hj, Subgroup.mem_map] at hy'
      obtain ⟨d, hd, hdy⟩ := hy'
      exact Subgroup.mem_map.2 ⟨d, hd,
        by simpa [MulAut.conj_apply] using congrArg Subtype.val hdy⟩
    · intro hy
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hy
      have hd' : (⟨d, hXL hd⟩ : ↥L) ∈ X.subgroupOf L := hd
      have := Subgroup.mem_map_of_mem (MulAut.conj j).toMonoidHom hd'
      rw [← hj] at this
      simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.1 this
  rw [heq]
  exact conj_mem_uniqueSet hXmem (CFSG.Open.IsSubnormal.le c.mem.1 j.2)

private theorem r920l2_mem_uniqueSet_of_card_three {D : Data G} {L D₃ A : Subgroup G} {n : ℕ}
    (c : R920CfgL2 D L D₃ A n) {E : Subgroup G} (hEL : E ≤ L) (hE : Nat.card E = 3) :
    E ∈ uniqueSet D.M :=
  r920l2_mem_uniqueSet_of_card_eq_prime c Nat.prime_three c.D₃_le c.D₃_card c.D₃_mem
    (fun T => r920l2_isCyclic_sylow_of_oddPrime c Nat.prime_three (by norm_num) T) hEL hE

private theorem r920l2_mem_uniqueSet_of_card_eq_card_A {D : Data G} {L D₃ A : Subgroup G}
    {n : ℕ} (c : R920CfgL2 D L D₃ A n) (hA2 : Nat.card A ≠ 2) {E : Subgroup G} (hEL : E ≤ L)
    (hE : Nat.card E = Nat.card A) : E ∈ uniqueSet D.M :=
  r920l2_mem_uniqueSet_of_card_eq_prime c c.A_prime c.A_le rfl c.A_mem
    (fun T => r920l2_isCyclic_sylow_of_oddPrime c c.A_prime hA2 T) hEL hE

private theorem r920l2_map_eq_of_isSylowOf_comap {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] (N : Subgroup Γ) [N.Normal] {Pb : Subgroup (Γ ⧸ N)} (hPb : IsPGroup p Pb)
    {P₁ : Subgroup Γ} (hP₁ : IsSylowOf p P₁ (Pb.comap (QuotientGroup.mk' N))) :
    P₁.map (QuotientGroup.mk' N) = Pb := by
  let π : Γ →* Γ ⧸ N := QuotientGroup.mk' N
  let H₁ : Subgroup Γ := Pb.comap π
  have hNle : N ≤ H₁ := by
    intro x hx
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show π x ∈ Pb
    rw [hx1]
    exact Pb.one_mem
  have hH₁map : H₁.map π = Pb :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Pb
  have hrel : (P₁.map π).relIndex Pb = (P₁ ⊔ N).relIndex H₁ := by
    have h := Subgroup.relIndex_map_map π P₁ H₁
    rw [hH₁map, QuotientGroup.ker_mk', sup_eq_left.mpr hNle] at h
    exact h
  have hP₁dvd : ¬ p ∣ P₁.relIndex H₁ := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP₁).2.2
  have hsup_le : P₁ ⊔ N ≤ H₁ := sup_le hP₁.le hNle
  have hnotdvd : ¬ p ∣ (P₁ ⊔ N).relIndex H₁ := by
    intro hdvd
    apply hP₁dvd
    rw [← Subgroup.relIndex_mul_relIndex (H := P₁) (K := P₁ ⊔ N) (L := H₁) le_sup_left hsup_le]
    exact dvd_mul_of_dvd_right hdvd _
  have hmap_le : P₁.map π ≤ Pb := by
    rw [← hH₁map]
    exact Subgroup.map_mono hP₁.le
  have hmap_pg : IsPGroup p (P₁.map π) := hP₁.isPGroup.map π
  have himg_syl : IsSylowOf p (P₁.map π) Pb := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hmap_le, hmap_pg, by rw [hrel]; exact hnotdvd⟩
  exact (himg_syl.eq_of_le hmap_le le_rfl hPb).symm

private theorem r920l2_exists_isSylowOf_comap_map_eq {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] (N : Subgroup Γ) [N.Normal] {Pb : Subgroup (Γ ⧸ N)}
    (hPb : IsPGroup p Pb) {B₁ : Subgroup Γ} (hB₁ : B₁ ≤ Pb.comap (QuotientGroup.mk' N))
    (hB₁pg : IsPGroup p B₁) :
    ∃ P₁ : Subgroup Γ, IsSylowOf p P₁ (Pb.comap (QuotientGroup.mk' N)) ∧ B₁ ≤ P₁ ∧
      P₁.map (QuotientGroup.mk' N) = Pb := by
  obtain ⟨Q, hQle⟩ :=
    (hB₁pg.comap_subtype (K := Pb.comap (QuotientGroup.mk' N))).exists_le_sylow
  have hP₁ : IsSylowOf p ((Q : Subgroup (Pb.comap (QuotientGroup.mk' N))).map
      (Pb.comap (QuotientGroup.mk' N)).subtype) (Pb.comap (QuotientGroup.mk' N)) := ⟨Q, rfl⟩
  refine ⟨_, hP₁, ?_, r920l2_map_eq_of_isSylowOf_comap N hPb hP₁⟩
  intro x hx
  exact ⟨⟨x, hB₁ hx⟩, hQle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem r920l2_normalizer_le_img9_of_pGroup {D : Data G} {L H : Subgroup G}
    (hLH : L ≤ H) {p : ℕ} [Fact p.Prime] {Pb : Subgroup (F09.Hbar9 H)} (hPb : IsPGroup p Pb)
    {B : Subgroup G} (hBL : B ≤ L) (hBcard : Nat.card B = p) (hBmem : B ∈ uniqueSet D.M)
    (hBimg : F09.img9 H B ≤ Pb) :
    normalizer (Pb : Set (F09.Hbar9 H)) ≤ F09.img9 H (H ⊓ D.M) := by
  classical
  have hBH : B ≤ H := hBL.trans hLH
  let N : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  haveI hNnorm : N.Normal := CFSG.pPrimeCore_normal
  let π : ↥H →* F09.Hbar9 H := QuotientGroup.mk' N
  let H₁ : Subgroup ↥H := Pb.comap π
  have hB₁ : B.subgroupOf H ≤ H₁ := fun x hx => hBimg (Subgroup.mem_map_of_mem π hx)
  have hB₁card : Nat.card (B.subgroupOf H) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv, hBcard]
  have hB₁pg : IsPGroup p (B.subgroupOf H) :=
    IsPGroup.of_card (n := 1) (by rw [hB₁card, pow_one])
  obtain ⟨P₁, hP₁syl, hB₁le, hPmap⟩ :=
    r920l2_exists_isSylowOf_comap_map_eq N hPb hB₁ hB₁pg
  have hP₁Gpg : IsPGroup p (P₁.map H.subtype) := hP₁syl.isPGroup.map H.subtype
  have hBmap : (B.subgroupOf H).map H.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hBH]
  have hBP₁G : B ≤ P₁.map H.subtype := by
    rw [← hBmap]
    exact Subgroup.map_mono hB₁le
  have hP₁GM : P₁.map H.subtype ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hBmem hBP₁G hP₁Gpg
  have hP₁Guniq : P₁.map H.subtype ∈ uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hBmem hBP₁G hP₁GM
  have hNormP₁G : normalizer (P₁.map H.subtype : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hP₁Guniq
  have hNormLe : normalizer (P₁ : Set ↥H) ≤ (H ⊓ D.M).subgroupOf H := by
    intro n hn
    have hn' : (n : G) ∈ normalizer (P₁.map H.subtype : Set G) :=
      Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem H.subtype hn)
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨n.2, hNormP₁G hn'⟩)
  have hmap_le_img : (normalizer (P₁ : Set ↥H)).map π ≤ F09.img9 H (H ⊓ D.M) := by
    show (normalizer (P₁ : Set ↥H)).map π ≤ ((H ⊓ D.M).subgroupOf H).map π
    exact Subgroup.map_mono hNormLe
  have hfrat : normalizer (Pb : Set (F09.Hbar9 H)) ≤
      (normalizer (P₁ : Set ↥H)).map π :=
    normalizer_le_map_normalizer_of_sylow N hPmap hP₁syl
  exact hfrat.trans hmap_le_img

private theorem r920l2_map_subtype_le_img9 {L Y H : Subgroup G} (hY : Opp 3 Y = L)
    {E : Subgroup (F09.Lbar9 Y H)} (hE : E ≤ xbar9 Y H) :
    E.map (F09.img9 H (F09.L9 Y H)).subtype ≤ F09.img9 H L := by
  let Kb : Subgroup (F09.Hbar9 H) := F09.img9 H (F09.L9 Y H)
  have hE' : E ≤ (F09.img9 H (Opp 3 Y)).subgroupOf Kb := by
    rw [xbar9] at hE
    exact hE
  have h1 : E.map Kb.subtype ≤ ((F09.img9 H (Opp 3 Y)).subgroupOf Kb).map Kb.subtype :=
    Subgroup.map_mono hE'
  rw [Subgroup.subgroupOf_map_subtype] at h1
  rw [← hY]
  exact h1.trans inf_le_left

private theorem r920l2_normalizer_le_of_card_three {D : Data G} {L D₃ A : Subgroup G} {n : ℕ}
    (c : R920CfgL2 D L D₃ A n) {Y H : Subgroup G} (hY : Opp 3 Y = L) (hLH : L ≤ H)
    {E : Subgroup (F09.Lbar9 Y H)} (hE : E ≤ xbar9 Y H) (hEcard : Nat.card E = 3) :
    normalizer (E : Set (F09.Lbar9 Y H)) ≤ wbar9 D Y H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Kb : Subgroup (F09.Hbar9 H) := F09.img9 H (F09.L9 Y H)
  have hEbL : E.map Kb.subtype ≤ F09.img9 H L := r920l2_map_subtype_le_img9 hY hE
  have hEbc : Nat.card (E.map Kb.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective Kb.subtype_injective, hEcard]
  have hEbpg : IsPGroup 3 (E.map Kb.subtype) :=
    IsPGroup.of_card (n := 1) (by rw [hEbc, pow_one])
  obtain ⟨B, hBL, hBcard, hBimg⟩ :=
    exists_le_card_eq_img9_eq hLH (isPGroup_ker_toImg9_of_isL2 hLH c.isL2)
      Nat.prime_three (by norm_num) hEbpg hEbL
  have hN := r920l2_normalizer_le_img9_of_pGroup hLH (p := 3) hEbpg hBL
    (hBcard.trans hEbc) (r920l2_mem_uniqueSet_of_card_three c hBL (hBcard.trans hEbc))
    (le_of_eq hBimg)
  intro q hq
  rw [wbar9, Subgroup.mem_subgroupOf]
  exact hN (Subgroup.le_normalizer_map Kb.subtype (Subgroup.mem_map_of_mem Kb.subtype hq))

private theorem r920l2_normalizer_le_of_isPGroup_card_A {D : Data G} {L D₃ A : Subgroup G}
    {n : ℕ} (c : R920CfgL2 D L D₃ A n) {Y H : Subgroup G} (hY : Opp 3 Y = L) (hLH : L ≤ H)
    (hA2 : Nat.card A ≠ 2) {B : Subgroup (F09.Lbar9 Y H)} (hBX : B ≤ xbar9 Y H)
    (hBcard : Nat.card B = Nat.card A) {P : Subgroup (F09.Lbar9 Y H)}
    (hP : IsPGroup (Nat.card A) ↥P) (hBP : B ≤ P) :
    normalizer (P : Set (F09.Lbar9 Y H)) ≤ wbar9 D Y H := by
  haveI : Fact (Nat.card A).Prime := ⟨c.A_prime⟩
  let Kb : Subgroup (F09.Hbar9 H) := F09.img9 H (F09.L9 Y H)
  have hBbL : B.map Kb.subtype ≤ F09.img9 H L := r920l2_map_subtype_le_img9 hY hBX
  have hBbc : Nat.card (B.map Kb.subtype) = Nat.card A := by
    rw [Subgroup.card_map_of_injective Kb.subtype_injective, hBcard]
  have hBbpg : IsPGroup (Nat.card A) (B.map Kb.subtype) :=
    IsPGroup.of_card (n := 1) (by rw [hBbc, pow_one])
  have hPbpg : IsPGroup (Nat.card A) (P.map Kb.subtype) := hP.map Kb.subtype
  obtain ⟨B', hB'L, hB'card, hB'img⟩ :=
    exists_le_card_eq_img9_eq hLH (isPGroup_ker_toImg9_of_isL2 hLH c.isL2)
      c.A_prime hA2 hBbpg hBbL
  have hB'mem : B' ∈ uniqueSet D.M :=
    r920l2_mem_uniqueSet_of_card_eq_card_A c hA2 hB'L (hB'card.trans hBbc)
  have hN := r920l2_normalizer_le_img9_of_pGroup hLH (p := Nat.card A) hPbpg hB'L
    (hB'card.trans hBbc) hB'mem ((le_of_eq hB'img).trans (Subgroup.map_mono hBP))
  intro q hq
  rw [wbar9, Subgroup.mem_subgroupOf]
  exact hN (Subgroup.le_normalizer_map Kb.subtype (Subgroup.mem_map_of_mem Kb.subtype hq))

theorem kCfgL2Odd_of_hyp97 {D : Data G} {L D₃ A : Subgroup G} {n : ℕ}
    (c : R920CfgL2 D L D₃ A n) {Y H S : Subgroup G} (h97 : F09.Hyp97 D Y H D₃ S)
    (hY : Opp 3 Y = L) (hSH : IsSylowOf 2 S H) :
    KCfgL2Odd (PartOne.Section9.xbar9 Y H) (PartOne.Section9.wbar9 D Y H)
      ((F09.img9 H S).subgroupOf (F09.img9 H (F09.L9 Y H))) n (Nat.card A) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYH : Y ≤ H := h97.1.2.1.1
  have hLH : L ≤ H := by
    rw [← hY]
    exact (F09.opp_le_self 3 Y).trans hYH
  have hXM : Opp 3 Y ≤ D.M := by
    rw [hY]
    exact CFSG.Open.IsSubnormal.le c.mem.1
  have hSM : S ≤ D.M := h97.2.2.2.le.trans h97.1.1.1
  have hAodd : Odd (2 ^ n - 1) := by
    refine Nat.Even.sub_odd (m := 2 ^ n) (n := 1) (Nat.one_le_pow n 2 (by norm_num)) ?_
      odd_one
    exact Even.pow_of_ne_zero (a := 2) (n := n) (by norm_num : Even 2)
      (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num) c.five_le))
  have hA2 : Nat.card A ≠ 2 := Odd.ne_two_of_dvd_nat hAodd c.A_dvd
  refine ⟨isL2_bar2_xbar9 hY hLH c.isL2, c.odd, c.five_le, c.A_prime, c.A_dvd, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [xbar9, wbar9]
    exact Subgroup.subgroupOf_mono _
      (Subgroup.map_mono (Subgroup.subgroupOf_mono H
        (le_inf ((F09.opp_le_self 3 Y).trans hYH) hXM)))
  · rw [wbar9]
    exact Subgroup.subgroupOf_mono _
      (Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_inf hSH.le hSM)))
  · exact isSylowOf_two_img9_subgroupOf hYH hSH
  · intro E hE hEcard
    exact r920l2_normalizer_le_of_card_three c hY hLH hE hEcard
  · intro B hBX hBcard P hPpg hBP
    exact r920l2_normalizer_le_of_isPGroup_card_A c hY hLH hA2 hBX hBcard hPpg hBP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
