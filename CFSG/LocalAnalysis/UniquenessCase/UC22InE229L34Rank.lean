module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Core
public import CFSG.RankThree.OddKernel.RankTwoPowerStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_l34_pRank_le {M Y N : Subgroup G} (hYM : Y ≤ M)
    (hnorm : M ≤ normalizer (Y : Set G)) (hN : N ≤ M)
    (hMN : ∀ m ∈ M, ∃ h ∈ N, ∃ y ∈ Y, m = h * y)
    (hN9 : ∀ R : Subgroup G, R ≤ N → IsPGroup 3 R → Nat.card R ≤ 3 ^ 2) :
    CFSG.Open.pRank 3 M ≤ CFSG.Open.pRank 3 Y + 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (Y.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 hnorm
  let φ : ↥N →* ↥M ⧸ Y.subgroupOf M :=
    (QuotientGroup.mk' (Y.subgroupOf M)).comp (Subgroup.inclusion hN)
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨h, hh, y, hy, hm⟩ := hMN m m.2
    refine ⟨⟨h, hh⟩, ?_⟩
    change ((⟨h, hN hh⟩ : ↥M) : ↥M ⧸ Y.subgroupOf M) = (m : ↥M ⧸ Y.subgroupOf M)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : h⁻¹ * (m : G) = y := by rw [hm]; group
    simpa [this] using hy
  have himage : ∀ E : Subgroup ↥M, IsPGroup 3 E →
      Nat.card (E.map (QuotientGroup.mk' (Y.subgroupOf M))) ≤ 9 := by
    intro E hE
    obtain ⟨Q, hQ⟩ := (hE.map (QuotientGroup.mk' (Y.subgroupOf M))).exists_le_sylow
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hφ 3 Q
    have h1 : Nat.card (E.map (QuotientGroup.mk' (Y.subgroupOf M))) ≤ Nat.card Q.toSubgroup :=
      Subgroup.card_le_of_le hQ
    have h2 : Nat.card Q.toSubgroup ≤ Nat.card P.toSubgroup := by
      rw [← hP, Sylow.coe_mapSurjective]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ φ)
    have h3 : Nat.card P.toSubgroup ≤ 9 := by
      have := hN9 (P.map N.subtype) (Subgroup.map_subtype_le _) (P.isPGroup'.map N.subtype)
      rwa [Subgroup.card_map_of_injective N.subtype_injective] at this
    omega
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEM hE => ?_
  have hEY : Nat.card ↥(E ⊓ Y) ≤ 3 ^ CFSG.Open.pRank 3 Y := by
    have hp : IsPGroup 3 ↥(E ⊓ Y) := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (hE.2 x x.2.1)⟩
    obtain ⟨j, hj⟩ := hp.exists_card_eq
    rw [hj]
    exact Nat.pow_le_pow_right (by norm_num)
      (CFSG.SectionRank.le_pRank (by norm_num) inf_le_right
        (CFSG.RankThree.OddKernel.isElemAbelian_inf_left hE Y) hj)
  have hEp : IsPGroup 3 (E.subgroupOf M) := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (Subtype.ext (hE.2 x x.2))⟩
  have h1 := Subgroup.relIndex_mul_card (QuotientGroup.mk' (Y.subgroupOf M)).ker (E.subgroupOf M)
  rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk'] at h1
  have h2 : Y.subgroupOf M ⊓ E.subgroupOf M = (Y ⊓ E).subgroupOf M := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYM)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, inf_comm] at h1
  calc Nat.card E = _ := h1.symm
    _ ≤ 9 * 3 ^ CFSG.Open.pRank 3 Y := Nat.mul_le_mul (himage _ hEp) hEY
    _ = 3 ^ (CFSG.Open.pRank 3 Y + 2) := by ring

theorem uc22ine229_l34_decomp (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {Y : Subgroup G} (hY : Y ∈ calC k.M) {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hXc : Nat.card X = q) (hq1 : CFSG.Open.pRank q Y ≤ 1)
    (hH : Sec7Core4.Config k (normalizer (X : Set G)))
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥(normalizer (X : Set G)) ⧸
        CFSG.pPrimeCore k.p ↥(normalizer (X : Set G))))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) :
    k.M ≤ normalizer (Y : Set G) ∧
      (∀ m ∈ k.M, ∃ h ∈ normalizer (X : Set G) ⊓ k.M, ∃ y ∈ Y, m = h * y) ∧
      Group.IsSolvable ↥(normalizer (X : Set G) ⊓ k.M) ∧
      ∀ R : Subgroup G, R ≤ normalizer (X : Set G) → IsPGroup 3 R → Nat.card R ≤ 3 ^ 2 := by
  obtain ⟨hsol, h9⟩ := uc22ine229_l34_solvable hG3 hRee k hp3 hH hF
  have hnorm := uc22ine229_l34_normalizes hY hXY hq (by omega) hXc hsol
  exact ⟨hnorm, uc22ine229_l34_eq_mul hY.1.le hnorm hXY hq (by omega) hXc hq1, hsol, h9⟩

theorem uc22ine229_l34_false_of_pRank_le_one (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    (h4 : 4 ≤ CFSG.Open.pRank k.p k.M) {Y : Subgroup G} (hY : Y ∈ calC k.M) {X : Subgroup G}
    (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hXc : Nat.card X = q)
    (hq1 : CFSG.Open.pRank q Y ≤ 1) (h31 : CFSG.Open.pRank 3 Y ≤ 1)
    (hH : Sec7Core4.Config k (normalizer (X : Set G)))
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥(normalizer (X : Set G)) ⧸
        CFSG.pPrimeCore k.p ↥(normalizer (X : Set G))))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) : False := by
  obtain ⟨hnorm, hmul, -, h9⟩ := uc22ine229_l34_decomp hG3 hRee k hp3 hY hXY hq hq5 hXc hq1 hH hF
  have h := uc22ine229_l34_pRank_le hY.1.le hnorm
    (inf_le_right : normalizer (X : Set G) ⊓ k.M ≤ k.M) hmul
    fun R hR hR3 => h9 R (hR.trans inf_le_left) hR3
  rw [hp3] at h4
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
