module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneGamma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_8_3At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  R19_3At D V₀ V p L K h → R19_8_1At D V₀ V p L K h → R19_8_2At D V₀ V p L K h →
    ((2 + mSub V₀ : ℕ) : ℕ∞) < gammaN 2 D.M V →
    (∀ v ∈ V, (∀ w ∈ E3.wClos V 2 D.T, ⁅v, w⁆ ∈ V₀) →
      v ∈ centralizer (E3.wClos V 2 D.T : Set G)) →
      ⁅E3.wClos V 0 D.T, V⁆ = ⊥

theorem nineteen_eight_three (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h126 : R126 D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h3 : R19_3At D V₀ V p L K h) (h4 : R19_4At D V₀ V p L K h)
    (h81 : R19_8_1At D V₀ V p L K h) (h82 : R19_8_2At D V₀ V p L K h)
    (hgap : Gap19_8_3At D V₀ V p L K h) : R19_8_3At D V₀ V p L K h := by
  refine ⟨?_, nineteen_eight_three_upper D h h4⟩
  by_contra hγ
  have hlt : ((2 + mSub V₀ : ℕ) : ℕ∞) < gammaN 2 D.M V := not_le.1 hγ
  have hrk : ∀ q ∈ D.sig, 3 ≤ CFSG.pRank q D.M := fun q hq => by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hx.three_le q hq
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hm4 : mBar D.M V₀ V h.hyp.isElemAbelian = 4 := h82
  have hH := (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp.hyp125 hV₀).hyp6H
  have hr2 : ((2 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) h81.1
  have h63 := six_three hH.hyp62 D.sylowM.le hr2 hlt
  have hN0 : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    fifteen_thirteen_a D (r129_1_of_r127 D h127) h61 hx.sig_nonempty hrk h.hyp.hyp125
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hgap h3 h81 h82 hlt h63.2))
  have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hkm : 0 + D.k < mBar D.M V₀ V h.hyp.isElemAbelian := by omega
  have hkr : ((0 + D.k : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) h81.1
  have hno : ∀ g : G, ¬ InCalO1 (0 + D.k) D.M V₀ V g := by
    intro g hg
    have hmem : conjSubgroup V g ∈ calO (0 + D.k) D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [h81.2.1 (0 + D.k) hkm] at hmem
    exact hmem
  exact S18.not_normalizer_wClos_le_of_no_calO1 D hx h61 h127 h1114 h126 h.hyp.hyp125 hV₀
    hkr hkm hno hN0

theorem s19_one_le_pRank_of_five_mem_pi (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h5 : R19_5At D V₀ V p L K h) {z : G}
    (hz : z ∈ V) (hz0 : z ∉ V₀) (hpi : 5 ∈ piSet (centModInM D V₀ z)) :
    1 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({z} : Set G)) := by
  have hHdvd : 5 ∣ Nat.card ↥(centModInM D V₀ z) := hpi.2
  obtain ⟨Q, hQ⟩ := h5 z hz hz0
  have hQdvd : 5 ∣ Nat.card ↥Q := Q.pow_dvd_card_of_pow_dvd_card (n := 1) (by simpa using hHdvd)
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 5 hQdvd
  let x : ↥(centModInM D V₀ z) := q.1
  have hxord : orderOf ((x : ↥(centModInM D V₀ z)) : G) = 5 := by
    rw [Subgroup.orderOf_coe x]
    exact (Subgroup.orderOf_coe q).trans hq
  have hxC : ((x : ↥(centModInM D V₀ z)) : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    hQ (Subgroup.mem_map_of_mem (centModInM D V₀ z).subtype q.2)
  have hxM : ((x : ↥(centModInM D V₀ z)) : G) ∈ D.M := x.2.1
  have hmem : ((x : ↥(centModInM D V₀ z)) : G) ∈ D.M ⊓ centralizer ({z} : Set G) :=
    ⟨hxM, hxC⟩
  refine CFSG.SectionRank.le_pRank (p := 5) (H := D.M ⊓ centralizer ({z} : Set G))
    (E := Subgroup.zpowers ((x : ↥(centModInM D V₀ z)) : G)) (by norm_num)
    (Subgroup.zpowers_le.2 hmem) (CFSG.Open.isElemAbelian_zpowers (p := 5) ?_) ?_
  · rw [← hxord]
    exact pow_orderOf_eq_one _
  · rw [Nat.card_zpowers, hxord, pow_one]

theorem nineteen_eight_four (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hSg : UC6S846.SigmaStd D) (h3 : R19_3At D V₀ V p L K h)
    (h5 : R19_5At D V₀ V p L K h) (h83 : R19_8_3At D V₀ V p L K h) :
    R19_8_4At D V₀ V p L K h := by
  by_contra hno
  have hall : ∀ v ∈ V, v ∉ V₀ → 5 ∈ piSet (centModInM D V₀ v) := by
    intro v hv hv0
    by_contra hpi
    exact hno ⟨v, hv, hv0, hpi⟩
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC h.hyp.hL.1
  have hsp : IsStronglyPEmbedded 5 D.M := UC6S846.sp_of_mem_sig hSg hns (h.p_eq ▸ h.hyp.hp)
  have hlt : ((2 + mSub V₀ : ℕ) : ℕ∞) < gammaN 2 D.M V := by
    refine s16n9b_lt_gammaN_of_good (P := {5}) h.hyp.isElemAbelian
      h.hyp.hyp125.pairFacts.le_normalizer ?_ 2 (2 + mSub V₀) ?_
    · intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact ⟨by norm_num, hsp⟩
    · intro t htM _ _ W hWV _ hWt
      obtain ⟨w, hwW, hw1⟩ := s16n9b_exists_commutator_ne_one hWt
      have hwmem : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
      refine ⟨_, hwmem, hw1, 5, Set.mem_singleton 5, ?_⟩
      by_cases hw0 : w⁻¹ * t⁻¹ * w * t ∈ V₀
      · exact s19_one_le_pRank_of_mem_V0 D h h3 hw0 hw1
      · have hzV : w⁻¹ * t⁻¹ * w * t ∈ V :=
          s16n9b_commElt_le hWV (h.hyp.hyp125.pairFacts.le_normalizer htM) hwmem
        exact s19_one_le_pRank_of_five_mem_pi D h h5 hzV hw0 (hall _ hzV hw0)
  exact absurd h83.1 (not_le.2 hlt)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
