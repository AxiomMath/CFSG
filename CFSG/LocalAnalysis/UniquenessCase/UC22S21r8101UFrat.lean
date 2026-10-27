module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCnt
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_exists_mem_normalizer (u : U4X D L K n)
    (hsp : IsStronglyPEmbedded n D.M) (hfour : 4 ≤ CFSG.Open.pRank n D.M) {R B : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) (hBR : B ≤ R)
    (hBel : IsElemAbelian (2 ^ n - 1) B) (hΩ : ∀ x ∈ R, x ^ (2 ^ n - 1) = 1 → x ∈ B)
    (hC1 : CFSG.Open.pRank n (centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1) :
    ∃ y ∈ normalizer (B : Set G) ⊓ D.M, orderOf y = n := by
  have hn : n.Prime := u.prime_n
  have hr := u.prime_r
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : Fact (2 ^ n - 1).Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : n ≠ 2 := by rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  obtain ⟨hcomm, hinf, -, -, -, hXn, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  haveI := hXn
  have hRH : barImage D.M R ≤ barImage D.M L ⊔ barImage D.M K ⊔
      centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
    fun β hβ => by
      obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ := u.u81_decomp hR hβ
      exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hx₀.2))
        (mem_sup_left (mem_sup_right hx₁.2))) (mem_sup_right hc.2)
  obtain ⟨E, -, -, hEel, hEc⟩ := u.u81_exists_elem hsp hfour
  have hEH : ¬ E ≤ barImage D.M L ⊔ barImage D.M K ⊔
      centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
    intro hle
    have hrk := CFSG.SectionRank.le_pRank hn.one_lt hle hEel hEc
    rw [PartTwo.s13_pRank_sup_eq_add hn le_rfl hXC,
      PartTwo.s13_pRank_sup_eq_add hn (fun y hy => Subgroup.mem_centralizer_iff.2
        fun x hx => hcomm x hx y hy) hinf,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage D.M L),
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage D.M K)] at hrk
    have h₀ := pRank_le_one_of_isL2_or_isSz (u4x_shape_barImage u.hL u.shape) hn hn2
    have h₁ := pRank_le_one_of_isL2_or_isSz (u4x_shape_barImage u.hK u.shapeK) hn hn2
    omega
  obtain ⟨e, heE, heH⟩ := SetLike.not_le_iff_exists.1 hEH
  obtain ⟨S, hS⟩ := (u4x_isSylowOf_barImage hR).of_le hRH le_top
  obtain ⟨x, hxo, hxN⟩ := CFSG.RankThree.PartOne.KFSU5.exists_orderOf_eq_normalizer_sylow_of_pow
    _ S (hEel.2 e heE) heH
  rw [hS] at hxN
  have hN2 : ¬ (2 ^ n - 1) ∣ Nat.card (CFSG.pCore 2 ↥D.M) := by
    intro hd
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M))
    rw [hj] at hd
    exact u.r_ne_two ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  have hlift := CFSG.GroupTheory.normal_coprime_quotient_normalizer (2 ^ n - 1)
    (CFSG.pCore 2 ↥D.M) hN2 (R.subgroupOf D.M) hR.isPGroup.comap_subtype
  have hx := orderOf_dvd_natCard
    (⟨x, hxN⟩ : ↥(normalizer ((barImage D.M R : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))))
  rw [Subgroup.orderOf_mk, hxo] at hx
  have hdvd : n ∣ Nat.card (normalizer ((R.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M)) := by
    refine Dvd.dvd.trans ?_ (Subgroup.card_map_dvd _ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)))
    rw [hlift]
    exact hx
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' n hdvd
  have hyR : ((y : ↥D.M) : G) ∈ normalizer (R : Set G) := by
    have h1 := Subgroup.le_normalizer_map D.M.subtype (Subgroup.mem_map_of_mem D.M.subtype y.2)
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hR.le] at h1
  refine ⟨(y : ↥D.M), ⟨Subgroup.mem_normalizer_fintype fun b hb => ?_, (y : ↥D.M).2⟩, ?_⟩
  · refine hΩ _ ((mem_normalizer_iff.1 hyR b).1 (hBR hb)) ?_
    rw [conj_pow, hBel.2 b hb, mul_one, mul_inv_cancel]
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hyo]

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
