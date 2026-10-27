module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Bar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UTr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCnt
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

namespace U4P

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem u81_inner_right (u : U4P D L K n p) {e : Bar2 D.M} (he : e ∈ commutator (Bar2 D.M))
    (h₀ : ∃ x₀ ∈ barImage D.M L, ∀ f ∈ barImage D.M L, e * f * e⁻¹ = x₀ * f * x₀⁻¹) :
    ∃ x₁ ∈ barImage D.M K, ∀ f ∈ barImage D.M K, e * f * e⁻¹ = x₁ * f * x₁⁻¹ := by
  obtain ⟨-, hinf, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  haveI := u.isMulCommutative_outer
  have hbot : barImage D.M L ≠ ⊥ := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv u.hL
    haveI : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) u.hL2
    haveI : Nontrivial ↥(barImage D.M L) := e.symm.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hcases : ∀ x : Bar2 D.M,
      (x ∈ normalizer (barImage D.M L : Set (Bar2 D.M)) ∧
        x ∈ normalizer (barImage D.M K : Set (Bar2 D.M))) ∨
      ((∀ f ∈ barImage D.M L, x * f * x⁻¹ ∈ barImage D.M K) ∧
        ∀ f ∈ barImage D.M K, x * f * x⁻¹ ∈ barImage D.M L) := by
    intro x
    obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective D.M x
    rcases u.conj_cases m.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨uc22ine229_mk_mem_normalizer h1, uc22ine229_mk_mem_normalizer h2⟩
    · exact Or.inr ⟨fun f hf => u4x_conj_mem_barImage h1 hf,
        fun f hf => u4x_conj_mem_barImage h2 hf⟩
  obtain ⟨m, hm, hmK⟩ := u.mem_K
  exact u81_inner_of_transfer hinf hbot hcases (t := uc22p21cPi D.M ⟨m, hm⟩)
    (fun f hf => u4x_conj_mem_barImage hmK.symm hf) he h₀

theorem u81_exists_elem (u : U4P D L K n p) (hsp : IsStronglyPEmbedded p D.M)
    (hfour : 4 ≤ CFSG.Open.pRank p D.M) :
    ∃ E : Subgroup (Bar2 D.M), E ≤ commutator (Bar2 D.M) ∧
      E ≤ normalizer (barImage D.M L : Set (Bar2 D.M)) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 4 := by
  have hn := u.prime_p
  haveI : Fact p.Prime := ⟨hn⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 := u.p_ne_two
  obtain ⟨S, hSM, hSM'⟩ :=
    UC6.sylow_le_commutator_map_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hsp
  obtain ⟨A, -, hAel, hAc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hn hfour
  have h4 : 4 ≤ CFSG.Open.pRank p (S : Subgroup G) := by
    rw [(CFSG.SectionRank.pRank_sylow S).1]
    exact CFSG.SectionRank.le_pRank hn.one_lt le_top hAel hAc
  obtain ⟨E, hES, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hn h4
  have hEM : E ≤ D.M := hES.trans hSM
  have hdisj : Disjoint (E.subgroupOf D.M) (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.disjoint_of_ne _ _ hn2 _ _ hEel.isPGroup.comap_subtype CFSG.pCore_isPGroup
  refine ⟨barImage D.M E, ?_, ?_, (hEel.subgroupOf D.M).map _, ?_⟩
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
    obtain ⟨m', hm', hmm'⟩ := Subgroup.mem_map.1 (hSM' (hES hm))
    obtain rfl : m' = m := Subtype.ext hmm'
    have hcm : (commutator ↥D.M).map (uc22p21cPi D.M) ≤ commutator (Bar2 D.M) := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hcm (Subgroup.mem_map_of_mem _ hm')
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
    refine uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd u.hc2 m.2 ?_)
    exact (hn.odd_of_ne_two hn2).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hEel.2 _ hm))
  · rw [barImage, UC6S846.card_map_of_disjoint_ker _ _ hdisj, ← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv

theorem u81_exists_mem_centralizer (u : U4P D L K n p) (hsp : IsStronglyPEmbedded p D.M)
    (hfour : 4 ≤ CFSG.Open.pRank p D.M) :
    ∃ c ∈ centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)),
      orderOf c = p := by
  have hn := u.prime_p
  haveI : Fact p.Prime := ⟨hn⟩
  have hn2 := u.p_ne_two
  obtain ⟨hcomm, hinf, -, -, -, -, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨E, hE', hEN, hEel, hEc⟩ := u.u81_exists_elem hsp hfour
  let χ : ↥E →* Outer ↥(barImage D.M L) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _)).comp
      ((barImage D.M L).normalizerMonoidHom.comp (Subgroup.inclusion hEN))
  have hker : p ^ 3 ≤ Nat.card χ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range χ
    rw [hEc] at h1
    have h2 : Nat.card χ.range ≤ p := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hn).1 (Dvd.intro_left _ h1)
      have hjn : p ^ j ∣ n := by
        rw [← hj]
        exact (Subgroup.card_subgroup_dvd_card _).trans (card_outer_dvd_of_isL2 u.isL2_barImage)
      have hj1 : j ≤ 1 := by
        by_contra h
        exact u.not_sq_dvd_n ((pow_dvd_pow p (by omega)).trans hjn)
      rw [hj]
      exact (Nat.pow_le_pow_right hn.pos hj1).trans_eq (pow_one p)
    have h3 : p ^ 3 * p ≤ Nat.card χ.ker * p := by
      calc p ^ 3 * p = Nat.card χ.ker * Nat.card χ.range := by rw [h1]; ring
        _ ≤ Nat.card χ.ker * p := Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h3 hn.pos
  by_contra hno
  have hle : χ.ker.map E.subtype ≤ barImage D.M L ⊔ barImage D.M K := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨y, hy, h₀⟩ := u81_exists_conj_of_outer (hEN e.2) (MonoidHom.mem_ker.1 he)
    obtain ⟨x₁, hx₁, h₁⟩ := u.u81_inner_right (hE' e.2) ⟨y, hy, h₀⟩
    have hcC := u4x_mul_inv_mem_centralizer hcomm hy hx₁ h₀ h₁
    have hcn : ((e : Bar2 D.M) * (y * x₁)⁻¹) ^ p = 1 := by
      have h1 : ((e : Bar2 D.M) * (y * x₁)⁻¹) ^ p = ((y * x₁)⁻¹) ^ p := by
        rw [(((u4x_commute_of_conj hy h₀).mul_right
          (u4x_commute_of_conj hx₁ h₁)).inv_right).mul_pow, hEel.2 _ e.2, one_mul]
      have h2 : ((e : Bar2 D.M) * (y * x₁)⁻¹) ^ p ∈ (barImage D.M L ⊔ barImage D.M K) ⊓
          centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) :
            Set (Bar2 D.M)) := by
        refine ⟨?_, pow_mem hcC p⟩
        rw [h1]
        exact pow_mem (inv_mem (mul_mem (mem_sup_left hy) (mem_sup_right hx₁))) p
      rw [hXC, Subgroup.mem_bot] at h2
      exact h2
    have hc1 : (e : Bar2 D.M) * (y * x₁)⁻¹ = 1 := by
      by_contra hc1
      exact hno ⟨_, hcC, orderOf_eq_prime hcn hc1⟩
    show (e : Bar2 D.M) ∈ barImage D.M L ⊔ barImage D.M K
    rw [mul_inv_eq_one.1 hc1]
    exact mul_mem (mem_sup_left hy) (mem_sup_right hx₁)
  have hel : IsElemAbelian p (χ.ker.map E.subtype) := hEel.mono (Subgroup.map_subtype_le _)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hel.isPGroup
  have hj3 : 3 ≤ j := by
    rw [Subgroup.card_map_of_injective E.subtype_injective] at hj
    refine (Nat.pow_le_pow_iff_right hn.one_lt).1 ?_
    rw [← hj]
    exact hker
  have hrk := CFSG.SectionRank.le_pRank hn.one_lt hle hel hj
  rw [PartTwo.s13_pRank_sup_eq_add hn (fun y hy => Subgroup.mem_centralizer_iff.2
      fun x hx => hcomm x hx y hy) hinf,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage D.M L),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage D.M K)] at hrk
  have h₀ := pRank_le_one_of_isL2_or_isSz (Or.inl u.isL2_barImage) hn hn2
  have h₁ := pRank_le_one_of_isL2_or_isSz (Or.inl u.symm.isL2_barImage) hn hn2
  omega

theorem u81_exists_mem_normalizer (u : U4P D L K n p) {r : ℕ} (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) (hsp : IsStronglyPEmbedded p D.M) (hfour : 4 ≤ CFSG.Open.pRank p D.M)
    {R B : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) (hBR : B ≤ R)
    (hBel : IsElemAbelian r B) (hΩ : ∀ x ∈ R, x ^ r = 1 → x ∈ B)
    (hC1 : CFSG.Open.pRank p (centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1) :
    ∃ y ∈ normalizer (B : Set G) ⊓ D.M, orderOf y = p := by
  have hn := u.prime_p
  haveI : Fact p.Prime := ⟨hn⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 := u.p_ne_two
  obtain ⟨hcomm, hinf, -, -, -, hXn, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  haveI := hXn
  have hRH : barImage D.M R ≤ barImage D.M L ⊔ barImage D.M K ⊔
      centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
    fun β hβ => by
      obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ := u.u81_decomp hr hrp hR hβ
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
    have h₀ := pRank_le_one_of_isL2_or_isSz (Or.inl u.isL2_barImage) hn hn2
    have h₁ := pRank_le_one_of_isL2_or_isSz (Or.inl u.symm.isL2_barImage) hn hn2
    omega
  obtain ⟨e, heE, heH⟩ := SetLike.not_le_iff_exists.1 hEH
  obtain ⟨S, hS⟩ := (u4x_isSylowOf_barImage hR).of_le hRH le_top
  obtain ⟨x, hxo, hxN⟩ := CFSG.RankThree.PartOne.KFSU5.exists_orderOf_eq_normalizer_sylow_of_pow
    _ S (hEel.2 e heE) heH
  rw [hS] at hxN
  have hN2 : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥D.M) := by
    intro hd
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M))
    rw [hj] at hd
    exact u.r_ne_two hr hrp
      ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  have hlift := CFSG.GroupTheory.normal_coprime_quotient_normalizer r
    (CFSG.pCore 2 ↥D.M) hN2 (R.subgroupOf D.M) hR.isPGroup.comap_subtype
  have hx := orderOf_dvd_natCard
    (⟨x, hxN⟩ : ↥(normalizer ((barImage D.M R : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))))
  rw [Subgroup.orderOf_mk, hxo] at hx
  have hdvd : p ∣ Nat.card (normalizer ((R.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M)) := by
    refine Dvd.dvd.trans ?_ (Subgroup.card_map_dvd _ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)))
    rw [hlift]
    exact hx
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hyR : ((y : ↥D.M) : G) ∈ normalizer (R : Set G) := by
    have h1 := Subgroup.le_normalizer_map D.M.subtype (Subgroup.mem_map_of_mem D.M.subtype y.2)
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hR.le] at h1
  refine ⟨(y : ↥D.M), ⟨Subgroup.mem_normalizer_fintype fun b hb => ?_, (y : ↥D.M).2⟩, ?_⟩
  · refine hΩ _ ((mem_normalizer_iff.1 hyR b).1 (hBR hb)) ?_
    rw [conj_pow, hBel.2 b hb, mul_one, mul_inv_cancel]
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hyo]

end U4P

end CFSG.LocalAnalysis.UniquenessCase.UC22
