module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UTr
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem u81_exists_conj_of_outer {F : Subgroup Q} {β : Q} (hβ : β ∈ normalizer (F : Set Q))
    (h : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥F)
      (F.normalizerMonoidHom ⟨β, hβ⟩) = 1) :
    ∃ y ∈ F, ∀ f ∈ F, β * f * β⁻¹ = y * f * y⁻¹ := by
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 h
  refine ⟨y, y.2, fun f hf => ?_⟩
  have h4 := congrArg (fun α : MulAut ↥F => ((α ⟨f, hf⟩ : ↥F) : Q)) hy
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h4
  rw [h4, Subgroup.normalizerMonoidHom_apply_apply_coe]

end Generic

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_exists_elem (u : U4X D L K n) (hsp : IsStronglyPEmbedded n D.M)
    (hfour : 4 ≤ CFSG.Open.pRank n D.M) :
    ∃ E : Subgroup (Bar2 D.M), E ≤ commutator (Bar2 D.M) ∧
      E ≤ normalizer (barImage D.M L : Set (Bar2 D.M)) ∧ IsElemAbelian n E ∧
      Nat.card E = n ^ 4 := by
  have hn : n.Prime := u.prime_n
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : n ≠ 2 := by rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  obtain ⟨S, hSM, hSM'⟩ :=
    UC6.sylow_le_commutator_map_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hsp
  obtain ⟨A, -, hAel, hAc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hn hfour
  have h4 : 4 ≤ CFSG.Open.pRank n (S : Subgroup G) := by
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

theorem u81_exists_mem_centralizer (u : U4X D L K n)
    (hsp : IsStronglyPEmbedded n D.M) (hfour : 4 ≤ CFSG.Open.pRank n D.M) :
    ∃ c ∈ centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)),
      orderOf c = n := by
  have hn : n.Prime := u.prime_n
  haveI : Fact n.Prime := ⟨hn⟩
  have hn2 : n ≠ 2 := by rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  obtain ⟨hcomm, hinf, -, -, -, -, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨E, hE', hEN, hEel, hEc⟩ := u.u81_exists_elem hsp hfour
  let χ : ↥E →* Outer ↥(barImage D.M L) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _)).comp
      ((barImage D.M L).normalizerMonoidHom.comp (Subgroup.inclusion hEN))
  have hker : n ^ 3 ≤ Nat.card χ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range χ
    rw [hEc] at h1
    have h2 : Nat.card χ.range ≤ n := Nat.le_of_dvd hn.pos
      ((Subgroup.card_subgroup_dvd_card _).trans
        (u81_card_outer_dvd (u4x_shape_barImage u.hL u.shape)))
    have h3 : n ^ 3 * n ≤ Nat.card χ.ker * n := by
      calc n ^ 3 * n = Nat.card χ.ker * Nat.card χ.range := by rw [h1]; ring
        _ ≤ Nat.card χ.ker * n := Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h3 hn.pos
  by_contra hno
  push_neg at hno
  have hle : χ.ker.map E.subtype ≤ barImage D.M L ⊔ barImage D.M K := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨y, hy, h₀⟩ := u81_exists_conj_of_outer (hEN e.2) (MonoidHom.mem_ker.1 he)
    obtain ⟨x₁, hx₁, h₁⟩ := u.u81_inner_right (hE' e.2) ⟨y, hy, h₀⟩
    have hcC := u4x_mul_inv_mem_centralizer hcomm hy hx₁ h₀ h₁
    have hcn : ((e : Bar2 D.M) * (y * x₁)⁻¹) ^ n = 1 := by
      have h1 : ((e : Bar2 D.M) * (y * x₁)⁻¹) ^ n = ((y * x₁)⁻¹) ^ n := by
        rw [(((u4x_commute_of_conj hy h₀).mul_right
          (u4x_commute_of_conj hx₁ h₁)).inv_right).mul_pow, hEel.2 _ e.2, one_mul]
      have h2 : ((e : Bar2 D.M) * (y * x₁)⁻¹) ^ n ∈ (barImage D.M L ⊔ barImage D.M K) ⊓
          centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) :
            Set (Bar2 D.M)) := by
        refine ⟨?_, pow_mem hcC n⟩
        rw [h1]
        exact pow_mem (inv_mem (mul_mem (mem_sup_left hy) (mem_sup_right hx₁))) n
      rw [hXC, Subgroup.mem_bot] at h2
      exact h2
    have hc1 : (e : Bar2 D.M) * (y * x₁)⁻¹ = 1 := by
      by_contra hc1
      exact hno _ hcC (orderOf_eq_prime hcn hc1)
    show (e : Bar2 D.M) ∈ barImage D.M L ⊔ barImage D.M K
    rw [mul_inv_eq_one.1 hc1]
    exact mul_mem (mem_sup_left hy) (mem_sup_right hx₁)
  have hel : IsElemAbelian n (χ.ker.map E.subtype) := hEel.mono (Subgroup.map_subtype_le _)
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
  have h₀ := pRank_le_one_of_isL2_or_isSz (u4x_shape_barImage u.hL u.shape) hn hn2
  have h₁ := pRank_le_one_of_isL2_or_isSz (u4x_shape_barImage u.hK u.shapeK) hn hn2
  omega

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
