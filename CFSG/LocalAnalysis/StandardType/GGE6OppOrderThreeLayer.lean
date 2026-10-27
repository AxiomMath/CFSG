module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate707001
public import Certificates.Certificate707002
import CFSG.LocalAnalysis.StandardType.GGE6OppRankAut
import CFSG.LocalAnalysis.StandardType.GGE6OppCompRank
import CFSG.LocalAnalysis.StandardType.GGE6OppFixedRank
import CFSG.LocalAnalysis.StandardType.GGE6OppInnerAction
import CFSG.LocalAnalysis.StandardType.GGE6OppConjDatum
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6OppTorsionLabel
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinAbs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.Mathlib.GroupTheory.InnerElemAbelian
public import Certificates.Data.E6TableT

public section

namespace CFSG.StandardType

open CFSG.Assembly TablePThreeKG

theorem le_normalizer_largeEvenLayer {H : Type} [Group H] (K : Subgroup H) :
    K ≤ Subgroup.normalizer (LargeEvenLayer K : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact map_conj_largeEvenLayer_le (Subgroup.le_normalizer hg) ⟨h, hh, rfl⟩
  · intro hh
    have := map_conj_largeEvenLayer_le (Subgroup.le_normalizer (K.inv_mem hg)) ⟨_, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem ggE6OppOrderThree_label
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {f : ℕ} (hf : 2 ≤ f)
    (hH : (GGHasLabel ⟨.E6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f - 1))
    {z : H} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) {J : Subgroup H}
    (hJ : J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)))
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H))) :
    (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (J ⧸ Subgroup.center J) := by
  obtain ⟨lab, -, hlab, hc⟩ := ggTorsion_E6Opp_unique_label hf
    (ggTorsionDatum_conj_of_e6Opp (by omega) hH hz1 hz3 hJc)
    (fun Q hQ => ((SpFin.layer_eq_of_isComponentOf
      (by rwa [D4Inner.ggAutFixedSubgroup_conj_eq_centralizer] at hQ)
      (by rw [← hJ]; exact hJc)).symm.trans hJ.symm))
  rcases hc with ⟨h3, rfl⟩ | ⟨h3, rfl⟩ | rfl
  · exact Or.inl ⟨h3, hlab⟩
  · exact Or.inr (Or.inl ⟨h3, hlab⟩)
  · exact Or.inr (Or.inr hlab)

theorem exists_elemAbelian_of_e6OppComp
    {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {f : ℕ} (hf : 1 ≤ f)
    (hXl : (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (X ⧸ Subgroup.center X)) ∨
      (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (X ⧸ Subgroup.center X)) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) ∧
      ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  rcases hXl with ⟨h3, hl⟩ | ⟨h3, hl⟩ | hl
  · exact exists_elemAbelian_of_ggHasLabel_A5 hX hf h3 hl
  · exact exists_elemAbelian_of_ggHasLabel_twA5 hX hf h3 hl
  · exact exists_elemAbelian_of_ggHasLabel_twD4 hX hf hl

theorem exists_fixed_elemAbelian_of_e6OppComp {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hXl : (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ X) ∨
      (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ X) ∨ GGHasLabel ⟨.twD, 4, f⟩ X)
    {α : MulAut X} (hα : α ^ 3 = 1) (hin : ∀ x : X, α ≠ MulAut.conj x) :
    ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 ∧ ∀ a ∈ A, α a = a := by
  rcases hXl with ⟨h3, hl⟩ | ⟨h3, hl⟩ | hl
  · exact exists_fixed_elemAbelian_of_ggHasLabel_A5 hf h3 hl hα hin
  · exact exists_fixed_elemAbelian_of_ggHasLabel_twA5 hf h3 hl hα hin
  · exact exists_fixed_elemAbelian_of_ggHasLabel_twD4 hl hα hin

theorem ggE6OppOrderThree_inner
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {f : ℕ} (hf : 1 ≤ f)
    (hH : (GGHasLabel ⟨.E6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f - 1))
    {z : H} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) {J : Subgroup H}
    (hJ : J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)))
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H)))
    (hJl : (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (J ⧸ Subgroup.center J))
    {g : H} (hg : g ∈ Subgroup.centralizer ({z} : Set H)) (hg3 : g ^ 3 = 1) :
    ∃ x ∈ J, ∀ y ∈ J, g * y * g⁻¹ = x * y * x⁻¹ := by
  have hJp : commutator J = ⊤ := hJc.2.2.1
  obtain ⟨hZJ, -⟩ := exists_elemAbelian_of_e6OppComp hJp hf hJl
  refine exists_inner_of_aut_dichotomy hJp hZJ (fun B hB => card_le_pow_four_of_e6Opp hf hH hB)
    (fun α hα => ?_) hz1 hz3 hJc.1 (hJ.symm ▸ le_normalizer_largeEvenLayer _ hg) hg hg3
  by_cases hin : ∃ x, α = MulAut.conj x
  · exact Or.inl hin
  · exact Or.inr (exists_fixed_elemAbelian_of_e6OppComp hf hJl hα (fun x hx => hin ⟨x, hx⟩))

theorem ggE6OppOrderThree_card_le
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {f : ℕ} (hf : 1 ≤ f)
    (hH : (GGHasLabel ⟨.E6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f - 1))
    {z : H} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) {J : Subgroup H}
    (hJ : J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)))
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H)))
    (hJl : (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (J ⧸ Subgroup.center J))
    {E : Subgroup H} (hEz : E ≤ Subgroup.centralizer ({z} : Set H)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ J : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJp : commutator J = ⊤ := hJc.2.2.1
  obtain ⟨hZJ, A, hA, hA3⟩ := exists_elemAbelian_of_e6OppComp hJp hf hJl
  obtain ⟨hAc, hAp⟩ := hA
  obtain ⟨hEc, hEp⟩ := hE
  refine CFSG.card_le_mul_card_inf_of_forall_inner (k := 3) (A := A.map J.subtype)
    hZJ (Subgroup.map_subtype_le A) ?_ ?_ ?_
    (fun B hBc hBp => card_le_pow_four_of_e6Opp hf hH ⟨hBc, hBp⟩) hEc hEp
    (fun e he => ggE6OppOrderThree_inner hf hH hz1 hz3 hJ hJc hJl (hEz he) (hEp e he))
  · have := hAc
    exact Subgroup.map_isMulCommutative A J.subtype
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hAp a ha, map_one]
  · rw [Subgroup.card_subtype, hA3]

theorem ggE6OppOrderThreeLayer_holds :
    GGE6OppOrderThreeLayer := by
  intro H _ _ _ f hf hH z hz1 hz3 J hJ hJc
  have hcard := fun hJl => fun E hEz hE =>
    ggE6OppOrderThree_card_le (H := H) hf hH hz1 hz3 hJ hJc hJl (E := E) hEz hE
  rcases Nat.lt_or_ge f 2 with hf2 | hf2
  · obtain rfl : f = 1 := by omega
    have hE6 : GGHasLabel ⟨.E6, 0, 1⟩ (H ⧸ Subgroup.center H) := by
      rcases hH with ⟨h, -⟩ | ⟨-, h3⟩
      · exact h
      · exact absurd h3 (by norm_num)
    rcases ggE6OppOrderThree_label_two hE6 hz1 hz3 hJ hJc with hA | hD | hA2
    · exact Or.inl ⟨Or.inl ⟨by norm_num, hA⟩, hcard (Or.inl ⟨by norm_num, hA⟩)⟩
    · exact Or.inl ⟨Or.inr (Or.inr hD), hcard (Or.inr (Or.inr hD))⟩
    · exact Or.inr ⟨rfl, hE6, hA2⟩
  · have hl := ggE6OppOrderThree_label hf2 hH hz1 hz3 hJ hJc
    exact Or.inl ⟨hl, hcard hl⟩

end CFSG.StandardType

end
