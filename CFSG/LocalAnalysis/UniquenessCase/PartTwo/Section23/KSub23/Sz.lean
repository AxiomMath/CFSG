module

import CFSG.LieType.SuzukiSubgroups.Torus
import CFSG.Quasithin.Vol2.E2TenSevenMult
import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

private theorem isSolvable_normalizer_sylow_of_isSz
    {S : Type} [Group S] [Finite S] {a : ℕ}
    (hSz : CFSG.Quasithin.IsSz a S) (Q : Sylow 2 S) :
    Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup S) : Set S)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup S := Subgroup.normalizer ((Q : Subgroup S) : Set S)
  let K : Subgroup ↥N := (Q : Subgroup S).subgroupOf N
  have hQle : (Q : Subgroup S) ≤ N := Subgroup.le_normalizer
  have hKn : K.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr le_rfl
  haveI : K.Normal := hKn
  have ha3 : 3 ≤ a := by
    obtain ⟨-, b, hb, -, -, -, haeq, -, -⟩ := hSz
    omega
  have hQcard : Nat.card (Q : Subgroup S) = (2 ^ a) ^ 2 :=
    (CFSG.LieType.SuzukiSubgroups.fusionBenderBorel_of_isSz (n := a) (H := S) hSz Q).2.2.2.2
  have hNcard : Nat.card N = (2 ^ a) ^ 2 * (2 ^ a - 1) := by
    dsimp only [N]
    exact CFSG.LieType.SuzukiSubgroups.card_normalizer_sylow_of_isSz hSz Q
  have hKcard : Nat.card K = (2 ^ a) ^ 2 := by
    dsimp only [K]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv, hQcard]
  have hquotcard : Nat.card (↥N ⧸ K) = 2 ^ a - 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hNcard, hKcard] at h1
    refine Nat.eq_of_mul_eq_mul_right (m := (2 ^ a) ^ 2) (by positivity) ?_
    rw [← h1]
    ring
  have hqeven : Even (2 ^ a) := by
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    exact ⟨2 ^ m, by rw [pow_succ]; ring⟩
  have hodd : Odd (2 ^ a - 1) := by
    obtain ⟨m, hm⟩ := hqeven
    have h2 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨m - 1, by omega⟩
  have hquotodd : Odd (Nat.card (↥N ⧸ K)) := by
    rw [hquotcard]
    exact hodd
  haveI : Group.IsSolvable (↥N ⧸ K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hquotodd
  have hKP : IsPGroup 2 ↥K :=
    (Q.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe hQle).symm
  haveI : Group.IsSolvable ↥K := by
    haveI : Group.IsNilpotent ↥K := hKP.isNilpotent
    infer_instance
  simpa only [N] using (Group.isSolvable_of_subgroup_quotient K : Group.IsSolvable ↥N)

private theorem eq_bot_of_no_four {S : Type} [Group S] [Finite S]
    {a : ℕ} (hSz : CFSG.Quasithin.IsSz a S) {Y : Subgroup S} (hY : ⁅Y, Y⁆ = Y)
    (h4 : ∀ E : Subgroup S, E ≤ Y → IsElemAbelian 2 E → Nat.card E ≠ 4) : Y = ⊥ := by
  obtain ⟨W, hWY, hWn, hWodd, hWmem⟩ :=
    CFSG.LieType.SuzukiSubgroups.exists_normal_odd_of_not_four hSz h4
  let K : Subgroup ↥Y := W.subgroupOf Y
  have hKn : K.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).mpr fun g hg =>
      Subgroup.mem_normalizer_iff.mpr fun w =>
        ⟨fun hw => hWn g hg w hw, fun hw => by
          have h := hWn g⁻¹ (Y.inv_mem hg) (g * w * g⁻¹) hw
          have heq : g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w := by group
          rwa [heq] at h⟩
  haveI : K.Normal := hKn
  have hP : IsPGroup 2 (↥Y ⧸ K) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    obtain ⟨e, n', hn'odd, hn'eq⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 2 (by norm_num)
    have hn'odd' : Odd n' :=
      Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
    have hgpow : (g ^ 2 ^ e) ^ n' = 1 := by
      rw [← pow_mul, ← hn'eq, pow_orderOf_eq_one]
    have hordodd : Odd (orderOf (g ^ 2 ^ e)) :=
      hn'odd'.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hgpow)
    have hamb : Odd (orderOf ((g ^ 2 ^ e : ↥Y) : S)) := by
      simpa only [Subgroup.orderOf_coe] using hordodd
    have hmemW : ((g ^ 2 ^ e : ↥Y) : S) ∈ W := hWmem _ (g ^ 2 ^ e).2 hamb
    have hmemK : g ^ 2 ^ e ∈ K := Subgroup.mem_subgroupOf.mpr hmemW
    refine ⟨e, ?_⟩
    rw [← map_pow (QuotientGroup.mk' K) g (2 ^ e)]
    exact (QuotientGroup.eq_one_iff _).mpr hmemK
  have hYsolv : Group.IsSolvable ↥Y := by
    have hKodd : Odd (Nat.card K) := by
      dsimp only [K]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv]
      exact hWodd
    haveI : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
    haveI : Group.IsSolvable (↥Y ⧸ K) := by
      haveI : Group.IsNilpotent (↥Y ⧸ K) := hP.isNilpotent
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient K
  by_contra hbot
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hbot
  haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  exact (Group.IsPerfect.not_isSolvable ↥Y) hYsolv

theorem eq_bot_or_isSimpleGroup_of_isSz
    {S : Type} [Group S] [Finite S] {a : ℕ} (hS : IsSz S a) (Y : Subgroup S) (hY : ⁅Y, Y⁆ = Y) :
    Y = ⊥ ∨ IsSimpleGroup ↥Y := by
  have hSzS : CFSG.Quasithin.IsSz a S := (CFSG.Blueprint.LieModel.twistedB2_iff.mp hS).2
  by_cases htop : Y = ⊤
  · right
    have hSsimple : IsSimpleGroup S :=
      CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz (Or.inr hSzS)
    exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup_congr.mpr hSsimple
  by_cases h4 : ∃ E : Subgroup S, E ≤ Y ∧ IsElemAbelian 2 E ∧ Nat.card E = 4
  · obtain ⟨E, hEY, hE, hE4⟩ := h4
    rcases CFSG.LieType.SuzukiSubgroups.le_normalizer_or_isSz hSzS htop hEY hE hE4 with
      ⟨Q, hYQ⟩ | ⟨k, hkdvd, hklt, hkSz⟩
    · left
      haveI : Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup S) : Set S)) :=
        isSolvable_normalizer_sylow_of_isSz hSzS Q
      have hYsolv : Group.IsSolvable ↥Y :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYQ)
          (Subgroup.inclusion_injective hYQ)
      by_contra hbot
      haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hbot
      haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
      exact (Group.IsPerfect.not_isSolvable ↥Y) hYsolv
    · right
      exact CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz (Or.inr hkSz)
  · left
    exact eq_bot_of_no_four hSzS hY fun E hEY hE hE4 => h4 ⟨E, hEY, hE, hE4⟩

theorem not_three_dvd_card_of_isSz {S : Type} [Group S] [Finite S]
    {a : ℕ} (hS : IsSz S a) : ¬ 3 ∣ Nat.card S := by
  have hSzS : CFSG.Quasithin.IsSz a S := (CFSG.Blueprint.LieModel.twistedB2_iff.mp hS).2
  exact CFSG.LieType.SuzukiSubgroups.not_three_dvd_card_of_isSz hSzS

end CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

end
