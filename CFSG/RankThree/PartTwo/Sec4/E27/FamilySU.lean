module

public import CFSG.RankThree.PartTwo.Sec4.E27.FixSU
public import CFSG.LieType.SeitzGeneration.UnitaryHyperPSU

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP CFSG.Assembly.LowTwoRank
open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27


theorem center_eq_bot_of_simple_nonab {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem hinner_su4 {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (hf : 4 ≤ f) :
    ∀ E : Subgroup (primeFormP h (idGram K 4)), IsElemAbelian 3 E → Nat.card E = 27 →
      HyperGen 3 (⊤ : Subgroup (primeFormP h (idGram K 4))) E := by
  intro E hE hc
  haveI := h.finite
  have hne : ¬ (4 = 3 ∧ 2 ^ f = 2) := by omega
  let ψ : primeFormP h (idGram K 4) ≃* StatedProj (StatedSU 4 (2 ^ f) K) :=
    (Classical.choice (unitary_prime_form_full_semilinear_realization h
      (isPrimeFormGram_idGram (K := K) (n := 4)) (by norm_num) hne).1).trans
      (unitaryPSUEquiv h (by omega))
  have hE' : IsElemAbelian 3 (E.map ψ.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _
  have hc' : Nat.card (E.map ψ.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hc]
    norm_num
  refine hyperGen_top_of_mulEquiv ψ ?_
  have h3 : ¬ 3 ∣ 2 ^ f := fun hd => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have h2f : 16 ≤ 2 ^ f := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_cases hq : 3 ∣ 2 ^ f + 1
  · refine hyperGen_statedProj_unitary_toral (n := 3) h Nat.prime_three hq (by omega) ?_ hE' hc'
    intro hd
    have : 3 ∣ 3 + 1 := hd.trans (Nat.gcd_dvd_left _ _)
    omega
  · have hq' : 3 ∣ 2 ^ f - 1 := by omega
    exact hyperGen_statedProj_unitary_split h (by norm_num) (fun h3 => absurd h3 (by norm_num))
      Nat.prime_three (by norm_num) hq' hE' hc'

theorem seitz27_su4 {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (hf : 4 ≤ f) :
    Seitz27 (primeFormP h (idGram K 4)) := by
  haveI := h.finite
  have hne : ¬ (4 = 3 ∧ 2 ^ f = 2) := by omega
  haveI : IsSimpleGroup (primeFormP h (idGram K 4)) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h (by norm_num) hne
  have hnab : ∃ a b : primeFormP h (idGram K 4), a * b ≠ b * a := by
    have hnc := CFSG.RankThree.Classical.not_commute_primeFormP_one h (by norm_num) hne
    push Not at hnc
    exact hnc
  exact seitz27_su4_of_inner h hf (center_eq_bot_of_simple_nonab hnab) (hinner_su4 h hf)

end CFSG.RankThree.PartTwo.Sec4.E27
