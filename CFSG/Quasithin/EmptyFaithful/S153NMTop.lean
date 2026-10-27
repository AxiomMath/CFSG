module

public import CFSG.Quasithin.EmptyFaithful.S153NMl3D
public import CFSG.Quasithin.EmptyFaithful.S153NMs5
public import CFSG.Quasithin.EmptyFaithful.S153NMcTop
public import CFSG.Quasithin.EmptyFaithful.S153NMl2
public import CFSG.Quasithin.EmptyFaithful.S153NMs3
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Two

variable {W : Type} [CommGroup W] [Finite W]

theorem two_le_of_natural_sl2_of_case1 {J : Subgroup (MulAut W)} (hc1 : B56Case1 J) {n : ℕ}
    (hnat : BinaryNaturalSL J ⊤ (fixV J) 2 n) : 2 ≤ n := by
  by_contra hn
  push Not at hn
  obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
  have hsurj : Function.Surjective π := hπ.1
  have hKcard : Nat.card K = 2 := by
    interval_cases n
    · exfalso
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      simp at hK
      omega
    · simpa using hK
  have h6 : Nat.card ↥(StatedSL 2 K) = 6 := by
    rw [card_statedSL_two1527d, hKcard]
    norm_num
  have hsolv : Group.IsSolvable ↥(StatedSL 2 K) := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    rw [h6]
    have h23 : Nat.primeFactors 6 = {2, 3} := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
      rfl
    rw [h23]
    decide
  have hsolv' : Group.IsSolvable (FFModel.nat (StatedSL 2 K)).Gam := hsolv
  have hJsolv : Group.IsSolvable ↥J := Group.isSolvable_of_surjective hsurj
  obtain ⟨hq, -⟩ := hc1
  have hXJ : quasithinGenFitting J ≤ J := quasithinGenFitting_le J
  have hXsolv : Group.IsSolvable ↥(quasithinGenFitting J) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXJ)
  have hperf : Group.IsPerfect ↥(quasithinGenFitting J) := hq.1
  obtain ⟨a, b, hab⟩ := hq.2.2
  have hnt0 : Nontrivial (↥(quasithinGenFitting J) ⧸ Subgroup.center ↥(quasithinGenFitting J)) :=
    ⟨⟨a, b, fun hh => hab (by rw [hh])⟩⟩
  have hnt : Nontrivial ↥(quasithinGenFitting J) :=
    Function.Surjective.nontrivial (QuotientGroup.mk_surjective
      (s := Subgroup.center ↥(quasithinGenFitting J)))
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(quasithinGenFitting J)
  rw [Group.IsPerfect.commutator_eq_top] at this
  exact lt_irrefl _ this

end Two

section Main

theorem input15367Module_of_b56
    (h56 : AsB56) : Input15367Module := by
  intro W _ _ hW Γ w 𝒪 hD
  have hJΓ : ffJ Γ ≤ Γ := B6.ffJ_le Γ
  have hJn : ((ffJ Γ).subgroupOf Γ).Normal := ffJ_subgroupOf_normal Γ
  obtain ⟨B, hB𝒪, hB0⟩ := hD.nontrivial
  obtain ⟨hBΓ, hBel, hBoff⟩ := hD.offender B hB𝒪
  have hFF : IsFFModule Γ := ⟨B, hBΓ, hB0, hBel, hBoff⟩
  have hJne : ffJ Γ ≠ ⊥ := InternalSec.ffJ_ne_bot_of_isFFModule hW hFF
  have hb53 : B53Hyp (ffJ Γ) := b53Hyp_ffJ_of_quot hD.sqtk hD.o2
  have hno : ¬ FFC.ThreeRank2 ↥(ffJ Γ) := fun h => hD.rank3 (h.of_le hJΓ)
  have hw : w ∉ fixV (ffJ Γ) := not_mem_fixV_of_gen hD.gen hJΓ hJn hJne
  have hS := exists_sylow_le_stab hD
  rcases sort_b56 h56 hW hb53 hJne hno with hc2 | ⟨hc1, hfl, hpiece⟩
  · exact relIndex_eq_three_of_case2 hW hD rfl hc2
  · exfalso
    rcases hpiece with ⟨-, hnat⟩ | ⟨-, m, K, hf, hfin, hK, hdir⟩ | hc
    · rcases hnat with ⟨n, hsl2⟩ | hsym | ⟨m, hsl3⟩
      · exact false_of_natural_sl2 hW hD rfl hJne (two_le_of_natural_sl2_of_case1 hc1 hsl2) hsl2
      · exact false_of_symmetric_five hW hJΓ hsym hw hD.three_prime
      · exact false_of_natural_sl3 hW hJΓ hsl3 hw hD.three_prime
    · exact false_of_two_natural_sl3 hW hJΓ hJn ⟨m, K, hf, hfin, hK, hdir⟩ hw hD.three_prime hS
    · obtain ⟨hiso, -, hcard, -, -⟩ := hc
      rw [Subgroup.card_top] at hcard
      exact false_of_l32_typeC hW hJΓ hJn hiso hcard hw hD.three_prime hS

end Main

end CFSG.Quasithin.S153N
