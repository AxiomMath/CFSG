module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSp
public import CFSG.LieType.SeitzGeneration.SpFourScope
public import CFSG.RankThree.PartTwo.Sec4.E27.FixStandard

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.RankThree.PartOne (card_semilinearFixedSubfield)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LieType.SeitzGeneration CFSG.Open
open TauCeti

section Main

theorem fixPlaneGen_sp4_three {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 4 ≤ f)
    (hK : Nat.card K = 2 ^ f) : FixPlaneGen (StatedProj (StatedSp 2 K)) 3 := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hpodd : Odd 3 := by decide
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card Nat.prime_two (by omega) hK
  have O : SpOuter 2 f 2 K := spOuter Nat.prime_two (by omega) le_rfl hK
  have hinj : Function.Injective (proj 2 K) := CFSG.RankThree.PartOne.proj_injective_sp hK (by omega) (by omega)
  refine fixPlaneGen_of_standard (spLinearAutGroup 2 K)
    {g | ∃ σ : K ≃+* K, orderOf σ = 3 ∧ g = fieldAut 2 K σ} ?_ ?_
  ·
    intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ 3 = 1 := hord ▸ pow_orderOf_eq_one α
    have hαE : α ∈ spSemilinearAutGroup 2 K :=
      mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hord ▸ hpodd)
    have hαD : α ∉ spLinearAutGroup 2 K := fun hD => by
      have := inner_normal (StatedProj (StatedSp 2 K))
      obtain ⟨g, hg⟩ := mem_of_pow_eq_one_of_relIndex_dvd_two
        (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) Nat.prime_three hp2 hD hαp
      exact hout g hg.symm
    obtain ⟨-, σ, hσord, h, hhD, hαh⟩ := O.descent 3 Nat.prime_three α hαE hαD hord
    exact ⟨h, hhD, fieldAut 2 K σ, ⟨σ, hσord, rfl⟩, hαh⟩
  ·
    rintro _ ⟨σ, hσ, rfl⟩ A hA hAa hAc
    have hσp : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
    rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp] at hA ⊢
    set k := descentField σ with hk
    have hpf : 3 ∣ f ∧ Nat.card k = 2 ^ (f / 3) :=
      card_semilinearFixedSubfield Nat.prime_two (by omega) hK hσ
    have hf6 : 6 ≤ f := by
      obtain ⟨⟨m, hm⟩, -⟩ := hpf
      omega
    have hk4 : 4 ≤ Nat.card k := by
      rw [hpf.2]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f / 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfk : Finite k := Nat.finite_of_card_ne_zero (by omega)
    have : CharP k 2 := inferInstance
    have h3k : (3 : k) ≠ 0 := by
      intro h
      have h1 : (1 : k) = 0 := by
        have : (3 : k) = 1 := by
          have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
          calc (3 : k) = 2 + 1 := by norm_num
            _ = 1 := by rw [h2, zero_add]
        rw [← this]
        exact h
      exact one_ne_zero h1
    set A0 : Subgroup (StatedSp 2 k) := A.comap (subfieldProj (r := 2) σ) with hA0
    have hinjΦ : Function.Injective (subfieldProj (r := 2) σ) := by
      intro a b hab
      have h1 : proj 2 K (subfieldSpHom 2 k a) = proj 2 K (subfieldSpHom 2 k b) := hab
      exact subfieldSpHom_injective k (hinj h1)
    have hmap : A0.map (subfieldProj (r := 2) σ) = A := Subgroup.map_comap_eq_self hA
    have hA0c : Nat.card A0 = 9 := by
      have := Subgroup.card_map_of_injective hinjΦ (K := A0)
      rw [hmap] at this
      rw [← this, hAc]
      norm_num
    have hcomm0 : ∀ x ∈ A0, ∀ y ∈ A0, x * y = y * x := by
      intro x hx y hy
      apply hinjΦ
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hAa.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    have hexp0 : ∀ x ∈ A0, x ^ 3 = 1 := by
      intro x hx
      apply hinjΦ
      rw [map_pow, map_one]
      exact hAa.2 _ hx
    have hclos := closure_centralizers_spFour_three h3k (exists_ne_zero_one (by omega))
      hcomm0 hexp0 hA0c
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    have hg : g ∈ Subgroup.closure {z : StatedSp 2 k | ∃ x ∈ A0, x ≠ 1 ∧ z * x = x * z} := by
      rw [hclos]
      exact Subgroup.mem_top g
    have h2 : subfieldProj (r := 2) σ g ∈
        (Subgroup.closure {z : StatedSp 2 k | ∃ x ∈ A0, x ≠ 1 ∧ z * x = x * z}).map
          (subfieldProj (r := 2) σ) := ⟨g, hg, rfl⟩
    rw [MonoidHom.map_closure] at h2
    refine (Subgroup.closure_mono ?_) h2
    rintro _ ⟨z, ⟨b, hb, hb1, hzb⟩, rfl⟩
    refine ⟨⟨z, rfl⟩, subfieldProj (r := 2) σ b, hb, fun h => hb1 (hinjΦ (by rw [h, map_one])), ?_⟩
    rw [← map_mul, ← map_mul, hzb]

end Main

end CFSG.RankThree.PartTwo.Sec4.E27
