module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplit
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUR
public import CFSG.RankThree.PartOne.KF.F122Sp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.ComponentClassification
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (statedProjEquivPrimeFormOne)

theorem outerRSplit_two_of_u4 {X : Type} [Group X] [Finite X] {n r : ℕ}
    (hX : LieModel X .PSU 4 2 n) (hr : r.Prime) (hr5 : 5 < r) (hrn : r ∣ 2 ^ n - 1) :
    OuterRSplit X r 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hn1 : 1 ≤ n := hX.admissible.2.1
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := (hX.statedClassicalModel (by decide)).2
  letI := hKf
  letI := hKfin
  have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hKcard, ← pow_mul, mul_comm]
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, hcard⟩
  have hq : ¬(4 = 3 ∧ 2 ^ n = 2) := by omega
  have hC := isPrimeFormGram_one (K := K) (n := 4)
  let e' : X ≃* primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    e.trans (statedProjEquivPrimeFormOne
      h (n := 4) (by norm_num))
  have hD : primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≤
      OuterAutomorphisms.inner (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
    have h3 := (unitary_full_diagonal_outer_order h (n := 4) (by norm_num) hq).2.2.1
    have hodd : Odd (2 ^ n + 1) := by
      simpa using
        CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one (f := n) (n := 1) hn1 le_rfl
    rw [CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one hodd] at h3
    have hidx : ((OuterAutomorphisms.inner (primeFormP h ((1 : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K))).subgroupOf
          (primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).index = 1 := h3
    exact Subgroup.subgroupOf_eq_top.1 (Subgroup.index_eq_one.1 hidx)
  have hCm : StatedClassicalModel (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      .PSU 4 2 n := ⟨(hX.statedClassicalModel (by decide)).1, K, hKf, hKfin, hKcard,
        ⟨(statedProjEquivPrimeFormOne
          h (n := 4) (by norm_num)).symm⟩⟩
  have hrq : ∀ m : ℕ, r ∣ 2 ^ m - 1 → r ∣ (2 ^ m) ^ 2 - 1 := fun m hm =>
    hm.trans (by simpa using Nat.sub_dvd_pow_sub_pow (x := 2 ^ m) (y := 1) (n := 2))
  refine (outerRSplit_of_normalForm (primeFormFieldHom h hC) (fun α _ _ => ?_) (fun σ hσ => ?_)
    (fun σ hσ => ?_)).of_mulEquiv e'.symm
  ·
    obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h hC (by norm_num) hq α
    obtain ⟨x, hx⟩ := hD ⟨A, rfl⟩
    exact ⟨x, φ, by rw [hA, hx]⟩
  ·
    have h1 := primeFormFieldFactor_apply h hC (by norm_num) hq 1 σ
    rw [map_one, one_mul] at h1
    have h2 : primeFormFieldHom h hC σ ∈
        (primeFormFieldFactor h hC (by norm_num) hq).ker := by
      rw [ker_primeFormFieldFactor]
      exact CFSG.SeitzReduction.UnitaryPilot.inner_le_primeFormD h _ hσ
    rw [MonoidHom.mem_ker, h1] at h2
    exact h2
  ·
    by_cases hσ1 : σ = 1
    · obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
        (H := ⊤) (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.two_le_pRank_psu_of_dvd
          le_rfl hCm hr (by omega) (hrq n hrn))
      exact ⟨E, hE, hEcard, fun x _ => by rw [hσ1, map_one, MulAut.one_apply]⟩
    · have hσr : orderOf σ = r := orderOf_eq_prime hσ hσ1
      obtain ⟨hrn', hcard0, -, hinj, hrange, -⟩ :=
        CFSG.RankThree.Classical.higher_unitary_prime_subfield_fixed_group_and_full_centralizer
          h (n := 4) (by norm_num) (by omega) hr hq σ hσr
      have h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hr (by omega) hσr
      have hr0 : r ∣ 2 ^ (n / r) - 1 := by
        refine CFSG.RankThree.PartOne.dvd_two_pow_sub_one_of_mul hr ?_
        rwa [Nat.mul_div_cancel' hrn']
      have hC₀ : StatedClassicalModel (primeFormP h₀
          ((1 : GL (Fin 4) (CFSG.LieType.Chevalley.fixSubfield σ)) :
            Matrix (Fin 4) (Fin 4) (CFSG.LieType.Chevalley.fixSubfield σ))) .PSU 4 2 (n / r) :=
        ⟨⟨Nat.prime_two, h₀.one_le, by norm_num, by simp⟩,
          CFSG.LieType.Chevalley.fixSubfield σ, inferInstance, h₀.finite, hcard0,
          ⟨(statedProjEquivPrimeFormOne
            h₀ (n := 4) (by norm_num)).symm⟩⟩
      have := h₀.finite
      obtain ⟨E₀, -, hE₀, hE₀card⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
        (H := ⊤) (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.two_le_pRank_psu_of_dvd
          le_rfl hC₀ hr (by omega) (hrq _ hr0))
      refine ⟨E₀.map (CFSG.RankThree.Classical.primeSubfieldPSU h hr (by omega) hσr 4),
        hE₀.map _, by rw [Subgroup.card_map_of_injective hinj, hE₀card], ?_⟩
      rintro _ ⟨y, -, rfl⟩
      have hy : CFSG.RankThree.Classical.primeSubfieldPSU h hr (by omega) hσr 4 y ∈
          CFSG.RankThree.Classical.fieldFixedPSU h 4 σ := hrange ▸ ⟨y, rfl⟩
      exact hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
