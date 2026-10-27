module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K620ExcB
import CFSG.LocalAnalysis.UniquenessCase.UC6K620Central
import CFSG.LocalAnalysis.UniquenessCase.UC6K620Fi22Cover
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylowAlt8
import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22Two

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Sporadic.Fi22
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.Alt8Sixteen (E16 card_E16 sq_of_mem_E16)

theorem three_lt_twoLocalPrimeRank_of_alt {X : Type} [Group X] [Finite X] (Y : Subgroup X)
    [Y.Normal] (hYodd : Odd (Nat.card Y))
    (hYrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q Y ≤ 3) {n : ℕ} (hn : 13 ≤ n)
    (eA : X ⧸ Y ≃* alternatingGroup (Fin n)) : 3 < CFSG.Open.twoLocalPrimeRank 3 X := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have : IsSimpleGroup (X ⧸ Y) := eA.isSimpleGroup
  have hnc : ∃ a b : X ⧸ Y, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hcomm : IsMulCommutative (alternatingGroup (Fin n)) :=
      ⟨⟨fun x y => by simpa using congrArg eA (hc (eA.symm x) (eA.symm y))⟩⟩
    have := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin n)).1 hcomm
    rw [Nat.card_fin] at this
    omega
  have hU : ∃ U : Subgroup (X ⧸ Y), CFSG.IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 1) := by
    have h8 : 8 ≤ n := by omega
    set U := (E16.map (CFSG.SectionRank.altEmbed h8)).map eA.symm.toMonoidHom with hUdef
    have hsq : ∀ x ∈ U, x * x = 1 := by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [← map_mul, ← map_mul, sq_of_mem_E16 hz, map_one, map_one]
    have hinv : ∀ z ∈ U, z⁻¹ = z := fun z hz => inv_eq_of_mul_eq_one_right (hsq z hz)
    refine ⟨U, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 U).mpr
      ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩, ?_⟩
    · change (a : X ⧸ Y) * b = b * a
      calc (a : X ⧸ Y) * b = ((a : X ⧸ Y) * b)⁻¹ := (hinv _ (U.mul_mem a.2 b.2)).symm
        _ = (b : X ⧸ Y)⁻¹ * (a : X ⧸ Y)⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [hinv _ b.2, hinv _ a.2]
    · rw [hUdef, Subgroup.card_map_of_injective eA.symm.injective,
        Subgroup.card_map_of_injective (CFSG.SectionRank.altEmbed_injective h8), card_E16]
      norm_num
  obtain ⟨K, hKs, hKz, -⟩ := exists_central_cover_of_odd_kernel 3 Y hYodd hYrank hnc hU
  have hπZ : (eA.toMonoidHom.comp ((QuotientGroup.mk' Y).comp K.subtype)).ker ≤ center K := by
    intro x hx
    apply hKz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff] at hx
    exact hx
  exact ((CFSG.RankThree.GroupTheory.alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
    _ (eA.surjective.comp hKs) hπZ).2.1 hn).1

theorem exists_cover_comp_mulEquiv {K Q G' : Type*} [Group K] [Group Q] [Group G']
    {J' : Subgroup G'} (π : K →* Q) (hπ : Function.Surjective π) (hZ : π.ker ≤ center K)
    (hodd : Odd (Nat.card π.ker)) (f : Q ≃* J') :
    ∃ ψ : K →* J', Function.Surjective ψ ∧ ψ.ker ≤ center K ∧ Odd (Nat.card ψ.ker) := by
  have hker : (f.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  exact ⟨f.toMonoidHom.comp π, f.surjective.comp hπ, hker ▸ hZ, hker ▸ hodd⟩

theorem three_lt_twoLocalPrimeRank_of_fi22
    {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) [Y.Normal] (hYodd : Odd (Nat.card Y))
    (hYrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q Y ≤ 3) (hF : IsSpor (X ⧸ Y) .Fi22) :
    3 < CFSG.Open.twoLocalPrimeRank 3 X := by
  obtain ⟨eF⟩ := hF
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) := isSimpleGroup_Fi22
  have : IsSimpleGroup (X ⧸ Y) := eF.isSimpleGroup
  have hnc : ∃ a b : X ⧸ Y, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    haveI : IsMulCommutative (X ⧸ Y) := ⟨⟨fun x y => hc x y⟩⟩
    have hp := IsSimpleGroup.prime_card (α := X ⧸ Y)
    have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) = 64561751654400 :=
      card_Fi22
    rw [Nat.card_congr eF.toEquiv, hcard] at hp
    exact absurd (hp.eq_one_or_self_of_dvd 2 (by norm_num)) (by norm_num)
  have hU : ∃ U : Subgroup (X ⧸ Y), CFSG.IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (4 + 1) := by
    obtain ⟨E, hEJ, hE, hEc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1021_J_two_rank_five
    obtain ⟨V, hV, hVc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1021_transport_elemAbelian hEJ hE
      (eF.trans fi22EquivJ)
    exact ⟨V, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mpr hV, hVc.trans hEc⟩
  obtain ⟨K, hKs, hKz, hKodd⟩ := exists_central_cover_of_odd_kernel 4 Y hYodd
    (fun q hq hq2 => (hYrank q hq hq2).trans (by norm_num)) hnc hU
  obtain ⟨ψ, hψs, hψz, hψodd⟩ := exists_cover_comp_mulEquiv _ hKs hKz hKodd (eF.trans fi22EquivJ)
  exact four_le_localRank_three_of_fi22_cover ψ hψs hψz hψodd

theorem three_lt_twoLocalPrimeRank_of_alt_or_fi22
    {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) [Y.Normal] (hYodd : Odd (Nat.card Y))
    (hYrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q Y ≤ 3)
    (hX : (∃ n : ℕ, 13 ≤ n ∧ IsAlt (X ⧸ Y) n) ∨ IsSpor (X ⧸ Y) .Fi22) :
    3 < CFSG.Open.twoLocalPrimeRank 3 X := by
  rcases hX with ⟨n, hn, ⟨eA⟩⟩ | hF
  · exact three_lt_twoLocalPrimeRank_of_alt Y hYodd hYrank hn eA
  · exact three_lt_twoLocalPrimeRank_of_fi22 Y hYodd hYrank hF

theorem k620excA_holds :
    K620ExcA :=
  fun _ _ _ _ Y _ hYodd hYrank hX => three_lt_twoLocalPrimeRank_of_alt_or_fi22 Y hYodd hYrank hX

theorem k620exc_holds :
    K620Exc :=
  k620exc_of_A k620excA_holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
