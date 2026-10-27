module

public import CFSG.Quasithin.Background.RonanE43Lift
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import Mathlib.Tactic.Group
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open

variable {U X : Type} [Group U] [Group X] {ψ : U →* X}

theorem finite_of_odd_card_ker [Finite X] (hodd : Odd (Nat.card ψ.ker)) : Finite U := by
  haveI : Finite ψ.ker := Nat.finite_of_card_ne_zero hodd.pos.ne'
  haveI : Finite (U ⧸ ψ.ker) :=
    Finite.of_equiv ψ.range (QuotientGroup.quotientKerEquivRange ψ).toEquiv.symm
  exact Finite.of_subgroup_quotient ψ.ker

theorem map_normalizer_eq_range_inf_normalizer_map (hker : ψ.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card ψ.ker)) {S : Subgroup U} (hS : IsPGroup 2 S) :
    (Subgroup.normalizer (S : Set U)).map ψ =
      ψ.range ⊓ Subgroup.normalizer ((S.map ψ : Subgroup X) : Set X) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, Subgroup.mem_normalizer_iff.2 fun x => ?_⟩
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨u * s * u⁻¹, (Subgroup.mem_normalizer_iff.1 hu s).1 hs, by simp⟩
    · rintro ⟨s, hs, hsx⟩
      refine ⟨u⁻¹ * s * u, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hu) s).1 hs
      · simp only [map_mul, map_inv, hsx]
        group
  · rintro _ ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, CFSG.Quasithin.RonanE43.mem_normalizer_of_map_mem ψ hker
      (Nat.coprime_two_right.2 hodd) hS hu, rfl⟩

theorem map_pCoreOf_eq_of_odd_central_ker [Finite X] (hker : ψ.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card ψ.ker)) {M : Subgroup U} (hM : ψ.ker ≤ M) :
    (pCoreOf 2 M).map ψ = pCoreOf 2 (M.map ψ) := by
  haveI : Finite U := finite_of_odd_card_ker hodd
  have hπker : ψ.rangeRestrict.ker = ψ.ker := ψ.ker_rangeRestrict
  have hle : M.map ψ ≤ ψ.range := Subgroup.map_le_range ψ M
  have hcomap : ((M.map ψ).subgroupOf ψ.range).comap ψ.rangeRestrict = M := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    change ψ x ∈ M.map ψ ↔ x ∈ M
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hM]
  have key := CFSG.Quasithin.RonanE43.map_pCoreOf_comap_eq ψ.rangeRestrict
    ψ.rangeRestrict_surjective (hπker ▸ hker) (hπker ▸ Nat.coprime_two_right.2 hodd)
    ((M.map ψ).subgroupOf ψ.range)
  rw [hcomap] at key
  have h1 : ((pCoreOf 2 M).map ψ.rangeRestrict).map ψ.range.subtype = (pCoreOf 2 M).map ψ := by
    rw [Subgroup.map_map]
    rfl
  have h2 : (pCoreOf 2 ((M.map ψ).subgroupOf ψ.range)).map ψ.range.subtype =
      pCoreOf 2 (M.map ψ) := by
    rw [GGRootNorm.pCoreOf_subgroupOf hle]
    exact Subgroup.map_subgroupOf_eq_of_le ((GGRootNorm.pCoreOf_le _).trans hle)
  rw [← h1, key, h2]

end CFSG.StandardType.LieKnownR2
