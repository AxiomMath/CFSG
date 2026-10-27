module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepair
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSU

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace SURepair

variable {K : Type} [Field K] {f : ℕ}

theorem nonempty_sl2_mulEquiv_unitarySU_two [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f) ≃*
      ↥(unitarySU 2 f K 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 2
  exact ⟨((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
    (CFSG.LieType.Universal.Unitary.conjEquiv P hP)).trans
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2))⟩

theorem isQuasisimple_unitarySU_two (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    CFSG.IsQuasisimple ↥(unitarySU 2 f K 2) := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_unitarySU_two (f := f) h.card_eq_sq
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.RankThree.Classical.isQuasisimple_SL2 ?_)
  classical
  have : Fintype ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f) := Fintype.ofFinite _
  have hcard : 4 ≤ (Finset.univ : Finset ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨s, hs⟩

theorem isQuasisimple_unitarySU_of_eq_two (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) {k : ℕ}
    (hk : k = 2) : CFSG.IsQuasisimple ↥(unitarySU 2 f K k) := by
  subst hk
  exact isQuasisimple_unitarySU_two h hf

variable {G : Type} [Group G] {n : ℕ}

theorem isQuasisimple_blockSU_two (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {S : Finset (Fin n)} (hS : S.card = 2) :
    CFSG.IsQuasisimple ↥(TableBUE.blockSU (K := K) (n := f) S) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (TableBUE.blockSUEquiv S h)
    (isQuasisimple_unitarySU_of_eq_two h hf hS)

theorem isQuasisimple_blockSU_of_two_le (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {S : Finset (Fin n)} (hS : 2 ≤ S.card) :
    CFSG.IsQuasisimple ↥(TableBUE.blockSU (K := K) (n := f) S) := by
  have : Finite K := h.finite
  rcases Nat.lt_or_ge S.card 3 with h3 | h3
  · exact isQuasisimple_blockSU_two h hf (by omega)
  · refine TableBUE.isQuasisimple_blockSU S h h.card_eq_sq h3 fun h' => ?_
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h'
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega

theorem isQuasisimple_map_of_isQuasisimple {H : Type} [Group H] {ψ : H →* G}
    (hker : ψ.ker ≤ Subgroup.center H) {U : Subgroup H} (hU : CFSG.IsQuasisimple ↥U) :
    CFSG.Assembly.IsQuasisimple ↥(U.map ψ) := by
  set φ := ψ.comp U.subtype with hφ
  have hkerφ : φ.rangeRestrict.ker ≤ Subgroup.center ↥U := by
    intro u hu
    have hu' : (u : H) ∈ ψ.ker := by
      have h1 : φ.rangeRestrict u = 1 := hu
      have h2 := congrArg Subtype.val h1
      exact h2
    have hz : (u : H) ∈ Subgroup.center H := hker hu'
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    exact Subtype.ext (hz g)
  have hq := CFSG.LocalCores.isQuasisimple_of_surjective hU φ.rangeRestrict
    φ.rangeRestrict_surjective hkerφ
  have hrange : φ.range = U.map ψ := by rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hrange) hq)

theorem isQuasisimple_map_blockSU_of_two_le (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {S : Finset (Fin n)} (hS : 2 ≤ S.card) :
    CFSG.Assembly.IsQuasisimple ↥((TableBUE.blockSU (K := K) (n := f) S).map ψ) :=
  isQuasisimple_map_of_isQuasisimple hker (isQuasisimple_blockSU_of_two_le h hf hS)

end SURepair

end CFSG.StandardType
