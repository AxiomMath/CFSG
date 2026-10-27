module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsL62
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalCoords
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalSixCent
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalSixPerfect
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.GroupTheory.WeirSylow.UniqueE27Linear
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup CFSG.ClassicalGroups
open CFSG.ClassicalGroups.SLnThreeLocal
open CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811 IsSignedCoords)

private theorem l6_setup
    {Y : Type} [Group Y] [Finite Y]
    (h : IsLie811 Y .l6 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ∧ center Y = ⊥ ∧ ¬ 3 ∣ Nat.card (center Y) ∧
      ∃ e : Y ⧸ center Y ≃* StatedProj (StatedSL 6 K),
        ∃ h₀ : IsSignedCoords ((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7)).range)
            (c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7)),
          UniqueElemSylow 3 3 (StatedProj (StatedSL 6 K)) ∧
          ¬ 3 ∣ Nat.card ((StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K)) ∧
          (StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K) = ⊥ := by
  have hZ : center Y = ⊥ := Theorem82.center_eq_bot_of_isLie811_of_ne h (by decide)
    (fun hf => by cases hf)
  have hZ3 : ¬ 3 ∣ Nat.card (center Y) := by
    rw [hZ, Subgroup.card_bot]; norm_num
  obtain ⟨-, -, -, hm⟩ := h
  rcases hm with ⟨-, hLM⟩ | ⟨h1, -⟩
  · obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
      Theorem82.ModelUnpack.exists_model_of_lieModel_psl (by norm_num) hLM
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have hK3 : Nat.card K % 3 = 2 := by rw [hK2]
    have h₀ : IsSignedCoords ((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7)).range)
        (c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7)) :=
      c₀_signedCoords (three_ne_zero_of_natCard_mod_three hK3) (Or.inl rfl)
    have hU : UniqueElemSylow 3 3 (StatedProj (StatedSL 6 K)) :=
      CFSG.GroupTheory.WeirSylow.uniqueElemSylow_statedProj_statedSL_of_mod_three_eq_two K
        hK3 (Or.inl rfl)
    have hN3 : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K)) :=
      Theorem82.ModelUnpack.not_dvd_card_scalars_of_not_dvd_card_sub_one Nat.prime_three
        (by rw [hK2]; norm_num) _
    have hN : (StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K) = ⊥ := by
      rw [StatedAPI.statedScalars_eq_bot_of_card_two hK2, Subgroup.bot_subgroupOf]
    exact ⟨K, inferInstance, inferInstance, hK2, hZ, hZ3, e, h₀, hU, hN3, hN⟩
  · exact absurd h1 (by decide)

private theorem exists_perfect_map_le_centralizer {H Y : Type} [Group H] [Group Y]
    (φ : H →* Y) (hφ : Function.Injective φ) {x : H} {y : Y} (hxy : φ x = y)
    {J : Subgroup H} (hJ : J ≤ Subgroup.centralizer ({x} : Set H))
    (hperf : ⁅J, J⁆ = J) (h7 : 7 ∣ Nat.card J) :
    ∃ L : Subgroup Y, L ≤ Subgroup.centralizer ({y} : Set Y) ∧ ⁅L, L⁆ = L ∧
      7 ∣ Nat.card L := by
  refine ⟨J.map φ, ?_, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    have hj' : j ∈ Subgroup.centralizer ({x} : Set H) := hJ hj
    rw [Subgroup.mem_centralizer_iff] at hj' ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [← hxy, ← map_mul, ← map_mul, ← hj' x (Set.mem_singleton x)]
  · rw [← Subgroup.map_commutator, hperf]
  · rwa [Subgroup.card_map_of_injective hφ]

theorem k7L6TwoCentA_holds :
    K7L6TwoCentA := by
  intro Y _ _ h A hA h27
  obtain ⟨K, _, _, hK2, hZ, hZ3, e, h₀, hU, hN3, hN⟩ := l6_setup h
  have hZi : Function.Injective (QuotientGroup.mk' (center Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hNi : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  let πY : Y ≃* Y ⧸ center Y := MulEquiv.ofBijective _ ⟨hZi, QuotientGroup.mk'_surjective _⟩
  let πH : StatedSL 6 K ≃* StatedProj (StatedSL 6 K) :=
    MulEquiv.ofBijective _ ⟨hNi, QuotientGroup.mk'_surjective _⟩
  have h1 : Nat.card (centralizer
      ((A.map (QuotientGroup.mk' (center Y)) : Subgroup (Y ⧸ center Y)) :
        Set (Y ⧸ center Y))) = Nat.card (centralizer (A : Set Y)) :=
    CFSG.GroupTheory.CoprimeTransport.card_centralizer_map_mulEquiv πY A
  have h3 : Nat.card (centralizer
      ((((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7)).range).map
        (QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K))) :
          Subgroup (StatedProj (StatedSL 6 K))) : Set (StatedProj (StatedSL 6 K)))) =
      Nat.card (centralizer
        (((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7)).range : Subgroup (StatedSL 6 K)) :
          Set (StatedSL 6 K))) :=
    CFSG.GroupTheory.CoprimeTransport.card_centralizer_map_mulEquiv πH _
  rw [← h1, Theorem82.ModelTransport.card_centralizer_map_eq_of_model hU hN3 hZ3 e
    h₀.isElemAbelian h₀.card_eq hA h27, h3]
  exact card_centralizer_range_c₀_six hK2

theorem k7L6TwoPerfect_holds :
    K7L6TwoPerfect := by
  intro Y _ _ h A hA h27 c hc v hv
  obtain ⟨K, _, _, hK2, hZ, hZ3, e, h₀, hU, hN3, hN⟩ := l6_setup h
  obtain ⟨g, hg⟩ := h₀.exists_conj_eq_of_model _ hN3 hU (center Y) hZ3 e hc
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hZi : Function.Injective (QuotientGroup.mk' (center Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hNi : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  let πH : StatedSL 6 K ≃* StatedProj (StatedSL 6 K) :=
    MulEquiv.ofBijective _ ⟨hNi, QuotientGroup.mk'_surjective _⟩
  let πY : Y ≃* Y ⧸ center Y := MulEquiv.ofBijective _ ⟨hZi, QuotientGroup.mk'_surjective _⟩
  let Θ : StatedSL 6 K ≃* Y := (πH.trans e.symm).trans πY.symm
  have hΘ : ∀ x, e (QuotientGroup.mk' (center Y) (Θ x)) = QuotientGroup.mk' _ x := fun x => by
    change e (πY (πY.symm (e.symm (πH x)))) = πH x
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hcw : ∀ w, c w = Θ (g₀ * c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) w * g₀⁻¹) := fun w => by
    apply hZi
    apply e.injective
    rw [hΘ, hg w, map_mul, map_mul, map_inv]
  let φ : StatedSL 6 K →* Y :=
    Θ.toMonoidHom.comp (MulAut.conj g₀).toMonoidHom
  have hφ : Function.Injective φ := Θ.injective.comp (MulAut.conj g₀).injective
  have hcv : c (Multiplicative.ofAdd v) =
      φ (c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7) (Multiplicative.ofAdd v)) := by
    rw [hcw]
    rfl
  rcases hv with rfl | rfl
  · obtain ⟨J, hJ, hperf, h7⟩ := exists_perfect_le_centralizer_c₀_six_weight_one hK2
    exact exists_perfect_map_le_centralizer φ hφ hcv.symm hJ hperf h7
  · obtain ⟨J, hJ, hperf, h7⟩ := exists_perfect_le_centralizer_c₀_six_weight_three hK2
    exact exists_perfect_map_le_centralizer φ hφ hcv.symm hJ hperf h7

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
