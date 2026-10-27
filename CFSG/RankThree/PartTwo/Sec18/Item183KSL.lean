module

public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
import CFSG.RankThree.PartTwo.KFacts.L34Models
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item183K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine (qSub card_qSub)

abbrev SL34 : Type := Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)

theorem card_SL34 : Nat.card SL34 = 60480 :=
  KFacts.L34.card_specialLinearGroup KFacts.L34.card_galoisField_two_two

theorem finite_SL34 : Finite SL34 :=
  Nat.finite_of_card_ne_zero (by rw [card_SL34]; norm_num)

theorem card_center_SL34 : Nat.card (Subgroup.center SL34) = 3 :=
  KFacts.L34.card_center_specialLinearGroup KFacts.L34.card_galoisField_two_two

theorem isQuasisimple_SL34 : IsQuasisimple SL34 := by
  have : Finite (GaloisField 2 2) :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.L34.card_galoisField_two_two]; norm_num)
  exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3
    (GaloisField 2 2) (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem qSub_isPGroup_and_not_dvd :
    IsPGroup 3 (qSub : Subgroup SL34) ∧ ¬ 3 ∣ (qSub : Subgroup SL34).index := by
  have hk := KFacts.L34.card_galoisField_two_two
  refine ⟨IsPGroup.of_card (n := 3) (by rw [card_qSub hk]; norm_num), ?_⟩
  have h := (qSub : Subgroup SL34).card_mul_index
  rw [card_qSub hk, card_SL34] at h
  have : (qSub : Subgroup SL34).index = 2240 := by omega
  rw [this]
  norm_num

theorem pow_three_eq_one_of_isPGroup_SL34 {P : Subgroup SL34} (hP : IsPGroup 3 P) {x : SL34}
    (hx : x ∈ P) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_SL34
  obtain ⟨hQ3, hidx⟩ := qSub_isPGroup_and_not_dvd
  obtain ⟨P', hPP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL34 (hQ3.toSylow hidx) P'
  have hxP' : x ∈ ((g • hQ3.toSylow hidx : Sylow 3 SL34) : Subgroup SL34) := by
    rw [hg]
    exact hPP' hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP'
  obtain ⟨q, hq, rfl⟩ := hxP'
  have h3 := KFacts.L34.qSub_pow_three KFacts.L34.card_galoisField_two_two ⟨q, hq⟩
  have hq3 : q ^ 3 = 1 := by simpa using congrArg Subtype.val h3
  rw [MulAut.smul_def, ← map_pow, hq3, map_one]

theorem card_sylow_SL34 (P : Sylow 3 SL34) : Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_SL34
  obtain ⟨hQ3, hidx⟩ := qSub_isPGroup_and_not_dvd
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (hQ3.toSylow hidx),
    IsPGroup.toSylow_coe, card_qSub KFacts.L34.card_galoisField_two_two]

theorem card_ne_of_isElemAbelian_SL34 {B : Subgroup SL34} (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≠ 27 := by
  intro h27
  have := finite_SL34
  have := hB.1
  have hEA : CFSG.IsElementaryAbelian 3 B :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hB.2 x x.2)⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup SL34, CFSG.IsElementaryAbelian 3 A ∧
      Nat.card A = 3 ^ r} := by
    refine ⟨Nat.card SL34, fun r hr => ?_⟩
    obtain ⟨A, -, hA⟩ := hr
    have h1 : r < 3 ^ r := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card A ≤ Nat.card SL34 := Subgroup.card_le_card_group A
    omega
  have hle := le_csSup hbdd (show (3 : ℕ) ∈ _ from ⟨B, hEA, by rw [h27]; norm_num⟩)
  have hrank := KFacts.L34.pRank_three_specialLinearGroup KFacts.L34.card_galoisField_two_two
  rw [CFSG.pRank] at hrank
  rw [hrank] at hle
  omega

section Iso

variable {X : Type*} [Group X]

theorem card_center_of_SL34 (e : X ≃* SL34) : Nat.card (Subgroup.center X) = 3 := by
  rw [← card_center_SL34, ← Subgroup.map_center_eq e,
    Subgroup.card_map_of_injective (f := (e : X →* SL34)) e.injective]

theorem card_of_SL34 (e : X ≃* SL34) : Nat.card X = 60480 := by
  rw [Nat.card_congr e.toEquiv, card_SL34]

theorem pow_three_eq_one_of_SL34 (e : X ≃* SL34) {P : Subgroup X} (hP : IsPGroup 3 P) {x : X}
    (hx : x ∈ P) : x ^ 3 = 1 := by
  have h := pow_three_eq_one_of_isPGroup_SL34 (hP.map (e : X →* SL34))
    (Subgroup.mem_map_of_mem (e : X →* SL34) hx)
  apply e.injective
  rw [map_pow, map_one]
  exact h

theorem card_sylow_of_SL34 [Finite X] (e : X ≃* SL34) (P : Sylow 3 X) : Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := card_sylow_SL34 (P.mapSurjective (f := (e : X →* SL34)) e.surjective)
  rwa [Sylow.coe_mapSurjective, Subgroup.card_map_of_injective (f := (e : X →* SL34))
    e.injective] at h

theorem card_ne_of_SL34 (e : X ≃* SL34) {B : Subgroup X} (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≠ 27 := by
  have hB' : CFSG.Assembly.IsElemAbelian 3 (B.map (e : X →* SL34)) := by
    have := hB.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      apply Subtype.ext
      change e x * e y = e y * e x
      rw [← map_mul, ← map_mul]
      exact congrArg e (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      change (e x) ^ 3 = 1
      rw [← map_pow, hB.2 x hx, map_one]
  have h := card_ne_of_isElemAbelian_SL34 hB'
  rwa [Subgroup.card_map_of_injective (f := (e : X →* SL34)) e.injective] at h

theorem isQuasisimple_of_SL34 (e : X ≃* SL34) : IsQuasisimple X :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_SL34

end Iso

theorem aschbacherSolvableCore_eq_pCore_of_SL34 {X : Type} [Group X] [Finite X]
    (e : X ⧸ CFSG.pCore 2 X ≃* SL34) : aschbacherSolvableCore 3 X = CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  refine le_antisymm ?_ (hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num))
  set Q := CFSG.pCore 2 X with hQ
  set f := QuotientGroup.mk' Q with hf
  set θX := aschbacherSolvableCore 3 X with hθX
  have hθn : θX.Normal := by
    have := hθ.2.1
    infer_instance
  set Z := θX.map f with hZ
  have hZn : Z.Normal := hθn.map f (QuotientGroup.mk'_surjective _)
  have h3 : ¬ 3 ∣ Nat.card Z := fun h => hθ.2.2.1 (h.trans (Subgroup.card_map_dvd θX f))
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups
      (isQuasisimple_of_SL34 e) hZn with htop | hc
  · exfalso
    apply h3
    rw [htop, Subgroup.card_top, card_of_SL34 e]
    norm_num
  · have hdvd : Nat.card Z ∣ 3 := by
      have := Subgroup.card_dvd_of_le hc
      rwa [card_center_of_SL34 e] at this
    have h1 : Nat.card Z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exact absurd (dvd_of_eq h.symm) h3
    have hbot : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z h1
    rw [hZ, Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk'] at hbot
    exact hbot

section InG

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem inSubgroup_theta_eq_of_SL34 (e : K ⧸ CFSG.pCore 2 K ≃* SL34) :
    inSubgroup (aschbacherSolvableCore 3) K = CFSG.Open.pCoreOf 2 K := by
  rw [inSubgroup, CFSG.Open.pCoreOf, aschbacherSolvableCore_eq_pCore_of_SL34 e]

omit [Finite G] in
theorem mk_eq_mk_iff {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    QuotientGroup.mk' (CFSG.pCore 2 K) (⟨x, hx⟩ : K) =
        QuotientGroup.mk' (CFSG.pCore 2 K) (⟨y, hy⟩ : K) ↔
      x * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Sec18.mem_pCore_iff_mem_pCoreOf]
  have hxN : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro h
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN _).mp (Subgroup.inv_mem _ h)
    have e : x * (x⁻¹ * y)⁻¹ * x⁻¹ = x * y⁻¹ := by group
    rwa [e] at h1
  · intro h
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) _).mp (Subgroup.inv_mem _ h)
    have e : x⁻¹ * (x * y⁻¹)⁻¹ * x⁻¹⁻¹ = x⁻¹ * y := by group
    rwa [e] at h1

theorem mem_thetaQuotCentralizer_iff_of_SL34 (e : K ⧸ CFSG.pCore 2 K ≃* SL34) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Sec4.thetaQuotCentralizer K ↔ ∀ y ∈ K, g * y * g⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  rw [Sec6.mem_thetaQuotCentralizer_iff, inSubgroup_theta_eq_of_SL34 e]
  constructor
  · rintro ⟨-, h⟩ y hy
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hy) _).mp (h y hy)
    have e : y * (y⁻¹ * (g * y * g⁻¹)) * y⁻¹ = g * y * g⁻¹ * y⁻¹ := by group
    rwa [e] at h1
  · intro h
    refine ⟨hg, fun y hy => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (K.inv_mem hy)) _).mp (h y hy)
    have e : y⁻¹ * (g * y * g⁻¹ * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * (g * y * g⁻¹) := by group
    rwa [e] at h1

theorem sectionCentralizer_eq_of_SL34 (e : K ⧸ CFSG.pCore 2 K ≃* SL34) {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (K : Set G)) :
    sectionCentralizer E K (CFSG.Open.pCoreOf 2 K) =
      ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (mem_thetaQuotCentralizer_iff_of_SL34 e (hE hx)).mpr h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (mem_thetaQuotCentralizer_iff_of_SL34 e (hE hx)).mp h⟩

end InG

end CFSG.RankThree.PartTwo.Sec18.Item183K
