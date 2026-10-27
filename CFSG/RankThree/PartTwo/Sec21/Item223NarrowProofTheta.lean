module

public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofTheta
import CFSG.RankThree.PartTwo.Sec21.Item223NarrowProofTools
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)
open Item223PrintProof
open scoped commutatorElement

theorem item223ThetaTrivial_of_narrow
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (h45 : Sec4.Item4_5)
    (h222 : Item222) (hKW : KOfWellDefinedAll) : Item223ThetaTrivial := by
  intro G _ _ A E U c L hpair hA81 φ hφ X hX hKX m hm ⟨eX⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hpair.standing
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe haA ha1 X hXa
  obtain ⟨n, -, -, ⟨eK⟩⟩ := exists_mulEquiv_kOf_odd h222 hpair hA81 hφ
  obtain ⟨z, hzA, hzK, hz3⟩ := exists_mem_inf_kOf hAF (hKW G A E U c L hpair) hφ eK
  have hXtop : X ≠ ⊤ := fun hXt =>
    Sec6.centralizer_ne_top_of_ne_one hst.toTheoremFourHyp ha1
      (top_le_iff.mp (hXt ▸ Sec6.le_centralizer_of_mem_thetaComponentsAt hXa))
  have hX4 : SectionFourHyp X := hst.toTheoremFourHyp.sectionFourHyp hXtop
  have hXp : Group.IsPerfect X := Sec6.isPerfect_of_mem_thetaComponentsAt hXa
  obtain ⟨hTXs, -, hTX3, -⟩ := solvable_prime_complement_core_characterization (H := X)
    Nat.prime_three
  suffices hcore : aschbacherSolvableCore 3 X = ⊥ by
    rw [inSubgroup, hcore, Subgroup.map_bot]
  have hAT : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
    le_normalizer_theta hAX
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hcardT : Nat.card (inSubgroup (aschbacherSolvableCore 3) X) =
      Nat.card (aschbacherSolvableCore 3 X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hcop : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) X)) := by
    rw [hcardT]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hTX3
  obtain ⟨S, hSA⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow 3 2
    Nat.prime_three Nat.prime_two A _ hA3 hAT hcop
  have hS2 : IsPGroup 2 ((S : Subgroup (inSubgroup (aschbacherSolvableCore 3) X)).map
      (inSubgroup (aschbacherSolvableCore 3) X).subtype) :=
    S.isPGroup'.map _
  have hcomm := Sec6.commutator_eq_bot_of_mem_partTwoS hpair.mem_S haA ha1 le_rfl
    ((Subgroup.map_subtype_le _).trans (theta_le_theta_centralizer hXa)) hS2 hSA
  have hzS : ∀ s ∈ (S : Subgroup (inSubgroup (aschbacherSolvableCore 3) X)).map
      (inSubgroup (aschbacherSolvableCore 3) X).subtype, z * s = s * z := by
    intro s hs
    have h1 := Subgroup.commutator_mem_commutator hs hzA
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  let w : aschbacherSolvableCore 3 X ≃* inSubgroup (aschbacherSolvableCore 3) X :=
    (aschbacherSolvableCore 3 X).equivMapOfInjective X.subtype X.subtype_injective
  have hw : ∀ s₀ : inSubgroup (aschbacherSolvableCore 3) X,
      (((w.symm s₀ : aschbacherSolvableCore 3 X) : X) : G) = s₀ := by
    intro s₀
    have h1 : ((w (w.symm s₀) : inSubgroup (aschbacherSolvableCore 3) X) : G) =
        X.subtype (w.symm s₀) :=
      Subgroup.coe_equivMapOfInjective_apply (aschbacherSolvableCore 3 X) X.subtype
        X.subtype_injective (w.symm s₀)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  let SX : Sylow 2 (aschbacherSolvableCore 3 X) :=
    Sylow.mapSurjective (f := w.symm.toMonoidHom) w.symm.surjective S
  set z' : X := ⟨z, hKX hzK⟩ with hz'
  have hz'T : z' ∉ aschbacherSolvableCore 3 X := by
    intro h
    have hdvd : orderOf (⟨z', h⟩ : aschbacherSolvableCore 3 X) ∣
        Nat.card (aschbacherSolvableCore 3 X) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz3] at hdvd
    exact hTX3 hdvd
  have hzSX : ∀ s ∈ (SX : Subgroup (aschbacherSolvableCore 3 X)).map
      (aschbacherSolvableCore 3 X).subtype, z' * s = s * z' := by
    rintro _ ⟨t, ⟨s₀, hs₀, rfl⟩, rfl⟩
    apply Subtype.ext
    have h1 := hzS _ ⟨s₀, hs₀, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_subtype]
    change z * ((w.symm s₀ : aschbacherSolvableCore 3 X) : X) =
      ((w.symm s₀ : aschbacherSolvableCore 3 X) : X) * z
    rw [hw s₀]
    exact h1
  exact Item223NarrowProof.eq_bot_of_centralizes_sylow hGA hX4.localRank_lt hXp hTXs hTX3
    (by omega) eX hz'T SX hzSX

end CFSG.RankThree.PartTwo.Sec21
