module

public import CFSG.Permutation.FiveTransitive.Degree25FiveCodeAutomorphism

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup
open FiveTransitive.Degree24

private theorem fourFive_subgroup_separates_coordinate_kernels
    (A : Subgroup Degree20.FourFiveBase)
    (hAcard : Nat.card A = 125)
    (hnoWeightOne :
      ¬∃ a : A,
        fiveWeight
          ((a : A) : Degree20.FourFiveBase) = 1)
    (i j : Fin 4) (hij : i ≠ j) :
    ∃ a : A, a.1 i = 1 ∧ a.1 j ≠ 1 := by
  classical
  let B : AddSubgroup FiveVector :=
    A.toAddSubgroup'
  let W : Submodule (ZMod 5) FiveVector :=
    AddSubgroup.toZModSubmodule 5 B
  let eAW : Additive A ≃+ W :=
    fourFiveSubgroupAddEquiv A
  have hWcard : Nat.card W = 125 := by
    calc
      Nat.card W = Nat.card (Additive A) :=
        Nat.card_congr eAW.symm.toEquiv
      _ = Nat.card A := Nat.card_congr Additive.toMul
      _ = 125 := hAcard
  have hnoWeightOneW :
      ¬∃ w : W, fiveWeight w = 1 := by
    rintro ⟨w, hw⟩
    apply hnoWeightOne
    let a : Additive A := eAW.symm w
    refine ⟨a.toMul, ?_⟩
    change fiveWeight (eAW a) = 1
    rw [eAW.apply_symm_apply]
    exact hw
  obtain ⟨w, hwi, hwj⟩ :=
    five_submodule_separates_coordinates
      W hWcard hnoWeightOneW i j hij
  let a : Additive A := eAW.symm w
  refine ⟨a.toMul, ?_, ?_⟩
  · change Multiplicative.ofAdd (w.1 i) = 1
    rw [hwi]
    rfl
  · change Multiplicative.ofAdd (w.1 j) ≠ 1
    simpa using hwj

private theorem fourFive_subgroup_coordinate_surjective
    (A : Subgroup Degree20.FourFiveBase)
    (hAcard : Nat.card A = 125)
    (hnoWeightOne :
      ¬∃ a : A,
        fiveWeight
          ((a : A) : Degree20.FourFiveBase) = 1)
    (i : Fin 4) (z : Degree20.FiveCycle) :
    ∃ a : A, a.1 i = z := by
  classical
  let j : Fin 4 :=
    if i = 0 then 1 else 0
  have hji : j ≠ i := by
    dsimp [j]
    split
    · omega
    · omega
  obtain ⟨a, _, hai⟩ :=
    fourFive_subgroup_separates_coordinate_kernels
      A hAcard hnoWeightOne j i hji
  have hcardFive :
      Nat.card Degree20.FiveCycle = 5 := by
    change Nat.card (ZMod 5) = 5
    rw [Nat.card_zmod]
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hzmem :
      z ∈ Subgroup.zpowers (a.1 i) :=
    mem_zpowers_of_prime_card hcardFive hai
  obtain ⟨k, hk⟩ :=
    Subgroup.mem_zpowers_iff.mp hzmem
  refine ⟨a ^ k, ?_⟩
  change (a.1 i) ^ k = z
  exact hk

theorem fourFive_subgroup_exists_weight_four
    (A : Subgroup Degree20.FourFiveBase)
    (hAcard : Nat.card A = 125)
    (hnoWeightOne :
      ¬∃ a : A,
        fiveWeight
          ((a : A) : Degree20.FourFiveBase) = 1) :
    ∃ a : A,
      fiveWeight
        ((a : A) : Degree20.FourFiveBase) = 4 := by
  classical
  let B : AddSubgroup FiveVector :=
    A.toAddSubgroup'
  let W : Submodule (ZMod 5) FiveVector :=
    AddSubgroup.toZModSubmodule 5 B
  let eAW : Additive A ≃+ W :=
    fourFiveSubgroupAddEquiv A
  have hWcard : Nat.card W = 125 := by
    calc
      Nat.card W = Nat.card (Additive A) :=
        Nat.card_congr eAW.symm.toEquiv
      _ = Nat.card A := Nat.card_congr Additive.toMul
      _ = 125 := hAcard
  have hnoWeightOneW :
      ¬∃ w : W, fiveWeight w = 1 := by
    rintro ⟨w, hw⟩
    apply hnoWeightOne
    let a : Additive A := eAW.symm w
    refine ⟨a.toMul, ?_⟩
    change fiveWeight (eAW a) = 1
    rw [eAW.apply_symm_apply]
    exact hw
  obtain ⟨w, hw⟩ :=
    five_submodule_exists_weight_four
      W hWcard hnoWeightOneW
  let a : Additive A := eAW.symm w
  refine ⟨a.toMul, ?_⟩
  change fiveWeight (eAW a) = 4
  rw [eAW.apply_symm_apply]
  exact hw

private theorem fourFive_subgroup_centralizer_card_dvd_six_hundred_twenty_five
    (A : Subgroup Degree20.FourFiveBase)
    (hAcard : Nat.card A = 125)
    (hnoWeightOne :
      ¬∃ a : A,
        fiveWeight
          ((a : A) : Degree20.FourFiveBase) = 1) :
    let ι : Degree20.FourFiveBase →*
        Equiv.Perm Degree20.TwentyFivePoints :=
      MulAction.toPermHom
        Degree20.FourFiveBase
        Degree20.TwentyFivePoints
    let R : Subgroup
        (Equiv.Perm Degree20.TwentyFivePoints) :=
      A.map ι
    Nat.card
        (Subgroup.centralizer
          (R : Set
            (Equiv.Perm Degree20.TwentyFivePoints))) ∣
      625 := by
  classical
  let Ω := Degree20.TwentyFivePoints
  let ι : Degree20.FourFiveBase →*
      Equiv.Perm Ω :=
    MulAction.toPermHom Degree20.FourFiveBase Ω
  let R : Subgroup (Equiv.Perm Ω) :=
    A.map ι
  let C : Subgroup (Equiv.Perm Ω) :=
    Subgroup.centralizer (R : Set (Equiv.Perm Ω))
  have hpreservesBlock
      (c : C) (i : Fin 4) (z : Degree20.FiveCycle) :
      (c.1 (i, z)).1 = i := by
    let j : Fin 4 := (c.1 (i, z)).1
    by_contra hji
    have hij : i ≠ j :=
      fun h => hji h.symm
    obtain ⟨a, hai, haj⟩ :=
      fourFive_subgroup_separates_coordinate_kernels
        A hAcard hnoWeightOne i j hij
    let ra : R :=
      ⟨ι a.1, Subgroup.mem_map_of_mem ι a.prop⟩
    have hcomm :
        Commute (c.1 : Equiv.Perm Ω)
          (ra.1 : Equiv.Perm Ω) :=
      (c.prop ra.1 ra.prop).symm
    have happ :=
      congrFun
        (congrArg DFunLike.coe hcomm.eq)
        (i, z)
    have hfix :
        (ra.1 : Equiv.Perm Ω) (c.1 (i, z)) =
          c.1 (i, z) := by
      calc
        (ra.1 : Equiv.Perm Ω) (c.1 (i, z)) =
            ((ra.1 : Equiv.Perm Ω) *
              (c.1 : Equiv.Perm Ω)) (i, z) := rfl
        _ = ((c.1 : Equiv.Perm Ω) *
              (ra.1 : Equiv.Perm Ω)) (i, z) := by
            rw [hcomm.eq]
        _ = c.1 (i, z) := by
          change c.1 (i, a.1 i * z) = c.1 (i, z)
          rw [hai, one_mul]
    have hsecond := congrArg Prod.snd hfix
    change a.1 j * (c.1 (i, z)).2 =
      (c.1 (i, z)).2 at hsecond
    apply haj
    rw [← mul_right_cancel_iff
      (a := (c.1 (i, z)).2)]
    simpa using hsecond
  let translation (c : C) :
      Degree20.FourFiveBase :=
    fun i => (c.1 (i, 1)).2
  have hformula
      (c : C) (i : Fin 4) (z : Degree20.FiveCycle) :
      c.1 (i, z) =
        (i, translation c i * z) := by
    obtain ⟨a, hai⟩ :=
      fourFive_subgroup_coordinate_surjective
        A hAcard hnoWeightOne i z
    let ra : R :=
      ⟨ι a.1, Subgroup.mem_map_of_mem ι a.prop⟩
    have hcomm :
        Commute (c.1 : Equiv.Perm Ω)
          (ra.1 : Equiv.Perm Ω) :=
      (c.prop ra.1 ra.prop).symm
    have happ :=
      congrFun
        (congrArg DFunLike.coe hcomm.eq)
        (i, (1 : Degree20.FiveCycle))
    apply Prod.ext
    · exact hpreservesBlock c i z
    · have hbaseFirst :=
        hpreservesBlock c i
          (1 : Degree20.FiveCycle)
      have hsecond := congrArg Prod.snd happ
      change
        (c.1 (i, a.1 i * 1)).2 =
          a.1 (c.1 (i, 1)).1 *
            (c.1 (i, 1)).2 at hsecond
      rw [hbaseFirst, hai, mul_one] at hsecond
      simpa only [translation, mul_comm] using hsecond
  let translationHom :
      C →* Degree20.FourFiveBase := {
    toFun := translation
    map_one' := by
      funext i
      rfl
    map_mul' c d := by
      funext i
      have hc :=
        hformula c i (translation d i)
      have hd :=
        hformula d i (1 : Degree20.FiveCycle)
      change
        ((c.1 * d.1) (i, 1)).2 =
          translation c i * translation d i
      rw [Equiv.Perm.mul_apply, hd, mul_one, hc] }
  have htranslationInjective :
      Function.Injective translationHom := by
    intro c d hcd
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rcases x with ⟨i, z⟩
    rw [hformula c i z, hformula d i z]
    rw [show translation c = translation d by
      exact hcd]
  have hdvd :
      Nat.card C ∣
        Nat.card Degree20.FourFiveBase :=
    Subgroup.card_dvd_of_injective
      translationHom htranslationInjective
  rw [Degree20.card_fourFiveBase] at hdvd
  exact hdvd

theorem subgroup_centralizer_card_dvd_six_hundred_twenty_five_of_equivariant
    (Y : Type) [Fintype Y] [DecidableEq Y]
    (A : Subgroup Degree20.FourFiveBase)
    (hAcard : Nat.card A = 125)
    (hnoWeightOne :
      ¬∃ a : A,
        fiveWeight
          ((a : A) : Degree20.FourFiveBase) = 1)
    (R : Subgroup (Equiv.Perm Y))
    (eAR : A ≃* R)
    (d : Y ≃ Degree20.TwentyFivePoints)
    (hequivariant :
      ∀ (a : A) (y : Y),
        d (((eAR a : R) : Equiv.Perm Y) y) =
          (MulAction.toPermHom
            Degree20.FourFiveBase
            Degree20.TwentyFivePoints)
              ((a : A) :
                Degree20.FourFiveBase) (d y)) :
    Nat.card
        (Subgroup.centralizer
          (R : Set (Equiv.Perm Y))) ∣
      625 := by
  classical
  let ι : Degree20.FourFiveBase →*
      Equiv.Perm Degree20.TwentyFivePoints :=
    MulAction.toPermHom
      Degree20.FourFiveBase
      Degree20.TwentyFivePoints
  let R₀ : Subgroup
      (Equiv.Perm Degree20.TwentyFivePoints) :=
    A.map ι
  let C : Subgroup (Equiv.Perm Y) :=
    Subgroup.centralizer
      (R : Set (Equiv.Perm Y))
  let C₀ : Subgroup
      (Equiv.Perm Degree20.TwentyFivePoints) :=
    Subgroup.centralizer
      (R₀ : Set
        (Equiv.Perm Degree20.TwentyFivePoints))
  let conjugation :
      Equiv.Perm Y →*
        Equiv.Perm Degree20.TwentyFivePoints :=
    d.permCongrHom.toMonoidHom
  have hconjugation (a : A) :
      conjugation
          ((eAR a : R) : Equiv.Perm Y) =
        ι ((a : A) :
          Degree20.FourFiveBase) := by
    apply Equiv.ext
    intro y
    change
      d (((eAR a : R) : Equiv.Perm Y)
        (d.symm y)) =
        ι ((a : A) :
          Degree20.FourFiveBase) y
    rw [hequivariant]
    rw [d.apply_symm_apply]
  have hconjugationMem :
      ∀ c : C, conjugation c.1 ∈ C₀ := by
    intro c
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨a, ha, rfl⟩ :=
      Subgroup.mem_map.mp hp
    let aA : A := ⟨a, ha⟩
    have hc :
        Commute (c.1 : Equiv.Perm Y)
          ((eAR aA : R) : Equiv.Perm Y) :=
      (c.prop
        ((eAR aA : R) : Equiv.Perm Y)
        (eAR aA).prop).symm
    have hmapped := hc.map conjugation
    rw [hconjugation aA] at hmapped
    exact hmapped.symm
  let conjugationC : C →*
      Equiv.Perm Degree20.TwentyFivePoints :=
    conjugation.comp C.subtype
  let centralizerMap : C →* C₀ :=
    conjugationC.codRestrict C₀ hconjugationMem
  have hcentralizerMapInjective :
      Function.Injective centralizerMap := by
    intro c₁ c₂ h
    apply Subtype.ext
    apply d.permCongrHom.injective
    change conjugation c₁.1 = conjugation c₂.1
    exact congrArg Subtype.val h
  have hCdvdC₀ :
      Nat.card C ∣ Nat.card C₀ :=
    Subgroup.card_dvd_of_injective
      centralizerMap hcentralizerMapInjective
  have hC₀dvd :
      Nat.card C₀ ∣ 625 := by
    simpa only [ι, R₀, C₀] using
      fourFive_subgroup_centralizer_card_dvd_six_hundred_twenty_five
        A hAcard hnoWeightOne
  exact hCdvdC₀.trans hC₀dvd

end FiveTransitive.Degree25

end CFSG
