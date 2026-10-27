module

public import CFSG.Quasithin.Vol2.F134L2
public import CFSG.Quasithin.Vol2.F134Cyclic
public import CFSG.Quasithin.Vol2.F134Suzuki
public import CFSG.Quasithin.Vol2.F134J1
public import CFSG.Quasithin.Vol2.F134Ree
public import CFSG.Quasithin.Vol2.F134Tits
public import CFSG.Quasithin.Vol2.F134M12
public import CFSG.Quasithin.Vol2.F134U33Native
public import CFSG.Quasithin.Vol2.F134A7Config
public import CFSG.Quasithin.Vol2.F134J1Local
public import CFSG.Quasithin.Vol2.F134M22
public import CFSG.Quasithin.Vol2.F134HS
public import CFSG.Quasithin.Vol2.F134M23
public import CFSG.Quasithin.Vol2.F134M24
public import CFSG.Quasithin.Vol2.F134Ru
public import CFSG.Quasithin.Vol2.F134TitsE9

public section

namespace CFSG.Quasithin.P134

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

theorem facts134E9_psl2OddOrder : ∀ p f : ℕ, p.Prime → p ≠ 2 → (f = 1 ∨ f = 2) →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 p f :=
  fun _ _ _ _ _ _ _ h => F134.three_dvd_card_of_statedPSL_two h

theorem facts134E9_psl3OddOrder : ∀ p : ℕ, p.Prime → p ≠ 2 →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1 :=
  fun _ _ _ _ _ h => F134.three_dvd_card_of_statedPSL_three h

theorem facts134E9_psu3OddOrder : ∀ p : ℕ, p.Prime → p ≠ 2 →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1 :=
  fun _ _ _ _ _ h => F134.three_dvd_card_of_statedPSU_three h

theorem facts134E9_psl2EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n :=
  fun _ _ _ h => F134.three_dvd_card_of_statedPSL_two h

theorem facts134E9_psl3EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n :=
  fun _ _ _ h => F134.three_dvd_card_of_statedPSL_three h

theorem facts134E9_psu3EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n :=
  fun _ _ _ h => F134.three_dvd_card_of_statedPSU_three h

theorem facts134E9_psp4EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSp 2 2 n :=
  fun _ _ _ h => F134.three_dvd_card_of_statedPSp_two_two h

theorem facts134E9_g2EvenOrder
    : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n :=
  fun _ _ _ h => F134.three_dvd_card_of_g2_two h

theorem facts134E9_d4EvenOrder
    : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n :=
  fun _ _ _ h => F134.three_dvd_card_of_trialityD4_two h

theorem facts134E9_f4EvenOrder
    : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n :=
  fun _ _ _ h => F134.three_dvd_card_of_twistedF4 h

theorem facts134E9_titsOrder
    : OrderThree fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1 :=
  fun _ _ h => F134.three_dvd_card_of_tits h

theorem facts134E9_szOrder
    : ∀ n : ℕ, ∀ (X : Type) [Group X], SuzukiModel X 2 n →
    ¬ 3 ∣ Nat.card X :=
  fun _ _ _ h => F134.not_three_dvd_card_of_suzukiModel h

theorem facts134E9_psl45Order : ∀ n : ℕ, (n = 4 ∨ n = 5) →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL n 2 1 :=
  fun _ hn _ _ h => F134.three_dvd_card_of_statedPSL_four_five hn h

theorem facts134E9_j1Order :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1) := by
  rintro X _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv, F134.card_carrier_J1]
  norm_num

theorem facts134E9_psl2OddCyclic
    : ∀ p f : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → (f = 1 ∨ f = 2) →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 p f :=
  fun _ _ _ _ hp3 _ => F134.noE9Config_of_noElemNine fun _ _ h =>
    F134.noElemNine_of_statedPSL_two hp3 h

theorem facts134E9_psl2EvenCyclic : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n :=
  fun _ => F134.noE9Config_of_noElemNine fun _ _ h =>
    F134.noElemNine_of_statedPSL_two (by norm_num) h

theorem facts134E9_psl3Minus : ∀ p : ℕ, p.Prime → p ≠ 2 → p % 3 = 2 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1 :=
  fun _ _ _ hp3 => F134.noE9Config_of_noElemNine fun _ _ h =>
    F134.noElemNine_of_statedPSL_three hp3 h

theorem facts134E9_psu3Plus : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1 :=
  fun _ _ hp3 => F134.noE9Config_of_noElemNine fun _ _ h =>
    F134.noElemNine_of_statedPSU_three hp3 h

theorem facts134E9_j1 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1) :=
  F134.noE9Config_of_not_dvd fun X _ ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, F134.card_carrier_J1]
    norm_num

theorem card_alternating_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem facts134E9_alt6 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 6)) :=
  F134.noE9Config_of_simple_card_360 fun _ _ h =>
    ⟨alternatingGroup (Fin 6), inferInstance, inferInstance,
      alternatingGroup.isSimpleGroup (by simp), card_alternating_six, h⟩

theorem facts134E9_alt7 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 7)) :=
  F134.noE9Config_alt7

theorem facts134E9_psl2Nine :
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 3 2 := by
  refine F134.noE9Config_of_simple_card_360 fun X _ h => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card (StatedProj (StatedSL 2 K)) = 360 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2), hK]
    decide
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hK]; norm_num))
      (Or.inr (by rw [hK]; norm_num))
  exact ⟨StatedProj (StatedSL 2 K), inferInstance,
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num),
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.isSimpleGroup, hcard, ⟨e⟩⟩

theorem facts134E9_m12 :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12) := by
  refine ⟨fun X _ ⟨e⟩ => ?_, F134.noE9Config_m12 fun X _ ⟨e⟩ => ⟨e.trans F134.carrierM12Equiv⟩⟩
  rw [Nat.card_congr (e.trans F134.carrierM12Equiv).toEquiv]
  exact F134.three_dvd_card_m12

theorem facts134E9_m22 :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22) :=
  ⟨F134.orderThree_m22, F134.noE9Config_m22⟩

theorem facts134E9_j2 :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2) :=
  ⟨F134.orderThree_j2, F134.noE9Config_j2⟩

theorem facts134E9_hs :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS) :=
  ⟨F134.orderThree_hs, F134.noE9Config_hs⟩

theorem facts134E9_m23 :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23) :=
  ⟨F134.orderThree_m23, F134.noE9Config_m23⟩

theorem facts134E9_m24 :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24) :=
  ⟨F134.orderThree_m24, F134.noE9Config_m24⟩

theorem facts134E9_ru :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru) :=
  ⟨F134.orderThree_ru, F134.noE9Config_ru⟩

theorem facts134E9_psu3Three :
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 3 1 :=
  F134.noE9Config_psu3_three

theorem facts134E9_tits
    :
    NoE9Config fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1 :=
  F134.noE9Config_tits

theorem facts134E9_psl2EvenBorel :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (n : ℕ) (y : A),
      SQTKHypCat A → StatedClassicalModel ↥L .PSL 2 2 n → U ≤ B → B ≤ L → IsSylowTwoOf U L →
        (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) → y ∈ B → orderOf y = 3 →
          Even n :=
  fun _ _ _ _ _ _ _ _ _ hL hUB hBL hU hB hy hy3 =>
    F134.even_of_le_statedPSL_two_two hL hUB hBL hU hB hy hy3

theorem facts134E9_szOut
    : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
    SQTKHypCat A → SuzukiModel ↥L 2 n → ∀ a ∈ Subgroup.normalizer (L : Set A),
      ∀ b ∈ Subgroup.normalizer (L : Set A), ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A) :=
  fun _ _ _ _ _ _ hL _ ha _ hb => F134.commutator_mem_of_suzukiModel hL ha hb

theorem facts134E9_j1Local
    : ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (y g : A),
    SQTKHypCat A → Nonempty (↥L ≃* NativeSporadic.Carrier .J1) → U ≤ B → B ≤ L →
      IsSylowTwoOf U L → (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) → y ∈ B →
      orderOf y = 3 → g ∈ Subgroup.normalizer (L : Set A) →
      g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) → g * y * g⁻¹ = y :=
  fun A _ _ L B U y g _ ⟨e⟩ hUB hBL hU hB hyB hy hgL hgU hgy =>
    F134.j1_local A L B U y g e hUB hBL hU hB hyB hy hgL hgU hgy

theorem facts134E9_he :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He) := by
  rintro X _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from
    CFSG.Sporadic.He.card_He]
  norm_num

structure Facts134E9Lie : Prop where
  psl3Plus : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1
  psu3Minus : ∀ p : ℕ, p.Prime → p ≠ 2 → p % 3 = 2 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1
  psl3Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n
  psu3Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n
  psp4Even : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A),
    StatedClassicalModel ↥L .PSp 2 2 n → E9Config L P T → Even n ∧ AutCyclic T P
  g2Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n
  d4Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n
  f4Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n

structure Facts134E9HeRest : Prop extends Facts134E9Lie where
  j4 : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4)

theorem facts134E9He_of_rest_of_he
    (h : Facts134E9HeRest)
    (hHe : OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He)) :
    Facts134E9He where
  alt6 := facts134E9_alt6
  alt7 := facts134E9_alt7
  psl2OddOrder := facts134E9_psl2OddOrder
  psl2OddCyclic := facts134E9_psl2OddCyclic
  psl2Nine := facts134E9_psl2Nine
  psl3OddOrder := facts134E9_psl3OddOrder
  psl3Minus := facts134E9_psl3Minus
  psl3Plus := h.psl3Plus
  psu3OddOrder := facts134E9_psu3OddOrder
  psu3Three := facts134E9_psu3Three
  psu3Plus := facts134E9_psu3Plus
  psu3Minus := h.psu3Minus
  psl2EvenOrder := facts134E9_psl2EvenOrder
  psl2EvenCyclic := facts134E9_psl2EvenCyclic
  psl2EvenBorel := facts134E9_psl2EvenBorel
  psl3EvenOrder := facts134E9_psl3EvenOrder
  psl3Even := h.psl3Even
  psu3EvenOrder := facts134E9_psu3EvenOrder
  psu3Even := h.psu3Even
  psp4EvenOrder := facts134E9_psp4EvenOrder
  psp4Even := h.psp4Even
  g2EvenOrder := facts134E9_g2EvenOrder
  g2Even := h.g2Even
  d4EvenOrder := facts134E9_d4EvenOrder
  d4Even := h.d4Even
  f4EvenOrder := facts134E9_f4EvenOrder
  f4Even := h.f4Even
  titsOrder := facts134E9_titsOrder
  tits := facts134E9_tits
  szOrder := facts134E9_szOrder
  szOut := facts134E9_szOut
  psl45Order := facts134E9_psl45Order
  j1Order := facts134E9_j1Order
  j1 := facts134E9_j1
  j1Local := facts134E9_j1Local
  m12 := facts134E9_m12
  m22 := facts134E9_m22
  m23 := facts134E9_m23
  m24 := facts134E9_m24
  j2 := facts134E9_j2
  j4 := h.j4
  hs := facts134E9_hs
  he := hHe
  ru := facts134E9_ru

theorem facts134E9He_of_rest
    (h : Facts134E9HeRest) : Facts134E9He :=
  facts134E9He_of_rest_of_he h facts134E9_he

end CFSG.Quasithin.P134
