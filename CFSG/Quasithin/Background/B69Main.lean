module

public import CFSG.Quasithin.Background.B69Comp
public import CFSG.Quasithin.Background.B69Red
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem not_isStrongFFModule_of_isSolvable (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X) (hO2 : pCoreOf 2 X = ⊥) : ¬ IsStrongFFModule X := by
  intro hstrong
  have hFF : IsFFModule X := by
    obtain ⟨A, hAX, hA0, hAe, hlt⟩ := hstrong
    exact ⟨A, hAX, hA0, hAe, hlt.le⟩
  have hq := (B1_8_3 hV hsolv (normal_two_subgroups_trivial_of_pCoreOf_eq_bot hO2) hFF).1
  exact not_isStrongFFModule_of_one_le_qOf hV (hq ▸ le_rfl) hstrong

theorem exists_isFFStarMin_below_eq {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    ∃ B, IsFFStarMin X B ∧ B ≤ A ∧
      Nat.card B * Nat.card (fixV B) = Nat.card A * Nat.card (fixV A) :=
  (B1.exists_isFFStarMin_le hA).imp fun _ h => ⟨h.2, h.1.2.2.1, h.1.2.2.2⟩

theorem exists_strong_pstar (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (h : IsStrongFFModule X) : ∃ A, IsFFStarMin X A ∧ rAV A < 1 := by
  obtain ⟨A₀, hA₀, hr₀⟩ := (isStrongFFModule_iff hV).1 h
  obtain ⟨B, -, hB, hrB⟩ := B1_4_4_lt hV hA₀ hr₀
  obtain ⟨A, hAmin, -, hAeq⟩ := exists_isFFStarMin_below_eq hB
  refine ⟨A, hAmin, ?_⟩
  rw [rAV_lt_one_iff hV hAmin.1.isA2, hAeq, ← rAV_lt_one_iff hV hB.isA2]
  exact hrB

@[expose] def redU (L A : Subgroup (MulAut V)) : Subgroup V := fixV (pCoreOf 2 (L ⊔ A))

@[expose] noncomputable def secGroup (L A : Subgroup (MulAut V)) (I : Subgroup ↥(redU L A)) :
    Subgroup (MulAut (Sec I (I ⊓ fixV (autSub L (redU L A))))) :=
  autSec (autSub L (redU L A) ⊔ autSub A (redU L A)) I (I ⊓ fixV (autSub L (redU L A)))

@[expose] noncomputable def secL (L A : Subgroup (MulAut V)) (I : Subgroup ↥(redU L A)) :
    Subgroup (MulAut (Sec I (I ⊓ fixV (autSub L (redU L A))))) :=
  autSec (autSub L (redU L A)) I (I ⊓ fixV (autSub L (redU L A)))

@[expose] def SectionHas (L A : Subgroup (MulAut V))
    (P : ∀ {S : Type} [CommGroup S] [Finite S], Subgroup (MulAut S) → Subgroup (MulAut S) → Prop) :
    Prop :=
  ∃ I : Subgroup ↥(redU L A), I ∈ IrrPlus (autSub L (redU L A)) (⊤ : Subgroup ↥(redU L A)) ∧
    P (secGroup L A I) (secL L A I)

theorem strong_component_case (h42 : AsB42) (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection)
    (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {H₀ : Type} [Group H₀] [Finite H₀]
    (hH₀ : SQTKGroup H₀) (φ : H₀ →* ↥X) (hφ : Function.Surjective φ) (hO2 : pCoreOf 2 X = ⊥)
    (hstrong : IsStrongFFModule X) :
    ∃ A L : Subgroup (MulAut V), IsFFStarMin X A ∧ rAV A < 1 ∧ CFSG.Open.IsComponentOf L X ∧
      ⁅L, A⁆ = L ∧
      (SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case2 G L') ∨
        SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case3 G L') ∨
        SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case9 G L') ∨
        SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case10ii G L')) := by
  obtain ⟨A, hA, hAs⟩ := exists_strong_pstar hV hstrong
  have hFA := strong_centralizes_fitting hV hO2 hA hAs
  obtain ⟨L, hL, hLA⟩ := exists_component hV hP4 hO2 hA hFA
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hSQ : SQTKGroup ↥L :=
    sqtk_subgroup hA21 hH₀ φ hφ hL.1 (B1Red.isQuasisimple_of_open hLq)
  have hred := exists_red hV hA hAs hL.1 hLq hLA hA21 hSQ
  obtain ⟨I, hI, hcase⟩ := hred.exists_strong_case h42 hA21 (B1.sq_eq_one_sub hV (redU L A))
  refine ⟨A, L, hA, hAs, hL, hLA, ?_⟩
  rcases hcase with c | c | c | c
  · exact Or.inl ⟨I, hI, c⟩
  · exact Or.inr (Or.inl ⟨I, hI, c⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨I, hI, c⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨I, hI, c⟩))

@[expose] def StrongComponent (V : Type) [CommGroup V] [Finite V] (X : Subgroup (MulAut V))
    (S M : Subgroup ↥X) (A L : Subgroup (MulAut V)) : Prop :=
  (∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
    CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f) ∧
  MinParabolic (⊤ : Subgroup ↥X) S M ∧ pCoreOf 2 (⊤ : Subgroup ↥X) = ⊥ ∧
    IsFFStarMin X A ∧ rAV A < 1 ∧ CFSG.Open.IsComponentOf L X ∧ ⁅L, A⁆ = L

@[expose] def AsB69NoStrongSL3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (S M : Subgroup ↥X) (A L : Subgroup (MulAut V)),
      StrongComponent V X S M A L →
      ¬ SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case2 G L')

@[expose] def AsB69NoStrongSp4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (S M : Subgroup ↥X) (A L : Subgroup (MulAut V)),
      StrongComponent V X S M A L →
      ¬ SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case3 G L')

@[expose] def AsB69NoStrongLn : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (S M : Subgroup ↥X) (A L : Subgroup (MulAut V)),
      StrongComponent V X S M A L →
      ¬ SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case9 G L')

@[expose] def AsB69NoStrongS8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (S M : Subgroup ↥X) (A L : Subgroup (MulAut V)),
      StrongComponent V X S M A L →
      ¬ SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case10ii G L')

@[expose] def AsB69StrongExcluded : Prop :=
  AsB69NoStrongSL3 ∧ AsB69NoStrongSp4 ∧ AsB69NoStrongLn ∧ AsB69NoStrongS8

theorem not_isStrongFFModule_of_inputs (h42 : AsB42) (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection)
    (hex : AsB69StrongExcluded) (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (S M : Subgroup ↥X) (hH : ∃ (H : Type) (_ : Group H) (_ : Finite H),
      CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧ CFSG.SectionRank.IsKGroupCat H ∧
        ∃ f : H →* ↥X, Function.Surjective f)
    (hmp : MinParabolic (⊤ : Subgroup ↥X) S M) (hO2 : pCoreOf 2 (⊤ : Subgroup ↥X) = ⊥) :
    ¬ IsStrongFFModule X := by
  intro hstrong
  have hO2' : pCoreOf 2 X = ⊥ := by
    have h1 : CFSG.Open.pCore 2 ↥X = ⊥ := by rw [← B6.pCoreOf_top]; exact hO2
    unfold pCoreOf
    rw [h1, Subgroup.map_bot]
  by_cases hsolv : Group.IsSolvable ↥X
  · exact not_isStrongFFModule_of_isSolvable hV hsolv hO2' hstrong
  · obtain ⟨H₀, _, _, hsq, hK, φ, hφ⟩ := hH
    obtain ⟨A, L, hA, hAs, hL, hLA, hcase⟩ :=
      strong_component_case h42 hP4 hA21 hV ⟨hsq, hK⟩ φ hφ hO2' hstrong
    have hdata : StrongComponent V X S M A L := ⟨⟨H₀, inferInstance, inferInstance, hsq, hK, φ, hφ⟩,
      hmp, hO2, hA, hAs, hL, hLA⟩
    rcases hcase with c | c | c | c
    · exact hex.1 V hV X S M A L hdata c
    · exact hex.2.1 V hV X S M A L hdata c
    · exact hex.2.2.1 V hV X S M A L hdata c
    · exact hex.2.2.2 V hV X S M A L hdata c

end B69

end CFSG.Quasithin
