module

public import CFSG.Quasithin.Recognition.St84.Gen.S3Slice
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Stroth


@[expose] def IdL2L2Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (m n : ℕ),
    F112Hyp L1 L2 S → 2 ≤ m → 2 ≤ n → ¬ (m = 2 ∧ n = 2) →
      IsL2Quot m (oTwoQuot ↥L1) → IsL2Quot n (oTwoQuot ↥L2) →
        (m = n ∧ (IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 n) ∨
            IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over n) ∨
            IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over n))) ∨
          (m = 3 * n ∧ IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 n)) ∨
          (n = 3 * m ∧ IsAmalgamOfGroup (f112Amalgam L2 L1 S) (IsLieOverTwo .trialityD4 0 m)) ∨
          (n = 2 * m ∧ (IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 m) ∨
            IsU4ExtTwo m (f112Amalgam L1 L2 S))) ∨
          (m = 2 * n ∧ (IsAmalgamOfGroup (f112Amalgam L2 L1 S) (IsLieOverTwo .PSU 4 n) ∨
            IsU4ExtTwo n (f112Amalgam L2 L1 S)))

@[expose] def Y9L3q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ),
    F112Hyp L1 L2 S → 3 ≤ f → IsL2Quot f (oTwoQuot ↥L1) → IsL2Quot f (oTwoQuot ↥L2) →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 f) →
        (IsBlock2 L1 L1 ∧ IsLin2Type L1 f) ∧ (IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∧
          PerfectOver L1 L2 S

@[expose] def Y9Sp4q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ),
    F112Hyp L1 L2 S → 3 ≤ f → IsL2Quot f (oTwoQuot ↥L1) → IsL2Quot f (oTwoQuot ↥L2) →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over f) →
        (IsBlock2 L1 L1 ∧ IsLin2Type L1 f) ∧ (IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∧
          PerfectOver L1 L2 S

@[expose] def G2qOriented {G : Type} [Group G] (f : ℕ) (L1 L2 S : Subgroup G) : Prop :=
  (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
    IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
    Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 5

@[expose] def Y9G2q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ),
    F112Hyp L1 L2 S → 3 ≤ f → IsL2Quot f (oTwoQuot ↥L1) → IsL2Quot f (oTwoQuot ↥L2) →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over f) →
        (G2qOriented f L1 L2 S ∨ G2qOriented f L2 L1 S) ∧ PerfectOver L1 L2 S

@[expose] def Y9D4q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ),
    F112Hyp L1 L2 S → 2 ≤ f → IsL2Quot (3 * f) (oTwoQuot ↥L1) → IsL2Quot f (oTwoQuot ↥L2) →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 f) →
        (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
            centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
          IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
          Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 11 ∧ PerfectOver L1 L2 S

@[expose] def Y9U4q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ),
    F112Hyp L1 L2 S → 2 ≤ f → IsL2Quot f (oTwoQuot ↥L1) → IsL2Quot (2 * f) (oTwoQuot ↥L2) →
      (IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f) ∨
          IsU4ExtTwo f (f112Amalgam L1 L2 S)) →
        (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
            centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
          IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
          IsBlock2 L2 L2 ∧ IsOmega4MinusType L2 f ∧
          (IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f) → PerfectOver L1 L2 S)

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem f112ConclC_of_D4q (hD : Y9D4q) {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {f : ℕ}
    (hf : 2 ≤ f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hX : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 f)) :
    F112ConclC L1 L2 S := by
  obtain ⟨hz, hs, hc, hp⟩ := hD G L1 L2 S f hF hf h1 h2 hX
  exact ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, orient_of_imp hz,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨f, by omega, hX, h1, hs, h2, hc⟩))), Or.inl hp⟩

theorem f112ConclC_of_U4q (hU : Y9U4q) {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {f : ℕ}
    (hf : 2 ≤ f) (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot (2 * f) (oTwoQuot ↥L2))
    (hX : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f) ∨
      IsU4ExtTwo f (f112Amalgam L1 L2 S)) :
    F112ConclC L1 L2 S := by
  obtain ⟨hz, hs, hb, ho, hp⟩ := hU G L1 L2 S f hF hf h1 h2 hX
  refine ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, orient_of_imp hz, ?_, ?_⟩
  · iterate 5 right
    exact Or.inl ⟨f, by omega, hX, h1, hs, hb, h2, ho, fun h => absurd h (by omega)⟩
  · rcases hX with hX | hX
    · exact Or.inl (hp hX)
    · iterate 13 right
      exact ⟨f, by omega, hX⟩

theorem f112ConclC_of_eq (hL : Y9L3q) (hSp : Y9Sp4q) (hG : Y9G2q) {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) {f : ℕ} (hf : 3 ≤ f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hX : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 f) ∨
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over f) ∨
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over f)) :
    F112ConclC L1 L2 S := by
  have hf1 : 1 ≤ f := by omega
  have hf2 : 2 ≤ f := by omega
  rcases hX with hX | hX | hX
  · obtain ⟨⟨b1, l1⟩, ⟨b2, l2⟩, hp⟩ := hL G L1 L2 S f hF hf h1 h2 hX
    exact f112ConclC_of_symm (Or.inl ⟨f, hf1, hX, Or.inl ⟨hf2, b1, l1, b2, l2⟩⟩)
      (Or.inl ⟨f, hf1, isAmalgamOfGroup_f112Amalgam_swap hX, Or.inl ⟨hf2, b2, l2, b1, l1⟩⟩) hp
  · obtain ⟨⟨b1, l1⟩, ⟨b2, l2⟩, hp⟩ := hSp G L1 L2 S f hF hf h1 h2 hX
    exact f112ConclC_of_symm (Or.inr (Or.inl ⟨f, hf1, hX, Or.inl ⟨hf2, b1, l1, b2, l2⟩⟩))
      (Or.inr (Or.inl ⟨f, hf1, isAmalgamOfGroup_f112Amalgam_swap hX,
        Or.inl ⟨hf2, b2, l2, b1, l1⟩⟩)) hp
  · obtain ⟨ho | ho, hp⟩ := hG G L1 L2 S f hF hf h1 h2 hX
    · obtain ⟨hz, hs, hc⟩ := ho
      exact ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, orient_of_imp hz,
        Or.inr (Or.inr (Or.inl ⟨f, hf1, hX, h1, h2, hs, hc⟩)), Or.inl hp⟩
    · obtain ⟨hz, hs, hc⟩ := ho
      exact ⟨L2, L1, Or.inr ⟨rfl, rfl⟩, fun h' => h'.elim hz id,
        Or.inr (Or.inr (Or.inl ⟨f, hf1, isAmalgamOfGroup_f112Amalgam_swap hX, h2, h1, hs, hc⟩)),
        Or.inl hp.symm⟩

theorem f112ConclC_of_L2L2 (hA : IdA5A5) (hL34 : Y9L34) (hSp44 : Y9Sp44) (hG24 : Y9G24)
    (hId : IdL2L2Gen) (hL : Y9L3q) (hSp : Y9Sp4q) (hG : Y9G2q) (hD : Y9D4q) (hU : Y9U4q)
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (hb1 : VBig L1) (hb2 : VBig L2) {m n : ℕ}
    (hm : IsL2Quot m (oTwoQuot ↥L1)) (hn : IsL2Quot n (oTwoQuot ↥L2)) : F112ConclC L1 L2 S := by
  have h2m := two_le_of_isL2Quot_of_vBig hF.1.h1.listed hb1 hm
  have h2n := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hb2 hn
  by_cases h22 : m = 2 ∧ n = 2
  · obtain ⟨rfl, rfl⟩ := h22
    exact f112ConclC_of_A5A5 hA hL34 hSp44 hG24 G L1 L2 S hF hm hn
  · rcases hId G L1 L2 S m n hF h2m h2n h22 hm hn with
      ⟨rfl, hX⟩ | ⟨rfl, hX⟩ | ⟨rfl, hX⟩ | ⟨rfl, hX⟩ | ⟨rfl, hX⟩
    · exact f112ConclC_of_eq hL hSp hG hF (by omega) hm hn hX
    · exact f112ConclC_of_D4q hD hF h2n hm hn hX
    · exact (f112ConclC_of_D4q hD hF.symm h2m hn hm hX).symm
    · exact f112ConclC_of_U4q hU hF h2m hm hn hX
    · exact (f112ConclC_of_U4q hU hF.symm h2n hn hm hX).symm

end Assembly

theorem f112SliceBigL2_of_parts (hA : IdA5A5) (hL34 : Y9L34) (hSp44 : Y9Sp44) (hG24 : Y9G24)
    (hId : IdL2L2Gen) (hL : Y9L3q) (hSp : Y9Sp4q) (hG : Y9G2q) (hD : Y9D4q) (hU : Y9U4q) :
    F112SliceBigL2 F112ConclPredC := by
  rintro G _ _ L1 L2 S hF ⟨⟨hb1, hb2⟩, ⟨m, hm⟩, ⟨n, hn⟩⟩
  exact f112ConclC_of_L2L2 hA hL34 hSp44 hG24 hId hL hSp hG hD hU hF hb1 hb2 hm hn

end CFSG.Quasithin.F112R
