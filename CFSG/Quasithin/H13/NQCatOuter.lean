module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Quasithin.SteinbergOuterPrimeControl

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem card_outer_le_of_perfect (J : Type*) [Group J] [Finite J] [Group.IsPerfect J]
    {T : Type*} [Group T] (e : J ⧸ Subgroup.center J ≃* T) :
    Nat.card (Outer J) ≤ Nat.card (Outer T) := by
  have : Finite T := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  exact Nat.card_le_card_of_injective _
    (LocalAnalysis.ComponentInitial.OuterDerived.outer_comp_injective J e)

theorem isMulCommutative_of_card_le_four {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsMulCommutative G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  interval_cases hc : Nat.card G
  · have : Subsingleton G := Finite.card_le_one_iff_subsingleton.1 hc.le
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hc
    exact IsCyclic.isMulCommutative
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic G := isCyclic_of_prime_card hc
    exact IsCyclic.isMulCommutative
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hc

theorem sylow_eq_bot_of_not_dvd {X : Type*} [Group X] [Finite X] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ¬ ℓ ∣ Nat.card X) (P : Sylow ℓ X) : (P : Subgroup X) = ⊥ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hk0
    exact h ((dvd_pow_self ℓ hk0).trans (hk ▸ Subgroup.card_subgroup_dvd_card _))
  rw [hk0, pow_zero, Subgroup.card_eq_one] at hk
  exact hk

theorem pRank_eq_zero_of_not_dvd {X : Type*} [Group X] [Finite X] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ¬ ℓ ∣ Nat.card X) : CFSG.pRank ℓ X = 0 := by
  rw [SectionRank.pRank_eq_open_pRank_top]
  exact RankThreeEvenClassification.Helpers.pRank_eq_zero_of_not_dvd ℓ hℓ h ⊤

theorem outer_large_prime_of_card_le_four {X : Type*} [Group X] [Finite X]
    (h : Nat.card X ≤ 4) : ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
      (∀ P : Sylow ℓ X, (P : Subgroup X) = ⊥) ∧ CFSG.pRank ℓ X = 0 := by
  intro ℓ hℓ hℓ5
  have hnd : ¬ ℓ ∣ Nat.card X := fun hd => by
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  exact ⟨sylow_eq_bot_of_not_dvd hℓ hnd, pRank_eq_zero_of_not_dvd hℓ hnd⟩

theorem sylow_isCyclic_pRank_le_one_of_isCyclic {X : Type*} [Group X] [Finite X] [IsCyclic X]
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (∀ P : Sylow ℓ X, IsCyclic P) ∧ CFSG.pRank ℓ X ≤ 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact ⟨fun P => inferInstance,
    OuterPrimeControl.pRank_le_one_of_forall_isCyclic fun V _ => inferInstance⟩

theorem sylow_isCyclic_pRank_le_one_of_isPGroup_two {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup 2 X) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    (∀ P : Sylow ℓ X, IsCyclic P) ∧ CFSG.pRank ℓ X ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hnd : ¬ ℓ ∣ Nat.card X := fun hd => by
    rw [hn] at hd
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hd))
  refine ⟨fun P => ?_, (pRank_eq_zero_of_not_dvd hℓ hnd).le.trans zero_le_one⟩
  rw [sylow_eq_bot_of_not_dvd hℓ hnd P]
  infer_instance

theorem sylow_isCyclic_pRank_le_one_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] (ι : X →* Y) (hι : Function.Injective ι) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : (∀ P : Sylow ℓ Y, IsCyclic P) ∧ CFSG.pRank ℓ Y ≤ 1) :
    (∀ P : Sylow ℓ X, IsCyclic P) ∧ CFSG.pRank ℓ X ≤ 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hY : ∀ V : Subgroup Y, IsPGroup ℓ V → IsCyclic V := fun V hV => by
    obtain ⟨P, hVP⟩ := hV.exists_le_sylow
    have := h.1 P
    exact Subgroup.isCyclic_of_le hVP
  have hX : ∀ V : Subgroup X, IsPGroup ℓ V → IsCyclic V := fun V hV =>
    OuterPrimeControl.isCyclic_of_isPGroup_of_injective ι hι hY hV
  exact ⟨fun P => hX P P.isPGroup', OuterPrimeControl.pRank_le_one_of_forall_isCyclic hX⟩

end CFSG.Quasithin.H13.NQCat
