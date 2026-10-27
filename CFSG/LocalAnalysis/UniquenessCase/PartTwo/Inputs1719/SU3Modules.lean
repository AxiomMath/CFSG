module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped Pointwise

@[expose] def K_SU3MinDegree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n → 2 ≤ n → 6 * n ≤ dMinDeg X

@[expose] def K_U34ThreeCentralizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 2 →
    ∀ x : X, orderOf x = 3 →
      IsCyclic (Subgroup.centralizer ({x} : Set X)) ∧
        Nat.card (Subgroup.centralizer ({x} : Set X)) = 15

@[expose] def K_SU3NaturalModule : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y K : Subgroup (MulAut W)) (n : ℕ),
      K ≤ Y → CFSG.Open.IsComponentOf K Y → K ≠ ⊥ → IsSU3 ↥K n → 3 ≤ n →
      (∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥) →
      IsBasicModule Y →
      fixV (⨆ X ∈ conjSet K Y, X) = ⊥ →
      E3.mParam Y ≤ 2 * n + 2 →
      CNatModSU3Sub W (CFSG.Quasithin.commSub (⊤ : Subgroup W) K) K n ∧
        E3.mParam Y = 2 * n

@[expose] def K_SU3NaturalH1 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (K : Subgroup (MulAut W)) (n : ℕ), IsSU3 ↥K n → 2 ≤ n →
      ∀ (Z W' : Subgroup W), StableUnder K Z → Z ≤ fixV K →
        W' ⊔ Z = ⊤ → W' ⊓ Z = ⊥ →
        NatSUn (autQuot K Z) ⊤ ⊥ 3 n →
          ∃ W'' : Subgroup W, StableUnder K W'' ∧ W'' ⊓ Z = ⊥ ∧ W'' ⊔ Z = ⊤ ∧
            W'' = CFSG.Quasithin.commSub (⊤ : Subgroup W) K ∧
            CNatModSU3Sub W W'' K n

section U34Consequences

variable {X : Type} [Group X] [Finite X]

theorem card_quot_center_eq_of_isSU3_two (h : IsSU3 X 2) :
    Nat.card (X ⧸ Subgroup.center X) = 62400 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (t := .PSU) (n := 3) (p := 2) (f := 2)
    (by norm_num) h.2]
  decide

theorem card_eq_mul_center_of_isSU3_two (h : IsSU3 X 2) :
    Nat.card X = 62400 * Nat.card (Subgroup.center X) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    card_quot_center_eq_of_isSU3_two h]

theorem center_eq_bot_of_isSU3_two (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer)
    (h : IsSU3 X 2) : Subgroup.center X = ⊥ := by
  have hcard := card_eq_mul_center_of_isSU3_two h
  have hdvd : Nat.card (Subgroup.center X) ∣ 3 := hZ X 2 h
  by_contra hne
  have : Nontrivial ↥(Subgroup.center X) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center X))
  let zX : X := (z : ↥(Subgroup.center X))
  have hzo' : orderOf zX ∣ 3 :=
    (Subgroup.orderOf_dvd_natCard (Subgroup.center X) z.2).trans hdvd
  have hz1 : zX ≠ 1 := fun h1 => hz (Subtype.ext h1)
  have hzo : orderOf zX = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 hzo' |>.resolve_left (fun h1 => hz1 (orderOf_eq_one_iff.1 h1))
  have hcent : Subgroup.centralizer ({zX} : Set X) = ⊤ := by
    refine top_le_iff.1 fun y _ => Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (Subgroup.mem_center_iff.1 z.2 y).symm
  have h15 : Nat.card X = 15 := by
    have h := (hC X h zX hzo).2
    rwa [hcent, Subgroup.card_top] at h
  have hle : 62400 ≤ Nat.card X := by
    rw [hcard]
    calc 62400 = 62400 * 1 := (mul_one _).symm
      _ ≤ 62400 * Nat.card (Subgroup.center X) :=
        Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')
  omega

theorem card_eq_of_isSU3_two (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer)
    (h : IsSU3 X 2) : Nat.card X = 62400 := by
  rw [card_eq_mul_center_of_isSU3_two h, center_eq_bot_of_isSU3_two hZ hC h,
    Subgroup.card_bot, mul_one]

theorem three_dvd_card_of_isSU3_two (h : IsSU3 X 2) : 3 ∣ Nat.card X := by
  have hq : 3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [card_quot_center_eq_of_isSU3_two h]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
  exact hq.mul_right _

theorem pRank_three_eq_one_of_isSU3_two (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer)
    (h : IsSU3 X 2) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nat.card X = 62400 := card_eq_of_isSU3_two hZ hC h
  refine le_antisymm ?_ ?_
  · refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    obtain ⟨P, hP, hEP⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge
      (K := (⊤ : Subgroup X)) le_top hE.isPGroup
    have hPcard : Nat.card P = 3 ^ (Nat.card X).factorization 3 := by
      have h := hP.card_eq
      rwa [Subgroup.card_top] at h
    rw [hX] at hPcard
    have hfac : (62400 : ℕ).factorization 3 = 1 := by decide +kernel
    rw [hfac, pow_one] at hPcard
    have h3 : Nat.card E ≤ Nat.card P :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hEP) (Subgroup.inclusion_injective hEP)
    omega
  · have hdvd : 3 ∣ Nat.card X := three_dvd_card_of_isSU3_two h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 hdvd
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      exact Nat.prime_three.ne_one hx.symm
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
      CFSG.Open.isElemAbelian_zpowers hx3
    have hcard : Nat.card (Subgroup.zpowers x) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hx, pow_one]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hel hcard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_eq_pow_mul_of_isSU3_bar2 (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer)
    (h : IsSU3 (Bar2 L) 2) : ∃ k : ℕ, Nat.card L = 2 ^ k * 62400 := by
  have hq : Nat.card (Bar2 L) = 62400 := card_eq_of_isSU3_two hZ hC h
  have hcard : Nat.card L = Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  rw [hq] at hcard
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)).exists_card_eq
  refine ⟨k, ?_⟩
  rw [hcard, hk]
  ring

theorem pRank_three_eq_one_of_isSU3_bar2 (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer)
    (h : IsSU3 (Bar2 L) 2) : CFSG.Open.pRank 3 L = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)).exists_card_eq
    rw [hk]
    exact fun hd => absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L,
    ← CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥L) h3]
  exact pRank_three_eq_one_of_isSU3_two hZ hC h

end U34Consequences

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
