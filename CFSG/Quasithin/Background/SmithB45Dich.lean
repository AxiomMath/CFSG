module

public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42DichProof
public import CFSG.Quasithin.Background.SmithB45ExcJ1
public import CFSG.Quasithin.Background.SmithB45ExcM11
public import CFSG.Quasithin.Background.SmithB45ExcJ4
public import CFSG.Quasithin.Background.SmithB45ExcHe
public import CFSG.Quasithin.Background.SmithB45ExcL2Cover
public import CFSG.Quasithin.Background.SmithB45ExcL225
public import CFSG.Quasithin.Background.SmithB45ExcL3
public import CFSG.Quasithin.Background.SmithB45ExcL33
public import CFSG.Quasithin.Background.SmithB45ExcU3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Bridge

namespace B45Exc

@[expose] def PSL3ThreeExclusion2F : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ Lb : Subgroup (MulAut W), Group.IsPerfect ↥Lb → X1.IsIrrOn Lb →
      StatedClassicalModel (CQ Lb) .PSL 3 3 1 →
      ∀ B : Subgroup (MulAut W), B ≤ Subgroup.normalizer (Lb : Set (MulAut W)) → B ≠ ⊥ →
        IsElemAbelian2 B → Nat.card B ^ 2 * Nat.card (fixV B) < Nat.card W

@[expose] def ThreeA7Exclusion2F : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → X1.IsIrrOn L →
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center ↥L ≠ ⊥ → E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ →
      IsElemAbelian2 E → Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W

theorem psl2TwentyFiveExclusion2F_holds :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ Lb : Subgroup (MulAut W), Group.IsPerfect ↥Lb → X1.IsIrrOn Lb →
        StatedClassicalModel (CQ Lb) .PSL 2 5 2 →
        ∀ B : Subgroup (MulAut W), B ≤ Subgroup.normalizer (Lb : Set (MulAut W)) → B ≠ ⊥ →
          IsElemAbelian2 B → Nat.card B ^ 2 * Nat.card (fixV B) < Nat.card W :=
  fun W _ _ hW Lb hperf hirr hmod B hBN hB1 hB2 =>
    primeSquareFiveExclusion2F 5 (by norm_num) rfl W hW Lb hperf hirr hmod B hBN hB1 hB2

theorem psl3ThreeExclusion2F_holds : PSL3ThreeExclusion2F :=
  fun W _ _ hW Lb hperf hirr hmod B hBN hB1 hB2 =>
    l33Exclusion2F W hW Lb hperf hirr hmod B hBN hB1 hB2

end B45Exc

open B45Exc Dichotomy in
theorem asB45DichotomyNat_of_exclusions
    (hHS : SporadicExclusion2F .HS) (hRu : SporadicExclusion2F .Ru)
    (hL33 : PSL3ThreeExclusion2F)
    (hA7 : ThreeA7Exclusion2F) : AsB45DichotomyNat := by
  have hL225 := B45Exc.psl2TwentyFiveExclusion2F_holds
  intro W _ _ hW L hq hirr hlist E hEN hE hel _hcub hoff
  have hirrOn : X1.IsIrrOn L := isIrrOn_of_isIrrSec hirr
  have : Nontrivial W := hirrOn.1
  have hcon : ¬ Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W := not_lt.2 hoff
  have hA7clause : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center ↥L = ⊥ := by
    intro h7
    by_contra hc
    exact hcon (hA7 W hW L E hq hirrOn h7 hc hEN hE hel)
  refine ⟨?_, hA7clause⟩
  have hperf : Group.IsPerfect ↥L := hq.1
  rcases hlist with halt | ⟨p, hp, hp2, hcl⟩ | hchar2 | hSL | ⟨s, hs, ⟨e⟩⟩
  · exact Or.inl (Or.inl halt)
  · rcases hcl with ⟨f, hf12, hmod⟩ | hmod | hmod
    · rcases hf12 with rfl | rfl
      · have : Fact p.Prime := ⟨hp⟩
        by_cases hp11 : 11 ≤ p
        · exfalso
          obtain ⟨α⟩ := Family.equiv_projectiveSL_of_model hmod
          exact hcon (primeLinearTwoExclusion2F hp11 hW hperf hirrOn.2 α E hEN hE hel)
        · have hp3 : 3 ≤ p := by have := hp.two_le; omega
          interval_cases p
          · exact absurd rfl hmod.1.2.2.2.2
          · norm_num at hp
          · exact Or.inl (Or.inr (Or.inl hmod))
          · norm_num at hp
          · exact Or.inl (Or.inr (Or.inr (Or.inl hmod)))
          all_goals norm_num at hp
      · by_cases hp3 : p = 3
        · subst hp3
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hmod))))
        · exfalso
          by_cases hp5 : p = 5
          · subst hp5
            exact hcon (hL225 W hW L hperf hirrOn hmod E hEN hE hel)
          · have hp7 : 7 ≤ p := by
              have h2 := hp.two_le
              have h4 : p ≠ 4 := by
                rintro rfl
                norm_num at hp
              have h6 : p ≠ 6 := by
                rintro rfl
                norm_num at hp
              omega
            exact hcon (primeSquareExclusion2F p hp hp7 W hW L hperf hirrOn hmod E hEN hE hel)
    · exfalso
      by_cases hp3 : p = 3
      · subst hp3
        exact hcon (hL33 W hW L hperf hirrOn hmod E hEN hE hel)
      · have hp5 : 5 ≤ p := by
          have h2 := hp.two_le
          have h4 : p ≠ 4 := by
            rintro rfl
            norm_num at hp
          omega
        exact hcon (primeLinearThreeExclusion2F p hp hp5 W hW L hperf hirrOn hmod E hEN hE hel)
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod)))))
      · exfalso
        have hp5 : 5 ≤ p := by
          have h2 := hp.two_le
          have h4 : p ≠ 4 := by
            rintro rfl
            norm_num at hp
          omega
        exact hcon (primeUnitaryThreeExclusion2F p hp hp5 W hW L hperf hirrOn hmod E hEN hE hel)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hchar2))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSL))))))
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (sporadicExclusion2F_M11 W hW L E hq hirrOn ⟨e⟩ hEN hE hel) hcon
    · exact Or.inr ⟨.M12, Or.inl rfl, ⟨e⟩⟩
    · exact Or.inr ⟨.M22, Or.inr (Or.inl rfl), ⟨e⟩⟩
    · exact Or.inr ⟨.M23, Or.inr (Or.inr (Or.inl rfl)), ⟨e⟩⟩
    · exact Or.inr ⟨.M24, Or.inr (Or.inr (Or.inr (Or.inl rfl))), ⟨e⟩⟩
    · exact absurd (sporadicExclusion2F_J1 W hW L E hq hirrOn ⟨e⟩ hEN hE hel) hcon
    · exact Or.inr ⟨.J2, Or.inr (Or.inr (Or.inr (Or.inr rfl))), ⟨e⟩⟩
    · exact absurd (sporadicExclusion2F_J4 W hW L E hq hirrOn ⟨e⟩ hEN hE hel) hcon
    · exact absurd (hHS W hW L E hq hirrOn ⟨e⟩ hEN hE hel) hcon
    · exact absurd (sporadicExclusion2F_He W hW L E hq hirrOn ⟨e⟩ hEN hE hel) hcon
    · exact absurd (hRu W hW L E hq hirrOn ⟨e⟩ hEN hE hel) hcon

end CFSG.Quasithin
