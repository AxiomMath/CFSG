module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaGen
public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2InvolNine
public import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open CFSG.RankThree.PartTwo.KFacts
open Hering214Even


theorem exists_e9_of_j2 {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* NativeSporadic.J2)) :
    ∃ Q : Subgroup X, IsElemAbelian 3 Q ∧ Nat.card Q = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨⟨⟨-, hP27, hexp⟩, -⟩, -⟩ := Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(P : Subgroup X)) 3 (n := 2)
    (by rw [hP27]; norm_num)
  have hQ9 : Nat.card (H.map (P : Subgroup X).subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective, hH]
    norm_num
  refine ⟨_, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hQ9]; norm_num),
    ?_⟩, hQ9⟩
  rintro _ ⟨h, -, rfl⟩
  have h3 := Monoid.pow_exponent_eq_one h
  rw [hexp] at h3
  rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, h3, Subgroup.coe_one]


theorem evenThetaFacts_of_j2 {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* NativeSporadic.J2)) : EvenThetaFacts X := by
  obtain ⟨e⟩ := hX
  exact evenThetaFacts_of_fixNine
    (KS14.center_eq_bot_of_mulEquiv e KS14.Native.center_nativeJ2_eq_bot)
    (fun σ hσ => ks17J2AutThree_of_outer
      CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
      X ⟨e⟩ σ hσ)
    (exists_e9_of_j2 ⟨e⟩)
    (fun E hE σ hσ hfix => ks152J2InvolNine X ⟨e⟩ E hE σ hσ hfix)

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
