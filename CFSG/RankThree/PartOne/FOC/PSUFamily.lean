module

public import CFSG.RankThree.PartOne.FOC.PSUInner
public import CFSG.RankThree.PartOne.FOC.PSUOuter
public import CFSG.RankThree.PartOne.FOC.LieAssemble
public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.PSUModel
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff LocalRankLeTwo)

@[expose] def PSUFiveSpecial : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (f : ℕ), IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    5 ∣ 2 ^ f + 1 → StatedLieAdmissible .PSU 5 2 f → LieModel T .PSU 5 2 f → FieldInnerT 5 T

theorem fieldInnerT_psu {T : Type} [Group T] [Finite T] {n f ℓ p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hs : IsSimpleGroup T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hmodel : LieModel T .PSU n ℓ f)
    (hspecial : ¬(ℓ = 2 ∧ n = 5 ∧ p = 5 ∧ p ∣ ℓ ^ f + 1)) : FieldInnerT p T := by
  have hC : StatedClassicalModel T .PSU n ℓ f := (lieModel_classical_iff (by decide)).mp hmodel
  obtain ⟨K, _, hKf, h, hn3, hne, ⟨e⟩⟩ := exists_psu_model hC
  have : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv T e.toEquiv
  have hZ : LocalRankLeTwo p T → ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := by
    intro hLR
    by_cases hsp : ℓ = 2 ∧ n = 5 ∧ p = 5
    · intro hd
      exact hspecial ⟨hsp.1, hsp.2.1, hsp.2.2, hd.trans (Nat.gcd_dvd_right _ _)⟩
    · exact not_dvd_gcd_of_localRank hp hp5 hC hLR hsp
  have hin : InnerComp p T := by
    intro hLR b y hbp hyp hby E hE
    exact InnerComp.of_mulEquiv e hp (innerComp_psu hp hp5 hpℓ (by omega) (hZ hLR)) hLR b y hbp
      hyp hby E hE
  have hout : OuterComp p T := by
    intro hLR β hβp hβout hLRA y hβy hyp E hE
    exact OuterComp.of_mulEquiv e hp (outerComp_psu h hn3 hne hp hp5 hpℓ (hZ hLR)) hLR β hβp
      hβout hLRA y hβy hyp E hE
  exact fieldInnerT_of_comp (center_eq_bot_of_nonab hs hnab) hin hout

theorem fieldInnerLie_PSU (hdefI : DefInnerComponent) (hdefO : DefOuterComponent)
    (hsp : PSUFiveSpecial) (ℓ : ℕ) : FieldInnerLie .PSU ℓ := by
  refine fieldInnerLie_of_nondef hdefI hdefO ?_
  intro T _ _ n f p hp hp5 hpℓ hs hnab hadm hmodel
  by_cases hspecial : ℓ = 2 ∧ n = 5 ∧ p = 5 ∧ p ∣ ℓ ^ f + 1
  · obtain ⟨rfl, rfl, rfl, hd⟩ := hspecial
    exact hsp T f hs hnab hd hadm hmodel
  · exact fieldInnerT_psu hp hp5 hpℓ hs hnab hmodel hspecial

end CFSG.RankThree.PartOne.FOC
