module

public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.GroupTheory.SubnormalJoin
import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Layer
import CFSG.LocalAnalysis.UniquenessCase.UC7P3NoBad
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha

open CFSG Subgroup
open CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Components

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem isComponent_map_subtype_of_normal {N : Subgroup X} (hN : N.Normal) {L : Subgroup N}
    (hL : CFSG.IsComponent L) : CFSG.IsComponent (L.map N.subtype) :=
  ⟨CFSG.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective N.subtype N.subtype_injective).symm hL.1,
    CFSG.GroupTheory.isSubnormal_map_subtype hL.2 hN.isSubnormal⟩

private theorem fittingSubgroupOf_pPrimeCore_eq_bot (hθ : aschbacherSolvableCore 3 X = ⊥) :
    CFSG.fittingSubgroupOf (G := X) (CFSG.pPrimeCore 3 X) = ⊥ := by
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X))
  have hle : CFSG.fittingSubgroupOf (G := X) (CFSG.pPrimeCore 3 X) ≤
      aschbacherSolvableCore 3 X := by
    have : Group.IsNilpotent ↥(CFSG.fittingSubgroupOf (G := X) (CFSG.pPrimeCore 3 X)) :=
      CFSG.fittingSubgroupOf_isNilpotent (G := X) (CFSG.pPrimeCore 3 X)
    refine (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.1
      (CFSG.fittingSubgroupOf (G := X) (CFSG.pPrimeCore 3 X))
      (CFSG.fittingSubgroupOf_normal (G := X) (CFSG.pPrimeCore 3 X)
        (CFSG.pPrimeCore_normal (p := 3) (G := X))) IsNilpotent.to_isSolvable ?_
    intro h3
    exact hN3 (h3.trans (Subgroup.card_dvd_of_le
      (CFSG.fittingSubgroupOf_le (G := X) (CFSG.pPrimeCore 3 X))))
  rwa [hθ, le_bot_iff] at hle

theorem pPrimeCore_eq_bot_of_three_dvd_components (hθ : aschbacherSolvableCore 3 X = ⊥)
    (hno : ∀ J : Subgroup X, CFSG.IsComponent J → 3 ∣ Nat.card J) :
    CFSG.pPrimeCore 3 X = ⊥ := by
  have hF : CFSG.fittingSubgroup ↥(CFSG.pPrimeCore 3 X) = ⊥ := by
    have hmap : (CFSG.fittingSubgroup ↥(CFSG.pPrimeCore 3 X)).map
        (CFSG.pPrimeCore 3 X).subtype = ⊥ :=
      fittingSubgroupOf_pPrimeCore_eq_bot (X := X) hθ
    exact (Subgroup.map_eq_bot_iff_of_injective (f := (CFSG.pPrimeCore 3 X).subtype)
      (CFSG.fittingSubgroup ↥(CFSG.pPrimeCore 3 X))
      (CFSG.pPrimeCore 3 X).subtype_injective).1 hmap
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X))
  by_contra hne
  have : Nontrivial ↥(CFSG.pPrimeCore 3 X) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(CFSG.pPrimeCore 3 X))
  obtain ⟨L, hL⟩ := CFSG.EvenSporadicStandard.SolomonRed.exists_component hF ⟨x, hx⟩
  have hcomp : CFSG.IsComponent (L.map (CFSG.pPrimeCore 3 X).subtype) :=
    isComponent_map_subtype_of_normal (CFSG.pPrimeCore_normal (p := 3) (G := X)) hL
  refine hN3 ((hno _ hcomp).trans (Subgroup.card_dvd_of_le ?_))
  exact Subgroup.map_subtype_le L

end Components

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_map_le_of_commutator_eq_bot {p : ℕ} {M C : Subgroup G}
    (hM : IsStronglyPEmbedded p M) (hθM : inSubgroup (aschbacherSolvableCore 3) C ≤ M)
    {Q : Subgroup G} (hQC : Q ≤ C) (hQM : Q ≤ M) (hpQ : p ∣ Nat.card Q)
    (hcomm : ⁅(Q.subgroupOf C).map (QuotientGroup.mk' (aschbacherSolvableCore 3 C)),
      (CFSG.pPrimeCore 3 C).map (QuotientGroup.mk' (aschbacherSolvableCore 3 C))⁆ = ⊥) :
    (CFSG.pPrimeCore 3 C).map C.subtype ≤ M := by
  let θ : Subgroup C := aschbacherSolvableCore 3 C
  let N : Subgroup C := CFSG.pPrimeCore 3 C
  let Q' : Subgroup C := Q.subgroupOf C
  have hker : (QuotientGroup.mk' θ).ker = θ := QuotientGroup.ker_mk' θ
  have hQN : ⁅Q', N⁆ ≤ θ := by
    rw [← hker, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator]
    exact hcomm
  have hNnorm : N ≤ Subgroup.normalizer ((Q' ⊔ θ : Subgroup C) : Set C) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    calc
      ⁅Q' ⊔ θ, N⁆ = ⁅Q', N⁆ ⊔ ⁅θ, N⁆ := Subgroup.commutator_sup_right Q' θ N
      _ ≤ θ := sup_le hQN (Subgroup.commutator_le_left θ N)
      _ ≤ Q' ⊔ θ := le_sup_right
  let J : Subgroup G := (Q' ⊔ θ).map C.subtype
  have hNJ : N.map C.subtype ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.map_mono (f := C.subtype) hNnorm).trans
      (Subgroup.le_normalizer_map (H := Q' ⊔ θ) (f := C.subtype))
  have hJeq : J = Q ⊔ inSubgroup (aschbacherSolvableCore 3) C := by
    dsimp only [J, Q', θ]
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hQC]
    rfl
  have hJM : J ≤ M := hJeq ▸ sup_le hQM hθM
  have hpJ : p ∣ Nat.card J := by
    rw [hJeq]
    exact hpQ.trans (Subgroup.card_dvd_of_le le_sup_left)
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.le_of_le_normalizer_of_dvd_of_strong
    hM hJM hNJ hpJ

theorem pPrimeCore_map_le_of_three_dvd_components {M C : Subgroup G}
    (hθM : inSubgroup (aschbacherSolvableCore 3) C ≤ M)
    (hno : ∀ J : Subgroup (C ⧸ aschbacherSolvableCore 3 C), CFSG.IsComponent J →
      3 ∣ Nat.card J) :
    (CFSG.pPrimeCore 3 C).map C.subtype ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let θ : Subgroup ↥C := aschbacherSolvableCore 3 ↥C
  let ρ : ↥C →* ↥C ⧸ θ := QuotientGroup.mk' θ
  have hθ : aschbacherSolvableCore 3 (↥C ⧸ θ) = ⊥ :=
    CFSG.RankThree.theta_quotient_core_and_ranks (G := ↥C).1
  have hbot : CFSG.pPrimeCore 3 (↥C ⧸ θ) = ⊥ :=
    pPrimeCore_eq_bot_of_three_dvd_components hθ hno
  have hmap : (CFSG.pPrimeCore 3 ↥C).map ρ ≤ ⊥ :=
    (CFSG.map_pPrimeCore_le ρ (QuotientGroup.mk'_surjective θ)).trans (le_of_eq hbot)
  have hle : CFSG.pPrimeCore 3 ↥C ≤ θ := by
    have h := (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hmap)
    simpa only [ρ, QuotientGroup.ker_mk'] using h
  refine (Subgroup.map_mono hle).trans ?_
  simpa only [θ, inSubgroup] using hθM

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha
