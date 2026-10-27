module

public import CFSG.LocalAnalysis.UniquenessCase.UC22D4FunCentralizer
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2G2Fun
import CFSG.ClassicalInvolution.AschTight.S19COrd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

section Charts


theorem d4_slLong_map_equiv {X : Type} [Group X] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hσ : ∀ c, iterateFrobenius (GaloisField p (3 * f)) p f
      (iterateFrobenius (GaloisField p (3 * f)) p f
        (iterateFrobenius (GaloisField p (3 * f)) p f c)) = c)
    (ψ : twistedGroup (iterateFrobenius (GaloisField p (3 * f)) p f) ≃* X) :
    Nonempty ((slLong _ hσ).range.map ψ.toMonoidHom ≃* SL(2, GaloisField p f)) := by
  obtain ⟨eF⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_ringEquiv_of_natCard_eq
    (F := CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
      (iterateFrobenius (GaloisField p (3 * f)) p f)) (F' := GaloisField p f) (by
      rw [CFSG.ClassicalInvolution.ModelFacts.card_fixedField_iterateFrobenius hf,
        GaloisField.card p f (by omega)])
  exact ⟨(Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).symm.trans
    ((MonoidHom.ofInjective (slLong_injective hσ)).symm.trans
      (CFSG.ClassicalInvolution.ModelFacts.slMapEquiv eF))⟩

theorem d4_slB_map_equiv {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (hσ : ∀ c, iterateFrobenius (GaloisField p (3 * f)) p f
      (iterateFrobenius (GaloisField p (3 * f)) p f
        (iterateFrobenius (GaloisField p (3 * f)) p f c)) = c)
    (ψ : twistedGroup (iterateFrobenius (GaloisField p (3 * f)) p f) ≃* X) :
    Nonempty ((slB _ hσ).range.map ψ.toMonoidHom ≃* SL(2, GaloisField p (3 * f))) :=
  ⟨(Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).symm.trans
    (MonoidHom.ofInjective (slB_injective hσ)).symm⟩

theorem d4_pRank_centralizer_of_mem_slLong {X : Type} [Group X] [Finite X] {p f : ℕ}
    [hp : Fact p.Prime] (hf : 1 ≤ f)
    (hσ : ∀ c, iterateFrobenius (GaloisField p (3 * f)) p f
      (iterateFrobenius (GaloisField p (3 * f)) p f
        (iterateFrobenius (GaloisField p (3 * f)) p f c)) = c)
    (ψ : twistedGroup (iterateFrobenius (GaloisField p (3 * f)) p f) ≃* X) {x : X}
    (hx : x ∈ (slLong _ hσ).range.map ψ.toMonoidHom) :
    3 * f ≤ Open.pRank p (centralizer ({x} : Set X)) := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
  let u : Multiplicative (GaloisField p (3 * f)) →* SL(2, GaloisField p (3 * f)) :=
    { toFun := fun t => CFSG.SectionRank.OddCover.slU t.toAdd
      map_one' := CFSG.SectionRank.OddCover.slU_zero
      map_mul' := fun s t => CFSG.SectionRank.OddCover.slU_add s.toAdd t.toAdd }
  have hu : Function.Injective u := fun s t h =>
    CFSG.SectionRank.OddCover.pslU_injective (congrArg CFSG.SectionRank.OddCover.pslMk h)
  refine CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt (fun a b => mul_comm a b)
    CFSG.SectionRank.OddCover.multiplicative_pow_char_eq_one ?_
    (ψ.toMonoidHom.comp ((slB _ hσ).comp u)) (ψ.injective.comp ((slB_injective hσ).comp hu)) ?_
  · rw [show Nat.card (Multiplicative (GaloisField p (3 * f))) = Nat.card (GaloisField p (3 * f))
      from Nat.card_congr Multiplicative.toAdd, GaloisField.card p (3 * f) (by omega)]
  · rintro _ ⟨t, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    change ψ (slLong _ hσ A) * ψ (slB _ hσ (u t)) = ψ (slB _ hσ (u t)) * ψ (slLong _ hσ A)
    rw [← map_mul ψ, ← map_mul ψ, slLong_comm_slB hσ A (u t)]

end Charts


theorem d4_fund_eq_long_or_short {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n p f) {K : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K) :
    ∃ (hσ : ∀ c, iterateFrobenius (GaloisField p (3 * f)) p f
          (iterateFrobenius (GaloisField p (3 * f)) p f
            (iterateFrobenius (GaloisField p (3 * f)) p f c)) = c)
      (ψ : twistedGroup (iterateFrobenius (GaloisField p (3 * f)) p f) ≃* X),
      K = (slLong _ hσ).range.map ψ.toMonoidHom ∨ K = (slB _ hσ).range.map ψ.toMonoidHom := by
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_mem_funSet (𝔉 := fundPred (p ^ f)) hK
  obtain ⟨hσ, ψ, hFun⟩ := d4_funSet_eq_pair hp2 hadm hX P
  rw [hFun] at hP
  refine ⟨hσ, ψ, ?_⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hP

theorem d4_fund_equiv_sl2 {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n p f) {K : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K) :
    Nonempty (K ≃* SL(2, GaloisField p f)) ∨ Nonempty (K ≃* SL(2, GaloisField p (3 * f))) := by
  obtain ⟨hσ, ψ, rfl | rfl⟩ := d4_fund_eq_long_or_short hp2 hadm hX hK
  · exact Or.inl (d4_slLong_map_equiv hadm.2.1 hσ ψ)
  · exact Or.inr (d4_slB_map_equiv hσ ψ)

theorem d4_pRank_centralizer_of_mem_long {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n p f) {K : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K) (eK : Nonempty (K ≃* SL(2, GaloisField p f))) {x : X}
    (hx : x ∈ K) : 3 * f ≤ Open.pRank p (centralizer ({x} : Set X)) := by
  have hp : p.Prime := Fact.out
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hσ, ψ, rfl | rfl⟩ := d4_fund_eq_long_or_short hp2 hadm hX hK
  · exact d4_pRank_centralizer_of_mem_slLong hf hσ ψ hx
  · exfalso
    obtain ⟨eK⟩ := eK
    obtain ⟨eS⟩ := d4_slB_map_equiv hσ ψ
    have hcard := Nat.card_congr (eK.symm.trans eS).toEquiv
    rw [CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.card_sl2,
      CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.card_sl2,
      GaloisField.card p f (by omega), GaloisField.card p (3 * f) (by omega)] at hcard
    have h1 : p ^ f < p ^ (3 * f) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    have h2 : (p ^ f) ^ 2 < (p ^ (3 * f)) ^ 2 := Nat.pow_lt_pow_left h1 two_ne_zero
    have h3 : 0 < (p ^ f) ^ 2 := pow_pos (pow_pos hp.pos f) 2
    exact (Nat.mul_lt_mul_of_lt_of_lt h1 (by omega)).ne hcard

end CFSG.LocalAnalysis.UniquenessCase.UC22
