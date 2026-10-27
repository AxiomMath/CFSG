module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG7
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus

section Std

theorem exists_stdSetup_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hperf : commutator ↥(adjointGroup .E6 K) = ⊤) :
    ∃ S : LangSetup .E6 (AlgebraicClosure K) 5, S.D.q = 2 ^ f ∧
      S.Γ = (adjointGroup .E6 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) ∧
      ∀ y : ModGL .E6 K,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y ∈
          adjointGroup .E6 (AlgebraicClosure K) →
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y ∈ S.D.model := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hf1 : 1 ≤ f := by
    by_contra h0
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hK
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hFr : ∀ c : AlgebraicClosure K,
      iterateFrobenius (AlgebraicClosure K) 2 f c = c ^ Nat.card K := fun c => by
    rw [hK]
    rfl
  have hFr' : ∀ c : AlgebraicClosure K,
      iterateFrobenius (AlgebraicClosure K) 2 f c = c ^ (2 ^ f) := fun c => rfl
  have hFix : ∀ y : ModGL .E6 K,
      entrywiseFrobGL .E6 (AlgebraicClosure K) 2 f
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
    intro y
    have hcomp : (iterateFrobenius (AlgebraicClosure K) 2 f).comp
        (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius (AlgebraicClosure K) 2 f) (algebraMap K (AlgebraicClosure K) c) =
        algebraMap K (AlgebraicClosure K) c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  let D : LangDatum .E6 (AlgebraicClosure K) :=
    LangDatum.ofFrobenius (iterateFrobenius (AlgebraicClosure K) 2 f) (2 ^ f) hFr' 1
      (g0 := 1) (one_mem _) (by rw [map_one, one_mul, canonicalRep_one])
  have hd : LangDescent D 7
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .E6 K).subtype) :=
    langDescent_untw 3 (Or.inl ⟨rfl, rfl⟩) hFr D rfl Nat.prime_seven (by norm_num) hperf
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved .E6 (AlgebraicClosure K) D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 :=
    ⟨Nat.prime_two.isPrimePow.pow (by omega),
      (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 _).2 (dvd_pow_self 2 (by omega))⟩
  have hpq : ¬ 5 ∣ D.q := fun h => by
    have h5 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
    omega
  refine ⟨D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hd.finite_model, rfl, ?_, ?_⟩
  · show D.Γ = _
    rw [hd.Γ_eq, MonoidHom.range_comp, Subgroup.range_subtype]
    have hconj : (MulAut.conj D.g0⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [D, LangDatum.ofFrobenius]
    rw [hconj, Subgroup.map_id]
  · intro y hy
    refine (LangDatum.mem_model (D := D)).2 ⟨hy, ?_⟩
    show canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) 1 *
        entrywiseFrobGL .E6 (AlgebraicClosure K) 2 f
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) *
        (canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) 1)⁻¹ = _
    rw [hFix y, canonicalRep_one]
    group

end Std

end CFSG.StandardType.TableCRes
