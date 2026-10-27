module

public import CFSG.RankThree.PartTwo.KFacts.AutTriality

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
variable (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
include hf hK hσ

theorem trialityHasKind_graphField_of_pow_three_eq_one
    {τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hτ : τ ^ 3 = 1)
    (hout : ¬ IsInnerAut τ) : trialityHasKind σ τ .graphField := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, δ, rfl⟩ := exists_conj_mul_fieldActor hf hK hσ τ
  set I := (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range with hI
  have hIn : I.Normal := ⟨fun d hd β => by
    obtain ⟨y, rfl⟩ := hd
    exact ⟨β y, (mul_mulAutConj_mul_inv β y).symm⟩⟩
  have hgI : MulAut.conj g ∈ I := ⟨g, rfl⟩
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    have h1 : fieldActor (t := TwistTag.D4) σ 1 = 1 := map_one (fieldActorHom (t := TwistTag.D4) σ)
    rw [h1, mul_one] at hout
    exact hout hgI
  have hδ3I : fieldActor (t := TwistTag.D4) σ δ ^ 3 ∈ I := by
    have hmk : ((MulAut.conj g * fieldActor σ δ :
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸ I) =
        ((fieldActor (t := TwistTag.D4) σ δ :
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸ I) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hgI, one_mul]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hmk, ← QuotientGroup.mk_pow, hτ,
      QuotientGroup.mk_one]
  have hδ3 : δ ^ 3 = 1 := by
    rw [← isInnerAut_fieldActor_iff hf hK hσ]
    have h1 : fieldActor (t := TwistTag.D4) σ (δ ^ 3) = fieldActor σ δ ^ 3 :=
      map_pow (fieldActorHom (t := TwistTag.D4) σ) δ 3
    rw [h1]
    exact hδ3I
  refine ⟨δ, (orderOf_eq_prime hδ3 hδ1).symm ▸ dvd_rfl, ?_⟩
  rw [mul_inv_cancel_right]
  exact hgI

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKindTriality_graphField {x : G} (hx3 : x ^ 3 = 1) (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    InducesKindTriality σ L x .graphField := by
  obtain ⟨hx, -⟩ := id hout
  exact ⟨e, hx, trialityHasKind_graphField_of_pow_three_eq_one hf hK hσ
    (inducedAutHom_pow_eq_one L e hx hx3) ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout)⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
