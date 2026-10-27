module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

theorem mem_of_mem_sup_range_of_odd {G A : Type*} [Group G] [Group A] [Finite A]
    (hA : Odd (Nat.card A)) (I : Subgroup G) [I.Normal] (f : A →* G) {a : G}
    (ha : a ∈ I ⊔ f.range) {n : ℕ} (h2 : a ^ (2 ^ n) = 1) : a ∈ I := by
  obtain ⟨i, hi, d, ⟨t, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  set x : G ⧸ I := ((f t : G) : G ⧸ I) with hx
  have key : ((i * f t : G) : G ⧸ I) = x := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff i).mpr hi, one_mul]
  have h1 : x ^ (2 ^ n) = 1 := by
    rw [← key, ← QuotientGroup.mk_pow, h2, QuotientGroup.mk_one]
  have h3 : x ^ (Nat.card A) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, ← map_pow, pow_card_eq_one', map_one, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ n) (Nat.card A) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hA)
  have hx1 : x = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h3⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hfI : f t ∈ I := (QuotientGroup.eq_one_iff _).mp hx1
  exact I.mul_mem hi hfI

private theorem odd_card_fun_units (K : Type) [Field K] [Finite K] [CharP K 2] (r : ℕ) :
    Odd (Nat.card (Fin r → Kˣ)) := by
  rw [Nat.card_fun, Nat.card_fin]
  exact (LayerExc.odd_card_units (K := K)).pow

theorem twInndiagAut_two_mem_inner
    (f : ℕ)
    {a : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (ha : a ∈ LayerSixE.twInndiagAut f) {n : ℕ} (h2 : a ^ (2 ^ n) = 1) :
    a ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range := by
  haveI : (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))
      →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range.Normal := by
    refine ⟨fun x ⟨g, hg⟩ y => ⟨y g, ?_⟩⟩
    subst hg
    ext z
    simp [MulAut.conj_apply]
  have hodd : Odd (Nat.card ↥(TableB.TwE6.compat (frobQ 2 f))) :=
    Odd.of_dvd_nat (odd_card_fun_units (GaloisField 2 (2 * f)) _)
      (Subgroup.card_subgroup_dvd_card _)
  exact mem_of_mem_sup_range_of_odd hodd _ (RootCentExc.compatParamAut (frobQ 2 f)) ha h2

end CFSG.StandardType.LieKnownR2
