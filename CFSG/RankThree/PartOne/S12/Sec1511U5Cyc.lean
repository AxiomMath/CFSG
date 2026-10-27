module

public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveEigen

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5L

open Module Module.End Polynomial

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem irreducible_minpoly_of_no_root [Nontrivial V] {E : End K V} {c : K}
    (hc : E ^ 5 = c • (1 : End K V)) (hb : ∀ t : K, t ^ 5 ≠ c) :
    Irreducible (minpoly K E) ∧ (minpoly K E).natDegree = 5 := by
  have hirr : Irreducible (X ^ 5 - C c : K[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_five hb
  have hroot : aeval E (X ^ 5 - C c : K[X]) = 0 := by
    simp [hc, Algebra.algebraMap_eq_smul_one]
  have hmin : minpoly K E = X ^ 5 - C c :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot (monic_X_pow_sub_C _ (by norm_num))).symm
  rw [hmin]
  exact ⟨hirr, natDegree_X_pow_sub_C⟩

theorem exists_fifth_root [FiniteDimensional K V] (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)} [Finite S]
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hnc : ¬ IsCyclic S)
    {a : LinearMap.GeneralLinearGroup K V} (ha : a ∈ S) {c : K}
    (hc : (a : End K V) ^ 5 = c • (1 : End K V)) : ∃ t : K, t ^ 5 = c := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  by_contra hb
  push Not at hb
  obtain ⟨hirr, hdeg⟩ := irreducible_minpoly_of_no_root hc hb
  apply hnc
  let ρ : S →* End K V := (Units.coeHom (End K V)).comp S.subtype
  refine KCEvenUnitaryFive.isCyclic_of_irreducible_minpoly (E := (a : End K V)) hirr
    (by rw [hdeg, hdim]) ρ (fun g g' h => Subtype.ext (Units.ext h)) fun g => ?_
  exact congrArg Units.val (hab g g.2 a ha)

theorem aeval_restrict_apply {E : End K V} {W : Submodule K V} (hW : ∀ w ∈ W, E w ∈ W) (P : K[X])
    (w : W) : ((aeval (E.restrict hW) P) w : V) = (aeval E P) (w : V) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply,
        LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul]
      congr 1
      rw [Module.End.pow_restrict n hW]
      rfl

theorem eq_top_of_irreducible_minpoly [FiniteDimensional K V] {E : End K V}
    (hirr : Irreducible (minpoly K E)) (hdeg : (minpoly K E).natDegree = finrank K V)
    (W : Submodule K V) (hW : ∀ w ∈ W, E w ∈ W) (hne : W ≠ ⊥) : W = ⊤ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hne
  set g : End K W := E.restrict hW with hg
  have hzero : aeval g (minpoly K E) = 0 := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [aeval_restrict_apply hW, minpoly.aeval]
    simp
  have hdvd : minpoly K g ∣ minpoly K E := minpoly.dvd K g hzero
  obtain ⟨q, hq⟩ := hdvd
  have hmon : (minpoly K g).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral g)
  rcases hirr.isUnit_or_isUnit hq with h | h
  · exact absurd (hmon.eq_one_of_isUnit h) (minpoly.ne_one K g)
  · have hq0 : q.natDegree = 0 := natDegree_eq_zero_of_isUnit h
    have hqne : q ≠ 0 := h.ne_zero
    have h5 : (minpoly K g).natDegree = finrank K V := by
      rw [← hdeg, hq, natDegree_mul hmon.ne_zero hqne, hq0, add_zero]
    have h6 : (minpoly K g).natDegree ≤ finrank K W := by
      have := natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly g)
        (LinearMap.charpoly_monic g).ne_zero
      rwa [LinearMap.charpoly_natDegree] at this
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) (h5 ▸ h6))

end U5L

end Sec1511

end CFSG.RankThree.PartOne
