module

public import CFSG.Quasithin.Vol2.Ch11SecBNPCase
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Vol2.Ch11SecBL2OOrd
public import CFSG.Quasithin.Vol2.Ch11SecBL2OPSL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

theorem L2BadType.isSimpleGroup {k : ℕ} (hk : 2 ≤ k) {Y : Type} [Group Y] (h : L2BadType k Y) :
    IsSimpleGroup Y := by
  rcases h with h | h | h | h
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity Y 2 k h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 2 k h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 k h).2
  · unfold E2.IsSp4Prime at h
    split_ifs at h with hk1
    · omega
    · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Y 2 2 k h

theorem isSolvable_SL2_three : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
  CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by decide)

theorem false_of_surjective_SL2
    {K Y : Type} [Group K] [Group Y] [Finite Y] [Group.IsPerfect K]
    {k p : ℕ} (hk : 2 ≤ k) (hY : L2BadType k Y)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ CFSG.Open.pCore 2 K))
    (ψ : K →* Y) (hψ : Function.Surjective ψ) (hp : p.Prime) (hp2 : p ≠ 2)
    (f : K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hf : Function.Surjective f) : False := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp3 : p = 3
  · subst hp3
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
      Group.IsPerfect.ofSurjective hf
    have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
      nontrivial_of_ne 1 (-1) (by decide)
    exact Group.IsPerfect.not_isSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
      isSolvable_SL2_three
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by decide)
    omega
  have hYs : IsSimpleGroup Y := hY.isSimpleGroup hk
  have hPs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    isSimpleGroup_psl2 hp5
  set g : K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (QuotientGroup.mk' _).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hN : IsPGroup 2 (CFSG.Open.pCore 2 K) := by
    exact CFSG.pCore_isPGroup
  have hNn : (CFSG.Open.pCore 2 K).Normal := by
    exact CFSG.pCore_normal
  have h1 := card_eq_of_surjective_of_isQuasisimple (nonabelian_of_perfect_surjective ψ hψ) hN hKq
    ψ hψ
  have h2 := card_eq_of_surjective_of_isQuasisimple (nonabelian_of_perfect_surjective g hgs) hN
    hKq g hgs
  have hcard : 2 * Nat.card Y = p * (p ^ 2 - 1) := by
    rw [h1, ← h2, two_mul_card_psl2 hp2]
  exact false_of_l2BadType_of_card hk hY hp hp2 hcard

end CFSG.Quasithin.Vol2.Ch11.SecB
