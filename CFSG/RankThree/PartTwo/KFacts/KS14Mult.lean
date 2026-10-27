module

public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.RankThree.PartTwo.KFacts.KS18Mult
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint

theorem not_sq_dvd_of_coprime_six {N : ℕ} (hN : N = 95040 ∨ N = 2520 ∨ N = 443520) {p : ℕ}
    (hp : p.Prime) (hp6 : Nat.Coprime 6 p) : ¬ p ^ 2 ∣ N := by
  have hcheck : ∀ q < 667, Nat.Coprime 6 q → 2 ≤ q →
      ¬ q ^ 2 ∣ 95040 ∧ ¬ q ^ 2 ∣ 2520 ∧ ¬ q ^ 2 ∣ 443520 := by
    decide +kernel
  intro hd
  have hN0 : 0 < N := by rcases hN with rfl | rfl | rfl <;> norm_num
  have hle := Nat.le_of_dvd hN0 hd
  have hp667 : p < 667 := by
    by_contra h
    have : 667 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    rcases hN with rfl | rfl | rfl <;> omega
  obtain ⟨h1, h2, h3⟩ := hcheck p hp667 hp6 hp.two_le
  rcases hN with rfl | rfl | rfl
  · exact h1 hd
  · exact h2 hd
  · exact h3 hd

theorem ks18Mult_sporadic (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hX : Group.IsPerfect X) (hZc : Z ≤ Subgroup.center X) (hcop : Nat.Coprime 6 (Nat.card Z))
    (hS : Nonempty (X ⧸ Z ≃* NativeSporadic.M12) ∨
      Nonempty (X ⧸ Z ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ⧸ Z ≃* NativeSporadic.M22)) : Z = ⊥ := by
  have hN : Nat.card (X ⧸ Z) = 95040 ∨ Nat.card (X ⧸ Z) = 2520 ∨ Nat.card (X ⧸ Z) = 443520 := by
    rcases hS with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine Or.inl ?_
      rw [Nat.card_congr e.toEquiv]
      obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M12.finite_card_le
      exact le_antisymm ((Nat.card_le_card_of_surjective _
        CFSG.Sporadic.Bridge.M12.toNative_surjective).trans hle)
        CFSG.Sporadic.Bridge.M12.le_card_native
    · refine Or.inr (Or.inl ?_)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    · refine Or.inr (Or.inr ?_)
      rw [Nat.card_congr e.toEquiv]
      obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
      exact le_antisymm ((Nat.card_le_card_of_surjective _
        CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
        CFSG.Sporadic.Bridge.M22.le_card_native
  refine eq_bot_of_isPerfect_of_not_sq_dvd hZc fun p hp hpZ => ?_
  have hp6 : Nat.Coprime 6 p := Nat.Coprime.coprime_dvd_right hpZ hcop
  exact not_sq_dvd_of_coprime_six hN hp hp6

theorem card_dvd_griess_of_le_center {X S : Type} [Group X] [Group S] (hX : Group.IsPerfect X)
    {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X) (e : X ⧸ Z ≃* S) :
    Nat.card Z ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  have := hX
  let q : X →* S := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' Z x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq (hker.le.trans hZc)
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq (hker.le.trans hZc))

theorem exceptionalOrders_dvd_twelve (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ) :
    (Blueprint.Multiplier.exceptionalOrders t n p f).1 ∣ 12 ∧
      (Blueprint.Multiplier.exceptionalOrders t n p f).2 ∣ 12 := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> norm_num

theorem card_griess_table_dvd {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) (p f : ℕ) :
    Nat.card (Blueprint.Multiplier.generic t 3 p f × Blueprint.Multiplier.exceptional t 3 p f) ∣
      6 ^ 4 := by
  have hcard : ∀ n : ℕ, Nat.card (Multiplicative (ZMod n)) = n := fun n => by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨he1, he2⟩ := exceptionalOrders_dvd_twelve t 3 p f
  have hg : (Blueprint.Multiplier.genericOrders t 3 p f).1 ∣ 3 ∧
      (Blueprint.Multiplier.genericOrders t 3 p f).2 = 1 := by
    rcases ht with rfl | rfl
    · exact ⟨Nat.gcd_dvd_left _ _, rfl⟩
    · exact ⟨Nat.gcd_dvd_left _ _, rfl⟩
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, hcard, hcard, hcard, hcard, hg.2, mul_one]
  have h1 : (Blueprint.Multiplier.genericOrders t 3 p f).1 *
      ((Blueprint.Multiplier.exceptionalOrders t 3 p f).1 *
        (Blueprint.Multiplier.exceptionalOrders t 3 p f).2) ∣ 3 * (12 * 12) :=
    Nat.mul_dvd_mul hg.1 (Nat.mul_dvd_mul he1 he2)
  exact h1.trans (by norm_num)

theorem eq_one_of_dvd_six_pow {m : ℕ} (hm : m ∣ 6 ^ 4) (hcop : Nat.Coprime 6 m) : m = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left 4 hcop).symm hm

theorem ks18Mult_lie (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal] (hX : Group.IsPerfect X)
    (hZc : Z ≤ Subgroup.center X) (hcop : Nat.Coprime 6 (Nat.card Z))
    (hS : Sec13.IsLThreePi (X ⧸ Z)) : Z = ⊥ := by
  obtain ⟨p, e, hp, he, hiso⟩ := hS
  have hdvdM := card_dvd_griess_of_le_center hX hZc (MulEquiv.refl (X ⧸ Z))
  have hq2 : 2 ≤ p ^ e := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
  rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 p e :=
      ⟨hp.out, he, by norm_num, by simp, by simp⟩
    have hm := KS21Mult.lieModel_of_mulEquiv φ (KS21Mult.lieModel_projSL hadm)
    obtain ⟨-, ⟨eM⟩⟩ := hGA _ .PSL 3 p e hm
    rw [Nat.card_congr eM.toEquiv] at hdvdM
    exact Subgroup.eq_bot_of_card_eq _
      (eq_one_of_dvd_six_pow (hdvdM.trans (card_griess_table_dvd (Or.inl rfl) p e)) hcop)
  · rcases (show p ^ e = 2 ∨ 2 < p ^ e by omega) with h2 | h2
    ·
      exfalso
      have hp2 : p = 2 := by
        have hdvd : p ∣ 2 := h2 ▸ dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hdvd
      subst hp2
      have he1 : e = 1 := by
        have : 2 ^ e = 2 ^ 1 := by rw [h2, pow_one]
        exact Nat.pow_right_injective le_rfl this
      subst he1
      have hsolU : Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSU 3 2 1) :=
        Sec13.isSolvable_projSU_two
      have hsol : Group.IsSolvable (X ⧸ Z) :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have hperf : Group.IsPerfect (X ⧸ Z) := inferInstance
      have hcard : Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 2 1) = 72 := by
        have hK : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
          rw [GaloisField.card 2 (2 * 1) (by norm_num)]
          norm_num
        have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl hK
          (n := 3) (by norm_num)
        rw [Nat.card_congr ((Census.statedProjEquivProjImage _).trans
          (MulEquiv.subgroupCongr (Census.projImage_statedSU 3 2 1))).toEquiv] at h
        rw [h, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
          Finset.prod_pair (by norm_num)]
        norm_num
      have hnt : Nontrivial (X ⧸ Z) := by
        rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_congr φ.toEquiv, hcard]
        norm_num
      exact Group.IsPerfect.not_isSolvable (X ⧸ Z) hsol
    · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 p e :=
        ⟨hp.out, he, le_rfl, by
          intro h
          have := (Prod.mk.inj h).2
          omega⟩
      have hm := KS21Mult.lieModel_of_mulEquiv φ (KS21Mult.lieModel_projSU hadm)
      obtain ⟨-, ⟨eM⟩⟩ := hGA _ .PSU 3 p e hm
      rw [Nat.card_congr eM.toEquiv] at hdvdM
      exact Subgroup.eq_bot_of_card_eq _
        (eq_one_of_dvd_six_pow (hdvdM.trans (card_griess_table_dvd (Or.inr rfl) p e)) hcop)

theorem ks18Mult_of_parts (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hJ2 : ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal], Group.IsPerfect X →
      Z ≤ Subgroup.center X → Nat.Coprime 6 (Nat.card Z) →
      Nonempty (X ⧸ Z ≃* NativeSporadic.J2) → Z = ⊥) :
    KS18Mult := by
  intro X _ _ Z _ hX hZc hcop hS
  rcases hS with hL | hM12 | hJ | hA7 | hM22
  · exact ks18Mult_lie hGA X Z hX hZc hcop hL
  · exact ks18Mult_sporadic X Z hX hZc hcop (Or.inl hM12)
  · exact hJ2 X Z hX hZc hcop hJ
  · exact ks18Mult_sporadic X Z hX hZc hcop (Or.inr (Or.inl hA7))
  · exact ks18Mult_sporadic X Z hX hZc hcop (Or.inr (Or.inr hM22))

end CFSG.RankThree.PartTwo.KFacts.KS14
