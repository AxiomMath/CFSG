module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofOutData
import CFSG.RankThree.PartTwo.Sec4.Item413Classical
import CFSG.RankThree.PartTwo.Sec4.Item413Cases
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartOne.Mult.Exceptional

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


namespace Res417Three

@[expose] def K417RankTwoLieP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    (∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .G2 p 1 →
      CFSG.pRank 3 X ≤ 2) ∧
    (p % 3 = 1 → CFSG.pRank 3 (projSU 4 p 1) ≤ 2) ∧
    (p % 3 = 2 → CFSG.pRank 3 (projSL 4 (GaloisField p 1)) ≤ 2)

@[expose] def K417CenterLieP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
    (ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .G2 p 1 ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* projSp 2 (GaloisField p 1)) ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* projSU 4 p 1) ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* projSL 4 (GaloisField p 1))) →
    ∀ r : ℕ, r.Prime → 3 < r → ¬ r ∣ Nat.card (Subgroup.center Y)

theorem pRank_le_two_of_card_le_nine {S : Type*} [Group S]
    (hS : ∀ F : Subgroup S, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9) :
    CFSG.pRank 3 S ≤ 2 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  have hB' : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨hB.toIsMulCommutative, fun x hx => ?_⟩
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hx⟩
    simpa using congrArg Subtype.val h
  have h9 := hS B hB'
  rw [hr] at h9
  by_contra hr2
  have : 3 ^ 3 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem pRank_projSp_two_le {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hs : IsSimpleGroup (projSp 2 (GaloisField p f))) :
    CFSG.pRank 3 (projSp 2 (GaloisField p f) ⧸ Subgroup.center (projSp 2 (GaloisField p f))) ≤
      2 := by
  set F := GaloisField p f
  have hF : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out hp3 hF
  refine pRank_le_two_of_card_le_nine fun B hB =>
    Sec4.card_le_of_projImage _ hs (m := 2) (by norm_num)
      (fun c hc => Sec4.sq_of_scalar_mem_closure_sp (by norm_num) hc) (by norm_num)
      (fun P hPH hcomm hexp => ?_) B hB
  have h := Sec4.card_sq_le_of_mem_closure_sp h3 P hPH hcomm hexp
  norm_num at h
  nlinarith

theorem k417CenterLieP_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : K417CenterLieP := by
  intro p _ hp3 Y _ _ hY hX r hr hr3 hrZ
  have hp : p.Prime := Fact.out
  have hr5 : 5 ≤ r := CFSG.RankThree.PartOne.five_le_of_prime' hr hr3
  have hr4 : ¬ r ∣ 4 := fun h => absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have hclass : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ},
      CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) t n p 1 →
      (t ≠ .PSL ∨ ¬ r ∣ n) → (t ≠ .PSU ∨ ¬ r ∣ n) → False := by
    intro t n hm h1 h2
    have hdvd := KFacts.KS21Mult.card_center_dvd_griess hY.1 (MulEquiv.refl (Y ⧸ Subgroup.center Y))
    obtain ⟨eM⟩ := (hGA _ t n p 1 hm).2
    rw [Nat.card_congr eM.toEquiv, Nat.card_prod, Res417.card_zmod_prod,
      Res417.card_zmod_prod] at hdvd
    rcases CFSG.RankThree.PartOne.prime_dvd_table hr hr3 (hrZ.trans hdvd) with
      ⟨ht, hrn, -⟩ | ⟨ht, hrn, -⟩
    · rcases h1 with h | h
      · exact h ht
      · exact h hrn
    · rcases h2 with h | h
      · exact h ht
      · exact h hrn
  have hp1 : p ^ 1 = p := pow_one p
  rcases hX with hG2 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact CFSG.RankThree.PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA Y hY
      (Or.inl ⟨.G2, p, 1, by simp [chevalleyExceptionalTags], hG2⟩) r hr hr3 hrZ
  · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp 2 p 1 :=
      ⟨hp, le_rfl, le_rfl, by rw [hp1]; intro h; simp at h; omega⟩
    exact hclass (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSp hadm))
      (Or.inl (by decide)) (Or.inl (by decide))
  · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 p 1 :=
      ⟨hp, le_rfl, by norm_num, by rw [hp1]; intro h; simp at h⟩
    exact hclass (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSU hadm))
      (Or.inl (by decide)) (Or.inr hr4)
  · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 4 p 1 :=
      ⟨hp, le_rfl, by norm_num, by rw [hp1]; intro h; simp at h, by rw [hp1]; intro h; simp at h⟩
    exact hclass (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSL hadm))
      (Or.inr hr4) (Or.inl (by decide))

end Res417Three

open Res417Three

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerOutConf417.isSimpleGroup (h : IsInnerOutConf417 L A E c m) :
    IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := by
  have hq := (CFSG.LocalCores.quasisimple_central_quotient h.2.2.1.1
    (aschbacherSolvableCore 3 L) (aschbacherSolvableCore_le_center h.2.2.1.1)).1
  have := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq h.2.2.2.2.2.2.2.2.2.2.1).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem item417OutLieP_of (hR : K417RankTwoLieP) (hC : K417CenterLieP) : Item417OutLieP := by
  intro G _ _ L A E c m hconf ⟨p, _, hp3, hX⟩
  have hp : p.Prime := Fact.out
  have eC := hconf.centerEquiv
  have hθ : aschbacherSolvableCore 3 L = ⊥ := by
    refine theta_eq_bot_of_two_three hconf.2.1 hconf.2.2.1 fun r hr hr3 => ?_
    refine hC p hp3 L hconf.2.2.1.1 ?_ r hr hr3
    rcases hX with hG2 | ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eC hG2)
    · exact Or.inr (Or.inl ⟨eC.trans φ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨eC.trans φ⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨eC.trans φ⟩))
  set eL : L ≃* L ⧸ aschbacherSolvableCore 3 L := (Res417.thetaQuotEquivOfEqBot hθ).symm
  rcases hX with hG2 | ⟨⟨φ⟩⟩ | ⟨hp1, ⟨φ⟩⟩ | ⟨hp2, ⟨φ⟩⟩
  · have hm := hconf.eq_three_of_pRank_le_two eC ((hR p hp3).1 _ hG2)
    exact Or.inr (Or.inr (Or.inl ⟨hm, p, inferInstance, hp3,
      Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eL hG2)⟩))
  · have := hconf.isSimpleGroup
    have hs : IsSimpleGroup (projSp 2 (GaloisField p 1)) := φ.symm.isSimpleGroup
    have : Finite (projSp 2 (GaloisField p 1)) := Finite.of_equiv _ (eC.trans φ).toEquiv
    have hZ : Subgroup.center (projSp 2 (GaloisField p 1)) = ⊥ := by
      rw [← Subgroup.map_center_eq φ, hconf.2.2.2.2.2.2.2.2.2.2.1, Subgroup.map_bot]
    have hm := hconf.eq_three_of_pRank_le_two
      (eC.trans (φ.trans (quotientCenterEquivOfBot hZ).symm))
      (pRank_projSp_two_le (by omega) le_rfl hs)
    exact Or.inr (Or.inr (Or.inl ⟨hm, p, inferInstance, hp3,
      Or.inr (Or.inl ⟨eL.trans φ⟩)⟩))
  · have : Finite (projSU 4 p 1) := Finite.of_equiv _ (eC.trans φ).toEquiv
    have hm := hconf.eq_three_of_pRank_le_two (eC.trans φ) ((hR p hp3).2.1 hp1)
    exact Or.inr (Or.inr (Or.inl ⟨hm, p, inferInstance, hp3,
      Or.inr (Or.inr (Or.inl ⟨hp1, ⟨eL.trans φ⟩⟩))⟩))
  · have : Finite (projSL 4 (GaloisField p 1)) := Finite.of_equiv _ (eC.trans φ).toEquiv
    have hm := hconf.eq_three_of_pRank_le_two (eC.trans φ) ((hR p hp3).2.2 hp2)
    exact Or.inr (Or.inr (Or.inl ⟨hm, p, inferInstance, hp3,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, ⟨eL.trans φ⟩⟩)))⟩))

end Certs

end CFSG.RankThree.PartTwo.Sec4
