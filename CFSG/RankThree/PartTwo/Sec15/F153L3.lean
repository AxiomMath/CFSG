module

public import CFSG.RankThree.PartTwo.Sec15.F153Leaf
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ln
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Unit
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddL3
import CFSG.RankThree.PartTwo.Sec4.Item47CasesAlt
import CFSG.HardMathSupport.Solomon.Proving.SU3CentreScalars

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Assembly.RankThreeEven (projSL projSU)

section KFacts

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic (noIrrFFOffender_transfer)
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd (noIrrFFOffender_lie_A noIrrFFOffender_lie_twistedA)

theorem noFFModule_of_isLThreeEpsAt_odd
    {T : Type} [Group T] {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hU : ¬ (p = 3 ∧ f = 1 ∧ Nonempty (T ≃* projSU 3 p f)))
    (hε : IsLThreeEpsAt T p f) : NoFFModule T := by
  let q : TauCeti.PrimePower := ⟨p, f, hp.out, hf⟩
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hq3' : 3 ≤ p ^ f := hp3.trans hpf
  rcases hε with ⟨⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
  · have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp
      exact fun h => by
        have h' : p ^ f = 2 := h
        omega
    have hcar : NoIrrFFOffender (TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) := by
      by_cases hf1 : f = 1
      · exact noIrrFFOffender_lie_odd ⟨.A 2 q, hv⟩ ⟨hf1, hp2⟩
      · exact noIrrFFOffender_lie_A hv hp2 le_rfl (by simp only [q]; omega)
    exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_transfer hcar
      ⟨(Census.typeAGroupEquivProjSL 2 q hv).trans φ.symm⟩)
  · have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp
      exact hq3'
    have hcar : NoIrrFFOffender (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) := by
      by_cases hf1 : f = 1
      · have hp5 : 5 ≤ p := by
          have hp3' : p ≠ 3 := fun h => hU ⟨h, hf1, ⟨φ⟩⟩
          have hp4 : p ≠ 4 := by
            rintro rfl
            exact absurd hp.out (by norm_num)
          omega
        exact noIrrFFOffender_lie_odd ⟨.twistedA 2 q, hv⟩ ⟨hf1, hp5⟩
      · exact noIrrFFOffender_lie_twistedA hv hp2 (by simp only [q]; omega) (by simp) (by simp)
    exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_transfer hcar
      ⟨(Census.typeTwistedAGroupEquivProjSU 2 q hv).trans φ.symm⟩)

end KFacts

section Glue

open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedScalars StatedProj StatedClassicalModel
  specialLinearGroupEquivStatedSL map_center_eq_statedScalars)

theorem exists_pos_isLThreeEpsAt {Q : Type} [Group Q] {p f : ℕ} [Fact p.Prime]
    (h : IsLThreeEpsAt Q p f) : ∃ n : ℕ, 1 ≤ n ∧ IsLThreeEpsAt Q p n := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rcases h with ⟨⟨φ⟩⟩ | ⟨h2, -⟩
    · letI : Fintype (GaloisField p 0) := Fintype.ofFinite _
      obtain ⟨n, hp, hn⟩ := FiniteField.card (GaloisField p 0) p
      have e1 : projSL 3 (GaloisField p 0) ≃* StatedProj (StatedSL 3 (GaloisField p 0)) :=
        (MulEquiv.subgroupCongr (Census.projImage_statedSL 3 (GaloisField p 0))).symm.trans
          (Census.statedProjEquivProjImage _).symm
      have hmod : StatedClassicalModel Q .PSL 3 p n :=
        ⟨⟨hp, n.pos, by norm_num, by simp, by simp⟩, GaloisField p 0, inferInstance,
          inferInstance, by rw [Nat.card_eq_fintype_card]; exact hn, ⟨φ.trans e1⟩⟩
      obtain ⟨e⟩ := Ronan148T.nonempty_projSL_of_statedClassicalModel hmod
      exact ⟨n, n.pos, Or.inl ⟨e⟩⟩
    · norm_num at h2
  · exact ⟨f, hf, h⟩

theorem exists_isLThreeEpsAt_quot_of_isSLThreeEpsAt {Q : Type} [Group Q]
    (hq : CFSG.IsQuasisimple Q) {q : ℕ} (h : Sec4.IsSLThreeEpsAt Q q) :
    ∃ (p n : ℕ) (_ : Fact p.Prime), 1 ≤ n ∧ IsLThreeEpsAt (Q ⧸ Subgroup.center Q) p n := by
  obtain ⟨K, _, _, h⟩ := h
  letI := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hKk : Nat.card K = ringChar K ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hk
  rcases h with ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩
  ·
    have hcen : (Subgroup.center Q).map φ.toMonoidHom =
        (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) :=
      (Subgroup.map_center_eq φ).trans
        ((Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 3 K)).symm.trans
          (map_center_eq_statedScalars 3 K))
    have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 3 (ringChar K) k :=
      ⟨⟨hp, k.pos, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance, hKk,
        ⟨QuotientGroup.congr _ _ φ hcen⟩⟩
    obtain ⟨e⟩ := Ronan148T.nonempty_projSL_of_statedClassicalModel hmod
    exact ⟨ringChar K, k, ⟨hp⟩, k.pos, Or.inl ⟨e⟩⟩
  ·
    have hq2 : q ^ 2 = ringChar K ^ (k : ℕ) := by rw [← hK, hKk]
    obtain ⟨m, -, hqm⟩ : ∃ m, m ≤ (k : ℕ) ∧ q = ringChar K ^ m :=
      (Nat.dvd_prime_pow hp).1 (Dvd.intro q (by rw [← sq, hq2]))
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exfalso
        have h1 : Nat.card K = 1 := by rw [hK, hqm]; simp
        have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
        omega
      · exact hm
    have hne2 : ringChar K ^ m ≠ 2 := by
      intro h2
      have hq2' : q = 2 := hqm.trans h2
      subst hq2'
      have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
        ⟨Nat.prime_two, le_rfl, by rw [hK]⟩
      have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
      have := Fintype.ofFinite (StatedSU 3 (2 ^ 1) K)
      have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
          (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
      exact Sec4.false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    subst hqm
    have hcen : (Subgroup.center Q).map φ.toMonoidHom =
        (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (ringChar K ^ m) K) :=
      (Subgroup.map_center_eq φ).trans
        (HardMathSupport.Solomon.Proving.center_statedSU_three_eq_scalars hK)
    have hpm : 2 ≤ ringChar K ^ m :=
      hp.two_le.trans (Nat.le_self_pow (by omega) _)
    have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 3 (ringChar K) m :=
      ⟨⟨hp, hm1, le_rfl, fun h => hne2 (Prod.ext_iff.mp h).2⟩, K, inferInstance, inferInstance, hK,
        ⟨QuotientGroup.congr _ _ φ hcen⟩⟩
    obtain ⟨e⟩ := Ronan148T.nonempty_projSU_of_statedClassicalModel hmod
    exact ⟨ringChar K, m, ⟨hp⟩, hm1, Or.inr ⟨lt_of_le_of_ne hpm (Ne.symm hne2), ⟨e⟩⟩⟩

theorem exists_isLThreeEpsAt_quot_of_isL3Type153 {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (h : IsL3Type153 Q) :
    ∃ (p n : ℕ) (_ : Fact p.Prime), 1 ≤ n ∧ IsLThreeEpsAt (Q ⧸ Subgroup.center Q) p n := by
  rcases h with ⟨p, f, hp, hε⟩ | ⟨q, hSL⟩
  · obtain ⟨n, hn, hε'⟩ := exists_pos_isLThreeEpsAt hε
    have hsimple : IsSimpleGroup Q := Main148.isSimpleGroup_of_isLThreeEpsAt148 hn hε'
    obtain ⟨e⟩ := nonempty_centerQuotient_equiv_of_simple hq hsimple (MulEquiv.refl Q)
    exact ⟨p, n, hp, hn, IsLThreeEpsAt.of_mulEquiv e.symm hε'⟩
  · exact exists_isLThreeEpsAt_quot_of_isSLThreeEpsAt hq hSL

end Glue

section Leaf

@[expose] noncomputable def Step153PushL3Char2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) → ∀ f : ℕ, 1 ≤ f →
          IsLThreeEpsAt ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) 2 f →
            Concl153Push A Y S

@[expose] noncomputable def Step153PushU33R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) →
          Nonempty (((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≃*
            projSU 3 3 1) → Concl153Push A Y S

theorem step153PushL3R_of_inputs
    (h149 : Sec16.Item149S14) (htwin : Claim153TwinR) (h2 : Step153PushL3Char2R)
    (h33 : Step153PushU33R) : Step153PushL3R := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY hT
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  obtain ⟨p, n, hp, hn, hε⟩ := exists_isLThreeEpsAt_quot_of_isL3Type153 hq hT
  by_cases hp2 : p = 2
  · subst hp2
    exact h2 G A c L hR Y hY S hS hno hFF hSY n hn hε
  · by_cases hU : p = 3 ∧ n = 1 ∧ Nonempty
        (((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≃* projSU 3 p n)
    · obtain ⟨rfl, rfl, hU'⟩ := hU
      exact h33 G A c L hR Y hY S hS hno hFF hSY hU'
    · exact concl153Push_of_noFFModule h149 htwin hR hY hS hno hFF hSY
        (noFFModule_of_isLThreeEpsAt_odd hp2 hn hU hε) (MulEquiv.refl _)

end Leaf

end CFSG.RankThree.PartTwo.Sec15.F153
