module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RU419Rank
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowRankTwo
public import CFSG.RankThree.PartTwo.Sec4.Item49OddChar
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.GorensteinWalter (PSL2)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem noCfgU419_psl2 {F : Type} [Field F] [Finite F] (h3 : ringChar F ≠ 3) :
    NoCfgU419 (PSL2 F) := by
  by_cases h4 : 4 ≤ Nat.card F
  · exact noCfgU419_of_autNoE27' (RonanK429.autNoE27_psl2 h3 h4)
  · have hc := RonanK432.card_psl2_mul_gcd F
    have hF : Nat.card F ≤ 3 := by omega
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    refine noCfgU419_of_two_pow_nine (M := Nat.card F * (Nat.card F ^ 2 - 1))
      (Dvd.intro _ hc) ?_
    interval_cases (Nat.card F) <;> decide

theorem noCfgU419_projSL_two {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (eX : X ≃* projSL 2 (GaloisField p e)) : NoCfgU419 X := by
  have : Finite (GaloisField p e) := inferInstance
  have hchar : ringChar (GaloisField p e) = p := ringChar.eq (GaloisField p e) p
  exact NoCfgU419.of_mulEquiv (eX.trans (projSLEquivPSL _)) (noCfgU419_psl2 (by rwa [hchar]))

section Rows


theorem rowsU419Two : RowsU419Two := by
  intro X _ _ _ _ hX
  apply NoCfgU419.rowU419
  obtain ⟨p, e, _, hp, he, he2, hX⟩ := hX
  have hp3 : p ≠ 3 := by omega
  have hf : ¬ 3 ∣ e := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hq : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
  refine noCfgU419_of_autNoE27' ?_
  rcases hX with ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact (RonanK429.autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_statedSL Fact.out hp3 hK hf)).of_mulEquiv φ
  · exact (RonanK429.autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_statedSU hp3 he hK hq hf)).of_mulEquiv φ
  · exact (RonanK429.autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL hp3 he hf)).of_mulEquiv φ
  · exact (RonanK429.autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU hp3 he hq hf)).of_mulEquiv φ

theorem forall_ne_of_noE27 {T : Type} [Group T] (h : RonanK429.NoE27 T) :
    ∀ E : Subgroup T, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27 :=
  fun E hE h27 => h E ⟨hE, h27⟩

theorem noCfgU419_of_simple_model {X T : Type} [Group X] [Finite X] [Group T] [Finite T]
    (hq : IsQuasisimple X) (eX : X ≃* T) (hT : IsSimpleGroup T)
    (hrank : CFSG.pRank 3 (T ⧸ Subgroup.center T) ≤ 2) (hout : ¬ 3 ∣ Nat.card (Outer X)) :
    NoCfgU419 X := by
  obtain ⟨a, b, hab⟩ := Census.exists_ne_of_isQuasisimple hq
  have hcenT : Subgroup.center T = ⊥ := by
    exact RonanK429.center_eq_bot_of_isSimpleGroup hT ⟨eX a, eX b, fun h => hab (eX.injective
      (by rw [map_mul, map_mul, h]))⟩
  have hcenX : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxT : eX x ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨y, rfl⟩ := eX.surjective t
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    rw [hcenT, Subgroup.mem_bot] at hxT
    exact (Subgroup.mem_bot).mpr (eX.injective (by rw [hxT, map_one]))
  have hN : RonanK429.NoE27 X :=
    (RonanK429.noE27_of_pRank_quot_le_two hcenT hrank).of_mulEquiv eX
  exact noCfgU419_of_noE27_of_cubeInner (by rw [hcenX]; exact IsPGroup.of_bot)
    (forall_ne_of_noE27 hN) (cubeInner_of_not_three_dvd_card_outer hout)

theorem rowsU419Three : RowsU419Three := by
  intro X _ _ hq hZ hX
  apply NoCfgU419.rowU419
  have hout := not_three_dvd_card_outer_list46_three X hX
  obtain ⟨p, _, hp, hX⟩ := hX
  have hp' : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  rcases hX with hG2 | ⟨⟨φ⟩⟩ | ⟨hp1, ⟨φ⟩⟩ | ⟨hp2, ⟨φ⟩⟩
  · exact noCfgU419_of_noE27_of_cubeInner hZ
      (Item434Spor.noE27_of_pRank_le_two (Res417Four.pRank_g2_le_two hp X hG2))
      (cubeInner_of_not_three_dvd_card_outer hout)
  · have hT : IsSimpleGroup (projSp 2 (GaloisField p 1)) := by
      have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
        (GaloisField p 1) 2 (by norm_num) (Or.inl (Or.inr (by rw [hK]; omega)))
      exact (projSpEquivStatedProj 2 (GaloisField p 1)).isSimpleGroup
    exact noCfgU419_of_simple_model hq φ hT (HeringUnitary.pRank_projSp_four_le_two hp) hout
  · have hT : IsSimpleGroup (projSU 4 p 1) :=
      CFSG.PGLModel.isSimpleGroup_projSU_of_admissible
        ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h⟩
    exact noCfgU419_of_simple_model hq φ hT
      (HeringUnitary.pRank_projSU_four_le_two (by omega) le_rfl (by rw [pow_one]; exact hp1)) hout
  · have hT : IsSimpleGroup (projSL 4 (GaloisField p 1)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
        (Or.inl (by norm_num))
    exact noCfgU419_of_simple_model hq φ hT
      (HeringUnitary.pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp2)) hout

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R
