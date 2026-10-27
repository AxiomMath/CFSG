module

public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (isoLThreePi_of_mulEquiv)
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem false_of_surjective_of_not_dvd [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup (X ⧸ K)] (hK : Group.IsSolvable K) {Y : Type*} [Group Y] (φ : X →* Y)
    (hφ : Function.Surjective φ) (hY1 : 1 < Nat.card Y) (hY : ¬ Nat.card (X ⧸ K) ∣ Nat.card Y) :
    False := by
  have : Finite Y := Finite.of_surjective φ hφ
  by_cases hle : φ.ker ≤ K
  · have hdvd : K.index ∣ φ.ker.index := Subgroup.index_dvd_of_le hle
    have hker : φ.ker.index = Nat.card Y := by
      rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
    rw [hker] at hdvd
    exact hY hdvd
  · have htop := Sec4.Census.eq_top_of_not_le hK hle
    have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp hY1
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hφ y
    have hx : x ∈ φ.ker := by
      rw [htop]
      exact Subgroup.mem_top x
    exact hy (MonoidHom.mem_ker.mp hx)

theorem false_of_isExtOf_of_not_dvd [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup (X ⧸ K)] (hK : Group.IsSolvable K) {M : Subgroup X} [M.Normal]
    {Y B : Type*} [Group Y] [Group B] (h : Sec4.IsExtOf (X ⧸ M) Y B) (hY1 : 1 < Nat.card Y)
    (hY : ¬ Nat.card (X ⧸ K) ∣ Nat.card Y) : False := by
  obtain ⟨M', hM', -, ⟨e⟩⟩ := h
  exact false_of_surjective_of_not_dvd hK
    (e.toMonoidHom.comp ((QuotientGroup.mk' M').comp (QuotientGroup.mk' M)))
    (e.surjective.comp ((QuotientGroup.mk'_surjective M').comp (QuotientGroup.mk'_surjective M)))
    hY1 hY

theorem reduce44_core (h44 : Sec4.Item4_4)
    (hX4 : SectionFourHyp X) [hperf : Group.IsPerfect X]
    [hsimp : IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X)]
    {E : Subgroup (X ⧸ aschbacherSolvableCore 3 X)} (hE3 : Monoid.exponent E ∣ 3)
    (hE9 : Nat.card E = 9)
    (hcard : ∀ m : ℕ, m = 60 ∨ m = 120 ∨ m = 360 ∨ m = 5616 →
      ¬ Nat.card (X ⧸ aschbacherSolvableCore 3 X) ∣ m)
    (hnq : ¬ IsQuasisimple (X ⧸ CFSG.pCore 2 X)) :
    CFSG.pCore 2 X = ⊥ ∧ CFSG.Open.pRank 2 (⊤ : Subgroup X) ≤ 2 ∧
      IsQuasisimple (X ⧸ CFSG.oddCore X) := by
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 X) := hθ.1
  have hA : ∀ n : ℕ, 5 ≤ n → n ≤ 6 →
      1 < Nat.card (alternatingGroup (Fin n)) ∧
        (Nat.card (alternatingGroup (Fin n)) = 60 ∨ Nat.card (alternatingGroup (Fin n)) = 360) := by
    intro n hn5 hn6
    rw [KFacts.KS14.card_alternatingGroup_fin (by omega)]
    interval_cases n <;> decide
  have hA5 := hA 5 le_rfl (by norm_num)
  have hA6 := hA 6 (by norm_num) le_rfl
  have hA5' : ¬ Nat.card (X ⧸ aschbacherSolvableCore 3 X) ∣
      Nat.card (alternatingGroup (Fin 5)) := by
    rcases hA5.2 with h | h <;> rw [h] <;> exact hcard _ (by simp)
  have hA6' : ¬ Nat.card (X ⧸ aschbacherSolvableCore 3 X) ∣
      Nat.card (alternatingGroup (Fin 6)) := by
    rcases hA6.2 with h | h <;> rw [h] <;> exact hcard _ (by simp)
  rcases h44 X hX4 hperf (aschbacherSolvableCore 3 X) hθs hsimp with
    h1 | he2 | ⟨p, hp, hp3, he3⟩ | (he4 | h4b) | ⟨hO2, h5⟩
  · exact absurd h1 hnq
  ·
    exfalso
    obtain ⟨e2⟩ := he2
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hc : Nat.card SL(2, ZMod 5) = 120 := by
      rw [Sec4.Census.card_SL2]
      norm_num
    exact false_of_surjective_of_not_dvd hθs (e2.toMonoidHom.comp (QuotientGroup.mk' _))
      (e2.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega)
      (by rw [hc]; exact hcard 120 (by simp))
  ·
    obtain ⟨e3⟩ := he3
    exact (false_of_oTwoP_equiv_SL2 hp hp3 e3 hE3 hE9).elim
  ·
    exfalso
    obtain ⟨e4⟩ := he4
    have hc : Nat.card (projSL 3 (GaloisField 3 1)) = 5616 := by
      rw [← Nat.card_congr Sec4.Census.sl3EquivProjSL.toEquiv, Sec4.Census.card_SL3_three]
    exact false_of_surjective_of_not_dvd hθs (e4.toMonoidHom.comp (QuotientGroup.mk' _))
      (e4.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega)
      (by rw [hc]; exact hcard 5616 (by simp))
  ·
    exact (false_of_isExtOf_of_not_dvd hθs h4b hA5.1 hA5').elim
  ·
    rcases h5 hθ.2.2.1 with ⟨hm, hO | hext⟩ | ⟨-, hext | hext | hext⟩
    · exact ⟨hO2, hm, hO⟩
    · exact (false_of_isExtOf_of_not_dvd hθs hext hA5.1 hA5').elim
    · exact (false_of_isExtOf_of_not_dvd hθs hext hA5.1 hA5').elim
    · exact (false_of_isExtOf_of_not_dvd hθs hext hA5.1 hA5').elim
    · exact (false_of_isExtOf_of_not_dvd hθs hext hA6.1 hA6').elim

theorem three_le_pRank_of_types (hK : KS135TwoRank) [Group.IsPerfect X]
    [IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X)]
    (hZbar : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥)
    (hO : IsQuasisimple (X ⧸ CFSG.oddCore X))
    (htype : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      ∃ f : ℕ, 1 ≤ f ∧ Sec4.IsoLThreePi (X ⧸ aschbacherSolvableCore 3 X) 2 f) :
    3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 X) := hθ.1
  have hOK := oddCore_le_of_isQuasisimple hθs hO
  have hZ := center_quotient_oddCore_eq_map hθs hZbar hO hOK
  let e : (X ⧸ CFSG.oddCore X) ⧸ Subgroup.center (X ⧸ CFSG.oddCore X) ≃*
      X ⧸ aschbacherSolvableCore 3 X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hOK)
  have hZ2 : IsPGroup 2 (Subgroup.center (X ⧸ CFSG.oddCore X)) :=
    Sec4.Census.isPGroup_two_center_of_oddCore_eq_bot
      (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot X)
  have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup (X ⧸ CFSG.oddCore X)) =
      CFSG.Open.pRank 2 (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_quotient_eq (CFSG.oddCore X) (fun h2 =>
      (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore X))
        (even_iff_two_dvd.mpr h2))
  rw [← hrank]
  refine hK (X ⧸ CFSG.oddCore X) hO hZ2 ?_
  rcases htype with hM | hJ | hM22 | ⟨f, hf, hL⟩
  · obtain ⟨φ⟩ := hM
    exact Or.inl ⟨e.trans φ⟩
  · obtain ⟨φ⟩ := hJ
    exact Or.inr (Or.inl ⟨e.trans φ⟩)
  · obtain ⟨φ⟩ := hM22
    exact Or.inr (Or.inr (Or.inl ⟨e.trans φ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨f, hf, isoLThreePi_of_mulEquiv e hL⟩))

end CFSG.RankThree.PartTwo.Sec13.ResProof
