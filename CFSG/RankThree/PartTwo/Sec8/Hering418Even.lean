module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Lin
public import CFSG.RankThree.PartTwo.Sec8.Hering418L2
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Two


@[expose] def IsLTwoTwoGe (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ Nonempty (X ≃* projSL 2 (GaloisField 2 k))

theorem kF418ModelOn_L2Two : KF418ModelOn (fun X _ => IsLTwoTwoGe X) := by
  refine kF418ModelOn_of_bound ?_
  intro X _ _ ⟨k, hk, ⟨φ⟩⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 k with hF
  have hFcard : Nat.card F = 2 ^ k := GaloisField.card 2 k (by omega)
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  let ψ : X ≃* PSL2 F := φ.trans (Sec4.projSLEquivPSLn 2 F)
  refine ⟨⊤, le_top, fun σ _ => Subgroup.mem_top σ, ?_⟩
  intro F' hF' _
  have hle := Sec4.Hering418L2.card_le_nine_of_mulAut_PSL2 hchar h4
    (F'.map (MulAut.congr ψ).toMonoidHom) (hF'.map _)
  rwa [Subgroup.card_map_of_injective (MulAut.congr ψ).injective] at hle

@[expose] def IsLThreeNotDvd (X : Type) [Group X] : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧ ¬ 3 ∣ k ∧ Nonempty (X ≃* projSL 3 (GaloisField 2 k))) ∨
    ∃ k : ℕ, 1 ≤ k ∧ ¬ 3 ∣ k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ k ∧
      Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)

theorem kF418ModelOn_L3Two : KF418ModelOn (fun X _ => IsLThreeNotDvd X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine kF418ModelOn_of_bound ?_
  intro X _ _ hX
  rcases hX with ⟨k, hk, h3k, ⟨φ⟩⟩ | ⟨k, hk, h3k, F, _, _, hF, ⟨φ⟩⟩
  ·
    set F := GaloisField 2 k with hFdef
    have hFcard : Nat.card F = 2 ^ k := GaloisField.card 2 k (by omega)
    have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hFcard
    let e' : X ≃* projectiveSL 3 F := φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
    refine exists_bound_of_hom (MulAut.congr e').toMonoidHom (MulAut.congr e').injective
      (linearAutGroup 3 F) ?_ ?_ ?_
    · intro x
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
      exact KFacts.innAut_le_linearAutGroup 3 F ⟨e' x, rfl⟩
    · intro σ hσ
      exact pow_three_mem_linearAutGroup Nat.prime_two hk hFcard h3k
        (α := MulAut.congr e' σ) (by rw [← map_pow, hσ, map_one])
    · intro F' hF' hFN
      have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
      rwa [inf_eq_left.mpr hFN] at this
  ·
    have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hF
    let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
    let φ' : MulAut X →* MulAut (projectiveSL 3 F) :=
      (descendAut 3 F).comp (MulAut.congr e').toMonoidHom
    have hφ' : Function.Injective φ' :=
      Sec4.descendAut_three_injective.comp (MulAut.congr e').injective
    refine exists_bound_of_hom φ' hφ' (linearAutGroup 3 F) ?_ ?_ ?_
    · intro x
      simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [KFacts.congr_mulAutConj, KFacts.descendAut_conj]
      exact KFacts.innAut_le_linearAutGroup 3 F ⟨_, rfl⟩
    · intro σ hσ
      exact pow_three_mem_linearAutGroup Nat.prime_two hk hF h3k
        (α := φ' σ) (by rw [← map_pow, hσ, map_one])
    · intro F' hF' hFN
      have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
      rwa [inf_eq_left.mpr hFN] at this

end Two

section G2


@[expose] def IsGTwoNotDvd (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, ¬ 3 ∣ f ∧ Blueprint.ChevalleyExceptionalModel X .G2 2 f

theorem kF418ModelOn_G2Two : KF418ModelOn (fun X _ => IsGTwoNotDvd X) := by
  refine kF418ModelOn_of_bound ?_
  rintro X _ _ ⟨f, h3f, hX⟩
  refine ⟨(MulAut.conj : X →* MulAut X).range, le_rfl, ?_, ?_⟩
  · intro σ hσ
    by_contra hout
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
    have hf3 : 3 ≤ 2 ^ f := hX.1.2.2.2
    have hf1 : 1 ≤ f := by
      by_contra h
      obtain rfl : f = 0 := by omega
      omega
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      by_contra h
      have hf1' : f ≤ 1 := by
        by_contra hf
        exact h (calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega))
      interval_cases f <;> omega
    have : Fintype K := Fintype.ofFinite K
    have hcharP : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
      (by rw [← Nat.card_eq_fintype_card, hK])
    have hK3 : ringChar K ≠ 3 := by
      rw [ringChar.eq K 2]
      norm_num
    have hα : (MulAut.congr e σ) ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
    have hα' : ¬ KFacts.IsInnerAut (MulAut.congr e σ) := fun h =>
      hout ((KFacts.isInnerAut_congr e σ).mp h)
    obtain ⟨τ, hτ, -⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hα hα'
    exact h3f (KFacts.eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hf1 hK hτ).1
  · intro F hF hFi
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
    have hk2 : k ≤ 2 := (Sec4.le_pRank_of_le_inner (MulEquiv.refl _) hF hFi hk).trans
      (Sec21.g2EvenThreeRankTwo X f hX)
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num

end G2

end CFSG.RankThree.PartTwo.Sec8.Hering418
