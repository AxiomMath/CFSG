module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Inner
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3PGL
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSAsm

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13

variable {Γ : Type} [Group Γ] [Finite Γ] {A L : Subgroup Γ} {b : Γ}

theorem sigGenConcl_top_of_pointFacts
    (hA : Late.IsE27 A) (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hLb : L ≤ Subgroup.centralizer ({b} : Set Γ)) (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hsec : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers b : Set Γ))
    (hL : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hns : ¬ Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (hpt : L3PointFacts A L b)
    (hQ : ∃ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Y ≠ ⊥ ∧ ¬ 3 ∣ Nat.card Y ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) :
    SigGenConcl (Sec4.autThetaQuot A L)
      (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperf, hZ⟩ := isPerfect_center_of_isLThreePi hL hns
  obtain ⟨hPe, -⟩ := autThetaQuot_e9 hA hbA hb1 hAL hsec
  have hP : IsPGroup 3 (Sec4.autThetaQuot A L) := fun g =>
    ⟨1, Subtype.ext (by simpa using hPe.2 g g.2)⟩
  obtain ⟨-, hfix, hcase, -, -⟩ := hpt
  have hgen : sSup {Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card Y ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y} = ⊤ := by
    rcases hcase with ⟨hbL, h9, hQ8⟩ | ⟨-, hM⟩
    · rcases gen_or_bot_inner hA hbA hb1 hLb hbL h9 hQ8 hL hns with h | h
      · exact h
      · exfalso
        obtain ⟨Y, hY1, hY3, hYP⟩ := hQ
        exact hY1 (h Y hY3 hYP)
    · exact gen_of_pglModel hM hperf
  rw [MonoidHom.range_eq_map]
  refine sigGenConcl_of_gen hZ hP hfix (fun x hx => hx) (le_of_eq_of_le hgen.symm ?_)
  exact sSup_le_sSup fun Y hY => ⟨le_top, hY.1, fun σ hσ y hy => hY.2 σ hσ ⟨y, hy, rfl⟩⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
