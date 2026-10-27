module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLM12
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC
public import CFSG.RankThree.PartTwo.Sec12.Item125Diag
public import CFSG.RankThree.PartTwo.Sec12.Item125TC

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)

@[expose] def KS128NotHJFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A → a ∉ Sec4.thetaQuotCentralizer L →
    ∀ K ∈ lA422 A a, c ∈ K →
      ¬ (Sec8.IsZ3PGLThreePi (lBarA a K A) ∧
          Nonempty (Sec4.autIn K A ≃* Multiplicative (ZMod 3)) ∧
          ∃ x ∈ A, x ≠ 1 ∧ Sec4.InducesTypeOn K x 3) ∧
      ¬ (Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
          Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3)))

section Unconditional

theorem item125DiagTC_closed
    : Item125DiagTC :=
  fun _ _ _ _ _ _ h hTC _ hE hEL hcE hEC hEL3 hexp =>
    Item125Diag.normalizer_le_of_tc Sec4.rank3II_4_5 h hTC
      (Item125Diag.diagHyp_of h (Or.inr hTC) hE hEL hcE hEC hEL3 hexp)

theorem item125BarTC_closed
    : Item125BarTC :=
  item125BarTC_of_item125DiagTC item125DiagTC_closed

theorem ks128NotHJFree_of_named
    (hAL : KS128SLAInL) (hM : KS128TypeCMove) : KS128NotHJFree := by
  intro G _ _ A c L h hAE hty a ha haB K hK hcK
  rcases hty with hSL | hTC
  · refine ⟨fun hpgl => ?_, fun hm12 => ?_⟩
    · have haL := hAL G A c L h hAE hSL a ha haB K hK hcK (Or.inl hpgl)
      obtain ⟨-, -, x, hxA, -, hx⟩ := hpgl
      exact KS128NotHJSL.false_of_pgl Sec4.rank3II_4_5 KFacts.ks12NormalizerMoves
        gap125NonCentralBar hM h hAE hSL ha haB haL hK hcK hxA hx
    · have haL := hAL G A c L h hAE hSL a ha haB K hK hcK (Or.inr hm12)
      obtain ⟨⟨φ⟩, -⟩ := hm12
      exact KS128NotHJSL.false_of_m12 Sec4.rank3II_4_5 KFacts.ks12NormalizerMoves
        gap125NonCentralBar hM h hAE hSL ha haB haL hK hcK φ
  · exact ks128NotHJTC item125BarTC_closed G A c L h hAE hTC a ha haB K hK hcK

end Unconditional

end CFSG.RankThree.PartTwo.Sec12
