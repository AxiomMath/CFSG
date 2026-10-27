module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeC

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14

theorem type148_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (h : Type148 Y) :
    Type148 X := by
  rcases h with ⟨p, e, hp, he, hiso⟩ | ⟨p, f, hp, hp3, hf, hL⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ |
      ⟨⟨ψ⟩⟩
  · refine Or.inl ⟨p, e, hp, he, ?_⟩
    rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩
  · refine Or.inr (Or.inl ⟨p, f, hp, hp3, hf, ?_⟩)
    rcases hL with ⟨⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨φ.trans ψ⟩
    · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩
  · exact Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨φ.trans ψ⟩))))

theorem ne_three_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi X p e) : p ≠ 3 := by
  rintro rfl
  have h0 : 3 ^ e % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
  rcases h with ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega

theorem type148_of_chosen {G : Type} [Group G] {Le : Subgroup G}
    (hLe : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    Type148 (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) := by
  rcases hLe with hJ | hL | hA | hM | hM'
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))
  · exact Or.inl hL
  · exact Or.inr (Or.inr (Or.inl hA))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hM')))

theorem type148_of_kThetaC148 {G : Type} [Group G] {K Le : Subgroup G}
    (hLe : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M12))
    (h : KThetaC148 K Le) : Type148 (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', hiso, hL3⟩
  · exact type148_of_mulEquiv φ (type148_of_chosen hLe)
  · exact Or.inr (Or.inr (Or.inl ⟨φ⟩))
  · exact Or.inr (Or.inl ⟨p, f, hp, ne_three_of_isoLThreePi (Nat.mul_pos hf he') hiso, hf, hL3⟩)

theorem type148_of_point (hKHJ : Step148KThetaHJ) (hKL3 : Step148KThetaL3)
    (hKA7 : Step148KThetaA7) (hKM22 : Step148KThetaM22) (hKM12 : Step148KThetaM12)
    (hKON : Step148KThetaON) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hs : ¬ Group.IsSolvable ↥Y) (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le) :
    Type148 (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  have hdisj := hP.2.2.2.2.2.2.2.2.2
  rcases hdisj with ⟨hΩ, hLe⟩ | ⟨c', L', hc'Ω, hc'B, hL', hJ2, hcent, htc⟩
  · have hLeT := (h.chosen136.2 e hΩ Le hLe).1
    have hKΩ : KThetaC148 K Le := by
      rcases hLeT with hJ | hL | hA | hM | hM'
      · exact hKHJ G A c L h Y hY hs hYB B Q e K Le hP hΩ hLe hJ
      · exact hKL3 G A c L h Y hY hs hYB B Q e K Le hP hΩ hLe hL
      · exact hKA7 G A c L h Y hY hs hYB B Q e K Le hP hΩ hLe hA
      · exact hKM22 G A c L h Y hY hs hYB B Q e K Le hP hΩ hLe hM
      · exact hKM12 G A c L h Y hY hs hYB B Q e K Le hP hΩ hLe hM'
    exact type148_of_kThetaC148 hLeT hKΩ
  · rcases hKON G A c L h Y hY hs hYB B Q e K Le hP c' L' hc'Ω hc'B hL' hJ2 hcent htc with
      hA7 | ⟨hp7, ⟨ψ⟩⟩
    · exact Or.inr (Or.inr (Or.inl hA7))
    · exact Or.inl ⟨7, 1, hp7, le_rfl, Or.inl ⟨by norm_num, ⟨ψ⟩⟩⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
