module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsThreeDvd
public import CFSG.Quasithin.Vol2.Ch11L2Q5cNot3
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

section CertifiedSz


theorem not_classicalEvenAltG2Der_of_isSz {X : Type} [Group X] {n : ℕ}
    (h : UC22.IsSz X n) : ¬ ClassicalEvenAltG2Der X := by
  intro hc
  have hsimple : IsSimpleGroup X :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
  have h3 : ¬ 3 ∣ Nat.card X :=
    CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 h
  have hG2 : ∀ g : ℕ, ¬ IsG2 X g := by
    intro g hg
    have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 g :=
      CFSG.Blueprint.LieModel.chevalleyExceptionalModel hg (by decide)
    have hcard : Nat.card X = ordG2 (2 ^ g) := by
      simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE
    exact h3 (hcard ▸ CFSG.Quasithin.Vol2.Ch11.SecB.three_dvd_ordG2 g)
  unfold ClassicalEvenAltG2Der at hc
  rcases hc with hcl | ⟨m, hG2Der⟩
  · unfold F12.ClassicalEvenAltG2 at hcl
    rcases hcl with ⟨hq, t, m, f, ht, hLie⟩ | ⟨hq, a, hAlt⟩ | ⟨g, hg⟩
    · have hqo : CFSG.Open.IsQuasisimple X := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      obtain ⟨e⟩ := @uc22p2214_quotCenter_of_simple X _ hsimple hqo
      have hLieX : CFSG.Blueprint.LieModel X t m 2 f :=
        CFSG.Blueprint.LieModel.of_mulEquiv e.symm hLie
      have hsc : CFSG.Open.StatedClassicalModel X t m 2 f :=
        hLieX.statedClassicalModel (by
          rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [CFSG.Blueprint.classicalTags])
      have hord := CFSG.Timmesfeld.card_statedClassicalModel_two hsc
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · have hm : 2 ≤ m := hsc.1.2.2.1
        exact h3 ((hord.1 rfl) ▸
          CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordA (by omega))
      · have hm : 3 ≤ m := hsc.1.2.2.1
        exact h3 ((hord.2.1 rfl) ▸
          CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordTwistedA (by omega))
      · have hm : 2 ≤ m := hsc.1.2.2.1
        exact h3 ((hord.2.2.1 rfl) ▸
          CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordBC (by omega))
      · have hm : 4 ≤ m := hsc.1.2.2
        exact h3 ((hord.2.2.2.1 rfl) ▸
          CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordD (by omega))
      · have hm : 4 ≤ m := hsc.1.2.2
        exact h3 ((hord.2.2.2.2 rfl) ▸
          CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordTwistedD (by omega))
    · have hqo : CFSG.Open.IsQuasisimple X := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      obtain ⟨e⟩ := @uc22p2214_quotCenter_of_simple X _ hsimple hqo
      obtain ⟨φ⟩ := hAlt
      have hcardAlt : Nat.card X = Nat.card (alternatingGroup (Fin a)) :=
        Nat.card_congr (e.trans φ).toEquiv
      by_cases ha : 3 ≤ a
      · have hnt : Nontrivial (Fin a) := Fin.nontrivial_iff_two_le.2 (by omega)
        rw [@nat_card_alternatingGroup (Fin a) _ _ hnt, Nat.card_fin] at hcardAlt
        apply h3
        rw [hcardAlt]
        exact Nat.dvd_div_of_mul_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
          (Nat.dvd_factorial (by norm_num) (by omega)) (Nat.dvd_factorial (by norm_num) ha))
      · have h1 : Nat.card (alternatingGroup (Fin a)) = 1 := by
          interval_cases a <;> rw [Nat.card_eq_fintype_card] <;> decide
        rw [h1] at hcardAlt
        have hsub : Subsingleton X := (Nat.card_eq_one_iff_unique.1 hcardAlt).1
        exact @not_subsingleton X hsimple.toNontrivial hsub
    · exact hG2 g hg
  · rcases hG2Der with ⟨-, hLie⟩ | ⟨-, hg⟩
    · exact h3 (by rw [CFSG.Blueprint.LieModel.card_psu_three_three hLie]; norm_num)
    · exact hG2 m hg

end CertifiedSz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
