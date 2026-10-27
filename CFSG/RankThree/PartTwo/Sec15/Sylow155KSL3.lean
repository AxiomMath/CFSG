module

public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQGen
import CFSG.RankThree.PartTwo.Sec8.Item82ProofPSL3
import CFSG.RankThree.PartTwo.Sec8.Hering418Orders
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix

theorem kSL3NonPiAutThree : KSL3NonPiAutThree := by
  intro X _ n hn h E hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨⟨e⟩, hq⟩ | ⟨h2, ⟨e⟩, hq⟩
  · have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hq
    have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 n)) :=
      Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) (GaloisField 2 n) →* _)
        ProjGenLinGroup.mk_surjective
    have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
      rw [GaloisField.card 2 n hn0]
      exact hq
    have hdiv : ¬ 3 ∣ Nat.gcd 3 (2 ^ n - 1) := fun h3 => by
      have h3' : 3 ∣ 2 ^ n - 1 := h3.trans (Nat.gcd_dvd_right _ _)
      generalize 2 ^ n = x at hq h3'
      omega
    refine Sec8.Item82Proof.card_inf_inner_le_three
      (KFacts.isCyclic_sylow_three_of_mulEquiv_projSL hK e) hE.2 fun α hα => ?_
    exact Sec8.Hering418.inner_projSL (n := 3) (p := 2) (f := n)
      ⟨Nat.prime_two, Nat.one_le_iff_ne_zero.mpr hn0, by norm_num, by simp, by simp⟩ hdiv hn e
      (hE.2 α hα)
  · have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at h2
    have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
      Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) (GaloisField 2 (2 * n)) →* _)
        ProjGenLinGroup.mk_surjective
    have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    have hdiv : ¬ 3 ∣ Nat.gcd 3 (2 ^ n + 1) := fun h3 => by
      have h3' : 3 ∣ 2 ^ n + 1 := h3.trans (Nat.gcd_dvd_right _ _)
      generalize 2 ^ n = x at hq h3'
      omega
    refine Sec8.Item82Proof.card_inf_inner_le_three
      (KFacts.isCyclic_sylow_three_of_mulEquiv_projSU hn0 hq e) hE.2 fun α hα => ?_
    exact Sec8.Hering418.inner_projSU (n := 3) (p := 2) (f := n)
      ⟨Nat.prime_two, Nat.one_le_iff_ne_zero.mpr hn0, le_refl _, fun h => by
        simp only [Prod.mk.injEq, true_and] at h
        omega⟩ hdiv hn e (hE.2 α hα)

end CFSG.RankThree.PartTwo.Sec15
