module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KFix
public import CFSG.RankThree.PartTwo.Sec12.Hering129LD4
public import CFSG.RankThree.PartTwo.Sec12.Hering129KModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Models


theorem exists_threeLocalModel {X : Type} [Group X] [Finite X] {r : TauCeti.PrimePower}
    {δ : ℕ} (hX : IsG2D4 X r δ) (h4 : 4 ≤ r.card) (hp3 : r.p ≠ 3) (hδ3 : δ = 3 → r.p = 2) :
    ∃ S M : Subgroup X, ThreeLocalModel X r (r.card ^ δ) S M := by
  rcases hX with ⟨rfl, hX1⟩ | ⟨rfl, hr, ⟨f⟩⟩
  · obtain ⟨K, hKf, hKfin, hK, hKp, ⟨e⟩⟩ := Hering129KModels.exists_adjoint_model hX1
    haveI : Finite (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := Finite.of_equiv X e.toEquiv
    have hK3 : ringChar K ≠ 3 := by rw [hKp]; exact hp3
    have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact h4
    have hM := g2_threeLocalModel r hK hK3 hK4
    rw [pow_one]
    exact ⟨_, _, hM.map e.symm⟩
  · have hp2 := hδ3 rfl
    obtain ⟨K, hKf, hKfin, σ, hK, hσ, ⟨e⟩⟩ := Hering129KModels.exists_d4_model f
    have hr2 : r.card = 2 ^ r.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
    have hn : 2 ≤ r.exponent := by
      by_contra hlt
      have h1 : r.exponent = 1 := by
        have := r.exponent_pos
        omega
      rw [h1] at hr2
      omega
    have P : Sec19.D4Par r.exponent K σ :=
      ⟨r.exponent_pos, by rw [hK, hr2], fun c => by rw [hσ c, hr2]⟩
    haveI : Finite (Sec19.C0 σ) := Finite.of_equiv X e.toEquiv
    exact ⟨_, _, (d4_threeLocalModel P hn r hr2).map e.symm⟩

theorem ks129ThreeLocalFix_holds : KS129ThreeLocalFix := by
  intro X _ _ r δ hX h4 hp3 hδ3
  obtain ⟨S, M, hM⟩ := exists_threeLocalModel hX h4 hp3 hδ3
  exact ⟨fun z hz => hM.clause_zero hz, fun z hz t ht hzt => hM.clause_a hz ht hzt,
    fun z hz t ht ht3 htz => hM.clause_c hz ht ht3 htz,
    fun t ht => ⟨fun g hg hg3 => hM.clause_d1 ht hg hg3,
      fun z hz hzt => hM.clause_d2 hz ht hzt⟩⟩

end Models

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
