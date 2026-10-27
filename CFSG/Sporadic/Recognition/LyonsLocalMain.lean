module

public import CFSG.Sporadic.Recognition.LyonsLocalCentralizerA3
public import CFSG.Sporadic.Recognition.LyonsLocalMcLPair

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

section Pair

theorem PairCentralizer162.of_mcl_checks (hrows : McLAS.ThreeFacts)
    (hpair : McLAS.pairCheck = true)
    {K : Type*} [Group K] (e : K ≃* CFSG.Blueprint.NativeSporadic.McL) :
    PairCentralizer162 K := by
  intro a b ha3 hb3 ha hb hab hnot
  exact McLAS.pair_card_of_equiv hrows hpair (e.trans mclPermEquiv) ha3 hb3 ha hb hab hnot

end Pair

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(Subgroup.centralizer ({t} : Set G)) →* Equiv.Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(Subgroup.centralizer ({t} : Set G))}

namespace LyData

theorem exists_sylowQ3_of_checks (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hrows : McLAS.ThreeFacts) (hpair : McLAS.pairCheck = true) :
    ∃ A : Subgroup G, SylowQ3 (x₁ : G) (x₂ : G) (x₃ : G) t A := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  exact D.exists_sylowQ3 S (PairCentralizer162.of_mcl_checks hrows hpair e)

theorem card_normalizer_A3_of_checks (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hrows : McLAS.ThreeFacts) (hpair : McLAS.pairCheck = true) :
    Nat.card ↥(Subgroup.normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)) = 23328 := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  exact D.card_normalizer_A3' S (PairCentralizer162.of_mcl_checks hrows hpair e)

end LyData

end Cert

end CFSG.Sporadic.Recognition.LyonsSims
