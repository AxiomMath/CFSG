module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Setup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (isSolvable_of_isCoatom_normalizer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.AGLEmbedding.KFactProofs.L28Local

theorem kf7_l28_case {X : Type} [Group X] [Finite X] {K N : Subgroup X} [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    (e : ↥K ≃* CFSG.Quasithin.F6.L28Res.G8)
    (T : Sylow 3 ↥K)
    (hN : IsStronglyPEmbedded 3 N)
    (hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K)
    (hne : N.subgroupOf K ≠ ⊤) : Group.IsSolvable ↥N := by
  have hdata : L28Data ↥K (T : Subgroup ↥K) := l28Data_of_equiv e T
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by
    have hneT : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≠ ⊤ := by
      intro htop
      exact hne (top_le_iff.mp (htop ▸ hle))
    refine ⟨hneT, ?_⟩
    intro Y hY
    rcases hdata.maximal hY.le with h | h
    · exact absurd h.symm (ne_of_lt hY)
    · exact h
  have hsol : Group.IsSolvable (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    hdata.isSolvable_normalizer
  have hout : Group.IsSolvable (Outer ↥K) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hAut : Nat.card (MulAut ↥K) = 1512 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact CFSG.Quasithin.F6.L28Res.card_mulAut
    have hKcard : Nat.card ↥K = 504 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.F6.L28Res.card_G8]
    have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := hdata.conj_injective
    have hinner : Nat.card (inner ↥K) = 504 := by
      rw [← hKcard]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hdec := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner ↥K)
    have h3 : Nat.card (Outer ↥K) = 3 := by
      change Nat.card (MulAut ↥K ⧸ inner ↥K) = 3
      rw [hAut, hinner] at hdec
      omega
    haveI : IsCyclic (Outer ↥K) := isCyclic_of_prime_card h3
    letI : CommGroup (Outer ↥K) := IsCyclic.commGroup
    exact Group.isSolvable_of_comm fun a b => mul_comm a b
  exact isSolvable_of_isCoatom_normalizer hKC hout hmax hsol hle hne

@[expose] def KF7ReeTypeOneRecognition : Prop :=
  ∀ {X : Type} [Group X] [Finite X], CFSG.pPrimeCore 3 X = ⊥ →
    ∀ {L N : Subgroup X}, L.Normal → genFittingFStar X ≤ L → F07.IsReeType ↥L 1 →
      IsStronglyPEmbedded 3 N → Nonempty (↥(genFittingFStar X) ≃* CFSG.Quasithin.F6.L28Res.G8)

theorem kf7_reeType_one_of_recognition (hRec : KF7ReeTypeOneRecognition) :
    ∀ {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 3 X = ⊥) {L N : Subgroup X},
      L.Normal → genFittingFStar X ≤ L → F07.IsReeType ↥L 1 →
        IsStronglyPEmbedded 3 N → Group.IsSolvable ↥N := by
  intro X _ _ hO L N hLN hKL hshape hN
  obtain ⟨-, -, hKn, hKC, ⟨_, T, _, _, _, hle, hne⟩⟩ :=
    kf7_setup (p := 3) (by norm_num) (by norm_num) hO hLN hKL hN
  haveI : (genFittingFStar X).Normal := hKn
  obtain ⟨e⟩ := hRec hO hLN hKL hshape hN
  exact kf7_l28_case (K := genFittingFStar X) (N := N) hKC e T hN hle hne

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
