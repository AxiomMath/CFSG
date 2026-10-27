module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthAInf
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

theorem ggOrth_caseA5
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) (hd : Module.finrank (ZMod 3) V = 5)
    (hA5 : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs)) : False := by
  obtain ⟨c₁, c₂, y, K, hc12, hc10, hc20, hnbr, hreflL, hreflK, hKweyl, hKneG2, hJK, hJL,
    hnLK, hnKL, hsup, htype⟩ := S.exists_nbr hL hP hPump hFix
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hALcard : Nat.card ↥(ggAutomizer L Bs) = 720 := by
    have h := ggWeylOfType_A_card hA5
    norm_num at h
    exact h
  have hdvd1 : 720 ∣ Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    rw [← hALcard]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∣ 103680 := by
    have h1 : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∣
        Nat.card ↥(ggAInf 3 B Bs x L D J) := Subgroup.card_dvd_of_le hsup
    rw [S.card_ggAInf, card_orthogonalGroup_of_finrank_eq_five Q S.nondeg hd] at h1
    exact h1
  have hN : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 12 ∨
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 1152 ∨
      ∃ n : ℕ, 2 ≤ n ∧
        Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 2 ^ n * n.factorial :=
    card_of_nonSimplyLaced htype
  exact (orth_order_arith _ hN).2.1 hdvd1 hdvd2

end CFSG.StandardType.OrthF3

end
