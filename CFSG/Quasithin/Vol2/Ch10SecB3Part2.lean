module

public import CFSG.Quasithin.Vol2.Ch10SecB3Five
public import CFSG.Quasithin.Vol2.Ch10SecB3SixZ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem trivOnV_of_trivOnU (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (h : ∀ p : ℕ, p.Prime → p ≠ 2 → TrivOnU T L I p) (H : Subgroup G) :
    TrivOnV T L I H := by
  intro p hp hp2 hpL A hA _ hAp
  exact commutator_fsuVM_eq_bot_of_U h37 h38 hyp
    (fun _ hA' hA'p => commutator_fsuUL_eq_bot_of hyp hp hp2 hpL (h p hp hp2) hA' hA'p) hA hAp

theorem trivOnV_of_cases
    (hF1 : FactCommNatSL) (hF2 : FactCommAlt5) (hF3 : FactCommOrth)
    (hF4 : FactCommSz) (hF5 : FactCommL3Pair) (hF6 : FactCommGL4) (h1011 : Stmt10_1_1)
    (h1022 : Stmt10_2_2) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4) (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) : TrivOnV T L I H := by
  obtain ⟨-, -, -, hcases⟩ := h1011 G T L I hyp
  rcases hcases with ⟨n, h1⟩ | h2 | h3 | ⟨n, h4⟩ | h5 | h6 | h7
  · exact trivOnV_of_trivOnU h37 h38 hyp (fun p hp hp2 => trivOnU_of_one hF1 h1 hp hp2) H
  · exact trivOnV_of_trivOnU h37 h38 hyp (fun p hp hp2 => trivOnU_of_two hF2 h2 hp hp2) H
  · exact trivOnV_of_trivOnU h37 h38 hyp (fun p hp hp2 => trivOnU_of_three hF1 h3 hp hp2) H
  · exact trivOnV_of_trivOnU h37 h38 hyp (fun p hp hp2 => trivOnU_of_four hF3 h4 hp hp2) H
  · exact trivOnV_of_five hF5 h37 h38 h322 hyp h5 H
  · exact trivOnV_of_six hF6 h1022 h37 h38 h322 h154 h331 hyp h6 hH
  · exact trivOnV_of_trivOnU h37 h38 hyp (fun p hp hp2 => trivOnU_of_seven hF4 h7 hp hp2) H

theorem stmt10_2_3_two
    (hF1 : FactCommNatSL) (hF2 : FactCommAlt5) (hF3 : FactCommOrth)
    (hF4 : FactCommSz) (hF5 : FactCommL3Pair) (hF6 : FactCommGL4)
    (hDHB : Ch11.SecB.DerivedHallBorel) (h4413 : TmpL6_4_4_13) (h443 : Stmt4_4_3')
    (h3228 : TmpL6_3_2_2_eight) (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (h1013 : Stmt10_1_3) (h1022 : Stmt10_2_2) :
    ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
        ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
          ∀ b ∈ B, (∀ l ∈ fsuL0 T L,
            b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) → b = 1 := by
  intro G _ _ T L I hyp H hH hn B hB b hb hbc
  exact hall_faithful_of hDHB h4413 h443 h3228 h331 h37 h38 h1013 hyp hH hn
    (trivOnV_of_cases hF1 hF2 hF3 hF4 hF5 hF6 h1011 h1022 h37 h38 h322 h154 h331 hyp hH) hB hb
    hbc

end CFSG.Quasithin.Vol2.Ch10.SecB
