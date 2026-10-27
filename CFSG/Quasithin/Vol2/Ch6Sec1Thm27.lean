module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem26
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Comp
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch6Skeleton

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem stmt6_1_27_of'
    (h616 : ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ),
      Hyp611 G T M L V n →
        T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ IsNatModCh5 L ⁅V, L⁆ n)
    (h6115 : Stmt6_1_15)
    (hno : ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ),
      Hyp6116 G T M L V n → False) : Stmt6_1_27 := by
  intro G _ _ T M L V n h
  obtain ⟨hCT, hnat⟩ := h616 G T M L V n h
  have hN := h.toNat hnat
  have hZS : Subgroup.centralizer (ch6ZS T L ⁅V, L⁆ : Set G) ≤ M := by
    by_contra hcon
    exact hno G T M L ⁅V, L⁆ n ⟨hN, hcon⟩
  rcases h6115 G T M L ⁅V, L⁆ n hN with hcon | ⟨rfl, h4⟩
  · exact absurd hZS hcon
  · exact ⟨rfl, ⟨hnat, hCT⟩, hZS, h4⟩

theorem stmt6_1_27_of_inputs
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h512 : Stmt5_1_2) (hE63 : Ch6InE63) (hE612 : Ch6InE612) (h614 : Stmt6_1_4)
    (h615 : Stmt6_1_5) (h6119 : Stmt6_1_19) (h6125 : Stmt6_1_25) : Stmt6_1_27 := by
  have h6110 := stmt6_1_10 h311 h432 hE63
  have h6111 := stmt6_1_11 h432 h6110
  have h6115 := stmt6_1_15 h432 h6110 h6111 (stmt6_1_12 h331 h6110)
    (stmt6_1_13 h432 h6110 hE612)
    (stmt6_1_14 h432 h6110 Vol2Native.a37ForSQTKCat_proved Vol2Native.a39ForSQTKCat_proved)
  have h6126 := stmt6_1_26 h331 h432 h615 h6110 h6111 h6119 h6125
  have hK := existsComponent6_1_25_of h432 h6110 h6111 h6119
  refine stmt6_1_27_of' (fun G _ _ T M L V n h => ?_) h6115 fun _ _ _ _ _ _ _ _ h =>
    h.false_of_lemma_6_1_25 h432 h6110 h6111 h6119 h6125 h6126 hK
  obtain ⟨⟨-, hCT⟩, hnat, -⟩ := h.lemma_6_1_6_one_two h331 h432 h512 h614 h615
  exact ⟨hCT, hnat⟩

end CFSG.Quasithin.H13
