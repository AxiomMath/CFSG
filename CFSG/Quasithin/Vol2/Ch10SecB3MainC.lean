module

public import CFSG.Quasithin.Vol2.Ch10SecB3Part2
public import CFSG.Quasithin.Vol2.Ch10SecB3Wr3
public import CFSG.Quasithin.Vol2.Ch10SecB3Five5
public import CFSG.Quasithin.Vol2.Ch10SecB3CHall
public import CFSG.Quasithin.Vol2.Ch10SecB3Obl
public import CFSG.Quasithin.Vol2.Ch10SecB3CartanC
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem part13_of_L32C (hF3 : Fact10_2_3CartanLe)
    (hF4 : Fact10_2_3Wreath) (hDHB : Ch11.SecB.DerivedHallBorel)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (hyp : Hyp10 G T L I) (hL32 : LBarL32 L)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn : 1 < E1.nParam H)
    (hfaith : HallFaithful T L I H) :
    E1.nParam H = 2 ∧ oTwoUpper (H ⊓ fsuM T L) ≤ fsuL0 T L ∧
      (∀ K : Subgroup G, IsLi T L K →
        IsMaxSubgroupIn K ((T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L)) ⊓ K)) ∧
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) ∧ ¬ Case10_1_1Five T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, α, ψ, hC⟩ := exists_L0CoordG h37 h38 hyp hL32 ht htn
  have hTM : T ≤ fsuM T L := SecA.le_fsuM T L
  have hInM : InM T (fsuM T L) := ⟨fsuM_isMaxTwoLocal h331 hyp, hTM⟩
  obtain ⟨B, hB, -, hTB⟩ := hDHB G T (fsuM T L) H hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow hInM (normalizer_T_le h331 hyp) hH hn
  have c : Ctx3 T L I H B t Ψ α ψ :=
    ⟨h37, h38, h322, h331, h1013, hyp, hH, hfaith, hB, ht, htn, hC⟩
  obtain ⟨n, hnH, hcart⟩ := hF3 G T (fsuM T L) H hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow hInM (normalizer_T_le h331 hyp) hH hn
  obtain ⟨b₀, hb₀, hb₀o⟩ := hcart B hB
  have hn2 : 2 ≤ n := E2.E22A.two_le_of_one_lt_of_le hn hnH
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hb₀
    rw [hb₀, orderOf_one] at hb₀o
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hnH2 : E1.nParam H = 2 :=
    E2.E22A.eq_two_of_one_lt_of_le_of_eq hn hnH (c.eq_two hn2 hb₀ hb₀o)
  refine ⟨hnH2, c.oTwoUpper_le, c.isMax hB1, ?_, fun h5 => c.not_case_five hB1 h5⟩
  exact hF4 G T (fsuM T L) H B hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
    hInM (normalizer_T_le h331 hyp) hH hnH2 hB (c.card_eq_nine hB1) (c.eight_le hB1 hTB)

theorem stmt10_2_3_ofC
    (hF1 : FactCommNatSL) (hF2 : FactCommAlt5) (hF3 : FactCommOrth)
    (hF4 : FactCommSz) (hF5 : FactCommL3Pair) (hF6 : FactCommGL4) (hCart : Fact10_2_3CartanLe)
    (hWr : Fact10_2_3Wreath) (hFld : FactCommField) (hBen : FactBenderOver)
    (hObl : Obl10_2_3Case1) (hDHB : Ch11.SecB.DerivedHallBorel) (h4413 : TmpL6_4_4_13)
    (h443 : Stmt4_4_3') (h3228 : TmpL6_3_2_2_eight) (h322 : TmpL6_3_2_2_two)
    (h154 : AsB15Part4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3)
    (h1022 : Stmt10_2_2) : Stmt10_2_3 := by
  intro G _ _ T L I hyp H hH hn
  have hfaith : HallFaithful T L I H := stmt10_2_3_two hF1 hF2 hF3 hF4 hF5 hF6 hDHB h4413 h443
    h3228 h322 h154 h37 h38 h331 h1011 h1013 h1022 G T L I hyp H hH hn
  have hInM : InM T (fsuM T L) := ⟨fsuM_isMaxTwoLocal h331 hyp, SecA.le_fsuM T L⟩
  obtain ⟨B, hB, -⟩ := hDHB G T (fsuM T L) H hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow hInM (normalizer_T_le h331 hyp) hH hn
  obtain ⟨m, hmH, hcart⟩ := hCart G T (fsuM T L) H hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow hInM (normalizer_T_le h331 hyp) hH hn
  obtain ⟨b₀, hb₀, hb₀o⟩ := hcart B hB
  have hm2 : 2 ≤ m := E2.E22A.two_le_of_one_lt_of_le hn hmH
  have hm22 : m = 2 → E1.nParam H = 2 := E2.E22A.eq_two_of_one_lt_of_le_of_eq hn hmH
  have hL32 := fun h : LBarL32 L =>
    part13_of_L32C hCart hWr hDHB h37 h38 h322 h331 h1013 hyp h hH hn hfaith
  have hcomm := fun (hc : (∃ n, Case10_1_1One T L I n) ∨ (∃ n, Case10_1_1Four T L I n) ∨
      Case10_1_1Seven T L I) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) =>
    stmt10_2_3_comm hFld hBen h37 h38 h1011 h1012 h1013 h331 hyp hc hH hZH hfaith hB hm2 hb₀
      hb₀o
  have hC1 : ¬ ∃ n, Case10_1_1One T L I n := by
    rintro ⟨n, h1⟩
    by_cases hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥
    · exact (hcomm (Or.inl ⟨n, h1⟩) hZH).2.1 n h1
    · exact hObl G T L I hyp H hH hn hZH n h1
  have hm32 : LBarL32 L → E1.nParam H = 2 := fun h => (hL32 h).1
  have h123 : (∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I ∨ Case10_1_1Three T L I →
      E1.nParam H = 2 := by
    rintro (h1 | ⟨⟨e⟩, -⟩ | ⟨h3, -⟩)
    · exact absurd h1 hC1
    · exact hm22 (eq_two_of_A5 h37 h38 h322 h331 h1013 hyp e hH hfaith hB hm2 hb₀ hb₀o)
    · exact hm32 h3
  have h47 : (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Seven T L I → E1.nParam H = 2 := by
    intro h
    by_cases hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥
    · exact hm22 (hcomm (Or.inr h) hZH).1
    · exact h123 (h1022 G T L I hyp H hH hZH).1.2
  have hnH2 : E1.nParam H = 2 := by
    rcases (h1011 G T L I hyp).2.2.2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact h123 (Or.inl h1)
    · exact h123 (Or.inr (Or.inl h2))
    · exact h123 (Or.inr (Or.inr h3))
    · exact h47 (Or.inl h4)
    · exact hm32 h5.1
    · exact hm32 h6.1
    · exact h47 (Or.inr h7)
  exact ⟨hnH2, hfaith, fun h => ⟨(hL32 h).2.1, (hL32 h).2.2.1, (hL32 h).2.2.2.1⟩, hC1⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
