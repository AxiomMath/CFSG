module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableNatRed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableAltRed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableAlt
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Adapters.RankTwoModelTransports
  CFSG.HardMathSupport.Solomon.Coordinator

private theorem s15k_tab_field_two {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ 1) :
    Nonempty (K ≃+* ZMod 2) := by
  have hK2 : Nat.card K = 2 := by simpa using hcard
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  exact ⟨(ZMod.ringEquivOfPrime K Nat.prime_two hK').symm⟩

private theorem s15k_tab_bc_eq_one {K : Type} [Field K] (e : K ≃+* ZMod 2) {b c : K}
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : e b = 1 ∧ e c = 1 := by
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e b * t + e c ≠ 0 := by
    intro t h0
    apply hpoly (e.symm t)
    apply e.injective
    simpa using h0
  have h0 := hpoly' 0
  have h1 := hpoly' 1
  generalize e b = x at h0 h1 ⊢
  generalize e c = y at h0 h1 ⊢
  revert x y
  decide

variable {V : Type} [CommGroup V] [Finite V] {K : Subgroup (MulAut V)} {Z : Subgroup V}

private theorem s15k_tab_sl {n : ℕ} (hn : 3 ≤ n) (h : BinaryNaturalSL K Z ⊥ n 1) :
    (∀ z ∈ Z, 1 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) ∧
      (5 ≤ n → ∀ z ∈ Z, 2 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) := by
  obtain ⟨F, hF, hfin, hcard, hreal⟩ := h
  obtain ⟨e⟩ := s15k_tab_field_two hcard
  have hreal' := s15k_jp_nat_transport e (glCongr_statedSL e n) hreal
  refine ⟨fun z hz => ?_, fun h5 z hz => ?_⟩
  · obtain ⟨m, hm⟩ := s15k_table_nat_red hreal' hz
    rw [mclt_statedSL_eq_top, top_inf_eq] at hm
    exact (s15k_table_sl_rank hn m).1.trans hm
  · obtain ⟨m, hm⟩ := s15k_table_nat_red hreal' hz
    rw [mclt_statedSL_eq_top, top_inf_eq] at hm
    exact ((s15k_table_sl_rank hn m).2 h5).trans hm

private theorem s15k_tab_sp {n : ℕ} (hn : 6 ≤ n) (h : NatSpn K Z ⊥ n 1) :
    ∀ z ∈ Z, 2 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z) := by
  obtain ⟨-, F, hF, hfin, hcard, hreal⟩ := h
  obtain ⟨e⟩ := s15k_tab_field_two hcard
  have hreal' := s15k_jp_nat_transport e (glCongr_statedSp e (n / 2)) hreal
  intro z hz
  obtain ⟨m, hm⟩ := s15k_table_nat_red hreal' hz
  exact (s15k_table_sp_rank (by omega) m).trans hm

private theorem s15k_tab_omplus {n : ℕ} (hn : 6 ≤ n) (h : NatOmegaPlus K Z ⊥ n 1) :
    ∀ z ∈ Z, 2 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z) := by
  obtain ⟨-, F, hF, hfin, hcard, hreal⟩ := h
  obtain ⟨e⟩ := s15k_tab_field_two hcard
  have hmap : (StatedOmega (StatedQuadPlus (n / 2) F)).map
      (glCongr (ι := Fin (n / 2) ⊕ Fin (n / 2)) e).toMonoidHom =
      StatedOmega (StatedQuadPlus (n / 2) (ZMod 2)) :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega e
      (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp e v)
  have hreal' := s15k_jp_nat_transport e hmap hreal
  intro z hz
  obtain ⟨m, hm⟩ := s15k_table_nat_red hreal' hz
  exact (s15k_table_omplus_rank (by omega) m).trans hm

private theorem s15k_tab_omminus {n : ℕ} (hn : 6 ≤ n) (h : NatOmegaMinus K Z ⊥ n 1) :
    ∀ z ∈ Z, 1 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z) ∧
      (7 ≤ n → 2 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) := by
  obtain ⟨hev, F, hF, hfin, b, c, hcard, hpoly, hreal⟩ := h
  obtain ⟨e⟩ := s15k_tab_field_two hcard
  obtain ⟨hb, hc⟩ := s15k_tab_bc_eq_one e hpoly
  have hmap : (StatedOmega (StatedQuadMinus (n / 2) F b c)).map
      (glCongr (ι := Fin (n / 2 - 1) ⊕ Fin (n / 2 - 1) ⊕ Fin 2) e).toMonoidHom =
      StatedOmega (StatedQuadMinus (n / 2) (ZMod 2) 1 1) :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega e
      (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp e hb hc v)
  have hreal' := s15k_jp_nat_transport e hmap hreal
  obtain ⟨t, ht⟩ := hev
  intro z hz
  obtain ⟨m, hm⟩ := s15k_table_nat_red hreal' hz
  obtain ⟨h1, h2⟩ := s15k_table_omminus_rank (k := n / 2) (by omega) m
  exact ⟨h1.trans hm, fun h7 => (h2 (by omega)).trans hm⟩

private theorem s15k_tab_alt {n : ℕ} (hn : 5 ≤ n) (h : AlternatingNatural K Z ⊥ n) :
    (∀ z ∈ Z, 1 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) ∧
      (8 ≤ n → ∀ z ∈ Z, 2 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) := by
  refine ⟨fun z hz => ?_, fun h8 z hz => ?_⟩
  · obtain ⟨x, hx⟩ := s15k_table_alt_red hn h hz
    exact (s15k_table_alt_rank hn x).1.trans hx
  · obtain ⟨x, hx⟩ := s15k_table_alt_red hn h hz
    exact ((s15k_table_alt_rank hn x).2 h8).trans hx

theorem rTable137_holds : RTable137 := by
  intro V _ _ _ K Z X _ hX
  suffices key : (∀ z ∈ Z, 1 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) ∧
      ((∀ z ∈ Z, 2 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) ∨
        s15ExcList X) by
    refine ⟨key.1, ?_⟩
    rintro ⟨z, hz, -, hle⟩
    rcases key.2 with hall | hexc
    · have h2 := hall z hz
      omega
    · exact hexc
  rcases hX with ⟨n, hn, hL, h⟩ | ⟨n, hn, hS, h⟩ | ⟨n, hn, hP, h⟩ | ⟨n, hn, hM, h⟩ |
    ⟨n, hn, hA, h⟩
  · obtain ⟨h1, h2⟩ := s15k_tab_sl hn h
    refine ⟨h1, ?_⟩
    by_cases h5 : 5 ≤ n
    · exact Or.inl (h2 h5)
    · right
      obtain rfl | rfl : n = 3 ∨ n = 4 := by omega
      · exact Or.inl hL
      · exact Or.inr (Or.inl hL)
  · have h2 := s15k_tab_sp hn h
    exact ⟨fun z hz => le_trans (by norm_num) (h2 z hz), Or.inl h2⟩
  · have h2 := s15k_tab_omplus hn h
    exact ⟨fun z hz => le_trans (by norm_num) (h2 z hz), Or.inl h2⟩
  · have h2 := s15k_tab_omminus hn h
    refine ⟨fun z hz => (h2 z hz).1, ?_⟩
    by_cases h7 : 7 ≤ n
    · exact Or.inl fun z hz => (h2 z hz).2 h7
    · obtain rfl : n = 6 := by omega
      right
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hM))))
  · obtain ⟨h1, h2⟩ := s15k_tab_alt hn h
    refine ⟨h1, ?_⟩
    by_cases h8 : 8 ≤ n
    · exact Or.inl (h2 h8)
    · right
      obtain rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 := by omega
      · exact Or.inr (Or.inr (Or.inl hA))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hA)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
