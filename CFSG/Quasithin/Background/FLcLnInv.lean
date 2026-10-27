module

public import CFSG.Quasithin.Background.S1549EA
public import CFSG.Quasithin.Background.FLcLn

public section

namespace CFSG.Quasithin

namespace S1549E

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lnInvariantParabolic_holds : LnInvariantParabolic := by
  intro A _ _ L X S P₀ P hiso hLX hLn hS hXLS hne hO2 hpar hP₀n hSP hPL hPn hcard
  have hXn : X ≤ Subgroup.normalizer (L : Set A) := FLc.le_normalizer_of_conj_mem hLn
  have hBL : IsSylowTwoOf (S ⊓ L) L := B6.isSylowTwoOf_inf_normal hS hLX hXn
  obtain ⟨iso⟩ := hiso
  obtain ⟨D⟩ := FLc.exists_borelIso (n := 4) (by norm_num) hBL
    (iso.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm)
  have hBN₀ : S ⊓ L ≤ Subgroup.normalizer (P₀ : Set A) :=
    inf_le_left.trans (FLc.le_normalizer_of_conj_mem' hP₀n)
  obtain ⟨hBP₀, hP₀L, hunique⟩ := FLc.minParabolic_transfer hpar hBL hBN₀
  obtain ⟨x₀, hx₀, hx₀P, hx₀u⟩ :=
    D.exists_unique_node_of_unique_max hBL.1 hBP₀ hP₀L hunique
  have hBcard : Nat.card (S ⊓ L : Subgroup A) = 64 := by
    have h1 := D.card_model (P := S ⊓ L) hBL.1
    rw [D.model_B] at h1
    rw [← h1]
    have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular (K := ZMod 2) 4
    rw [Nat.card_zmod] at this
    simpa using this
  have hmax : IsMaxSubgroupIn P (S ⊓ L) :=
    FLc.isMaxSubgroupIn_of_card hSP (by rw [hcard, hBcard])
  obtain ⟨x₁, hx₁, hx₁P, hx₁u⟩ := D.exists_unique_node_of_isMax hBL.1 hPL hmax
  obtain ⟨s, hsS, hsL⟩ : ∃ s ∈ S, s ∉ L := by
    by_contra h
    push Not at h
    have hSL : S ≤ L := h
    exact hne (le_antisymm hLX (hXLS.trans (sup_eq_left.2 hSL).le))
  have hf₁ := FLc.cutsOf_flip_invariant (n := 4) (by norm_num) D hLX hLn hS hXLS hO2 hsS hsL hSP hPn
  have hf₀ := FLc.cutsOf_flip_invariant (n := 4) (by norm_num) D hLX hLn hS hXLS hO2 hsS hsL hBP₀.le
    hP₀n
  have h₁ := FLc.two_mul_eq_of_flip (fun i hi => D.isNode_of_mem_cutsOf hi) hf₁ hx₁ hx₁P hx₁u
  have h₀ := FLc.two_mul_eq_of_flip (fun i hi => D.isNode_of_mem_cutsOf hi) hf₀ hx₀ hx₀P hx₀u
  have hxx : x₁ = x₀ := by omega
  refine D.eq_of_cutsOf_eq hBL.1 hSP hPL hBP₀.le hP₀L ?_
  refine FLc.eq_of_unique_missing (x := x₁) (fun i hi => D.isNode_of_mem_cutsOf hi)
    (fun i hi => D.isNode_of_mem_cutsOf hi) hx₁P (hxx ▸ hx₀P) hx₁u
    (fun y hy hyJ => (hx₀u y hy hyJ).trans hxx.symm)

end S1549E

end CFSG.Quasithin
