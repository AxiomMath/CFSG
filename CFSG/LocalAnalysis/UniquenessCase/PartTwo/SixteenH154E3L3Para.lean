module

import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Mat
import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1L3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup Matrix

private theorem s16h_e3_l3_orders9 : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 4 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 7 = 1 := by
  decide

private theorem s16h_e3_l3_mat_orders (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : M.det = 1) : M ^ 4 = 1 ∨ M ^ 3 = 1 ∨ M ^ 7 = 1 := by
  have := s16h_e3_l3_orders9 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2)
    (M 2 0) (M 2 1) (M 2 2)
  rw [← Matrix.eta_fin_three M] at this
  exact this h

private theorem s16h_e3_l3_orders (g : SL3F2) :
    g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  have h := s16h_e3_l3_mat_orders (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) g.property
  rcases h with h | h | h
  · exact Or.inl (Subtype.ext (by simpa using h))
  · exact Or.inr (Or.inl (Subtype.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Subtype.ext (by simpa using h)))

private theorem s16h_e3_l3_pow_twelve_of_card {P : Subgroup SL3F2} (hP : Nat.card P = 24)
    (q : P) : q ^ 12 = 1 := by
  rcases s16h_e3_l3_orders (q : SL3F2) with h4 | h3 | h7
  · have h4' : q ^ 4 = 1 := Subtype.ext (by simpa using h4)
    calc q ^ 12 = (q ^ 4) ^ 3 := by rw [show (12 : ℕ) = 4 * 3 by norm_num, pow_mul]
      _ = 1 := by rw [h4', one_pow]
  · have h3' : q ^ 3 = 1 := Subtype.ext (by simpa using h3)
    calc q ^ 12 = (q ^ 3) ^ 4 := by rw [show (12 : ℕ) = 3 * 4 by norm_num, pow_mul]
      _ = 1 := by rw [h3', one_pow]
  · have h7' : q ^ 7 = 1 := Subtype.ext (by simpa using h7)
    have h24 : q ^ 24 = 1 := by
      simpa [hP] using pow_card_eq_one' (x := q)
    have hdvd : orderOf q ∣ Nat.gcd 7 24 :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h7') (orderOf_dvd_iff_pow_eq_one.mpr h24)
    have h1 : q = 1 := orderOf_eq_one_iff.mp (by
      rw [show Nat.gcd 7 24 = 1 by norm_num, Nat.dvd_one] at hdvd
      exact hdvd)
    rw [h1, one_pow]

theorem s16h_e3_l3_parabolic_of_sylow {X : Type} [Group X] [Finite X] (hX : IsSLn X 3 1)
    {S : Subgroup X} (hS : IsPGroup 2 S) (hS8 : Nat.card S = 8) :
    ∃ P : Subgroup X, Subgroup.normalizer (S : Set X) ≤ P ∧ Nat.card P = 24 ∧
      ∀ p ∈ P, p ^ 12 = 1 := by
  classical
  obtain ⟨K, hfield, hfin, hcard, ⟨eX⟩⟩ := hX
  letI : Field K := hfield
  letI : Finite K := hfin
  haveI : Fintype K := Fintype.ofFinite K
  have hKcard : Nat.card K = 2 := by simpa using hcard
  have hKf : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ZMod.card]
    exact hKcard
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hKf
  let e0 : SpecialLinearGroup (Fin 3) K ≃* StatedSL 3 K :=
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (StatedAPI.statedSL_eq_range_toGL 3 K).symm)
  let e : X ≃* SL3F2 := eX.trans (e0.symm.trans (slMulEquivOfRingEquiv ε 3))
  let S' : Subgroup SL3F2 := S.map e.toMonoidHom
  have hS'card : Nat.card S' = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, hS8]
  have hSLcard : Nat.card SL3F2 = 168 := by
    simpa only [SL3F2] using CFSG.Quasithin.H13.L829N.s9_card_SL3_F2
  have hS'p : IsPGroup 2 S' := IsPGroup.map hS e.toMonoidHom
  have hS'syl : CFSG.QuasithinUnique.IsSylowTwoOf S' ⊤ := by
    refine ⟨le_top, hS'p, ?_⟩
    rw [show (S'.subgroupOf ⊤).index = S'.index from Subgroup.relIndex_top_right S']
    have h := Subgroup.index_mul_card (H := S')
    rw [hS'card, hSLcard] at h
    omega
  obtain ⟨P', hP'max, hP'norm⟩ := CFSG.Quasithin.H13.L829N.s9_exists_parabolic S' hS'syl
  have hP'card : Nat.card P' = 24 :=
    CFSG.Quasithin.S15223P4.D1.card_maxParabolic hP'max
  have hnormP' : Subgroup.normalizer (S' : Set SL3F2) ≤ P' := by
    simpa using hP'norm
  refine ⟨P'.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨e x, ?_, by simp⟩
    have hxn : e x ∈ Subgroup.normalizer (S' : Set SL3F2) := by
      rw [← Subgroup.map_equiv_normalizer_eq S e]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact hnormP' hxn
  · rw [Subgroup.card_map_of_injective e.symm.injective, hP'card]
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    have hq12 : q ^ 12 = 1 := by
      have h := s16h_e3_l3_pow_twelve_of_card hP'card ⟨q, hq⟩
      simpa using congrArg (fun x : P' => (x : SL3F2)) h
    rw [← map_pow, hq12, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
