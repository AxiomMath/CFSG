module

public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGOmegaFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LieType.Universal.Spin

private abbrev s1614_pl_Vec := Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2

private def s1614_pl_v (x1 x2 y1 y2 u vv : ZMod 2) : s1614_pl_Vec :=
  Sum.elim ![x1, x2] (Sum.elim ![y1, y2] ![u, vv])

private def s1614_pl_fA : Fin 8 → s1614_pl_Vec :=
  ![s1614_pl_v 0 0 0 0 0 1, s1614_pl_v 0 0 0 1 0 1, s1614_pl_v 0 0 0 1 1 0,
    s1614_pl_v 0 0 0 1 1 1, s1614_pl_v 0 1 0 0 0 1, s1614_pl_v 0 1 0 0 1 0,
    s1614_pl_v 0 1 0 0 1 1, s1614_pl_v 0 1 0 1 0 0]

private def s1614_pl_fA' : Fin 8 → s1614_pl_Vec :=
  ![s1614_pl_v 0 0 0 0 1 0, s1614_pl_v 0 0 1 0 1 0, s1614_pl_v 0 0 1 0 1 1,
    s1614_pl_v 0 0 1 0 0 1, s1614_pl_v 1 0 0 0 1 0, s1614_pl_v 1 0 0 0 1 1,
    s1614_pl_v 1 0 0 0 0 1, s1614_pl_v 1 0 1 1 0 0]

private def s1614_pl_fX : Fin 8 → s1614_pl_Vec :=
  ![s1614_pl_v 0 1 0 1 0 0, s1614_pl_v 0 1 0 0 1 0, s1614_pl_v 0 1 0 0 1 1,
    s1614_pl_v 0 1 0 0 0 1, s1614_pl_v 0 0 0 1 1 0, s1614_pl_v 0 0 0 1 1 1,
    s1614_pl_v 0 0 0 1 0 1, s1614_pl_v 0 0 0 0 0 1]

private def s1614_pl_fX' : Fin 8 → s1614_pl_Vec :=
  ![s1614_pl_v 1 0 1 1 0 0, s1614_pl_v 1 0 0 0 0 1, s1614_pl_v 1 0 0 0 1 0,
    s1614_pl_v 1 0 0 0 1 1, s1614_pl_v 0 0 1 0 0 1, s1614_pl_v 0 0 1 0 1 0,
    s1614_pl_v 0 0 1 0 1 1, s1614_pl_v 0 0 0 0 1 0]

private lemma s1614_pl_frame_ok :
    ∀ i, S1614OmFrame (quadMinus 3 (ZMod 2) 1 1)
      (s1614_pl_fA i) (s1614_pl_fA' i) (s1614_pl_fX i) (s1614_pl_fX' i) := by
  simp only [S1614OmFrame, quadMinus_apply, polar_quadMinus, Fin.sum_univ_two]
  decide

private lemma s1614_pl_cover :
    ∀ s : s1614_pl_Vec, s ≠ 0 →
      ∃ i, dotProduct s (s1614_pl_fA i) = 0 ∧ dotProduct s (s1614_pl_fA' i) = 0 := by
  decide

private lemma s1614_pl_zmod_two_eq_one (y : ZMod 2) (hy : y ≠ 0) : y = 1 := by
  revert y
  decide

private lemma s1614_pl_zmod_two_add_one (y : ZMod 2) : 1 + y + 1 = y := by
  revert y
  decide

variable {K : Type} [Field K]

private def s1614_pl_map (K : Type) [Field K] (φ : ZMod 2 →+* K) (w : s1614_pl_Vec) :
    Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K := fun i => φ (w i)

private lemma s1614_pl_map_sub_three (φ : ZMod 2 →+* K) (A B C : ZMod 2) :
    φ A - φ B - φ C = φ (A - B - C) := by
  rw [RingHom.map_sub, RingHom.map_sub]

private lemma s1614_pl_Q (φ : ZMod 2 →+* K) (w : s1614_pl_Vec) :
    quadMinus 3 K 1 1 (s1614_pl_map K φ w) = φ (quadMinus 3 (ZMod 2) 1 1 w) := by
  simp only [s1614_pl_map, quadMinus_apply, map_add, map_mul, map_pow, map_sum,
    map_one, map_ofNat]

private lemma s1614_pl_polar (φ : ZMod 2 →+* K) (w w' : s1614_pl_Vec) :
    QuadraticMap.polar (quadMinus 3 K 1 1) (s1614_pl_map K φ w) (s1614_pl_map K φ w') =
      φ (QuadraticMap.polar (quadMinus 3 (ZMod 2) 1 1) w w') := by
  simp only [QuadraticMap.polar]
  have hsum : (s1614_pl_map K φ w) + (s1614_pl_map K φ w') = s1614_pl_map K φ (w + w') := by
    ext i
    simp [s1614_pl_map, map_add]
  rw [hsum, s1614_pl_Q, s1614_pl_Q, s1614_pl_Q]
  exact s1614_pl_map_sub_three φ _ _ _

private lemma s1614_pl_Q_eq (φ : ZMod 2 →+* K) (w : s1614_pl_Vec) {t : ZMod 2}
    (h : quadMinus 3 (ZMod 2) 1 1 w = t) :
    quadMinus 3 K 1 1 (s1614_pl_map K φ w) = φ t := by
  rw [s1614_pl_Q]
  exact congrArg φ h

private lemma s1614_pl_polar_eq (φ : ZMod 2 →+* K) (w w' : s1614_pl_Vec) {t : ZMod 2}
    (h : QuadraticMap.polar (quadMinus 3 (ZMod 2) 1 1) w w' = t) :
    QuadraticMap.polar (quadMinus 3 K 1 1) (s1614_pl_map K φ w)
      (s1614_pl_map K φ w') = φ t := by
  rw [s1614_pl_polar]
  exact congrArg φ h

private lemma s1614_pl_frame_map (φ : ZMod 2 →+* K) {a a' x x' : s1614_pl_Vec}
    (h : S1614OmFrame (quadMinus 3 (ZMod 2) 1 1) a a' x x') :
    S1614OmFrame (quadMinus 3 K 1 1) (s1614_pl_map K φ a) (s1614_pl_map K φ a')
      (s1614_pl_map K φ x) (s1614_pl_map K φ x') := by
  simp only [S1614OmFrame] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨by simpa using s1614_pl_Q_eq φ a h1,
    by simpa using s1614_pl_Q_eq φ a' h2,
    by simpa using s1614_pl_Q_eq φ x h3,
    by simpa using s1614_pl_Q_eq φ x' h4,
    by simpa using s1614_pl_polar_eq φ a a' h5,
    by simpa using s1614_pl_polar_eq φ x x' h6,
    by simpa using s1614_pl_polar_eq φ a x h7,
    by simpa using s1614_pl_polar_eq φ a x' h8,
    by simpa using s1614_pl_polar_eq φ a' x h9,
    by simpa using s1614_pl_polar_eq φ a' x' h10⟩

private lemma s1614_pl_dot (φ : ZMod 2 →+* K) (t w : s1614_pl_Vec) :
    dotProduct (s1614_pl_map K φ t) (s1614_pl_map K φ w) = φ (dotProduct t w) := by
  simp only [dotProduct, s1614_pl_map, map_sum, map_mul]

theorem s1614_om_planes (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {s : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K} (hs : s ≠ 0) :
    ∃ a a' x x' : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
      S1614OmFrame (quadMinus 3 K b c) a a' x x' ∧ dotProduct s a = 0 ∧ dotProduct s a' = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card, hK]
  haveI : CharP K 2 := charP_of_card_eq_prime hcardK
  let e : K ≃+* ZMod 2 :=
    FiniteField.ringEquivOfCardEq (by rw [hcardK, ZMod.card])
  have hc0 : c ≠ 0 := by
    intro hc0
    exact hbc 0 (by simp [hc0])
  have hc1 : e c = 1 :=
    s1614_pl_zmod_two_eq_one (e c) (by simpa using hc0)
  have hc : c = 1 := e.injective (by simpa using hc1)
  have hb1' : 1 + b + 1 ≠ 0 := by
    intro h
    exact hbc 1 (by simpa [hc] using h)
  have hb1 : e b = 1 := by
    have hne : 1 + e b + 1 ≠ 0 := by
      intro h
      apply hb1'
      apply e.injective
      simpa using h
    have hz : e b ≠ 0 := by
      simpa [s1614_pl_zmod_two_add_one] using hne
    exact s1614_pl_zmod_two_eq_one (e b) hz
  have hb : b = 1 := e.injective (by simpa using hb1)
  let φ : ZMod 2 →+* K := e.symm
  have hsZ : (e ∘ s) ≠ 0 := by
    intro h
    apply hs
    funext i
    have hi := congrFun h i
    simp only [Function.comp_apply, Pi.zero_apply] at hi
    exact e.injective (by simpa using hi)
  obtain ⟨i, hia, hia'⟩ := s1614_pl_cover (e ∘ s) hsZ
  refine ⟨s1614_pl_map K φ (s1614_pl_fA i), s1614_pl_map K φ (s1614_pl_fA' i),
    s1614_pl_map K φ (s1614_pl_fX i), s1614_pl_map K φ (s1614_pl_fX' i), ?_, ?_, ?_⟩
  · have h := s1614_pl_frame_map φ (s1614_pl_frame_ok i)
    simpa [hb, hc] using h
  · have hs_eq : s = s1614_pl_map K φ (e ∘ s) := by
      funext j
      simp [s1614_pl_map, φ]
    have h := s1614_pl_dot φ (e ∘ s) (s1614_pl_fA i)
    rw [hs_eq, h, hia, map_zero]
  · have hs_eq : s = s1614_pl_map K φ (e ∘ s) := by
      funext j
      simp [s1614_pl_map, φ]
    have h := s1614_pl_dot φ (e ∘ s) (s1614_pl_fA' i)
    rw [hs_eq, h, hia', map_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
