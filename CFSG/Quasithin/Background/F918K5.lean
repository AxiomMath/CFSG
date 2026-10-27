module

public import CFSG.Quasithin.Background.F918K0
public import CFSG.Quasithin.Background.F918K2
public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Walter.Cited.CentralSplit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

private theorem isShapeGroup_of_mulEquiv_psl_two {X : Type} [Group X] {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) : Vol2.Ch10.SecA.IsShapeGroup X := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := n)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    H13.center_sl_eq_bot fun r hr => by
      have h1 : (r - 1) ^ 2 = 0 := by
        rw [sub_sq, hr, mul_one, two_mul, CharTwo.add_self_eq_zero, sub_zero, one_pow,
          CharTwo.add_self_eq_zero]
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)
  exact Or.inl ⟨n, hn, K, inferInstance, inferInstance, hK,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

private theorem isShapeGroup_of_isPSL_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    Vol2.Ch10.SecA.IsShapeGroup X := by
  obtain ⟨⟨-, hf, -, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn : 2 ≤ n := by
    by_contra hlt
    exact h22 (by simp [show n = 1 by omega])
  have e' : X ≃* StatedProj (StatedSL 2 K) := e
  exact isShapeGroup_of_mulEquiv_psl_two hn hK
    (e'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)

private theorem isShapeGroup_of_isPSL_two_five {X : Type} [Group X]
    (h : IsPSL 2 5 1 X) : Vol2.Ch10.SecA.IsShapeGroup X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* StatedProj (StatedSL 2 K) := e
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr (by rw [hK]; norm_num))
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨e4⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := alternatingGroup (Fin 5)) h60
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isShapeGroup_of_mulEquiv_psl_two (K := GaloisField 2 2) le_rfl
    (by rw [GaloisField.card 2 2 (by norm_num)]) ((e'.trans e5).trans e4)

private theorem isShapeGroup_of_isPSL_two_seven {X : Type} [Group X]
    (h : IsPSL 2 7 1 X) : Vol2.Ch10.SecA.IsShapeGroup X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* StatedProj (StatedSL 2 K) := e
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let f₁ : StatedProj (StatedSL 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  exact Or.inr (Or.inr ⟨(((e'.trans f₁).trans e₄.symm).trans e₃.symm)⟩)

private theorem exists_mul_ne_of_isSimpleGroup_of_not_prime {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => hc a b }
  exact hp IsSimpleGroup.prime_card

private theorem not_prime_ordA_one {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ (ordA 1 p).Prime := by
  intro hN
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2 := H13.VolI.two_mul_ordA_one_of_odd hodd
  have hdvd : p ∣ ordA 1 p := by
    rcases (Nat.Prime.dvd_mul hp).mp (⟨p ^ 2 - 1, h2⟩ : p ∣ 2 * ordA 1 p) with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · exact h
  have hpN : p = ordA 1 p := (Nat.prime_dvd_prime_iff_eq hp hN).mp hdvd
  rw [← hpN] at h2
  have h3 : 2 = p ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
  have h4 : 11 * 11 ≤ p * p := Nat.mul_le_mul hp11 hp11
  have h5 : p ^ 2 = p * p := sq p
  omega

theorem nsGroup_of_a38Types
    {X : Type} [Group X] (hA : A38Types X) (hns : ¬ Vol2.Ch10.SecA.IsShapeGroup X) : NSGroup X := by
  have hs : IsSimpleGroup X := H13.VolI.isSimpleGroup_of_a38Types hA
  rcases hA with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hpsl⟩
  · exact absurd (isShapeGroup_of_isPSL_two_two hn) hns
  · exact absurd (Or.inr (Or.inl ⟨n, hn⟩)) hns
  · have hcard : Nat.card X = 175560 := by
      obtain ⟨e⟩ := hJ
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    have hnc := exists_mul_ne_of_isSimpleGroup_of_not_prime hs (by rw [hcard]; norm_num)
    exact ⟨hs, hnc, Or.inl hcard, fun E hc hsq => card_le_eight_of_isSporadic_J1 hJ E hc hsq⟩
  · have h11 : 11 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p
      · norm_num at hp
      · exact hns (isShapeGroup_of_isPSL_two_five hpsl)
      · norm_num at hp
      · exact hns (isShapeGroup_of_isPSL_two_seven hpsl)
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
    have hcard : Nat.card X = ordA 1 p := by
      have h := CFSG.GH74.card_of_lieModel_PSL (by norm_num) (Or.inl ⟨by decide, hpsl⟩)
      simpa using h
    have hnc := exists_mul_ne_of_isSimpleGroup_of_not_prime hs
      (by rw [hcard]; exact not_prime_ordA_one hp h11)
    refine ⟨hs, hnc, Or.inr ⟨p, hp, h11, hcard⟩, fun E hc hsq => ?_⟩
    exact (card_le_four_of_isPSL_two hp (by omega) hpsl E hc hsq).trans (by norm_num)

end CFSG.Quasithin
