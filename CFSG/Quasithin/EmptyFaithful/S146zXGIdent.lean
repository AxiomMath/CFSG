module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Dihedral.Glauberman.DicksonMaxB

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
  CFSG.LocalAnalysis.ComponentInitial.LinearCover

@[expose] def ListI (p : ℕ) (X : Type) [Group X] : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ p ∣ 2 ^ m - 1 ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) ∨
    (p = 3 ∧ Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))

theorem nonempty_mulEquiv_sl_two_galoisField {X : Type} [Group X] {n : ℕ}
    (hn : StatedClassicalModel X StatedLieTag.PSL 2 2 n) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_galoisField X 2 2 n hn
  exact ⟨e.trans ((projectiveSpecialLinearEquivProjectiveSL 2 (GaloisField 2 n)).trans
    (projectiveSLTwoEquivSL (GaloisField 2 n)))⟩

theorem two_le_of_psl_two_two {X : Type} [Group X] {n : ℕ}
    (hn : StatedClassicalModel X StatedLieTag.PSL 2 2 n) : 2 ≤ n := by
  obtain ⟨⟨-, h1, -, hne, -⟩, -⟩ := hn
  by_contra hlt
  obtain rfl : n = 1 := by omega
  exact hne (by norm_num)

theorem listI_of_psl2_even {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {n : ℕ}
    (hn : StatedClassicalModel X StatedLieTag.PSL 2 2 n) (hdvd : p ∣ 2 ^ n - 1) : ListI p X := by
  have _ := hp
  obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_galoisField hn
  exact Or.inl ⟨n, two_le_of_psl_two_two hn, hdvd, ⟨e⟩⟩

theorem center_specialLinearGroup_eq_bot_of_card_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hA⟩ := hA
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by simp; omega)] at hr
    exact zero_ne_one hr
  have hunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
  have hr1 : r = 1 := by
    have := hsub.elim (Units.mk0 r hr0) 1
    simpa using congrArg Units.val this
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [← hA, hr1]; simp)

noncomputable def projectiveSpecialLinearEquivSpecialLinear {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  (QuotientGroup.quotientMulEquivOfEq (center_specialLinearGroup_eq_bot_of_card_two hK hn)).trans
    QuotientGroup.quotientBot

theorem nonempty_mulEquiv_sl_zmod_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X StatedLieTag.PSL n 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨⟨-, -, hn, -⟩, K, hF, hfin, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  exact ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
    ((projectiveSpecialLinearEquivSpecialLinear hK2 (by omega)).trans
      (specialLinearGroupCongr (Fin n) ε))⟩

theorem nonempty_mulEquiv_sl_three_zmod_two {X : Type} [Group X]
    (h : StatedClassicalModel X StatedLieTag.PSL 3 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  nonempty_mulEquiv_sl_zmod_two h

theorem nonempty_mulEquiv_sl_two_four_of_alt_five :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃*
      ↥(alternatingGroup (Fin 5))) := by
  obtain ⟨e⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  exact ⟨((projectiveSLTwoEquivSL (GaloisField 2 2)).symm.trans
    (projectiveSpecialLinearEquivProjectiveSL 2 (GaloisField 2 2)).symm).trans e⟩

end CFSG.Quasithin.S146zX
