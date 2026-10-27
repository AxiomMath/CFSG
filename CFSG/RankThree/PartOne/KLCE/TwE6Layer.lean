module

public import CFSG.RankThree.PartOne.KLCE.TwE6Frame
public import CFSG.RankThree.PartOne.KLCE.FrobAut
public import CFSG.RankThree.PartOne.KLCE.E8Seven
public import CFSG.RankThree.PartOne.KLCE.LayerDatum

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Classical (conjSL)

open Matrix
open scoped MatrixGroups Polynomial

section Layer

variable {L : Type} [Field L]

theorem map_surjective_sl2 {Φ : L →+* L} (hΦ : Function.Bijective Φ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2) Φ) := by
  let e : L ≃+* L := RingEquiv.ofBijective Φ hΦ
  intro B
  refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom B, ?_⟩
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact e.apply_symm_apply _

theorem diag_fixes_Qtheta (B : SL(2, L)) :
    diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
      (diagramMap TwistTag.E6 L)⁻¹ = rootSL2 TwistTag.E6.tag L e6HighestRoot B := by
  obtain ⟨-, -, -, -, hrange, hPfix, -⟩ := E6_highest_root_graph_fixed_and_signed_order_five_descent L
  exact hPfix _ (by rw [← hrange]; exact ⟨B, rfl⟩)

theorem exists_frobAut_layer {k : Type} [Field k] [Finite k] [CharP k 2] {n m : ℕ}
    (hk : Nat.card k = 2 ^ n) (hm : 0 < m) (hmn : m < n) :
    ∃ σ' : k ≃+* k, σ' ≠ 1 ∧ ∀ a, σ' a = a ^ 2 ^ m :=
  ⟨frobAut k m, frobAut_ne_one hk hm hmn, fun a => frobAut_apply m a⟩

theorem twE6_layer_family [IsAlgClosed L] [CharP L 2] {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hf₀ : 1 ≤ f₀) (k : Type) [Field k] [Finite k] [Algebra k L] (hk : Nat.card k = 2 ^ (f₀ * p)) :
    ∃ P : Unit → Subgroup (ModGL TwistTag.E6.tag L),
      IsSigmaFamilyΦ (normSeq (e6HRn L) (twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀)) p)
        (twistHom TwistTag.E6 L (iterateFrobenius L 2 (f₀ * p))) {e6O5Theta, -e6O5Theta} P ∧
      rootSpan TwistTag.E6.tag L {e6O5Theta, -e6O5Theta} ⊓
        twistedFixedPoints (normSeq (e6HRn L) (twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀)) p)
          (twistHom TwistTag.E6 L (iterateFrobenius L 2 (f₀ * p))) ≤ ⨆ i : Unit, P i ∧
      LayerDatum p (fun u => e6HRn L * twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀) u *
        (e6HRn L)⁻¹) (P ()) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ := hpodd
  have hθ : IsRoot TwistTag.E6.tag e6HighestRoot := isRoot_e6HighestRoot
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFr
  set F₀ := twistHom TwistTag.E6 L Φ₀ with hF₀
  set n₀ := e6HRn L with hn₀
  set N := normSeq n₀ F₀ p with hN
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  have hΦ₀bij : Function.Bijective Φ₀ := ⟨Φ₀.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 ^ f₀ by positivity)
    exact ⟨x, by rw [hΦ₀c, hx]⟩⟩
  have hρ : ∀ B, F₀ (rootSL2 TwistTag.E6.tag L e6HighestRoot B) =
      rootSL2 TwistTag.E6.tag L e6HighestRoot (SpecialLinearGroup.map Φ₀ B) :=
    e6_twist_rootSL2 Φ₀
  have hnρ := e6_rootSL2_conj (L := L)
  have hJ : SpecialLinearGroup.map Φ₀ (WSL : SL(2, L)) = WSL := map_WSL Φ₀
  have hJ2 : (WSL : SL(2, L)) * WSL = 1 := WSL_mul_self_of_charTwo
  have hJp : (WSL : SL(2, L)) ^ p = WSL := by
    rw [hm, pow_succ, pow_mul, pow_two, hJ2, one_pow, one_mul]
  have hNρ : ∀ B, N * diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
      (N * diagramMap TwistTag.E6 L)⁻¹ = rootSL2 TwistTag.E6.tag L e6HighestRoot (WSL * B * WSL⁻¹) := by
    intro B
    have h := normSeq_action F₀ n₀ (rootSL2 TwistTag.E6.tag L e6HighestRoot)
      (SpecialLinearGroup.map Φ₀) (map_surjective_sl2 hΦ₀bij) WSL hJ hρ hnρ p B
    rw [hJp] at h
    rw [← h, _root_.mul_inv_rev]
    calc N * diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
          ((diagramMap TwistTag.E6 L)⁻¹ * N⁻¹)
        = N * (diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
          (diagramMap TwistTag.E6 L)⁻¹) * N⁻¹ := by group
      _ = _ := by rw [diag_fixes_Qtheta]
  obtain ⟨k₀, _, _, _, hk₀⟩ := exists_finite_field_into 2 f₀ hf₀ L
  have hFr₀ : ∀ c, Φ₀ c = c ^ Nat.card k₀ := fun c => by rw [hk₀]; exact hΦ₀c c
  obtain ⟨P₀, hP₀⟩ := exists_WSL_twist (K := k₀) (L := L) Φ₀ hFr₀
  have hJGL : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) =
      Matrix.SpecialLinearGroup.toGL WSL := by
    have h2 : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Φ₀ (WSL : SL(2, L))) := by
      ext i j
      rfl
    rw [h2, hJ]
  have hsq : Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) *
      Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) = 1 := by
    rw [← map_mul, hJ2, map_one]
  have hP : P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹ =
      Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
    have h1 := P_frobenius_pow hJGL hP₀ p
    rw [hFr, h1, hm, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
  have hX := a1_hX_of_J (N := N * diagramMap TwistTag.E6 L) hNρ Fr hP
  have : CharP k 2 := ⟨fun x => by
    rw [← (algebraMap k L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hFrk : ∀ c, Fr c = c ^ Nat.card k := fun c => by
    rw [hk]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f₀ * p) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  obtain ⟨P, hfam, hPeq⟩ := a1_sigma_family_of_action (K := k) hk4 hθ Fr hFrk P₀ hX
  have hfix := a1_fixed_range_of_action (K := k) hθ Fr hFrk P₀ hX
  refine ⟨P, isSigmaFamilyΦ_twist N Fr _ P hfam, ?_, ?_⟩
  · have htf : twistedFixedPoints N (twistHom TwistTag.E6 L Fr) =
        twistedFixedPoints (N * diagramMap TwistTag.E6 L) (Units.map (entrywiseHom Fr)) :=
      twistedFixedPoints_twist N Fr
    rw [htf, iSup_unique]
    change _ ≤ P ()
    rw [hPeq, ← hfix]
    exact le_rfl
  · obtain ⟨σ', hσ'1, hσ'a⟩ := exists_frobAut_layer (k := k) (n := f₀ * p) (m := f₀) hk
      (by omega) (by nlinarith)
    have hσ'L : ∀ c : k, Φ₀ (algebraMap k L c) = algebraMap k L (σ' c) := fun c => by
      rw [hσ'a, hΦ₀c, map_pow]
    have hk' : Nat.card k = 2 ^ (p * f₀) := by rw [hk, mul_comm]
    refine layerDatum_of_sl (m := 0) hp (by omega) (by omega) hf₀ _ (P ()) hk' hσ'1
      (a1HomConj TwistTag.E6.tag k L e6HighestRoot P₀) (a1HomConj_injective _ _) hPeq.symm ?_
    intro d
    have e1 : F₀ (a1HomConj TwistTag.E6.tag k L e6HighestRoot P₀ d) =
        Units.map (entrywiseHom Φ₀) (a1HomConj TwistTag.E6.tag k L e6HighestRoot P₀ d) := by
      rw [a1HomConj_apply, hρ, entrywise_rootSL2_of_field]
    show n₀ * F₀ (a1HomConj TwistTag.E6.tag k L e6HighestRoot P₀ d) * n₀⁻¹ = _
    rw [e1]
    exact a1_F0_compat_II hnρ hσ'L hP₀ d

end Layer

end CFSG.RankThree.PartOne.KLCE
