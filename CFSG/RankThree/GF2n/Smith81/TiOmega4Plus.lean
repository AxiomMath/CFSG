module

public import CFSG.RankThree.GF2n.Smith81.TiD2Alg
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount

public section

namespace CFSG.RankThree.GF2n.Smith81

open Matrix
open scoped MatrixGroups

namespace D2

variable {K : Type*} [Field K]

@[expose] def detCoords (K : Type*) [Field K] : Mat2 K ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K) where
  toFun X := Sum.elim ![X 0 0, X 1 0] ![X 1 1, X 0 1]
  invFun v := !![v (Sum.inl 0), v (Sum.inr 1); v (Sum.inl 1), v (Sum.inr 0)]
  map_add' X Y := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  map_smul' c X := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  left_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  right_inv v := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp

theorem quadPlus_detCoords [CharP K 2] (X : Mat2 K) :
    CFSG.LieType.Universal.Spin.quadPlus 2 K (detCoords K X) = X.det := by
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [detCoords]
  linear_combination (X 0 1 * X 1 0) * h2K

theorem det_detCoords_symm [CharP K 2] (w : Fin 2 ⊕ Fin 2 → K) :
    ((detCoords K).symm w).det = CFSG.LieType.Universal.Spin.quadPlus 2 K w := by
  rw [← quadPlus_detCoords, LinearEquiv.apply_symm_apply]

@[expose] def detIsomEquiv [CharP K 2] : ↥(detIsom K) ≃
    ↥(TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 2 K)) where
  toFun T := ⟨(detCoords K).symm.trans (T.1.trans (detCoords K)),
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    show CFSG.LieType.Universal.Spin.quadPlus 2 K
      (detCoords K (T.1 ((detCoords K).symm v))) = CFSG.LieType.Universal.Spin.quadPlus 2 K v
    rw [quadPlus_detCoords, T.2, det_detCoords_symm]⟩
  invFun S := ⟨(detCoords K).trans (S.1.trans (detCoords K).symm), fun X => by
    show ((detCoords K).symm (S.1 (detCoords K X))).det = X.det
    rw [det_detCoords_symm, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp S.2,
      quadPlus_detCoords]⟩
  left_inv T := Subtype.ext (LinearEquiv.ext fun X => by simp)
  right_inv S := Subtype.ext (LinearEquiv.ext fun v => by simp)

theorem card_detIsom [Finite K] [CharP K 2] :
    Nat.card (detIsom K) = 2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
  rw [Nat.card_congr detIsomEquiv]
  have h := (CFSG.ClassicalInvolution.card_singular_and_orthogonalGroup_quadPlus (K := K) 1).2
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hq2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq
  simp only [Finset.Icc_self, Finset.prod_singleton] at h
  zify [hq2]
  convert h using 1
  ring

@[expose] def pairHom (K : Type*) [Field K] :
    SL(2, K) × SL(2, K) →* (Mat2 K ≃ₗ[K] Mat2 K) where
  toFun p := pairEquiv p.1 p.2
  map_one' := LinearEquiv.ext fun X => by simp
  map_mul' p q := LinearEquiv.ext fun X => by
    simp only [pairEquiv_apply, LinearEquiv.mul_apply, Prod.fst_mul, Prod.snd_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem pairHom_apply (p : SL(2, K) × SL(2, K)) : pairHom K p = pairEquiv p.1 p.2 := rfl

theorem pairHom_injective [CharP K 2] : Function.Injective (pairHom K) := by
  intro p q h
  have := pair_unique (g := p.1) (g' := q.1) (h := p.2) (h' := q.2) fun X => by
    have := LinearEquiv.congr_fun h X
    simpa [pairHom_apply] using this
  exact Prod.ext this.1 this.2

theorem pairGroup_eq_range : pairGroup K = (pairHom K).range := by
  ext T
  constructor
  · rintro ⟨g, h, hT⟩
    exact ⟨(g, h), LinearEquiv.ext fun X => by rw [pairHom_apply, hT X]; rfl⟩
  · rintro ⟨⟨g, h⟩, rfl⟩
    exact ⟨g, h, fun X => rfl⟩

theorem card_pairGroup [Finite K] [CharP K 2] :
    Nat.card (pairGroup K) = Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
  rw [pairGroup_eq_range, ← Nat.card_congr (MonoidHom.ofInjective pairHom_injective).toEquiv,
    Nat.card_prod, card_sl2]
  ring

theorem pairGroup_le_detIsom : pairGroup K ≤ detIsom K := by
  rintro T ⟨g, h, hT⟩ X
  have : T = pairEquiv g h := LinearEquiv.ext fun X => by rw [hT X]; rfl
  rw [this]
  exact det_pairEquiv g h X

theorem relIndex_pairGroup [Finite K] [CharP K 2] :
    (pairGroup K).relIndex (detIsom K) = 2 := by
  have h := Subgroup.relIndex_mul_card (H := pairGroup K) (K := detIsom K)
  rw [inf_of_le_left pairGroup_le_detIsom, card_pairGroup, card_detIsom] at h
  have h2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hpos : 0 < Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
    have h3 : 0 < Nat.card K ^ 2 - 1 := by
      have : 4 ≤ Nat.card K ^ 2 := by nlinarith
      omega
    positivity
  have : (pairGroup K).relIndex (detIsom K) * (Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) =
      2 * (Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem exists_dicksonHom (K : Type*) [Field K] [Finite K] [CharP K 2] :
    ∃ δ : ↥(detIsom K) →* Multiplicative (ZMod 2),
      ∀ T : ↥(detIsom K), δ T = 1 ↔ (T : Mat2 K ≃ₗ[K] Mat2 K) ∈ pairGroup K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup ↥(detIsom K) := (pairGroup K).subgroupOf (detIsom K) with hH
  have hidx : H.index = 2 := relIndex_pairGroup
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (↥(detIsom K) ⧸ H) = 2 := hidx
  have hcard' : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let e : (↥(detIsom K) ⧸ H) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hcard hcard'
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' H), fun T => ?_⟩
  show e (QuotientGroup.mk' H T) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hH,
    Subgroup.mem_subgroupOf]

end D2

end CFSG.RankThree.GF2n.Smith81
