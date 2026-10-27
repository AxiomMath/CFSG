module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourDefs
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module Matrix QuadraticMap
open scoped MatrixGroups commutatorElement

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

@[expose] noncomputable def hermFourIsometry :
    (evenNormTailForm D.N 1).IsometryEquiv (hermFourForm D) where
  toLinearEquiv := hermFourCoord D
  map_app' v := by
    simp [hermFourForm, QuadraticMap.comp_apply]

theorem hermFourForm_coord (v : ((Fin 1 → K) × (Fin 1 → K)) × E) :
    hermFourForm D (hermFourCoord D v) = v.1.1 0 * v.1.2 0 + D.N v.2 := by
  have := (hermFourIsometry D).map_app v
  rw [show (hermFourIsometry D) v = hermFourCoord D v from rfl] at this
  rw [this, evenNormTailForm_apply]
  simp

theorem det_hermFourMat (a b : K) (z : E) :
    (hermFourMat D.σ a b z).det = algebraMap K E a * algebraMap K E b - z * D.σ z := by
  simp [hermFourMat, Matrix.det_fin_two]

theorem coe_hermFourCoord (v : ((Fin 1 → K) × (Fin 1 → K)) × E) :
    ((hermFourCoord D v : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      hermFourMat D.σ (v.1.1 0) (v.1.2 0) v.2 :=
  rfl

theorem algebraMap_hermFourForm (X : hermFourSpace D.σ) :
    algebraMap K E (hermFourForm D X) = (X : Matrix (Fin 2) (Fin 2) E).det := by
  obtain ⟨v, rfl⟩ := (hermFourCoord D).surjective X
  rw [hermFourForm_coord, coe_hermFourCoord, det_hermFourMat]
  have : CharP E 2 := charP_two_of_algebra (K := K)
  rw [map_add, map_mul, D.algebraMap_N, sub_eq_add_neg, CharTwo.neg_eq]

section SL2

theorem sl2_center_eq_bot {F : Type} [Field F] [CharP F 2] : Subgroup.center SL(2, F) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem sl2_isSimpleGroup {F : Type} [Field F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup SL(2, F) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SL(2, F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot.symm)
  exact e.isSimpleGroup

theorem sl2_isPerfect {F : Type} [Field F] (h4 : 4 ≤ Nat.card F) : Group.IsPerfect SL(2, F) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

theorem card_sl2 {F : Type} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card F with hq
  have hq1 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := F)
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, _root_.sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by omega)]

end SL2

section IndexTwo

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

theorem sq_mem_of_index_two (hN : N.index = 2) (x : G) : x ^ 2 ∈ N := by
  have hcard : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index, hN]
  have h := pow_card_eq_one' (G := G ⧸ N) (x := (x : G ⧸ N))
  rw [hcard] at h
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact h

theorem mem_of_odd_orderOf_of_index_two (hN : N.index = 2) {g : G} (hg : Odd (orderOf g)) :
    g ∈ N := by
  obtain ⟨k, hk⟩ := hg
  have h1 : g = (g ^ 2)⁻¹ ^ k * g ^ orderOf g := by
    rw [hk]
    group
  rw [h1, pow_orderOf_eq_one, mul_one]
  exact N.pow_mem (N.inv_mem (sq_mem_of_index_two N hN g)) k

theorem commutatorElement_mem_of_index_two (hN : N.index = 2) (a b : G) : ⁅a, b⁆ ∈ N := by
  have hcard : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index, hN]
  have : Fact (Nat.card (G ⧸ N)).Prime := ⟨by rw [hcard]; exact Nat.prime_two⟩
  have hcyc : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  have h := map_commutatorElement (QuotientGroup.mk' N) a b
  simp only [QuotientGroup.mk'_apply] at h
  rw [← QuotientGroup.eq_one_iff, h, commutatorElement_eq_one_iff_mul_comm]
  exact IsCyclic.commGroup.mul_comm _ _

end IndexTwo

section Rho

theorem hermFourRho_mem (g : SL(2, E)) :
    hermFourRho D g ∈ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro X
  apply (algebraMap K E).injective
  rw [algebraMap_hermFourForm, algebraMap_hermFourForm, coe_hermFourRho, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose]
  have h1 : (g.1.map D.σ).det = D.σ g.1.det := by
    simpa using (AlgHom.map_det D.σ.toAlgHom g.1).symm
  rw [h1, g.2, map_one, one_mul, mul_one]

theorem hermFourRho_range_le :
    (hermFourRho D).range ≤ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D) := by
  rintro _ ⟨g, rfl⟩
  exact hermFourRho_mem D g

theorem hermFourRho_injective (h4 : 4 ≤ Nat.card E) : Function.Injective (hermFourRho D) := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have hS := sl2_isSimpleGroup h4
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hS.eq_bot_or_eq_top_of_normal (hermFourRho D).ker with h | h
  · exact h
  · exfalso
    let t : SL(2, E) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have ht : t ∈ (hermFourRho D).ker := by rw [h]; trivial
    have h1 : hermFourRho D t = 1 := ht
    let X : hermFourSpace D.σ := ⟨hermFourMat D.σ 0 1 0, hermFourMat_mem D 0 1 0⟩
    have h2 : (((hermFourRho D t) X : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) 0 0 =
        ((X : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) 0 0 := by
      rw [h1]
      rfl
    rw [coe_hermFourRho] at h2
    simp [Matrix.mul_apply, Fin.sum_univ_two, hermFourMat, t, X] at h2

end Rho

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Module Matrix QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups commutatorElement

theorem even_minus_four_hermitian_derived_model {K E : Type} [Field K] [Finite K] [CharP K 2]
    [Field E] [Algebra K E] (D : EvenNormPlane K E) :
    (∀ X : Matrix (Fin 2) (Fin 2) E,
        X ∈ hermFourSpace D.σ ↔ ∃ (a b : K) (z : E), X = hermFourMat D.σ a b z) ∧
    (∀ (a b a' b' : K) (z z' : E), hermFourMat D.σ a b z = hermFourMat D.σ a' b' z' →
        a = a' ∧ b = b' ∧ z = z') ∧
    (∀ (a b : K) (z : E),
        hermFourForm D ⟨hermFourMat D.σ a b z, hermFourMat_mem D a b z⟩ = a * b + D.N z) ∧
    (∀ X : hermFourSpace D.σ,
        algebraMap K E (hermFourForm D X) = (X : Matrix (Fin 2) (Fin 2) E).det) ∧
    finrank K (hermFourSpace D.σ) = 4 ∧ (polarBilin (hermFourForm D)).Nondegenerate ∧
    (∀ U : Submodule K (hermFourSpace D.σ), (∀ u ∈ U, hermFourForm D u = 0) →
        finrank K U ≤ 1) ∧
    (∀ g, hermFourRho D g ∈ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)) ∧
    Function.Injective (hermFourRho D) ∧
    IsSimpleGroup (hermFourRho D).range ∧ Group.IsPerfect (hermFourRho D).range ∧
    (¬ ∀ x y : (hermFourRho D).range, x * y = y * x) ∧
    Nat.card (hermFourRho D).range = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)) =
      2 * (Nat.card K ^ 2 * (Nat.card K ^ 4 - 1)) ∧
    ((hermFourRho D).range.subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D))).index = 2 ∧
    ((hermFourRho D).range.subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D))).Normal ∧
    ⁅TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D),
        TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)⁆ = (hermFourRho D).range ∧
    (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D), Odd (orderOf g) →
        g ∈ (hermFourRho D).range) := by
  classical
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hE4 : 4 ≤ Nat.card E := by
    rw [D.card_E]
    nlinarith
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have := D.finite_E
  have hinj := hermFourRho_injective D hE4
  obtain ⟨hnd, ⟨-, hts⟩, -, -, -, -, hcard1, -⟩ :=
    even_norm_tail_orthogonal_group_order D.finrank_eq D.σ D.σ_ne_one D.N D.algebraMap_N 1
  have hsimple : IsSimpleGroup SL(2, E) := sl2_isSimpleGroup hE4
  have hperf : Group.IsPerfect SL(2, E) := sl2_isPerfect hE4
  let e : SL(2, E) ≃* (hermFourRho D).range := MonoidHom.ofInjective hinj
  have hJsimple : IsSimpleGroup (hermFourRho D).range := e.symm.isSimpleGroup
  have hJperf : Group.IsPerfect (hermFourRho D).range := Group.IsPerfect.range (hermFourRho D)
  have hJcard : Nat.card (hermFourRho D).range = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [← Nat.card_congr e.toEquiv, card_sl2, D.card_E, ← pow_mul]
  have hOcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)) =
      2 * (Nat.card K ^ 2 * (Nat.card K ^ 4 - 1)) := by
    rw [← CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr (hermFourIsometry D), hcard1,
      mul_assoc]
  have hJO : (hermFourRho D).range ≤ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D) :=
    hermFourRho_range_le D
  have hpos : 0 < Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    have : 1 < Nat.card K ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    exact Nat.mul_pos (by positivity) (by omega)
  have hidx : ((hermFourRho D).range.subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D))).index = 2 := by
    have h1 := Subgroup.card_mul_index ((hermFourRho D).range.subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJO).toEquiv, hJcard, hOcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  have hnormal : ((hermFourRho D).range.subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D))).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  have hcomm : ⁅TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D),
      TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)⁆ = (hermFourRho D).range := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact Subgroup.mem_subgroupOf.mp (commutatorElement_mem_of_index_two _ hidx ⟨a, ha⟩ ⟨b, hb⟩)
    · calc (hermFourRho D).range = ⁅(hermFourRho D).range, (hermFourRho D).range⁆ :=
            Subgroup.commutator_eq_self.symm
        _ ≤ _ := Subgroup.commutator_mono hJO hJO
  have hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D), Odd (orderOf g) →
      g ∈ (hermFourRho D).range := by
    intro g hg ho
    exact Subgroup.mem_subgroupOf.mp (mem_of_odd_orderOf_of_index_two _ hidx
      (g := (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup (hermFourForm D)))
      (by rwa [Subgroup.orderOf_mk]))
  have hcoord : ∀ (a b : K) (z : E), (⟨hermFourMat D.σ a b z, hermFourMat_mem D a b z⟩ :
      hermFourSpace D.σ) = hermFourCoord D ((fun _ => a, fun _ => b), z) :=
    fun a b z => Subtype.ext rfl
  refine ⟨fun X => ⟨fun hX => ?_, fun ⟨a, b, z, h⟩ => h ▸ hermFourMat_mem D a b z⟩,
    fun a b a' b' z z' h => ?_, fun a b z => ?_, algebraMap_hermFourForm D, ?_,
    CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv (hermFourIsometry D) hnd,
    fun U hU => ?_, hermFourRho_mem D, hinj, hJsimple, hJperf, fun h => ?_, hJcard, hOcard, hidx,
    hnormal, hcomm, hodd⟩
  · obtain ⟨v, hv⟩ := hermFourCoordLin_surjective D ⟨X, hX⟩
    refine ⟨v.1.1 0, v.1.2 0, v.2, ?_⟩
    have := congrArg Subtype.val hv
    rw [coe_hermFourCoordLin] at this
    exact this.symm
  · have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    have h01 := congrFun (congrFun h 0) 1
    simp only [hermFourMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h11 h01
    exact ⟨(algebraMap K E).injective h00, (algebraMap K E).injective h11, h01⟩
  · rw [hcoord, hermFourForm_coord]
  · rw [← (hermFourCoord D).finrank_eq, finrank_evenNormTailSpace D.finrank_eq 1]
  · have := hts (U.map (hermFourCoord D).symm.toLinearMap) (fun u hu => by
      obtain ⟨w, hw, rfl⟩ := hu
      have h1 := (hermFourIsometry D).map_app ((hermFourCoord D).symm w)
      have h2 : (hermFourIsometry D) ((hermFourCoord D).symm w) = w :=
        (hermFourCoord D).apply_symm_apply w
      rw [h2] at h1
      exact h1.symm.trans (hU w hw))
    rwa [LinearEquiv.finrank_map_eq] at this
  · have := hJsimple
    exact Group.IsPerfect.not_isMulCommutative (G := (hermFourRho D).range) ⟨⟨h⟩⟩

end CFSG.RankThree.PartOne
