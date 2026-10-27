module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixUnitary
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.LocalAnalysis

section Six

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem EvenNormPlane.finrank_sixSpace : finrank K D.sixSpace = 6 := by
  rw [← D.sixCoord.finrank_eq, finrank_evenNormTailSpace D.finrank_eq 2]

theorem EvenNormPlane.card_orthogonalGroup_sixForm :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup D.sixForm) =
      2 * Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1) := by
  obtain ⟨-, -, -, -, -, -, -, hcard⟩ :=
    even_norm_tail_orthogonal_group_order D.finrank_eq D.σ D.σ_ne_one D.N D.algebraMap_N 2
  rw [← CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr D.sixIsometry, hcard]

end Six

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Module Matrix QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis
open scoped commutatorElement

theorem even_minus_six_unitary_derived_model {K E : Type} [Field K] [Finite K] [CharP K 2]
    [Field E] [Algebra K E] (D : EvenNormPlane K E) :
    (∀ X : Matrix (Fin 4) (Fin 4) E,
        X ∈ D.sixSpace ↔ ∃ (a c d f₀ : K) (b : E), X = D.sixMat a c d f₀ b) ∧
    (∀ (a c d f₀ a' c' d' f₀' : K) (b b' : E), D.sixMat a c d f₀ b = D.sixMat a' c' d' f₀' b' →
        a = a' ∧ c = c' ∧ d = d' ∧ f₀ = f₀' ∧ b = b') ∧
    (∀ (a c d f₀ : K) (b : E),
        D.sixForm ⟨D.sixMat a c d f₀ b, D.sixMat_mem a c d f₀ b⟩ = a * f₀ + c * d + D.N b) ∧
    (∀ X : D.sixSpace,
        algebraMap K E (D.sixForm X) = CFSG.LocalAnalysis.pfaff (X : Matrix (Fin 4) (Fin 4) E)) ∧
    finrank K D.sixSpace = 6 ∧ (polarBilin D.sixForm).Nondegenerate ∧
    (∀ U : Submodule K D.sixSpace, (∀ u ∈ U, D.sixForm u = 0) → finrank K U ≤ 2) ∧
    (∀ g, D.sixRho g ∈ TauCeti.QuadraticMap.orthogonalGroup D.sixForm) ∧
    Function.Injective D.sixRho ∧
    IsSimpleGroup D.sixRho.range ∧ Group.IsPerfect D.sixRho.range ∧
    (¬ ∀ x y : D.sixRho.range, x * y = y * x) ∧
    Nat.card D.sixRho.range =
      Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1) ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup D.sixForm) =
      2 * (Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
        (Nat.card K ^ 4 - 1)) ∧
    (D.sixRho.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup D.sixForm)).index = 2 ∧
    (D.sixRho.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup D.sixForm)).Normal ∧
    ⁅TauCeti.QuadraticMap.orthogonalGroup D.sixForm,
        TauCeti.QuadraticMap.orthogonalGroup D.sixForm⁆ = D.sixRho.range ∧
    (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup D.sixForm, Odd (orderOf g) →
        g ∈ D.sixRho.range) ∧
    (∀ (g : D.sixSU) (X : D.sixSpace), ((D.sixRho g X : D.sixSpace) : Matrix (Fin 4) (Fin 4) E) =
        ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * X *
          ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ) ∧
    (Nat.card K = 2 → Nat.card D.sixRho.range = 25920 ∧
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup D.sixForm) = 51840) := by
  classical
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have := D.finite_E
  have hinj := D.sixRho_injective
  have hSsimple := D.sixSU_isSimpleGroup
  have hSperf := D.sixSU_isPerfect
  obtain ⟨hnd, ⟨-, hts⟩, -, -, -, -, -, -⟩ :=
    even_norm_tail_orthogonal_group_order D.finrank_eq D.σ D.σ_ne_one D.N D.algebraMap_N 2
  let e : D.sixSU ≃* D.sixRho.range := MonoidHom.ofInjective hinj
  have hJsimple : IsSimpleGroup D.sixRho.range := e.symm.isSimpleGroup
  have hJperf : Group.IsPerfect D.sixRho.range := Group.IsPerfect.range D.sixRho
  have hJcard : Nat.card D.sixRho.range =
      Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1) := by
    rw [← Nat.card_congr e.toEquiv]
    exact D.card_sixSU
  have hOcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup D.sixForm) =
      2 * (Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
        (Nat.card K ^ 4 - 1)) := by
    rw [D.card_orthogonalGroup_sixForm]
    ring
  have hJO : D.sixRho.range ≤ TauCeti.QuadraticMap.orthogonalGroup D.sixForm :=
    D.sixRho_range_le
  have hpos : 0 < Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
      (Nat.card K ^ 4 - 1) := by
    have h2 : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    have h4 : 1 < Nat.card K ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by positivity))
      (by omega)
  have hidx : (D.sixRho.range.subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup D.sixForm)).index = 2 := by
    have h1 := Subgroup.card_mul_index (D.sixRho.range.subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup D.sixForm))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJO).toEquiv, hJcard, hOcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  have hnormal : (D.sixRho.range.subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup D.sixForm)).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  have hcomm : ⁅TauCeti.QuadraticMap.orthogonalGroup D.sixForm,
      TauCeti.QuadraticMap.orthogonalGroup D.sixForm⁆ = D.sixRho.range := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact Subgroup.mem_subgroupOf.mp (commutatorElement_mem_of_index_two _ hidx ⟨a, ha⟩ ⟨b, hb⟩)
    · calc D.sixRho.range = ⁅D.sixRho.range, D.sixRho.range⁆ :=
            Subgroup.commutator_eq_self.symm
        _ ≤ _ := Subgroup.commutator_mono hJO hJO
  have hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup D.sixForm, Odd (orderOf g) →
      g ∈ D.sixRho.range := by
    intro g hg ho
    exact Subgroup.mem_subgroupOf.mp (mem_of_odd_orderOf_of_index_two _ hidx
      (g := (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup D.sixForm))
      (by rwa [Subgroup.orderOf_mk]))
  refine ⟨D.mem_sixSpace_iff, fun a c d f₀ a' c' d' f₀' b b' h => D.sixMat_inj h,
    fun a c d f₀ b => D.sixForm_sixElement a c d f₀ b, D.algebraMap_sixForm,
    D.finrank_sixSpace,
    CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv D.sixIsometry hnd,
    fun U hU => ?_, D.sixRho_mem, hinj, hJsimple, hJperf, fun h => ?_, hJcard, hOcard, hidx,
    hnormal, hcomm, hodd, fun g X => D.coe_sixRho g X, fun h2 => ?_⟩
  · have := hts (U.map D.sixCoord.symm.toLinearMap) (fun u hu => by
      obtain ⟨w, hw, rfl⟩ := hu
      have h1 := D.sixIsometry.map_app (D.sixCoord.symm w)
      have h2 : D.sixIsometry (D.sixCoord.symm w) = w := D.sixCoord.apply_symm_apply w
      rw [h2] at h1
      exact h1.symm.trans (hU w hw))
    rwa [LinearEquiv.finrank_map_eq] at this
  · have := hJsimple
    exact Group.IsPerfect.not_isMulCommutative (G := D.sixRho.range) ⟨⟨h⟩⟩
  · rw [hJcard, hOcard, h2]
    norm_num

end CFSG.RankThree.PartOne
