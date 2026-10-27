module

public import CFSG.OddTranspositions.PartFour.ThirteenCompFactorFive
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin CFSG.Quasithin.H13.L829N
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn orthTuples)

private theorem oddTranspFactor_of_modelIn_orthTuples_three {d : ℕ} {L : Type} [Group L]
    (h : ModelIn 3 (orthTuples d 1) L) : OddTranspFactor (L ⧸ Subgroup.center L) := by
  obtain ⟨t, m, f, hT, -, hL⟩ := h
  have q3 : (3 = 3 ∨ 3 = 5) := Or.inl rfl
  rcases hT with ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h | h⟩ <;>
    simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h
  · exact Or.inr (Or.inr (Or.inl ⟨3, 0, 1, q3, by norm_num, Or.inl hL⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, 0, 1, q3, by norm_num, Or.inl hL⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, 0, 2 * 1, q3, by norm_num, Or.inl hL⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, 0, 0, q3, by norm_num, Or.inr (Or.inl hL)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, 0, 0, q3, by norm_num, Or.inr (Or.inr (Or.inl hL))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, 0, 0, q3, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inl hL)))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, d / 2, 0, q3, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, d / 2, 0, q3, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, d / 2, 0, q3, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL)))))⟩))

section Orthogonal

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem oddTranspFactors_of_isComponent_three (hK : Nat.card K = 3) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (h3 : 3 ≤ Module.finrank K W)
    {M : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : CFSG.IsComponent M) :
    OddTranspFactors ↥M :=
  OddTranspFactors.of_isQuasisimple hM.1 (oddTranspFactor_of_modelIn_orthTuples_three
    (CFSG.ComponentClassification.CatLeafProof.X10Lin.orthogonal_component_models
      Nat.prime_three (by norm_num) le_rfl (by rw [hK]; norm_num) Q hQ h3 hM))

theorem oddTranspFactors_commutator_orthogonalGroup_three (hK : Nat.card K = 3)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (h5 : 5 ≤ Module.finrank K W) :
    OddTranspFactors ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hC : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)).Normal := inferInstance
  have hder : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) →
      OddTranspFactors ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := fun hq =>
    oddTranspFactors_of_isComponent_three hK Q hQ (by omega) ⟨hq, hC.isSubnormal⟩
  by_cases hT : ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    exact hder (CFSG.ComponentClassification.CatalogueBOrthogonal.derived_quasisimple Q h2 hQ
      hT3.ge hTQ)
  have h6 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three
      hodd Q hQ hT
  rcases (show Module.finrank K W = 5 ∨ Module.finrank K W = 6 by omega) with h | h
  · obtain ⟨-, -, -, -, -, -, hq, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_five_derived hodd Q hQ h
    exact hder hq
  · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived hodd Q hQ h hT
    exact hder hq

end Orthogonal

section Reflections

open CFSG.ClassicalGroups.Orthogonal

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}

private theorem fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

attribute [local instance] fact_prime_three

private theorem three_eq_zero : (3 : ZMod 3) = 0 := by
  decide

theorem bilin_map_of_mem_orthogonalGroup_three (hsym : ∀ x y, b x y = b y x)
    {g : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))
    (x y : Fin n → ZMod 3) : b (g x) (g y) = b x y := by
  have hQ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have hp : QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap b) (g x) (g y) =
      QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap b) x y := by
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hQ, hQ, hQ]
  rw [LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.BilinMap.polar_toQuadraticMap,
    hsym (g y) (g x), hsym y x, ← two_mul, ← two_mul] at hp
  exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) hp

theorem f3ReflectionGroup_le_orthogonalGroup (hsym : ∀ x y, b x y = b y x) :
    (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => b x y)
        fun v => b v v = 1)).map (toLinEquiv (Fin n) (ZMod 3)).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b) := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨m, ⟨v, hv, hmv⟩, rfl⟩
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hmv, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv,
    hsym v x]
  linear_combination (b x v * b x v) * three_eq_zero

theorem conj_mem_f3Reflections (hsym : ∀ x y, b x y = b y x)
    {g : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))
    {m : GL (Fin n) (ZMod 3)}
    (hm : m ∈ CFSG.Open.fischerTransvections (fun x y => b x y) fun v => b v v = 1) :
    g * (toLinEquiv (Fin n) (ZMod 3)).toMonoidHom m * g⁻¹ ∈
      (toLinEquiv (Fin n) (ZMod 3)).toMonoidHom ''
        CFSG.Open.fischerTransvections (fun x y => b x y) fun v => b v v = 1 := by
  obtain ⟨v, hv, hmv⟩ := hm
  have key : ∀ x, b (g.symm x) v = b x (g v) := fun x => by
    have := bilin_map_of_mem_orthogonalGroup_three hsym hg (g.symm x) v
    rw [g.apply_symm_apply] at this
    exact this.symm
  refine ⟨(toLinEquiv (Fin n) (ZMod 3)).symm (g * (toLinEquiv (Fin n) (ZMod 3)).toMonoidHom m *
    g⁻¹), ⟨g v, ?_, fun x => ?_⟩, MulEquiv.apply_symm_apply _ _⟩
  · show b (g v) (g v) = 1
    rw [bilin_map_of_mem_orthogonalGroup_three hsym hg, hv]
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    change g ((toLinEquiv (Fin n) (ZMod 3)) m (g.symm x)) = _
    rw [toLinEquiv_apply, hmv, map_add, map_smul, g.apply_symm_apply]
    simp only [key]

theorem conj_mem_f3ReflectionGroup (hsym : ∀ x y, b x y = b y x)
    {g : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))
    {h : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)}
    (hh : h ∈ (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => b x y)
        fun v => b v v = 1)).map (toLinEquiv (Fin n) (ZMod 3)).toMonoidHom) :
    g * h * g⁻¹ ∈ (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => b x y)
        fun v => b v v = 1)).map (toLinEquiv (Fin n) (ZMod 3)).toMonoidHom := by
  rw [MonoidHom.map_closure] at hh ⊢
  have hle : (Subgroup.closure ((toLinEquiv (Fin n) (ZMod 3)).toMonoidHom ''
      CFSG.Open.fischerTransvections (fun x y => b x y) fun v => b v v = 1)).map
        (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure ((toLinEquiv (Fin n) (ZMod 3)).toMonoidHom ''
        CFSG.Open.fischerTransvections (fun x y => b x y) fun v => b v v = 1) := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact conj_mem_f3Reflections hsym hg hm
  exact hle ⟨h, hh, rfl⟩

theorem oddTranspFactors_f3ReflectionGroup (hn : 5 ≤ n) (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    OddTranspFactors ↥(Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => b x y)
      fun v => b v v = 1)) := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hQ : (LinearMap.BilinMap.toQuadraticMap b).polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hnd v fun w => by
      have := hv w
      rw [LinearMap.BilinMap.polar_toQuadraticMap, hsym w v, ← two_mul] at this
      exact (mul_eq_zero.mp this).resolve_left h2
  have hdim : 5 ≤ Module.finrank (ZMod 3) (Fin n → ZMod 3) := by
    rw [Module.finrank_fin_fun]
    exact hn
  have hO := oddTranspFactors_commutator_orthogonalGroup_three (K := ZMod 3)
    (by rw [Nat.card_eq_fintype_card, ZMod.card]) _ hQ hdim
  have hle := f3ReflectionGroup_le_orthogonalGroup hsym
  haveI : (((Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => b x y)
      fun v => b v v = 1)).map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n)
        (ZMod 3)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact conj_mem_f3ReflectionGroup hsym g.2 hx⟩
  have hHO : OddTranspFactors ↥(((Subgroup.closure (CFSG.Open.fischerTransvections
      (fun x y => b x y) fun v => b v v = 1)).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) (ZMod 3)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))) :=
    OddTranspFactors.of_normal_commutator _ hO
  exact (hHO.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)).of_mulEquiv
    ((Subgroup.closure _).equivMapOfInjective _
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) (ZMod 3)).injective).symm

end Reflections

end CFSG.OddTranspositions.PartFour
