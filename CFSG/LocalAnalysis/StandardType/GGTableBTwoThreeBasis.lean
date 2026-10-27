module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeBlock

public section

namespace CFSG.StandardType.TwoThree

open Matrix Module

variable {m : ℕ} {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_conj_eq_g0 (hK : Nat.card K = 2) {g : Matrix (Fin (m + 2)) (Fin (m + 2)) K}
    (hg3 : g ^ 3 = 1) (hrank : finrank K (LinearMap.range (Matrix.toLinAlgEquiv' g - 1)) = 2) :
    ∃ P : GL (Fin (m + 2)) K, (P : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * g *
      ((P⁻¹ : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
        (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) := by
  classical
  set f : Module.End K (Fin (m + 2) → K) := Matrix.toLinAlgEquiv' g with hf
  have hf3 : f ^ 3 = 1 := by rw [hf, ← map_pow, hg3, map_one]
  set U := LinearMap.range (f - 1) with hU
  set W := LinearMap.ker (f - 1) with hW
  have hUW : U ⊓ W = ⊥ := by
    have h := inf_ker_map_eq_bot hf3 ⊤
    rwa [top_inf_eq, Submodule.map_top, inf_comm] at h
  have hrn : finrank K U + finrank K W = m + 2 := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have hWm : finrank K W = m := by omega
  have hmemW : ∀ w, w ∈ W ↔ f w = w := fun w => by
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hfU : ∀ u ∈ U, f u ∈ U := by
    rintro _ ⟨v, rfl⟩
    refine ⟨f v, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, sub_mul, mul_sub, one_mul, mul_one]
  have hfp : ∀ u ∈ U, f u = u → u = 0 := fun u hu h => by
    have : u ∈ U ⊓ W := ⟨hu, (hmemW u).mpr h⟩
    rwa [hUW, Submodule.mem_bot] at this
  have hf2 : ∀ u ∈ U, f (f u) = u + f u := by
    intro u hu
    have h := sum_apply_eq_zero hf3 hfU hfp hu
    simp only [LinearMap.add_apply, Module.End.one_apply, sq, Module.End.mul_apply] at h
    have h2 : f (f u) = -(u + f u) := eq_neg_of_add_eq_zero_right h
    rw [h2, ← neg_one_smul K (u + f u), CharTwo.neg_eq, one_smul]
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrank
    exact absurd hrank (by norm_num)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hfu0 : f u ≠ 0 := by
    intro h
    have h1 := hf2 u hu
    rw [h, map_zero, add_zero] at h1
    exact hu0 h1.symm
  let wb : Basis (Fin m) K W := Module.finBasisOfFinrankEq K W hWm
  let w' : Fin m → (Fin (m + 2) → K) := fun k => (wb k : Fin (m + 2) → K)
  let v : Fin (m + 2) → (Fin (m + 2) → K) := Fin.cons u (Fin.cons (f u) w')
  have hspan : Submodule.span K (Set.range w') = W := by
    have h := wb.span_eq
    have h2 := congrArg (Submodule.map W.subtype) h
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
    exact h2
  have hli : LinearIndependent K v := by
    rw [linearIndependent_finCons, linearIndependent_finCons]
    refine ⟨⟨wb.linearIndependent.map' W.subtype (Submodule.ker_subtype W), ?_⟩, ?_⟩
    · rw [hspan]
      intro hW'
      have : f u ∈ U ⊓ W := ⟨hfU u hu, hW'⟩
      rw [hUW, Submodule.mem_bot] at this
      exact hfu0 this
    · rw [Fin.range_cons, Submodule.span_insert, hspan]
      intro hmem
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have hzU : z ∈ U := by
        rw [eq_sub_of_add_eq' hyz]
        exact U.sub_mem hu (U.smul_mem c (hfU u hu))
      have hz0 : z = 0 := by
        have : z ∈ U ⊓ W := ⟨hzU, hz⟩
        rwa [hUW, Submodule.mem_bot] at this
      rw [hz0, add_zero] at hyz
      rcases eq_zero_or_eq_one_of_card hK c with hc | hc
      · rw [hc, zero_smul] at hyz
        exact hu0 hyz.symm
      · rw [hc, one_smul] at hyz
        exact hu0 (hfp u hu hyz)
  have hcard : Fintype.card (Fin (m + 2)) = finrank K (Fin (m + 2) → K) := by
    rw [Module.finrank_fin_fun, Fintype.card_fin]
  let bb : Basis (Fin (m + 2)) K (Fin (m + 2) → K) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbb : ∀ i, bb i = v i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  set e := Pi.basisFun K (Fin (m + 2)) with he
  have hmat : LinearMap.toMatrix bb bb f = (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) := by
    have h01 := fin_zero_ne_one' (m := m)
    ext i j
    rw [LinearMap.toMatrix_apply, coe_g0_apply']
    refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun k => ?_) j') j
    · have h1 : f (bb 0) = bb 1 := by
        rw [hbb, hbb]
        rfl
      rw [h1, Basis.repr_self, Finsupp.single_apply]
      by_cases hi : i = 1
      · subst hi
        simp
      · simp [hi, Ne.symm hi]
    · have h1 : f (bb 1) = bb 0 + bb 1 := by
        simp only [hbb]
        exact hf2 u hu
      rw [Fin.succ_zero_eq_one, h1, map_add, Basis.repr_self, Basis.repr_self,
        Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hi0 : i = 0
      · subst hi0
        simp [h01, Ne.symm h01]
      · by_cases hi1 : i = 1
        · subst hi1
          simp [h01, Ne.symm h01]
        · simp [hi0, hi1, Ne.symm hi0, Ne.symm hi1, Ne.symm h01]
    · have h1 : f (bb k.succ.succ) = bb k.succ.succ := by
        rw [hbb]
        exact (hmemW _).mp (wb k).2
      have hne0 : (k.succ.succ : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (k.succ.succ : Fin (m + 2)) ≠ 1 := by
        intro h
        exact Fin.succ_ne_zero k (Fin.succ_injective _ (h.trans Fin.succ_zero_eq_one.symm))
      rw [h1, Basis.repr_self, Finsupp.single_apply, ite_eq_right hne0, ite_eq_right hne1]
      by_cases hi : i = k.succ.succ
      · subst hi
        simp
      · simp [hi, Ne.symm hi]
  have hfe : LinearMap.toMatrix e e f = g := by
    rw [he, LinearMap.toMatrix_eq_toMatrix', hf]
    exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' g
  have hconj := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := bb) (c := bb)
    (b' := e) (c' := e) f
  rw [hfe, hmat] at hconj
  refine ⟨⟨bb.toMatrix e, e.toMatrix bb, bb.toMatrix_mul_toMatrix_flip e,
    e.toMatrix_mul_toMatrix_flip bb⟩, ?_⟩
  exact hconj

end CFSG.StandardType.TwoThree
