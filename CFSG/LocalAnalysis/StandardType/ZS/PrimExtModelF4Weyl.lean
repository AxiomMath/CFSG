module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelF4Data
import CFSG.LocalAnalysis.StandardType.GGResIWStar

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def f44MatFun {K : Type} [Field K] : Fin 4 → Matrix (Fin 4) (Fin 4) K :=
  ![halfOnesMat 4, diagSignMat 0, pijMat 0 1 1, pijMat 1 2 1]

theorem range_f44MatFun {K : Type} [Field K] : Set.range (f44MatFun (K := K)) = weylF4Mats := by
  ext M
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [f44MatFun, weylF4Mats]
  · intro hM
    simp only [weylF4Mats, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨0, rfl⟩

theorem f44Cartan_eq : f44Cartan = CartanMatrix.F₄ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem evMat_f44G (hp : p ≠ 2) (k : Fin 4) :
    evMat (Int.castRingHom (ZMod p)) 1 (f44G k) = f44MatFun k := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa using intCast_ne_zero_of_goodZ hp (show GoodZ 2 by norm_num [GoodZ])
  fin_cases k <;>
    ext i j <;>
      fin_cases i <;> fin_cases j <;>
        simp [f44G, f44MatFun, evMat, halfOnesMat, pijMat, diagSignMat] <;>
        (try field_simp [h2]) <;> ring

theorem f44_basisClosure_eq (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    basisClosure f weylF4Mats = f44Tab.group (Int.castRingHom (ZMod p)) f := by
  rw [← range_f44MatFun]
  exact ReflTable.basisClosure_eq_group (T := f44Tab) (φ := Int.castRingHom (ZMod p))
    (f := f) (good := GoodZ) (M := f44MatFun) f44Tab_valid hp
    (fun k => by rw [f44Tab_gen k, evMat_f44G hp k])

theorem linWeyl_basisClosure_weylF4Mats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    LinWeyl p (basisClosure f weylF4Mats) := by
  rw [f44_basisClosure_eq hp f]
  obtain ⟨M, hW, hC⟩ := ggWCartanI_spec .F 4 rfl
  have hCF : ggWCartanI .F 4 = f44Cartan := by
    rw [f44Cartan_eq]
    simp only [ggWCartanI]
    rfl
  have hC' : GGIntCartan M f44Cartan := by
    rwa [← hCF]
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa using intCast_ne_zero_of_goodZ hp (show GoodZ 2 by norm_num [GoodZ])
  refine ggResI_linWeyl_T (C := f44Cartan) hp hW hC'
    (fun k => f44Tab.refl (Int.castRingHom (ZMod p)) f (f44Tab.gen k))
    (fun k => f44Tab.vecU (Int.castRingHom (ZMod p)) f (f44Tab.gen k))
    (fun k => f44Tab.covecU (Int.castRingHom (ZMod p)) f (f44Tab.gen k)) ?_ ?_ ?_
  · intro i w
    exact ReflTable.refl_apply (T := f44Tab) (φ := Int.castRingHom (ZMod p)) (f := f)
      (good := GoodZ) f44Tab_valid hp (f44Tab.gen i) w
  · intro i j
    rw [ReflTable.covecU, ReflTable.vecU, covecR_vecR, f44_cartan i j]
    rw [show Int.castRingHom (ZMod p) (2 * f44Cartan i j) =
        (2 : ZMod p) * (f44Cartan i j : ZMod p) by
      rw [map_mul]; norm_num]
    rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  · have hspan : ⊤ ≤ Submodule.span (ZMod p)
        (Set.range fun k => f44Tab.vecU (Int.castRingHom (ZMod p)) f (f44Tab.gen k)) := by
      rw [← f.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_sum_smul_eq hp (Int.castRingHom (ZMod p)) f (f44Span l) l (f44_span l)
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by
      rw [Module.finrank_eq_card_basis f])

end CFSG.StandardType.ZS.PrimModel

end
