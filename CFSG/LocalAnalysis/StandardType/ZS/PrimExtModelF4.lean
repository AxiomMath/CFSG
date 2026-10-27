module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelF4Data

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def f45MatFun {K : Type} [Field K] : Fin 4 → Matrix (Fin 5) (Fin 5) K :=
  ![Matrix.blockSucc (diagSignMat 0), Matrix.blockSucc (pijMat 0 1 1),
    Matrix.blockSucc (pijMat 1 2 1), Matrix.blockSucc (halfOnesMat 4)]

theorem range_f45MatFun {K : Type} [Field K] : Set.range (f45MatFun (K := K)) = f4ExtMats := by
  ext M
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨diagSignMat 0, by simp [weylF4Mats], rfl⟩
    · exact ⟨pijMat 0 1 1, by simp [weylF4Mats], rfl⟩
    · exact ⟨pijMat 1 2 1, by simp [weylF4Mats], rfl⟩
    · exact ⟨halfOnesMat 4, by simp [weylF4Mats], rfl⟩
  · rintro ⟨N, hN, rfl⟩
    simp only [weylF4Mats, Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem evMat_f45G (hp : p ≠ 2) (k : Fin 4) :
    evMat (Int.castRingHom (ZMod p)) 1 (f45G k) = f45MatFun k := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa using intCast_ne_zero_of_goodZ hp (show GoodZ 2 by norm_num [GoodZ])
  fin_cases k <;>
    ext i j <;>
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp [f45MatFun]
          rw [show (4 : Fin 5) = Fin.last 4 from rfl]
          rw [Matrix.blockSucc_last_last]
          simp [f45G, evMat]
          field_simp [h2]
        | cast j =>
          simp [f45MatFun]
          rw [show (4 : Fin 5) = Fin.last 4 from rfl]
          rw [Matrix.blockSucc_last_castSucc]
          fin_cases j <;> simp [f45G, evMat]
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp [f45MatFun]
          rw [show (4 : Fin 5) = Fin.last 4 from rfl]
          rw [Matrix.blockSucc_castSucc_last]
          fin_cases i <;> simp [f45G, evMat]
        | cast j =>
          simp [f45MatFun]
          fin_cases i <;> fin_cases j <;>
            simp [f45G, evMat, halfOnesMat, diagSignMat, pijMat] <;>
            field_simp [h2] <;> ring

theorem f45_basisClosure_eq (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) :
    basisClosure f f4ExtMats = f45Tab.group (Int.castRingHom (ZMod p)) f := by
  rw [← range_f45MatFun]
  exact ReflTable.basisClosure_eq_group (T := f45Tab) (φ := Int.castRingHom (ZMod p))
    (f := f) (good := GoodZ) (M := f45MatFun) f45Tab_valid hp
    (fun k => by rw [f45Tab_gen k, evMat_f45G hp k])

theorem f45_transvectionFree (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) :
    QTwoLin.TransvectionFree (f45Tab.group (Int.castRingHom (ZMod p)) f) := by
  exact ReflTable.transvectionFree_group (T := f45Tab) (φ := Int.castRingHom (ZMod p))
    (f := f) (good := GoodZ) f45Tab_valid (fun x hx => intCast_ne_zero_of_goodZ hp hx)
    hp f45D f45D_good f45Tab_form

end CFSG.StandardType.ZS.PrimModel

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime]

private theorem f45_exists_conj_le_inf_ker {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∀ x ∈ basisClosure f f4ExtMats, IsRefl p x →
      HardMathSupport.Kantor79.movedSpace x ≤
        Submodule.span (ZMod p) (f '' ↑({0, 1, 2} : Finset (Fin 5))) →
      ∃ g ∈ basisClosure f f4ExtMats,
        HardMathSupport.Kantor79.movedSpace
            (g * PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 * g⁻¹) ≤
          Submodule.span (ZMod p) (f '' ↑({0, 1, 2} : Finset (Fin 5))) ⊓
            LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  have hgood : ∀ x, PrimModel.GoodZ x → Int.castRingHom (ZMod p) x ≠ 0 :=
    fun x hx => PrimModel.intCast_ne_zero_of_goodZ hp hx
  intro x hx hxr hm
  have hx' : x ∈ PrimModel.f45Tab.group (Int.castRingHom (ZMod p)) f := by
    rwa [PrimModel.f45_basisClosure_eq hp f] at hx
  obtain ⟨g, hg, hg'⟩ := PrimModel.ReflTable.exists_conj_le_inf_ker
    (T := PrimModel.f45Tab) (φ := Int.castRingHom (ZMod p)) (f := f) (good := PrimModel.GoodZ)
    PrimModel.f45Tab_valid hgood hp (PrimModel.f45_transvectionFree hp f)
    ({0, 1, 2} : Finset (Fin 5)) 0 PrimModel.f45Wit PrimModel.f45Tab_wit x hx' hxr hm
  exact ⟨g, by rwa [PrimModel.f45_basisClosure_eq hp f], hg'⟩

private theorem f45_toMatrix_z {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) :
    LinearMap.toMatrix f f
      (PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 *
       PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 1 *
       PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 3 : U ≃ₗ[ZMod p] U) =
      Matrix.diagonal (fun i => if i ∈ ({0, 1, 2} : Finset (Fin 5)) then -1 else 1) := by
  obtain ⟨h0, h1, h3, _⟩ := PrimModel.f45Tab_diag
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
    LinearMap.toMatrix_mul, LinearMap.toMatrix_mul,
    PrimModel.ReflTable.toMatrix_refl PrimModel.f45Tab_valid hp 0,
    PrimModel.ReflTable.toMatrix_refl PrimModel.f45Tab_valid hp 1,
    PrimModel.ReflTable.toMatrix_refl PrimModel.f45Tab_valid hp 3,
    h0, h1, h3, PrimModel.evMat_diagZ hp (Int.castRingHom (ZMod p)) 0,
    PrimModel.evMat_diagZ hp (Int.castRingHom (ZMod p)) 1,
    PrimModel.evMat_diagZ hp (Int.castRingHom (ZMod p)) 2,
    PrimModel.diagSignMat_mul_diagSignMat_mul_diagSignMat (by decide) (by decide)
      (by decide)]

private theorem f45_primFrameData_refl {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) :
    PrimFrameData p (basisClosure f f4ExtMats)
      (PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0)
      (PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 *
        PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 1 *
        PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 3)
      (PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 11) := by
  obtain ⟨h0, _, _, h11⟩ := PrimModel.f45Tab_diag
  have hh₁T : LinearMap.toMatrix f f
      (PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 : U →ₗ[ZMod p] U) =
      diagSignMat (0 : Fin 5) := by
    rw [PrimModel.ReflTable.toMatrix_refl PrimModel.f45Tab_valid hp 0, h0,
      PrimModel.evMat_diagZ hp (Int.castRingHom (ZMod p)) 0]
  have hτT : LinearMap.toMatrix f f
      (PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 11 : U →ₗ[ZMod p] U) =
      diagSignMat (3 : Fin 5) := by
    rw [PrimModel.ReflTable.toMatrix_refl PrimModel.f45Tab_valid hp 11, h11,
      PrimModel.evMat_diagZ hp (Int.castRingHom (ZMod p)) 3]
  have hzG : PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 *
      PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 1 *
      PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 3 ∈ basisClosure f f4ExtMats := by
    rw [PrimModel.f45_basisClosure_eq hp f]
    exact mul_mem (mul_mem
      (PrimModel.ReflTable.refl_mem_group PrimModel.f45Tab_valid hp 0)
      (PrimModel.ReflTable.refl_mem_group PrimModel.f45Tab_valid hp 1))
      (PrimModel.ReflTable.refl_mem_group PrimModel.f45Tab_valid hp 3)
  have hh₁G : PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 ∈
      basisClosure f f4ExtMats := by
    rw [PrimModel.f45_basisClosure_eq hp f]
    exact PrimModel.ReflTable.refl_mem_group PrimModel.f45Tab_valid hp 0
  have hτG : ∃ g ∈ basisClosure f f4ExtMats,
      PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 11 =
        g * PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 * g⁻¹ := by
    obtain ⟨g, hg, hg'⟩ := PrimModel.ReflTable.exists_conj_of_cls_eq
      (T := PrimModel.f45Tab) (φ := Int.castRingHom (ZMod p)) (f := f) (j := 0) (j' := 11)
      PrimModel.f45Tab_valid hp (by decide)
    exact ⟨g, by rwa [PrimModel.f45_basisClosure_eq hp f], hg'⟩
  exact PrimModel.primFrameData_of_diagonal hp f ({0, 1, 2} : Finset (Fin 5))
    (by decide) (by decide) (by decide) (f45_toMatrix_z hp f) hh₁T hτT hzG hh₁G hτG
    (f45_exists_conj_le_inf_ker hp f)

theorem tfF4Model_holds : TFF4Model p := by
  intro W _ _ f hp _ h₁ z τ hh₁ hz hτ
  have hh₁' : h₁ = PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 := by
    apply PrimModel.eq_of_toMatrix_eq
    rw [hh₁, PrimModel.ReflTable.toMatrix_refl PrimModel.f45Tab_valid hp 0,
      PrimModel.f45Tab_diag.1, PrimModel.evMat_diagZ hp (Int.castRingHom (ZMod p)) 0]
  have hτ' : τ = PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 11 := by
    apply PrimModel.eq_of_toMatrix_eq
    rw [hτ, PrimModel.ReflTable.toMatrix_refl PrimModel.f45Tab_valid hp 11,
      PrimModel.f45Tab_diag.2.2.2, PrimModel.evMat_diagZ hp (Int.castRingHom (ZMod p)) 3]
  have hz' : z = PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 0 *
      PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 1 *
      PrimModel.f45Tab.refl (Int.castRingHom (ZMod p)) f 3 := by
    apply PrimModel.eq_of_toMatrix_eq
    rw [hz, f45_toMatrix_z hp f,
      PrimModel.diagSignMat_mul_diagSignMat_mul_diagSignMat (by decide) (by decide) (by decide)]
  rw [hh₁', hz', hτ']
  exact f45_primFrameData_refl hp f

end CFSG.StandardType.ZS

end
