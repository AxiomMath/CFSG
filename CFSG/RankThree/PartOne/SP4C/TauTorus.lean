module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.RankThree.PartOne.KF.SpSylow

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauEquiv tauAut tauAut_proj tauMat_apply
  tauPair_ι₀ tauPair_ι₁ tauPair_ι₂ tauPair_ι₃)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def tpt (a b : Kˣ) : ↥(spRev K) :=
  ⟨diagU (dvec4 a b), diagU_dvec4_mem_spRev a b⟩

@[expose] noncomputable def tauRev : ↥(spRev K) ≃* ↥(spRev K) :=
  (spRevEquiv K).symm.trans (tauEquiv.trans (spRevEquiv K))

@[expose] noncomputable def fieldRev (σ : K ≃+* K) : ↥(spRev K) ≃* ↥(spRev K) :=
  (spRevEquiv K).symm.trans ((fieldSp 2 K σ).trans (spRevEquiv K))

omit [Finite K] [CharP K 2] in
theorem symm_matrix (t : ↥(spRev K)) (i j : Fin 2 ⊕ Fin 2) :
    ((((spRevEquiv K).symm t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i j =
    ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (spIdx i) (spIdx j) := rfl

omit [Finite K] [CharP K 2] in
theorem spIdx_inl0 : spIdx (Sum.inl 0 : Fin 2 ⊕ Fin 2) = 0 := rfl
omit [Finite K] [CharP K 2] in
theorem spIdx_inl1 : spIdx (Sum.inl 1 : Fin 2 ⊕ Fin 2) = 1 := rfl
omit [Finite K] [CharP K 2] in
theorem spIdx_inr0 : spIdx (Sum.inr 0 : Fin 2 ⊕ Fin 2) = 3 := rfl
omit [Finite K] [CharP K 2] in
theorem spIdx_inr1 : spIdx (Sum.inr 1 : Fin 2 ⊕ Fin 2) = 2 := rfl

theorem symm_tauRev (t : ↥(spRev K)) :
    (spRevEquiv K).symm (tauRev t) = tauEquiv ((spRevEquiv K).symm t) := by
  simp [tauRev]

omit [Finite K] [CharP K 2] in
theorem symm_fieldRev (σ : K ≃+* K) (t : ↥(spRev K)) :
    (spRevEquiv K).symm (fieldRev σ t) = fieldSp 2 K σ ((spRevEquiv K).symm t) := by
  simp [fieldRev]

omit [Finite K] in
theorem tpt_symm_matrix (a b : Kˣ) (i j : Fin 2 ⊕ Fin 2) :
    ((((spRevEquiv K).symm (tpt a b) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i j =
    if spIdx i = spIdx j then (dvec4 a b (spIdx i) : K) else 0 := by
  rw [symm_matrix]
  simp only [tpt, diagU_val, Matrix.diagonal_apply]

theorem tauRev_tpt (a b : Kˣ) : tauRev (tpt a b) = tpt (a * b) (a * b⁻¹) := by
  apply (spRevEquiv K).symm.injective
  rw [symm_tauRev]
  have h1 : (tauEquiv ((spRevEquiv K).symm (tpt a b)) : StatedSp 2 K) =
      tauSp ((spRevEquiv K).symm (tpt a b)) := rfl
  rw [h1]
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp]
  ext r c
  rw [tauMat_apply]
  fin_cases r <;> fin_cases c <;>
    simp [tpt_symm_matrix, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, spIdx_inl0, spIdx_inl1,
      spIdx_inr0, spIdx_inr1, dvec4, mul_comm]

omit [Finite K] in
theorem fieldRev_tpt (σ : K ≃+* K) (a b : Kˣ) :
    fieldRev σ (tpt a b) = tpt (Units.map (σ : K →* K) a) (Units.map (σ : K →* K) b) := by
  apply (spRevEquiv K).symm.injective
  rw [symm_fieldRev]
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp]
  ext r c
  have key : ∀ i : Fin 4, ((dvec4 (Units.map (σ : K →* K) a) (Units.map (σ : K →* K) b) i : Kˣ) :
      K) = σ ((dvec4 a b i : Kˣ) : K) := by
    intro i
    fin_cases i <;> simp [dvec4]
  simp only [Matrix.map_apply, tpt_symm_matrix]
  by_cases h : spIdx r = spIdx c
  · simp [h, key]
  · simp [h]

section Torus

variable {p : ℕ}

@[expose] noncomputable def torC (p : ℕ) (K : Type) [Field K] [CharP K 2] :
    D8Mod p K →* ↥(spRev K) :=
  (spDiag K).comp ((rootsOfUnity p K).subtype.prodMap (rootsOfUnity p K).subtype)

omit [Finite K] in
theorem torC_apply (v : D8Mod p K) :
    torC p K v = tpt ((v.1 : rootsOfUnity p K) : Kˣ) ((v.2 : rootsOfUnity p K) : Kˣ) := rfl

omit [Finite K] in
theorem coe_torC (v : D8Mod p K) :
    ((torC p K v : ↥(spRev K)) : GL (Fin 4) K) = diagU (d8Vec 4 v) := by
  rw [torC_apply, d8Vec_four]
  rfl

omit [Finite K] in
theorem torC_injective : Function.Injective (torC p K) := by
  intro v w h
  have h1 := spDiag_injective (K := K) h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h1)) (Subtype.ext (congrArg Prod.snd h1))

@[expose] def Mvec (p : ℕ) (K : Type) [Field K] : D8Mod p K →* D8Mod p K where
  toFun v := (v.1 * v.2, v.1 * v.2⁻¹)
  map_one' := by simp
  map_mul' v w := by
    refine Prod.ext ?_ ?_
    · show v.1 * w.1 * (v.2 * w.2) = v.1 * v.2 * (w.1 * w.2)
      exact mul_mul_mul_comm _ _ _ _
    · show v.1 * w.1 * (v.2 * w.2)⁻¹ = v.1 * v.2⁻¹ * (w.1 * w.2⁻¹)
      rw [_root_.mul_inv_rev]
      ac_rfl

theorem tauRev_torC (v : D8Mod p K) : tauRev (torC p K v) = torC p K (Mvec p K v) := by
  rw [torC_apply, tauRev_tpt]
  rfl

@[expose] noncomputable def sigVec (σ : K ≃+* K) : D8Mod p K →* D8Mod p K :=
  (restrictRootsOfUnity σ p).prodMap (restrictRootsOfUnity σ p)

omit [Finite K] in
theorem fieldRev_torC (σ : K ≃+* K) (v : D8Mod p K) :
    fieldRev σ (torC p K v) = torC p K (sigVec σ v) := by
  rw [torC_apply, fieldRev_tpt]
  rfl

end Torus

end CFSG.RankThree.PartOne.SP4C
