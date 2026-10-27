module

public import CFSG.RankThree.CentralLiftU.HypBlock
public import CFSG.RankThree.CentralLiftU.HyperbolicSpecialLinear

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section Index

@[expose] def pairIdx (i : Fin r) : Fin 2 → HypIndex r ε := ![.inl i, .inr (.inr i)]

@[expose] def quadIdx (i j : Fin r) : Fin 2 ⊕ Fin 2 → HypIndex r ε :=
  Sum.elim ![.inl i, .inl j] ![.inr (.inr i), .inr (.inr j)]

@[expose] def tripIdx (i : Fin r) : Fin 3 → HypIndex r 1 := ![.inl i, .inr (.inl 0), .inr (.inr i)]

theorem pairIdx_injective (i : Fin r) : Function.Injective (pairIdx (ε := ε) i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [pairIdx]

theorem quadIdx_injective {i j : Fin r} (hij : i ≠ j) :
    Function.Injective (quadIdx (ε := ε) i j) := by
  rintro (a | a) (b | b) hab <;> fin_cases a <;> fin_cases b <;>
    simp_all [quadIdx, Ne.symm hij]

theorem tripIdx_injective (i : Fin r) : Function.Injective (tripIdx i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [tripIdx]

theorem pairIdx_closed (i : Fin r) : PartnerClosed (pairIdx (ε := ε) i) := by
  intro a
  fin_cases a
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem quadIdx_closed (i j : Fin r) : PartnerClosed (quadIdx (ε := ε) i j) := by
  rintro (a | a) <;> fin_cases a
  · exact ⟨.inr 0, rfl⟩
  · exact ⟨.inr 1, rfl⟩
  · exact ⟨.inl 0, rfl⟩
  · exact ⟨.inl 1, rfl⟩

theorem tripIdx_closed (i : Fin r) : PartnerClosed (tripIdx i) := by
  intro a
  fin_cases a
  · exact ⟨2, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem restrGram_pairIdx (i : Fin r) :
    restrGram K (pairIdx (ε := ε) i) = hypGramTwo K := by
  ext a b
  rw [restrGram_apply]
  fin_cases a <;> fin_cases b <;> simp [pairIdx, hypGramTwo]

@[expose] def quadGram (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks 0 1 1 0

theorem restrGram_quadIdx {i j : Fin r} (hij : i ≠ j) :
    restrGram K (quadIdx (ε := ε) i j) = quadGram K := by
  ext a b
  rw [restrGram_apply]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [quadIdx, quadGram, Ne.symm hij, hij, one_apply]

@[expose] def gramJ3 (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem restrGram_tripIdx (i : Fin r) : restrGram K (tripIdx i) = gramJ3 K := by
  ext a b
  rw [restrGram_apply]
  fin_cases a <;> fin_cases b <;> simp [tripIdx, gramJ3]

end Index

section Rho

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def rho4Mat (g : SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (g : Matrix (Fin 2) (Fin 2) K) 0 0
    (((adjugate (g : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ)

theorem rho4Mat_mul (g g' : SpecialLinearGroup (Fin 2) K) :
    rho4Mat h (g * g') = rho4Mat h g * rho4Mat h g' := by
  simp only [rho4Mat, fromBlocks_multiply, Matrix.SpecialLinearGroup.coe_mul, adjugate_mul_distrib,
    Matrix.map_mul, transpose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem rho4Mat_one : rho4Mat h 1 = 1 := by
  simp only [rho4Mat, Matrix.SpecialLinearGroup.coe_one, adjugate_one,
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, fromBlocks_one]

theorem det_rho4Mat (g : SpecialLinearGroup (Fin 2) K) : (rho4Mat h g).det = 1 := by
  have hg : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
  have hmap : ((adjugate (g : Matrix (Fin 2) (Fin 2) K)).map h.bar).det =
      h.bar (adjugate (g : Matrix (Fin 2) (Fin 2) K)).det :=
    (RingHom.map_det h.bar _).symm
  rw [rho4Mat, det_fromBlocks_zero₂₁, det_transpose, hmap, det_adjugate, hg, one_pow, map_one,
    mul_one]

theorem rho4Mat_isometry (g : SpecialLinearGroup (Fin 2) K) :
    ((rho4Mat h g).map h.bar)ᵀ * quadGram K * rho4Mat h g = quadGram K := by
  have hg : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
  have hbb : ∀ M : Matrix (Fin 2) (Fin 2) K, (M.map h.bar).map h.bar = M := fun M => by
    ext a b; simp [h.bar_bar]
  have h1 : adjugate (g : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [adjugate_mul, hg, one_smul]
  have h2 : ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
      (((adjugate (g : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ) = 1 := by
    rw [← transpose_mul, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _),
      transpose_one]
  rw [rho4Mat, quadGram, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.map_zero _ (map_zero h.bar), transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, transpose_map,
    transpose_transpose, hbb, h1, h2]

@[expose] noncomputable def rho4 : SpecialLinearGroup (Fin 2) K →* gramSU h (quadGram K) where
  toFun g := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rho4Mat h g)
      (by rw [det_rho4Mat]; exact one_ne_zero),
    by rw [mem_gramSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
       exact ⟨rho4Mat_isometry h g, det_rho4Mat h g⟩⟩
  map_one' := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, rho4Mat_one]; rfl))
  map_mul' g g' := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, rho4Mat_mul]; rfl))

theorem coe_rho4 (g : SpecialLinearGroup (Fin 2) K) :
    ((rho4 h g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      rho4Mat h g :=
  rfl

@[expose] noncomputable def rhoU {i j : Fin r} (hij : i ≠ j) :
    SpecialLinearGroup (Fin 2) K →* hypSU h r ε :=
  (blockHom h (quadIdx_injective hij) (quadIdx_closed i j) (restrGram_quadIdx hij)).comp (rho4 h)

theorem coe_rhoU {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) K) :
    ((rhoU (ε := ε) h hij g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blockMat (quadIdx i j) (rho4Mat h g) :=
  rfl

theorem rhoU_injective {i j : Fin r} (hij : i ≠ j) :
    Function.Injective (rhoU (ε := ε) h hij) := by
  intro g g' hgg'
  have h1 := blockHom_injective h (quadIdx_injective (ε := ε) hij) (quadIdx_closed i j)
    (restrGram_quadIdx hij) hgg'
  have h2 := congrArg (fun x : gramSU h (quadGram K) =>
    (((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).toBlocks₁₁) h1
  simp only [coe_rho4, rho4Mat, toBlocks_fromBlocks₁₁] at h2
  exact Subtype.ext h2

end Rho

section Iota

variable (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

@[expose] noncomputable def iotaU (i : Fin r) :
    SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε :=
  (blockHom h (pairIdx_injective i) (pairIdx_closed i) (restrGram_pairIdx i)).comp
    (hypSLEquiv hc hc0).symm.toMonoidHom

theorem coe_iotaU (i : Fin r) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((iotaU (ε := ε) h hc hc0 i g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blockMat (pairIdx i) !![((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K),
          c⁻¹ * ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K);
        c * ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K),
          ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K)] := by
  rw [iotaU, MonoidHom.comp_apply, coe_blockHom]
  congr 1

theorem iotaU_injective (i : Fin r) : Function.Injective (iotaU (ε := ε) h hc hc0 i) :=
  (blockHom_injective h (pairIdx_injective i) (pairIdx_closed i) (restrGram_pairIdx i)).comp
    (hypSLEquiv hc hc0).symm.injective

end Iota

section Kappa

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def kappaU (i : Fin r) : gramSU h (gramJ3 K) →* hypSU h r 1 :=
  blockHom h (tripIdx_injective i) (tripIdx_closed i) (restrGram_tripIdx i)

theorem coe_kappaU (i : Fin r) (g : gramSU h (gramJ3 K)) :
    ((kappaU h i g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      blockMat (tripIdx i) ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem kappaU_injective (i : Fin r) : Function.Injective (kappaU h (r := r) i) :=
  blockHom_injective h (tripIdx_injective i) (tripIdx_closed i) (restrGram_tripIdx i)

end Kappa

end CFSG.RankThree.CentralLiftU
