module

public import CFSG.RankThree.PartOne.K133C.FixedVectors
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.RankThree.PartOne.K133C.SpForm

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

set_option linter.unusedSectionVars false

section Standard

variable {r : ℕ} {K : Type} [Field K]

theorem formJ_transpose_two [CharP K 2] : (formJ r K)ᵀ = formJ r K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [formJ, Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

theorem formJ_alt (y : Fin r ⊕ Fin r → K) : y ⬝ᵥ (formJ r K *ᵥ y) = 0 :=
  CFSG.RankThree.Classical.SteinbergBY.spForm_self y

theorem formJ_nondeg (w : Fin r ⊕ Fin r → K) (h : formJ r K *ᵥ w = 0) : w = 0 := by
  rw [CFSG.RankThree.Classical.SteinbergBY.formJ_mulVec] at h
  funext i
  rcases i with i | i
  · have := congrFun h (Sum.inr i)
    simpa using this
  · have := congrFun h (Sum.inl i)
    simpa using this

theorem mem_statedSp_iff_isoGrp {g : GL (Fin r ⊕ Fin r) K} :
    g ∈ StatedSp r K ↔ g ∈ isoGrp (formJ r K) :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff

end Standard

section Descent

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem vmap_mulVec (σ : K ≃+* K) (A : Matrix ι ι K) (v : ι → K) :
    vmap σ (A *ᵥ v) = (A.map σ) *ᵥ (vmap σ v) := by
  funext i
  exact RingHom.map_mulVec (σ : K →+* K) A v i

theorem trvM_map (J : Matrix ι ι K) (σ : K ≃+* K) (hσJ : J.map σ = J) (v : ι → K) (a : K) :
    (trvM J v a).map σ = trvM J (vmap σ v) (σ a) := by
  ext i j
  have h1 : σ ((J *ᵥ v) j) = (J *ᵥ vmap σ v) j := by
    have := congrFun (vmap_mulVec σ J v) j
    rw [hσJ] at this
    exact this
  simp only [trvM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, map_add, map_mul, h1]
  by_cases hij : i = j
  · subst hij
    simp [vmap]
  · simp [hij, vmap]

end Descent

section Transvections

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι K)
  (hJa : ∀ y : ι → K, y ⬝ᵥ (J *ᵥ y) = 0)

@[expose] def trvHom (v : ι → K) : Multiplicative K →* GL ι K where
  toFun a := trvGL J hJa v (Multiplicative.toAdd a)
  map_one' := trvGL_zero J hJa v
  map_mul' a b := trvGL_add J hJa v (Multiplicative.toAdd a) (Multiplicative.toAdd b)

@[expose] def trvSub (v : ι → K) : Subgroup (GL ι K) := (trvHom J hJa v).range

theorem mem_trvSub {v : ι → K} {g : GL ι K} :
    g ∈ trvSub J hJa v ↔ ∃ a : K, trvGL J hJa v a = g :=
  ⟨fun ⟨a, ha⟩ => ⟨Multiplicative.toAdd a, ha⟩, fun ⟨a, ha⟩ => ⟨Multiplicative.ofAdd a, ha⟩⟩

theorem trvGL_mem_trvSub (v : ι → K) (a : K) : trvGL J hJa v a ∈ trvSub J hJa v :=
  (mem_trvSub J hJa).2 ⟨a, rfl⟩

theorem trvSub_sq {v : ι → K} {g : GL ι K} (hg : g ∈ trvSub J hJa v) : g * g = 1 := by
  obtain ⟨a, rfl⟩ := (mem_trvSub J hJa).1 hg
  exact trvGL_sq J hJa v a

end Transvections

end CFSG.RankThree.PartOne.K133C
