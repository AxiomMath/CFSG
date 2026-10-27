module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem minorMap_map {K L : Type} [Field K] [Field L] (f : K →+* L)
    (M : Matrix (Fin 4) (Fin 4) K) : minorMap (M.map f) = (minorMap M).map f := by
  ext a b
  simp only [Matrix.map_apply, minorMap_apply, map_sub, map_mul]

theorem mem_antiSp_of_map_mem {K L : Type} [Field K] [Field L] (f : K →+* L) {g : GL (Fin 4) K}
    (hg : GeneralLinearGroup.map f g ∈ antiSp L) : g ∈ antiSp K := by
  rw [mem_antiSp] at hg ⊢
  apply Matrix.map_injective f.injective
  beta_reduce
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, minorJ_map]
  exact hg

section Frobenius

variable (k : Type) [Field k] [CharP k 2]

theorem eq_one_of_mul_self_eq_one (a : k) (h : a * a = 1) : a = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have : (a - 1) ^ 2 = 0 := by linear_combination h + (1 - a) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 this)

theorem det_glMat_eq_one {g : GL (Fin 4) k} (hg : g ∈ antiSp k) : (glMat g).det = 1 := by
  have hJ : (minorJ k).det = 1 := eq_one_of_mul_self_eq_one k _ (by
    rw [← det_mul, minorJ_mul_self, det_one])
  have h := congrArg Matrix.det (mem_antiSp.mp hg)
  rw [det_mul, det_mul, det_transpose, hJ, mul_one] at h
  exact eq_one_of_mul_self_eq_one k _ h

@[expose] def frobPow (b : ℕ) : antiSp k →* antiSp k :=
  ((GeneralLinearGroup.map (iterateFrobenius k 2 b)).comp (antiSp k).subtype).codRestrict
    (antiSp k) fun g => by
      rw [mem_antiSp]
      change ((glMat g).map (iterateFrobenius k 2 b))ᵀ * minorJ k *
        (glMat g).map (iterateFrobenius k 2 b) = minorJ k
      rw [← minorJ_map (iterateFrobenius k 2 b), ← transpose_map, ← Matrix.map_mul,
        ← Matrix.map_mul, mem_antiSp.mp g.2]

theorem glMat_frobPow (b : ℕ) (g : antiSp k) :
    glMat (frobPow k b g : GL (Fin 4) k) = (glMat (g : GL (Fin 4) k)).map fun x => x ^ 2 ^ b :=
  rfl

theorem frobPow_injective (b : ℕ) : Function.Injective (frobPow k b) := by
  intro g h hgh
  have h1 := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) hgh
  simp only [glMat_frobPow] at h1
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have h2 := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at h2
  exact (iterateFrobenius k 2 b).injective h2

theorem frobPow_surjective [IsAlgClosed k] (b : ℕ) : Function.Surjective (frobPow k b) := by
  have hbij : Function.Bijective (iterateFrobenius k 2 b) :=
    ⟨(iterateFrobenius k 2 b).injective, fun x => by
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x (pow_pos two_pos b)
      exact ⟨y, hy⟩⟩
  let φ : k ≃+* k := RingEquiv.ofBijective (iterateFrobenius k 2 b) hbij
  rintro ⟨h, hh⟩
  let g₀ : GL (Fin 4) k := GeneralLinearGroup.map (φ.symm : k →+* k) h
  have hg₀h : GeneralLinearGroup.map (iterateFrobenius k 2 b) g₀ = h :=
    Matrix.GeneralLinearGroup.ext fun i j => φ.apply_symm_apply _
  have hg₀ : g₀ ∈ antiSp k := by
    refine mem_antiSp_of_map_mem (iterateFrobenius k 2 b) ?_
    rw [hg₀h]
    exact hh
  exact ⟨⟨g₀, hg₀⟩, Subtype.ext (Units.ext (Matrix.ext fun i j => φ.apply_symm_apply _))⟩

@[expose] def suzukiMap (b : ℕ) : antiSp k →* antiSp k := (frobPow k b).comp (minorHom k)

theorem glMat_suzukiMap (b : ℕ) (g : antiSp k) :
    glMat (suzukiMap k b g : GL (Fin 4) k) =
      (minorMap (glMat (g : GL (Fin 4) k))).map fun x => x ^ 2 ^ b :=
  rfl

theorem suzukiMap_comp_self (b : ℕ) (g : antiSp k) :
    suzukiMap k b (suzukiMap k b g) = frobPow k (2 * b + 1) g := by
  have h1 := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) (minorHom_minorHom g)
  simp only [glMat_minorHom, glMat_frobHom] at h1
  refine Subtype.ext (Units.ext ?_)
  change glMat (suzukiMap k b (suzukiMap k b g) : GL (Fin 4) k) =
    glMat (frobPow k (2 * b + 1) g : GL (Fin 4) k)
  rw [glMat_suzukiMap, glMat_suzukiMap, glMat_frobPow]
  have hf : (fun x : k => x ^ 2 ^ b) = ⇑(iterateFrobenius k 2 b) := rfl
  rw [hf, minorMap_map, h1, Matrix.map_map, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply, iterateFrobenius_def]
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

variable {k}

theorem suzukiMap_bijective [IsAlgClosed k] (b : ℕ) : Function.Bijective (suzukiMap k b) := by
  have hF : Function.Bijective (frobPow k (2 * b + 1)) :=
    ⟨frobPow_injective k _, frobPow_surjective k _⟩
  have hcomp : (suzukiMap k b) ∘ (suzukiMap k b) = frobPow k (2 * b + 1) :=
    funext (suzukiMap_comp_self k b)
  rw [← hcomp] at hF
  exact ⟨hF.1.of_comp, hF.2.of_comp⟩

variable (k)

@[expose] def suzukiAut [IsAlgClosed k] (b : ℕ) : MulAut (antiSp k) :=
  MulEquiv.ofBijective (suzukiMap k b) (suzukiMap_bijective b)

theorem glMat_suzukiAut [IsAlgClosed k] (b : ℕ) (g : antiSp k) :
    glMat (suzukiAut k b g : GL (Fin 4) k) =
      (minorMap (glMat (g : GL (Fin 4) k))).map fun x => x ^ 2 ^ b :=
  rfl

end Frobenius

end CFSG.RankThree.PartOne.KE
