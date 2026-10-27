module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeLang
import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.LieType.Chevalley.SignKernelComponentPerfect

public section

namespace CFSG.StandardType.N2E6Native

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def e6NativeSwapWord : Fin 4 → Fin 4 → List (Fin Tag.E6.rank) :=
  (![![[], [2, 3, 0, 2], [2, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2],
        [4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 2, 1, 3, 2, 1]],
      ![[2, 3, 0, 2], [], [4, 5, 3, 4], [4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 1]],
      ![[2, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2], [4, 5, 3, 4], [],
        [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2, 1]],
      ![[4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 2, 1, 3, 2, 1],
        [4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 1],
        [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2, 1], []]] :
    Fin 4 → Fin 4 → List (Fin 6))

theorem e6NativeSwap_check : ∀ x y i : Fin 4,
    (e6NativeSwapWord x y).foldr (fun k v => reflect Tag.E6 k v) (e6NativeGamma i) =
      e6NativeGamma (Equiv.swap x y i) := by
  decide +kernel

theorem wordProd_e6NativeSwapWord_smul
    (x y i : Fin 4) :
    (coxeterSystem Tag.E6).wordProd (e6NativeSwapWord x y) • e6NativeGamma i =
      e6NativeGamma (Equiv.swap x y i) := by
  rw [wordProd_smul_eq_foldr_reflect, e6NativeSwap_check]

theorem exists_weyl_perm
    (σ : Equiv.Perm (Fin 4)) :
    ∃ w : WeylGroup Tag.E6, ∀ i, w • e6NativeGamma i = e6NativeGamma (σ i) := by
  refine Equiv.Perm.swap_induction_on σ ⟨1, fun i => one_smul _ _⟩ ?_
  rintro f x y - ⟨w, hw⟩
  exact ⟨(coxeterSystem Tag.E6).wordProd (e6NativeSwapWord x y) * w, fun i => by
    rw [mul_smul, hw, wordProd_e6NativeSwapWord_smul, Equiv.Perm.mul_apply]⟩

end CFSG.StandardType.N2E6Native

end
