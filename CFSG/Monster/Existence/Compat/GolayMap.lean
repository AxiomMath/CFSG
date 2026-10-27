module

public import CFSG.Monster.Code.Basis
public import CFSG.Open.MonsterDefs

public section

namespace CFSG.Monster.Existence.Compat

open CFSG.Monster.Code CFSG.Open

@[expose] def sigmaFun : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 7, 12, 10, 5, 23, 17, 14, 8, 15, 16, 19, 11, 6, 9, 22, 13, 18, 20, 21]

@[expose] def sigmaInvFun : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 8, 17, 5, 12, 18, 7, 16, 6, 20, 11, 13, 14, 10, 21, 15, 22, 23, 19, 9]

@[expose] def sigma : Equiv.Perm (Fin 24) where
  toFun := sigmaFun
  invFun := sigmaInvFun
  left_inv := by decide
  right_inv := by decide

theorem sigma_apply (i : Fin 24) : sigma i = sigmaFun i := rfl

theorem sigma_symm_apply (j : Fin 24) : sigma.symm j = sigmaInvFun j := rfl

@[expose] def permLin : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) sigma.symm

theorem permLin_apply (x : Fin 24 → ZMod 2) (j : Fin 24) : permLin x j = x (sigma.symm j) := rfl

theorem permLin_symm_apply (y : Fin 24 → ZMod 2) (i : Fin 24) : permLin.symm y i = y (sigma i) :=
  rfl

@[expose] def coefB (i k : Fin 12) : ZMod 2 :=
  if (k : ℕ) ∈ ([[1, 2], [0, 2], [0, 2, 4, 5, 6], [0, 2, 4, 6, 7, 8], [0, 2, 4, 7, 8, 9, 10, 11],
    [0, 2, 4, 6, 7, 10], [2, 3, 4, 5, 6, 7, 9, 10], [1, 5, 6, 8, 10, 11], [6, 8, 10, 11],
    [6, 7, 8, 10], [9, 11], [6, 8, 11]] : List (List ℕ)).getD i [] then 1 else 0

theorem permLin_B : ∀ i : Fin 12, permLin (B i) = ∑ k, coefB i k • monsterGolayGen k := by
  decide +kernel

theorem permLin_symm_gen : ∀ k : Fin 12, permLin.symm (monsterGolayGen k) ∈ C := by
  decide +kernel

theorem C_eq_comap_golay : C = monsterGolayCode.comap permLin.toLinearMap := by
  apply le_antisymm
  · rw [← span_B]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    show permLin (B i) ∈ monsterGolayCode
    rw [permLin_B]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro x hx
    have hx' : permLin x ∈ monsterGolayCode := hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hx'
    have hx2 : x = ∑ k, c k • permLin.symm (monsterGolayGen k) := by
      apply permLin.injective
      rw [map_sum]
      simp only [map_smul, LinearEquiv.apply_symm_apply]
      exact hc.symm
    rw [hx2]
    exact C.sum_mem fun k _ => C.smul_mem _ (permLin_symm_gen k)

theorem mem_C_iff_mem_golay (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ (fun j => x (sigma.symm j)) ∈ monsterGolayCode := by
  rw [C_eq_comap_golay]
  rfl

theorem allOnes_mem_golay : (fun _ : Fin 24 => (1 : ZMod 2)) ∈ monsterGolayCode :=
  (mem_C_iff_mem_golay _).1 Ω_mem_C

end CFSG.Monster.Existence.Compat
