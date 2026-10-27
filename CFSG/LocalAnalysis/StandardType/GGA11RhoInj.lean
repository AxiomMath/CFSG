module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem

namespace CFSG.StandardType.A11

private theorem a11ri_swapBlocks_three : swapBlocks 3 = 1 := by
  decide

private theorem a11ri_swap01 :
    Equiv.swap ((0 : Fin 8).castSucc) ((0 : Fin 8).succ) = (Equiv.swap (0 : Fin 9) 1) := by
  decide

private theorem a11ri_swap12 :
    Equiv.swap ((1 : Fin 8).castSucc) ((1 : Fin 8).succ) = (Equiv.swap (1 : Fin 9) 2) := by
  decide

private theorem a11ri_coe_permSL_simple (k : Fin 8) :
    (((permSL 8) (Equiv.swap k.castSucc k.succ) : SL 9) : Matrix (Fin 9) (Fin 9) F2)
      = signedPerm (Equiv.swap k.castSucc k.succ) (1 : Fin 9 → F2) := by
  have hhom : typeAWeylHom 8 (Equiv.swap k.castSucc k.succ) =
      (coxeterMatrix (isFiniteType_A 8)).toCoxeterSystem.simple k :=
    typeARealizes_inj 8 (typeAWeylOf_spec 8 (Equiv.swap k.castSucc k.succ))
      (typeARealizes_simple 8 k)
  change (((slWeylLift 8 two_eq_zero) (typeAWeylHom 8 (Equiv.swap k.castSucc k.succ)) :
    SL 9) : Matrix (Fin 9) (Fin 9) F2) = _
  rw [hhom, slWeylLift_simple]
  exact coe_weylRep_of_two 8 two_eq_zero k

private theorem a11ri_coe_permSL_01 :
    (((permSL 8) (Equiv.swap (0 : Fin 9) 1) : SL 9) : Matrix (Fin 9) (Fin 9) F2)
      = signedPerm (Equiv.swap (0 : Fin 9) 1) (1 : Fin 9 → F2) := by
  have h := a11ri_coe_permSL_simple 0
  rwa [a11ri_swap01] at h

private theorem a11ri_coe_permSL_12 :
    (((permSL 8) (Equiv.swap (1 : Fin 9) 2) : SL 9) : Matrix (Fin 9) (Fin 9) F2)
      = signedPerm (Equiv.swap (1 : Fin 9) 2) (1 : Fin 9 → F2) := by
  have h := a11ri_coe_permSL_simple 1
  rwa [a11ri_swap12] at h

private theorem a11ri_permSL_three_ne_one :
    (permSL 8 (Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2) : SL 9) ≠ 1 := by
  intro h
  have hcoe : (((permSL 8 (Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2) : SL 9) :
      Matrix (Fin 9) (Fin 9) F2)) = 1 := by rw [h]; rfl
  have hentry : ((signedPerm (Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2)
      (1 : Fin 9 → F2)) : Matrix (Fin 9) (Fin 9) F2) 0 0 = 0 := by
    rw [signedPerm_apply]
    simp [Equiv.Perm.mul_def, Equiv.swap_apply_def]
  have hprod : (((permSL 8 (Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2) : SL 9) :
      Matrix (Fin 9) (Fin 9) F2))
      = signedPerm (Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2) (1 : Fin 9 → F2) := by
    rw [map_mul]
    change (((permSL 8 (Equiv.swap (0 : Fin 9) 1) : SL 9) : Matrix (Fin 9) (Fin 9) F2) *
        ((permSL 8 (Equiv.swap (1 : Fin 9) 2) : SL 9) : Matrix (Fin 9) (Fin 9) F2)) = _
    rw [a11ri_coe_permSL_01, a11ri_coe_permSL_12]
    rw [signedPerm_mul_signedPerm]
    congr 1
    funext s
    simp
  have h0 : (((permSL 8 (Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2) : SL 9) :
      Matrix (Fin 9) (Fin 9) F2)) 0 0 = 0 := by rw [hprod]; exact hentry
  have h1 : (((permSL 8 (Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2) : SL 9) :
      Matrix (Fin 9) (Fin 9) F2)) 0 0 = 1 := by
    rw [hcoe, Matrix.one_apply]; simp
  rw [h0] at h1
  exact zero_ne_one h1

private theorem a11ri_trAt_three_01 :
    trAt 3 (0 : Fin 12) 1 = permSL 8 (Equiv.swap (0 : Fin 9) (1 : Fin 9)) := by
  simp only [trAt, a11ri_swapBlocks_three, Equiv.Perm.one_apply]
  rw [dif_pos (by decide : (0 : Fin 12).val < 9 ∧ (1 : Fin 12).val < 9 ∧ (0 : Fin 12) ≠ 1)]
  rfl

private theorem a11ri_trAt_three_12 :
    trAt 3 (1 : Fin 12) 2 = permSL 8 (Equiv.swap (1 : Fin 9) (2 : Fin 9)) := by
  simp only [trAt, a11ri_swapBlocks_three, Equiv.Perm.one_apply]
  rw [dif_pos (by decide : (1 : Fin 12).val < 9 ∧ (2 : Fin 12).val < 9 ∧ (1 : Fin 12) ≠ 2)]
  rfl

theorem a11RhoInjInput_holds :
    ∀ (G : Type) [Group G] (Φ : Fin 4 → SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G),
      Function.Injective (Φ 3) → RhoEval Φ ρ → Function.Injective ρ := by
  intro G _ Φ ρ hΦ hρeval
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  have hN : Nontrivial ρ.ker := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    exact ⟨w, MonoidHom.mem_ker.mpr hw, hne⟩
  have hAle := Equiv.Perm.alternatingGroup_le_of_normal (N := ρ.ker)
    (by simp : 5 ≤ Nat.card (Fin 12)) hN
  let c9 : Equiv.Perm (Fin 9) := Equiv.swap (0 : Fin 9) 1 * Equiv.swap (1 : Fin 9) 2
  let c12 : Equiv.Perm (Fin 12) := Equiv.swap (0 : Fin 12) 1 * Equiv.swap (1 : Fin 12) 2
  have hcA : c12 ∈ alternatingGroup (Fin 12) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 12) ≠ 1),
      Equiv.Perm.sign_swap (by decide : (1 : Fin 12) ≠ 2)]
    decide
  have hmem : ρ c12 = 1 := MonoidHom.mem_ker.mp (hAle hcA)
  have hρ01 : ρ (Equiv.swap (0 : Fin 12) 1) = Φ 3 (trAt 3 (0 : Fin 12) 1) :=
    hρeval 3 0 1 (by decide) (by decide) (by decide)
  have hρ12 : ρ (Equiv.swap (1 : Fin 12) 2) = Φ 3 (trAt 3 (1 : Fin 12) 2) :=
    hρeval 3 1 2 (by decide) (by decide) (by decide)
  have hc : ρ c12 = Φ 3 (permSL 8 c9) := by
    dsimp only [c12, c9]
    rw [map_mul, hρ01, hρ12, ← map_mul]
    congr 1
    rw [a11ri_trAt_three_01, a11ri_trAt_three_12, ← map_mul]
  have hΦne : Φ 3 (permSL 8 c9) ≠ 1 := by
    intro hx
    have h1 : Φ 3 (permSL 8 c9) = Φ 3 1 := by rw [hx, map_one]
    exact a11ri_permSL_three_ne_one (hΦ h1)
  exact hΦne (hc.symm.trans hmem)

end CFSG.StandardType.A11

end
