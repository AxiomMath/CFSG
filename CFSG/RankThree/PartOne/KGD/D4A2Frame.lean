module

public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2
public import CFSG.RankThree.PartOne.KF4.A2Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups

section Standard

theorem d4ChainA2_add : ∀ i j k : Fin 3, chainRoot d4ChainA2 i j + chainRoot d4ChainA2 j k =
    chainRoot d4ChainA2 i k := by
  decide +kernel

theorem d4A2Rep_bijective (L : Type) [Field L] : Function.Bijective (d4A2Rep L) :=
  ⟨d4A2Rep_injective, d4A2Rep_surjective⟩

@[expose] def d4A2Equiv (L : Type) [Field L] :
    SL(3, L) ≃* subsystemGroup Tag.D4 L d4SuppA2 :=
  (MulEquiv.ofBijective (d4A2Rep L) (d4A2Rep_bijective L)).symm

@[expose] def d4rhoStd (L : Type) [Field L] : SL(3, L) →* ModGL Tag.D4 L :=
  (subsystemGroup Tag.D4 L d4SuppA2).subtype.comp (d4A2Equiv L).toMonoidHom

variable {L : Type} [Field L]

theorem d4A2Rep_d4A2Equiv (X : SL(3, L)) : d4A2Rep L (d4A2Equiv L X) = X :=
  (MulEquiv.ofBijective (d4A2Rep L) (d4A2Rep_bijective L)).apply_symm_apply X

theorem d4rhoStd_d4A2Rep {g : ModGL Tag.D4 L} (hg : g ∈ subsystemGroup Tag.D4 L d4SuppA2) :
    d4rhoStd L (d4A2Rep L ⟨g, hg⟩) = g := by
  have h := (MulEquiv.ofBijective (d4A2Rep L) (d4A2Rep_bijective L)).symm_apply_apply
    (⟨g, hg⟩ : subsystemGroup Tag.D4 L d4SuppA2)
  exact congrArg Subtype.val h

theorem d4rhoStd_mem (X : SL(3, L)) : d4rhoStd L X ∈ subsystemGroup Tag.D4 L d4SuppA2 :=
  (d4A2Equiv L X).2

theorem d4A2Mat_d4rhoStd (X : SL(3, L)) :
    d4A2Mat (d4rhoStd L X) = (X : Matrix (Fin 3) (Fin 3) L) :=
  congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) (d4A2Rep_d4A2Equiv X)

theorem d4rhoStd_injective : Function.Injective (d4rhoStd L) := by
  intro X Y h
  apply Subtype.ext
  rw [← d4A2Mat_d4rhoStd X, ← d4A2Mat_d4rhoStd Y, h]

theorem d4rhoStd_range : (d4rhoStd L).range = subsystemGroup Tag.D4 L d4SuppA2 := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ d4rhoStd_mem X) fun g hg => ?_
  exact ⟨d4A2Rep L ⟨g, hg⟩, d4rhoStd_d4A2Rep hg⟩

theorem d4rhoStd_transvection (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, d4rhoStd L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.D4 L (chainRoot d4ChainA2 i j) ((ε : L) * t) := by
  obtain ⟨ε₀, hε₀, hfam⟩ := d4A2RootFamily_all (K := L) i j hij
  obtain ⟨ε, hε⟩ : ∃ ε : Lˣ, (ε : L) = (ε₀ : L) := by
    rcases hε₀ with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  have hεε : (ε : L) * (ε : L) = 1 := by
    rw [hε]
    rcases hε₀ with rfl | rfl <;> simp
  refine ⟨ε, fun s => ?_⟩
  have hmem := pinnedX_mem_d4A2Group (chainRootA2_mem_parabolicRoots hij) ((ε : L) * s)
  have hrep : d4A2Rep L ⟨pinnedX Tag.D4 L (chainRoot d4ChainA2 i j) ((ε : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_d4A2Rep, hfam, CFSG.LinearGroups.coe_transvection, ← hε, ← mul_assoc, hεε, one_mul]
  rw [← hrep]
  exact d4rhoStd_d4A2Rep hmem

theorem d4rhoStd_diag (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    d4rhoStd L A ∈ torusGroup Tag.D4 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have hrep : d4A2Rep L ⟨d4A2TorusElt ua ub, d4A2TorusElt_mem ua ub⟩ = A := by
    apply Subtype.ext
    rw [coe_d4A2Rep, d4A2Mat_d4A2TorusElt, hdiag]
    have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
        ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hJ : d4rhoStd L A = d4A2TorusElt ua ub := by
    rw [← hrep]
    exact d4rhoStd_d4A2Rep (d4A2TorusElt_mem ua ub)
  rw [hJ]
  have hmem : d4A2TorusElt ua ub ∈ subsystemGroup Tag.D4 L d4SuppA2 ⊓ torusGroup Tag.D4 L :=
    (D4_native_A2_root_subgroup_faithful_SL3 L).2.2.2.2.2.2.2.2.2.1 _ |>.2 ⟨ua, ub, rfl⟩
  exact hmem.2

theorem d4Std_frame :
    IsA2Frame (d4rhoStd L) (fun i j => chainRoot d4ChainA2 i j) where
  injective := d4rhoStd_injective
  isRoot i j hij := (chainRootA2_mem_parabolicRoots hij).1
  neg i j := chainRoot_swap d4ChainA2 i j
  add i j k := d4ChainA2_add i j k
  transv i j hij := d4rhoStd_transvection i j hij
  range := by
    rw [d4rhoStd_range, subsystemGroup_eq_rootSpan]
    congr 1
    rw [parabolicRoots_d4SuppA2]
    ext r
    constructor
    · intro hr
      obtain ⟨k, l, hkl, hr'⟩ : ∃ k l : Fin 3, k ≠ l ∧ chainRoot d4ChainA2 k l = r := by
        simp only [d4A2Sigma, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, 1, by decide, chainRootA2_values.1⟩
        · exact ⟨1, 0, by decide, chainRootA2_values.2.2.1⟩
        · exact ⟨1, 2, by decide, chainRootA2_values.2.1⟩
        · exact ⟨2, 1, by decide, chainRootA2_values.2.2.2⟩
        · exact ⟨0, 2, by decide, by rw [← d4ChainA2_add 0 1 2, chainRootA2_values.1,
            chainRootA2_values.2.1]⟩
        · exact ⟨2, 0, by decide, by
            rw [chainRoot_swap d4ChainA2 0 2, ← d4ChainA2_add 0 1 2, chainRootA2_values.1,
              chainRootA2_values.2.1]⟩
      exact ⟨k, l, hkl, hr'.symm⟩
    · rintro ⟨k, l, hkl, rfl⟩
      rcases chainRootA2_cases k l hkl with h | h | h | h | h | h <;> rw [h] <;>
        simp [d4A2Sigma]
  diag A hA := d4rhoStd_diag A hA

end Standard

end CFSG.RankThree.PartOne.KGD
