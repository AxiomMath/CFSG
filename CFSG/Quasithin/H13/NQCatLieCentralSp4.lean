module

public import CFSG.Quasithin.H13.NQCatLieCentralCore
public import CFSG.Quasithin.H13.NQCatLieThompsonSp4U
public import CFSG.Quasithin.H13.NQCatParabolicSp4

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.H13.NQCat.LieThompson.Sp4
open CFSG.Quasithin.H13.NQCat.Sp4 (xA xB spMat_xA spMat_xB xA_mul xB_mul xA_mem xB_mem)
open CFSG.QuasithinUnique.Lin2.Five (projEquiv)

variable {F : Type} [Field F] [CharP F 2]

theorem spMat_xA_eq (t : F) : spMat (xA t) = uMat t 0 0 0 := by
  rw [spMat_xA]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [uMat, CharTwo.neg_eq]

omit [CharP F 2] in
theorem spMat_xB_eq (t : F) : spMat (xB t) = uMat 0 0 0 t := by
  rw [spMat_xB]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [uMat]

theorem piA_eq_zero_of_commute {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) {t : F} (ht : t ≠ 0)
    (h : xB t * u = u * xB t) : piA u = 0 := by
  obtain ⟨a, c₀, c₁, c₂, hu'⟩ := exists_uMat hu
  have h1 := congrArg spMat h
  rw [spMat_mul, spMat_mul, spMat_xB_eq, hu', uMat_mul, uMat_mul] at h1
  have h2 := congrFun (congrFun h1 (Sum.inl 1)) (Sum.inr 0)
  simp only [uMat, fromBlocks_apply₁₂, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one] at h2
  rw [piA_of hu']
  have h3 : a * t = 0 := by linear_combination h2
  exact (mul_eq_zero.1 h3).resolve_right ht

theorem piB_eq_zero_of_commute {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) {s : F} (hs : s ≠ 0)
    (h : xA s * u = u * xA s) : piB u = 0 := by
  obtain ⟨a, c₀, c₁, c₂, hu'⟩ := exists_uMat hu
  have h1 := congrArg spMat h
  rw [spMat_mul, spMat_mul, spMat_xA_eq, hu', uMat_mul, uMat_mul] at h1
  have h2 := congrFun (congrFun h1 (Sum.inl 1)) (Sum.inr 0)
  simp only [uMat, fromBlocks_apply₁₂, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one] at h2
  rw [piB_of hu']
  have h3 : s * c₂ = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h3).resolve_left hs

@[expose] noncomputable def xAHom : Multiplicative F →* StatedSp 2 F where
  toFun a := xA (Multiplicative.toAdd a)
  map_one' := mul_left_cancel ((xA_mul (0 : F) 0).trans (by rw [add_zero, mul_one]))
  map_mul' a b := (xA_mul _ _).symm

@[expose] noncomputable def xBHom : Multiplicative F →* StatedSp 2 F where
  toFun a := xB (Multiplicative.toAdd a)
  map_one' := mul_left_cancel ((xB_mul (0 : F) 0).trans (by rw [add_zero, mul_one]))
  map_mul' a b := (xB_mul _ _).symm

theorem xAHom_injective : Function.Injective (xAHom (F := F)) := fun a b h => by
  have h1 := congrArg piA h
  change piA (xA _) = piA (xA _) at h1
  rw [piA_of (spMat_xA_eq _), piA_of (spMat_xA_eq _)] at h1
  exact Multiplicative.toAdd.injective h1

omit [CharP F 2] in
theorem xBHom_injective : Function.Injective (xBHom (F := F)) := fun a b h => by
  have h1 := congrArg piB h
  change piB (xB _) = piB (xB _) at h1
  rw [piB_of (spMat_xB_eq _), piB_of (spMat_xB_eq _)] at h1
  exact Multiplicative.toAdd.injective h1

theorem centralIndex_sp4 [Finite F] (hF : 4 ≤ Nat.card F) : CentralIndex (StatedSp 2 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := F) 2 2
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent 2 F) ⊤ :=
    hQ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Q
  refine centralIndex_of_sylow hU fun x hx hidx => ?_
  obtain ⟨t, ht, htx⟩ := exists_ne_zero_commute_of_hom xBHom xBHom_injective
    (fun a => xB_mem _) (by omega) hidx
  obtain ⟨s, hs, hsx⟩ := exists_ne_zero_commute_of_hom xAHom xAHom_injective
    (fun a => xA_mem _) (by omega) hidx
  have hA := piA_eq_zero_of_commute hx ht htx
  have hB := piB_eq_zero_of_commute hx hs hsx
  exact Subgroup.mem_centralizer_iff.2 fun u hu => mul_comm_of_piA_eq_zero hu hx hA hB

theorem centralIndex_projSp4 [Finite F] (hF : 4 ≤ Nat.card F) :
    CentralIndex (StatedProj (StatedSp 2 F)) :=
  CentralIndex.of_mulEquiv (projEquiv F).symm (centralIndex_sp4 hF)

end CFSG.Quasithin.H13.NQCat.LieCentral.Sp4
