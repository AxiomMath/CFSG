module

public import CFSG.LieType.Steinberg.CurtisDatum
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.LieType.Universal.SymplecticExtras.TorusWeyl
public import CFSG.LieType.Universal.SymplecticExtras.Torus
import all CFSG.LieType.Universal.SymplecticRoots
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.Quasithin.SmithCurtis CFSG.Open

variable (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def spCurtisDatum : CurtisDatum (StatedSp n K)
    (coxeterMatrix (rootDatum n K).isFiniteType).toCoxeterSystem 2 :=
  curtisDatumOf (D := rootDatum n K) (n := weylRep n K) (H := torus n K)
    (isCTGroupDatum n K) (steinbergExtras n K) CFSG.StandardType.GGRootSp.bruhatExtras 2
    (fun _ hγ => CFSG.StandardType.GGRootSp.isPGroup_rootGroup hγ)

theorem spCurtisDatum_Y (i : Fin n) :
    (spCurtisDatum n K).Y i = rootGroup n K (-Pi.single i 1) := rfl

theorem spCurtisDatum_n (i : Fin n) : (spCurtisDatum n K).n i = weylRep n K i := rfl

theorem spCurtisDatum_H : (spCurtisDatum n K).H = ⨆ i, torus n K i := rfl

variable {n K}

theorem spCurtisDatum_H_le : (spCurtisDatum n K).H ≤ (diagHom n K).range := by
  intro x hx
  obtain ⟨t, rfl⟩ := exists_diagonal_of_mem_iSup_torus hx
  exact ⟨t, rfl⟩

theorem spCurtisDatum_H_pow {h : StatedSp n K} (hh : h ∈ (spCurtisDatum n K).H) :
    h ^ (Nat.card K - 1) = 1 := by
  obtain ⟨t, rfl⟩ := spCurtisDatum_H_le hh
  rw [← map_pow]
  have ht : t ^ (Nat.card K - 1) = 1 := by
    funext a
    have : Fintype K := Fintype.ofFinite K
    apply Units.ext
    rw [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (t a).ne_zero
  rw [ht, map_one]

theorem spCurtisDatum_splitOver (k : Type*) [Field k] [Algebra K k] :
    SplitOver k (spCurtisDatum n K).H :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.splitOver_of_pow_card_sub_one
    (K := K) k (fun _ hh => spCurtisDatum_H_pow hh)

theorem diagHom_corootVec_mem_H (k : Fin n) (c : Kˣ) :
    diagHom n K (corootVec n K k c) ∈ (spCurtisDatum n K).H :=
  Subgroup.mem_iSup_of_mem k (diagonal_mem_torus n K k c)

omit [Finite K] [CharP K 2] in
theorem diagHom_three_eq (t : Fin 3 → Kˣ) :
    diagHom 3 K t = diagHom 3 K (corootVec 3 K 0 (t 0)) *
      diagHom 3 K (corootVec 3 K 1 (t 0 * t 1)) *
      diagHom 3 K (corootVec 3 K 2 (t 0 * t 1 * t 2)) := by
  rw [← map_mul, ← map_mul]
  congr 1
  funext a
  fin_cases a <;> simp [corootVec]
  group

theorem diagHom_mem_H_three (t : Fin 3 → Kˣ) : diagHom 3 K t ∈ (spCurtisDatum 3 K).H := by
  rw [diagHom_three_eq]
  exact mul_mem (mul_mem (diagHom_corootVec_mem_H 0 _) (diagHom_corootVec_mem_H 1 _))
    (diagHom_corootVec_mem_H 2 _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
