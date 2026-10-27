module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpCore
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
import all CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.Quasithin.SmithCurtis
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.QuasithinUnique.Setup.X7 TauCeti.GLSymplecticFin
open scoped Matrix

variable {K k : Type} [Field K] [Field k]

private theorem sp_matMap_elt {n : ℕ} (φ : K →+* k) (r : RootSubgroupIndex n) (c : K) :
    matMap φ (mat n K) (elt r c) = 1 + φ c • E k r := by
  rw [matMap_apply, mat_elt, Matrix.map_add φ φ.map_add,
    Matrix.map_one φ (map_zero φ) (map_one φ),
    Matrix.map_smul' φ c (E K r) φ.map_mul,
    CFSG.SeitzReduction.F4Pilot.map_E_of_ringHomClass φ r]

private theorem sp_natMap_elt {n : ℕ} (φ : K →+* k) (r : RootSubgroupIndex n) (c : K)
    (v : Fin n ⊕ Fin n → k) :
    matRep (matMap φ (mat n K)) (elt r c) v = v + φ c • (E k r *ᵥ v) := by
  rw [matRep_apply, sp_matMap_elt, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

theorem isSimpleRep_sp_matMap {n : ℕ} (hn : 1 ≤ n) (φ : K →+* k) :
    IsSimpleRep (matRep (matMap φ (mat n K))) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨inferInstance, fun S hS => ?_⟩
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hroot : ∀ r : RootSubgroupIndex n, ∀ v ∈ S, mat n k (elt r 1) *ᵥ v ∈ S := by
    intro r v hv
    have heq : matMap φ (mat n K) (elt r 1) = mat n k (elt r 1) := by
      rw [sp_matMap_elt, mat_elt, map_one]
    simpa only [matRep_apply, heq] using hS (elt r 1) v hv
  have hsingle : ∀ a, Pi.single a (1 : k) ∈ S :=
    CFSG.StandardType.AutPSp.single_mem_of_invariant hroot hw hw0
  rw [eq_top_iff]
  intro v _
  rw [← Finset.univ_sum_single v]
  exact S.sum_mem fun a _ => by
    rw [show Pi.single a (v a) = v a • Pi.single a (1 : k) by
      ext b
      by_cases h : b = a <;> simp [h]]
    exact S.smul_mem (v a) (hsingle a)

section Six

variable [Fintype K] [CharP K 2] [CharP k 2]

omit [CharP k 2] in
private theorem sp6_natMap_fixU (φ : K →+* k) :
    (Pi.single (Sum.inl (0 : Fin 3)) (1 : k)) ∈
      (spCurtisDatum 3 K).fixU (matRep (matMap φ (mat 3 K))) := by
  intro g hg
  change g ∈ ⨆ γ ∈ {γ | γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ ∧
    0 < CFSG.LieType.Steinberg.ht γ}, rootGroup 3 K γ at hg
  have hbelow := idBelow_of_mem_iSup 1 _ (fun γ hγ =>
    ⟨hγ.1, by
      have hpos : 0 < CFSG.LieType.Steinberg.ht γ := hγ.2
      simpa only [one_mul] using (show 1 ≤ CFSG.LieType.Steinberg.ht γ by omega)⟩) hg
  change ((mat 3 K g).map φ) *ᵥ Pi.single (Sum.inl (0 : Fin 3)) (1 : k) = _
  ext a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply]
  have hlev : (1 : ℤ) * lvl (Sum.inl (0 : Fin 3)) - (1 : ℤ) * lvl a < 1 := by
    rcases a with i | i <;> simp only [lvl, Fin.val_zero] <;> omega
  rw [hbelow _ _ hlev]
  simp [Matrix.one_apply, Pi.single_apply]

omit [Fintype K] [CharP K 2] [CharP k 2] in
private theorem sp6_natMap_diag (φ : K →+* k) (t : Fin 3 → Kˣ) :
    matRep (matMap φ (mat 3 K)) (diagHom 3 K t)
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : k)) =
      φ (t 0) • Pi.single (Sum.inl (0 : Fin 3)) (1 : k) := by
  have hd : mat 3 K (diagHom 3 K t) =
      Matrix.diagonal (Sum.elim (fun i => (t i : K)) (fun i => ((t i)⁻¹ : Kˣ))) :=
    mat_equiv_diagonal t
  rw [matRep_apply, matMap_apply, Matrix.mulVec_single_one]
  ext a
  rw [Matrix.col_apply, Matrix.map_apply, hd]
  rcases a with i | i <;> fin_cases i <;> simp

omit [Fintype K] in
private theorem sp6_natMap_weyl (φ : K →+* k) (i : Fin 3) :
    matRep (matMap φ (mat 3 K)) (weylRep 3 K i)
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : k)) =
      if i = 0 then Pi.single (Sum.inl (1 : Fin 3)) 1 else
        Pi.single (Sum.inl (0 : Fin 3)) 1 := by
  fin_cases i
  · rw [weylRep_eq_short (by decide)]
    simp only [map_mul, Module.End.mul_apply, sp_natMap_elt, E, Matrix.sub_mulVec,
      Matrix.single_mulVec_eq, Pi.single_apply, map_one, CharTwo.neg_eq, one_smul]
    ext a
    rcases a with j | j <;> fin_cases j <;> simp [Pi.add_apply, CharTwo.add_self_eq_zero]
  · rw [weylRep_eq_short (by decide)]
    simp [map_mul, Module.End.mul_apply, sp_natMap_elt, E, Matrix.sub_mulVec,
      Matrix.single_mulVec_eq]
    ext a
    rcases a with j | j <;> fin_cases j <;> simp [Matrix.col_apply]
  · rw [weylRep_eq_long (by decide)]
    simp [map_mul, Module.End.mul_apply, sp_natMap_elt, E, Matrix.single_mulVec_eq]
    ext a
    rcases a with j | j <;> fin_cases j <;> simp [Matrix.col_apply]

private theorem sp6_natMap_hecke (hK : 4 ≤ Fintype.card K) (φ : K →+* k) (i : Fin 3) :
    (spCurtisDatum 3 K).heckeT (matRep (matMap φ (mat 3 K))) i
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : k)) = 0 := by
  classical
  let D := spCurtisDatum 3 K
  have : Fintype (D.X i) := Fintype.ofFinite _
  erw [CurtisDatum.heckeT_apply D]
  have hbij : Function.Bijective (fun c : K =>
      (⟨elt (simpleIdx i) c, (mem_X_iff i).mpr ⟨c, rfl⟩⟩ : D.X i)) := by
    refine ⟨fun c d hcd => elt_injective _ (congrArg Subtype.val hcd), fun x => ?_⟩
    obtain ⟨c, hc⟩ := (mem_X_iff i).mp x.2
    exact ⟨c, Subtype.ext hc.symm⟩
  rw [← hbij.sum_comp]
  simp only [map_mul, Module.End.mul_apply]
  change (∑ c : K, matRep (matMap φ (mat 3 K)) (elt (simpleIdx i) c)
    (matRep (matMap φ (mat 3 K)) (weylRep 3 K i)
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : k)))) = 0
  rw [sp6_natMap_weyl]
  have hcard : (Fintype.card K : k) = 0 := natCast_card_eq_zero_charTwo
  have hsum : ∑ c : K, φ c = 0 := sum_additive_eq_zero hK φ.toAddMonoidHom
  fin_cases i <;> simp [simpleIdx, sp_natMap_elt, E, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul k, hcard, hsum]

theorem isCurtisType_sp6_matMap (hK : 4 ≤ Fintype.card K) (φ : K →+* k)
    (χ : StatedSp 3 K → k)
    (hχ : ∀ t : Fin 3 → Kˣ, χ (diagHom 3 K t) = φ (t 0)) :
    (spCurtisDatum 3 K).IsCurtisType (matRep (matMap φ (mat 3 K)))
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : k)) χ 0 := by
  refine ⟨sp6_natMap_fixU φ, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_, ?_⟩
  · intro h hh
    obtain ⟨t, rfl⟩ := spCurtisDatum_H_le hh
    rw [hχ]
    exact sp6_natMap_diag φ t
  · intro i
    simpa using sp6_natMap_hecke hK φ i

end Six

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
