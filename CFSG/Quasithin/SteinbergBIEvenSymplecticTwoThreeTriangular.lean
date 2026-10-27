module

public import CFSG.Quasithin.SteinbergBITwoThreeSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp

public section

namespace CFSG.Quasithin.SteinbergBI

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a

variable {r : ℕ} {K : Type} [Field K]

theorem pairMat_injective {ι : Type*} [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    Function.Injective (pairMat a b : Matrix (Fin 2) (Fin 2) K → Matrix ι ι K) := by
  intro g g' h
  obtain ⟨g1, g2, g3, g4⟩ := pairMat_apply_pair hab g
  obtain ⟨g1', g2', g3', g4'⟩ := pairMat_apply_pair hab g'
  ext p q
  revert p q
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← g1, ← g1', h]
  · rw [← g2, ← g2', h]
  · rw [← g3, ← g3', h]
  · rw [← g4, ← g4', h]

theorem injective_lam (i : Fin r) :
    Function.Injective (lam i : SpecialLinearGroup (Fin 2) K →* StatedSp r K) := by
  intro g g' h
  have h' := congrArg (fun x : StatedSp r K =>
    ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
  simp only [coe_lam] at h'
  exact Subtype.ext (pairMat_injective Sum.inl_ne_inr h')

theorem injective_rho {i j : Fin r} (hij : i ≠ j) :
    Function.Injective (rho i j hij : SpecialLinearGroup (Fin 2) K →* StatedSp r K) := by
  intro g g' h
  have h' := congrArg (fun x : StatedSp r K =>
    ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
  simp only [coe_rho'] at h'
  exact Subtype.ext (pairMat_injective hij (Matrix.fromBlocks_inj.1 h').1)

theorem transvection_zero_one_eq_sl2Up (c : K) :
    SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c = sl2Up K c := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun p q => ?_
  rw [SpecialLinearGroup.transvection_coe]
  fin_cases p <;> fin_cases q <;> simp [sl2Up]

theorem transvection_one_zero_eq_sl2Low (c : K) :
    SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c = sl2Low K c := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun p q => ?_
  rw [SpecialLinearGroup.transvection_coe]
  fin_cases p <;> fin_cases q <;> simp [sl2Low]

theorem sl2Weyl_mul_sl2Up (t : K) :
    sl2Up K 1 * sl2Low K (-1) * sl2Up K 1 * sl2Up K (-t) =
      sl2Low K t * (sl2Up K 1 * sl2Low K (-1) * sl2Up K 1) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun p q => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases p <;> fin_cases q <;> simp [sl2Up, sl2Low, mul_apply, Fin.sum_univ_two]

theorem exists_simpleRoot_sl2 (k : Fin r) :
    ∃ φ : SpecialLinearGroup (Fin 2) K →* StatedSp r K, Function.Injective φ ∧
      (∀ t, φ (sl2Up K t) = pairRootElt (inl_ne_simpleSnd k) t) ∧
      ∀ t, φ (sl2Low K t) = pairRootElt (inl_ne_simpleSnd k).symm t := by
  have e2 : ∀ {b : Fin r ⊕ Fin r} (hb : simpleSnd k = b) (hkb : Sum.inl k ≠ b) (t : K),
      pairRootElt (inl_ne_simpleSnd k) t = pairRootElt hkb t ∧
        pairRootElt (inl_ne_simpleSnd k).symm t = pairRootElt hkb.symm t := by
    intro b hb hkb t
    subst hb
    exact ⟨rfl, rfl⟩
  by_cases h : (k : ℕ) + 1 < r
  · set k' : Fin r := ⟨k + 1, h⟩
    have hkk' : k ≠ k' := fun e => by
      have := congrArg Fin.val e
      simp [k'] at this
    have hsnd : simpleSnd k = Sum.inl k' := by
      unfold simpleSnd
      rw [dite_eq_left h]
    refine ⟨rho k k' hkk', injective_rho hkk', fun t => ?_, fun t => ?_⟩
    · rw [(e2 hsnd (fun e => hkk' (Sum.inl_injective e)) t).1, pairRootElt_short hkk']
    · rw [(e2 hsnd (fun e => hkk' (Sum.inl_injective e)) t).2, pairRootElt_short' hkk']
  · have hsnd : simpleSnd k = Sum.inr k := by
      unfold simpleSnd
      rw [dite_eq_right h]
    refine ⟨lam k, injective_lam k, fun t => ?_, fun t => ?_⟩
    · rw [(e2 hsnd Sum.inl_ne_inr t).1, pairRootElt_long]
    · rw [(e2 hsnd Sum.inl_ne_inr t).2, pairRootElt_long']

theorem weylRep_not_mem_of_card_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {M : Subgroup (StatedSp r K)} (hUM : unipotent r K ≤ M) {a b : ℕ}
    (hM : Nat.card M = 2 ^ a * 3 ^ b) (k : Fin r) : weylRep K k ∉ M := by
  intro hk
  obtain ⟨φ, hφ, hup, hlow⟩ := exists_simpleRoot_sl2 (K := K) k
  have hupM : ∀ t, φ (sl2Up K t) ∈ M := fun t => by
    rw [hup]
    refine hUM (rootSubgroup_le_unipotent (simpleRootVec_mem_posRoots k) ?_)
    rw [← rootVec_simpleSnd]
    exact pairRootElt_mem_rootSubgroup _ _
  have hw : φ (sl2Up K 1 * sl2Low K (-1) * sl2Up K 1) = weylRep K k := by
    rw [map_mul, map_mul, hup, hlow]
    rfl
  have hlowM : ∀ t, φ (sl2Low K t) ∈ M := fun t => by
    rw [← mul_inv_eq_iff_eq_mul.2 (sl2Weyl_mul_sl2Up (K := K) t), map_mul, map_mul, map_inv, hw]
    exact mul_mem (mul_mem hk (hupM _)) (inv_mem hk)
  refine not_range_le_of_card_eq hq hφ hM
    (range_le_of_transvection_mem φ M (fun c => ?_) (fun c => ?_))
  · rw [transvection_zero_one_eq_sl2Up]
    exact hupM c
  · rw [transvection_one_zero_eq_sl2Low]
    exact hlowM c

theorem even_symplectic_two_three_overgroups_of_full_unitriangular_subgroups_are_triangular
    [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ∀ M : Subgroup (StatedSp r K), unipotent r K ≤ M →
      ∀ a b : ℕ, Nat.card M = 2 ^ a * 3 ^ b → M ≤ borelSubgroup r K := by
  intro M hUM a b hM g hg
  have hQ := le_flagStabilizer_borelCuts M hUM hg
  refine mem_borelSubgroup.2 fun i hi1 hir => ?_
  exact mem_flagStabilizer.1 hQ i
    ⟨⟨i - 1, by omega⟩, by simp; omega, weylRep_not_mem_of_card_eq hq hUM hM _⟩

end CFSG.Quasithin.SteinbergBI
