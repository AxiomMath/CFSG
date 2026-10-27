module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuType

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix CFSG.Quasithin.SmithCurtis

theorem coord_eq_zero_of_row {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    {x : Fin n → ZMod 2} (hx : A *ᵥ x = x) (r k : Fin n)
    (hrow : ∀ m, A r m = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r m + if m = k then 1 else 0) :
    x k = 0 := by
  have h := congrFun hx r
  simp only [mulVec, dotProduct, hrow, add_mul, Finset.sum_add_distrib, one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact add_eq_left.mp h

theorem eq_smul_single {n : ℕ} {x : Fin (n + 1) → ZMod 2}
    (h : ∀ k : Fin (n + 1), k ≠ 0 → x k = 0) : x = 0 ∨ x = Pi.single 0 1 := by
  have e : x = x 0 • Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [h i hi]
      simp [hi]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (x 0) with h0 | h0
  · left
    rw [e, h0, zero_smul]
  · right
    rw [e, h0, one_smul]

abbrev trivRep : Representation (ZMod 2) G6 (ZMod 2) := Representation.trivial (ZMod 2) G6 (ZMod 2)

theorem triv_fixU (x : ZMod 2) : x ∈ fixU trivRep := fun _ _ => rfl

theorem triv_gen : orbitSpan trivRep 1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h := Submodule.smul_mem (orbitSpan trivRep 1) x (mem_orbitSpan_self trivRep 1)
  rwa [smul_eq_mul, mul_one] at h

theorem triv_simple : IsSimpleRep trivRep :=
  isSimpleRep_of_fixU trivRep (fun x _ => (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) x) triv_gen

theorem triv_type (s : Fin 3) : Th trivRep s 1 = 0 := by
  rw [Th_apply, Representation.trivial_apply, Representation.trivial_apply]
  decide

@[expose] def natRep : Representation (ZMod 2) G6 (Fin 6 → ZMod 2) where
  toFun g := (gM g).mulVecLin
  map_one' := LinearMap.ext fun v => by simp [gM_one]
  map_mul' g h := LinearMap.ext fun v => by simp [gM_mul, mulVec_mulVec]

theorem natRep_apply (g : G6) (v : Fin 6 → ZMod 2) : natRep g v = gM g *ᵥ v := rfl

@[expose] def e0 : Fin 6 → ZMod 2 := Pi.single 0 1

theorem e0_ne : e0 ≠ 0 := by decide

theorem e0_mem_fixU : e0 ∈ fixU natRep := by
  rw [mem_fixU]
  intro u hu
  have h := mem_Ugrp.mp hu
  funext i
  simp only [natRep_apply, e0, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs with hi
  · exact (h i 0).2 hi
  · exact (h i 0).1 (Fin.pos_iff_ne_zero.mpr hi)

@[expose] def rowS : Fin 6 → Fin 3 := ![0, 0, 1, 2, 1, 0]

@[expose] def rowR : Fin 6 → Fin 6 := ![0, 0, 1, 2, 3, 4]

theorem natRep_rows : ∀ k : Fin 6, k ≠ 0 → ∀ m : Fin 6,
    xM (rowS k) (rowR k) m =
      (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (rowR k) m + if m = k then 1 else 0 := by
  decide +kernel

theorem natRep_fix {x : Fin 6 → ZMod 2} (hx : x ∈ fixU natRep) : x = 0 ∨ x = e0 := by
  refine eq_smul_single fun k hk => ?_
  exact coord_eq_zero_of_row (xM (rowS k)) (hx _ (xE_mem (rowS k))) (rowR k) k (natRep_rows k hk)

@[expose] def natIdx : Fin 6 → Fin 48 := ![0, 1, 6, 14, 21, 25]

theorem natIdx_spec : ∀ i : Fin 6, toMat (bword (canW (natIdx i))) *ᵥ e0 = Pi.single i 1 := by
  decide +kernel

theorem natRep_wE (k : Fin 48) (v : Fin 6 → ZMod 2) :
    natRep (wE k) v = toMat (bword (canW k)) *ᵥ v := by
  rw [natRep_apply, wE, wordProd_coe]

theorem natRep_gen : orbitSpan natRep e0 = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin 6)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, ← natIdx_spec i, ← natRep_wE]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem natRep_simple : IsSimpleRep natRep :=
  isSimpleRep_of_fixU natRep (fun _ hx => natRep_fix hx) natRep_gen

theorem natRep_Th_checks : ∀ s : Fin 3,
    yM s *ᵥ e0 + (xM s * yM s) *ᵥ e0 = if s = 0 then e0 else 0 := by
  decide +kernel

theorem natRep_type (s : Fin 3) : Th natRep s e0 = 0 ↔ s ≠ 0 := by
  rw [Th_apply, natRep_apply, natRep_apply]
  change yM s *ᵥ e0 + (xM s * yM s) *ᵥ e0 = 0 ↔ _
  rw [natRep_Th_checks]
  split_ifs with h
  · simp [h, e0_ne]
  · simp [h]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
