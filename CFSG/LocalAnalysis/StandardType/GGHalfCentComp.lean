module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentDefs
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.StandardType.CoordSL CFSG.RankThree.CALinearPlane Matrix

private lemma centComp_cast01 {s : ℕ} {k : Fin s → ℕ} (hk : ∀ i, k i = 0 ∨ k i = 1) (i : Fin s) :
    (k i : ZMod 3) = 0 ∨ (k i : ZMod 3) = 1 := by
  rcases hk i with h | h <;> rw [h] <;> simp

private lemma centComp_aligned {s : ℕ} {k : Fin s → ℕ} (hk : ∀ i, k i = 0 ∨ k i = 1) :
    Aligned root_phi3_pow_three (fun i => (k i : ZMod 3)) := by
  intro i j hj u _ hiu
  have hj1 : (k j : ZMod 3) = 1 := by
    rcases centComp_cast01 hk j with h | h
    · exact absurd h hj
    · exact h
  rcases centComp_cast01 hk i with hi | hi
  · have huz : (u : ZMod 3) = 0 := by
      have h := hiu
      dsimp only at h
      rw [hi, hj1, mul_one] at h
      exact h.symm
    exact absurd huz (Units.ne_zero u)
  · dsimp only
    rw [hi, hj1]

private lemma centComp_nsSL_val {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ) :
    SLNS.nsSL ε det_rootMat_phi3 k =
      SLNS.nsSL ε det_rootMat_phi3 (fun i => ((k i : ZMod 3)).val) :=
  SLNS.nsSL_congr ε det_rootMat_phi3 rootMat_phi3_pow_three (fun _ => by
    simp [ZMod.val_natCast])

theorem isComponentOf_zeroBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) (h3 : 3 ≤ n + 1 - 2 * ones k) :
    CFSG.Assembly.IsComponentOf (zeroBlk ε k)
      (Subgroup.centralizer ({SLNS.nsSL ε det_rootMat_phi3 k} :
        Set (SpecialLinearGroup (Fin (n + 1)) F2))) := by
  classical
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hprim : IsPrimitiveRoot (AdjoinRoot.root phi3) 3 :=
    root_isPrimitiveRoot Nat.prime_three natCast_three_ne_zero phi3_dvd_cyclotomic
  have hal := centComp_aligned (k := k) hk
  have hYeq := centComp_nsSL_val (n := n) (s := s) (r := r) ε k
  set C₀ : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) :=
    Subgroup.centralizer ({SLNS.nsSL ε det_rootMat_phi3 k} :
      Set (SpecialLinearGroup (Fin (n + 1)) F2)) with hC₀
  have hk0 : ∀ i, (k i : ZMod 3) = 0 → k i = 0 := by
    intro i hi
    rcases hk i with h | h
    · exact h
    · exfalso
      rw [h] at hi
      exact (one_ne_zero : (1 : ZMod 3) ≠ 0) (by simpa using hi)
  have hZle : zeroBlk ε k ≤ C₀ := by
    intro M hM
    rw [hC₀, Subgroup.mem_centralizer_singleton_iff]
    exact (comm_zeroBlock_of_torus (β := fun i => (k i : ZMod 3)) (ε := ε)
      (hC := det_rootMat_phi3) (k := k) hk0 hM).symm
  have hZn : ((zeroBlk ε k).subgroupOf C₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZle]
    intro h u hh hu
    rw [hC₀] at hu
    have hu' : u * SLNS.nsSL ε det_rootMat_phi3 (fun i => ((k i : ZMod 3)).val) =
        SLNS.nsSL ε det_rootMat_phi3 (fun i => ((k i : ZMod 3)).val) * u := by
      simpa [hYeq] using (Subgroup.mem_centralizer_singleton_iff.mp hu)
    exact conj_mem_zeroBlock hprim hal hu' hh
  have hQs : CFSG.Assembly.IsQuasisimple (zeroBlk ε k) := by
    refine (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥(zeroBlk ε k)).2 ?_
    change CFSG.IsQuasisimple (coordBlockSL F2 (zeroCoords ε (fun i => (k i : ZMod 3))))
    have hJ : 3 ≤ (zeroCoords ε (fun i => (k i : ZMod 3))).card := by
      rw [card_zeroCoords ε k hk]
      exact h3
    haveI : Finite F2 := inferInstance
    have hSL : CFSG.IsQuasisimple
        (SpecialLinearGroup (Fin (zeroCoords ε (fun i => (k i : ZMod 3))).card) F2) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        (zeroCoords ε (fun i => (k i : ZMod 3))).card F2 (by omega)
        (Or.inl (by omega)) (Or.inl (by omega))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective (blockSLOn_injective (k := F2)
        (zeroCoords ε (fun i => (k i : ZMod 3))))).trans
        (MulEquiv.subgroupCongr (range_blockSLOn (k := F2)
          (zeroCoords ε (fun i => (k i : ZMod 3)))))) hSL
  exact ⟨hZle, CFSG.Assembly.IsSubnormal.step hZle hZn (CFSG.Assembly.IsSubnormal.refl _), hQs⟩

theorem isComponentOf_classBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) (h2 : 2 ≤ ones k) :
    CFSG.Assembly.IsComponentOf (classBlk ε k)
      (Subgroup.centralizer ({SLNS.nsSL ε det_rootMat_phi3 k} :
        Set (SpecialLinearGroup (Fin (n + 1)) F2))) := by
  classical
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hprim : IsPrimitiveRoot (AdjoinRoot.root phi3) 3 :=
    root_isPrimitiveRoot Nat.prime_three natCast_three_ne_zero phi3_dvd_cyclotomic
  have hal := centComp_aligned (k := k) hk
  have hYeq := centComp_nsSL_val (n := n) (s := s) (r := r) ε k
  set C₀ : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) :=
    Subgroup.centralizer ({SLNS.nsSL ε det_rootMat_phi3 k} :
      Set (SpecialLinearGroup (Fin (n + 1)) F2)) with hC₀
  have hkc : ∀ i j, (k i : ZMod 3) = 1 → (k j : ZMod 3) = 1 → k i = k j := by
    intro i j hi hj
    have hi1 : k i = 1 := by
      rcases hk i with h | h
      · exfalso
        rw [h] at hi
        exact (zero_ne_one : (0 : ZMod 3) ≠ 1) (by simpa using hi)
      · exact h
    have hj1 : k j = 1 := by
      rcases hk j with h | h
      · exfalso
        rw [h] at hj
        exact (zero_ne_one : (0 : ZMod 3) ≠ 1) (by simpa using hj)
      · exact h
    rw [hi1, hj1]
  have hKC : classBlk ε k ≤ C₀ := by
    rintro M ⟨N, hN, rfl⟩
    rw [hC₀, Subgroup.mem_centralizer_singleton_iff]
    exact comm_classBlock_of_torus (β := fun i => (k i : ZMod 3)) (ε := ε)
      (hC := det_rootMat_phi3) (c := 1) (k := k) hkc hN
  have hKn : ((classBlk ε k).subgroupOf C₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKC]
    intro h u hh hu
    rw [hC₀] at hu
    obtain ⟨N, hN, rfl⟩ := hh
    have hu' : u * SLNS.nsSL ε det_rootMat_phi3 (fun i => ((k i : ZMod 3)).val) =
        SLNS.nsSL ε det_rootMat_phi3 (fun i => ((k i : ZMod 3)).val) * u := by
      simpa [hYeq] using (Subgroup.mem_centralizer_singleton_iff.mp hu)
    exact conj_mem_classBlock hprim hal one_ne_zero hu' hN
  have hQs : CFSG.Assembly.IsQuasisimple (classBlk ε k) := by
    refine (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥(classBlk ε k)).2 ?_
    haveI : Finite (AdjoinRoot phi3) := finite_adjoinRoot
    have hS2 : 2 ≤ (classSet (fun i => (k i : ZMod 3)) 1).card := by
      rw [card_classSet k hk]
      exact h2
    have h4 : 4 ≤ Nat.card (AdjoinRoot phi3) := by
      rw [natCard_adjoinRoot_phi3]
    have hq0 : CFSG.IsQuasisimple
        (coordBlockSL (AdjoinRoot phi3) (classSet (fun i => (k i : ZMod 3)) 1)) :=
      isQuasisimple_coordBlockSL (k := AdjoinRoot phi3) hS2 h4
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (coordBlockSL (AdjoinRoot phi3)
        (classSet (fun i => (k i : ZMod 3)) 1)) (theta phi3 ε) (theta_injective phi3 ε)) hq0
  exact ⟨hKC, CFSG.Assembly.IsSubnormal.step hKC hKn (CFSG.Assembly.IsSubnormal.refl _), hQs⟩

end CFSG.StandardType.GGHalf

end
