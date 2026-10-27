module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux3
public import CFSG.LocalAnalysis.StandardType.GGTPNSL6Bridge
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.StandardType.CommonJRowLinTwo

open CFSG.Assembly
open CFSG.StandardType.CoordSL
open CFSG.StandardType.GGHalf

private theorem nsSL_reindexSL {N n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
    (φ : Fin N ≃ Fin n) (k : Fin s → ℕ) :
    SLNS.nsSL (φ.trans ε) det_rootMat_phi3 k =
      CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL φ.symm
        (SLNS.nsSL ε det_rootMat_phi3 k) := by
  apply Subtype.ext
  change (SLNS.nsCore (r := r) (rootMat phi3) k).submatrix (φ.trans ε) (φ.trans ε) =
    Matrix.reindex φ.symm φ.symm
      ((SLNS.nsCore (r := r) (rootMat phi3) k).submatrix ε ε)
  rw [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_submatrix]
  rfl

theorem ggCommonJRowLinTwo_hcompDichotomy {d m : ℕ} (hd : d = 2 * m ∨ d = 2 * m + 1)
    (hm : 3 ≤ m) (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m))
    (f : Fin m → Multiplicative (ZMod 3))
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d) F2)}
    (hJ : IsComponentOf J (Subgroup.centralizer
      ({(ggCommonJRowLinTwo_torus ε) f} : Set (Matrix.SpecialLinearGroup (Fin d) F2))))
    (hcard : Nat.card ↥((ggCommonJRowLinTwo_torus ε).range ⊓
      Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin d) F2))) = 3) :
    (GGCoordSparse f ∧
      Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin (d - 2)) F2)) ∨
    (GGCoordDense f ∧
      Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2))) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdN : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  let φ : Fin (d - 1 + 1) ≃ Fin d := finCongr hdN
  let e : Matrix.SpecialLinearGroup (Fin d) F2 ≃*
      Matrix.SpecialLinearGroup (Fin (d - 1 + 1)) F2 :=
    CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL φ.symm
  let ε' : Fin (d - 1 + 1) ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m) :=
    φ.trans ε
  let k : Fin m → ℕ := fun i => (f i).toAdd.val
  set kc : ℕ := (Finset.univ.filter fun i : Fin m => f i ≠ 1).card with hkc
  have hτ : (ggCommonJRowLinTwo_torus ε) f = SLNS.nsSL ε det_rootMat_phi3 k := by
    have h := SlNsRootGen.torusSL_apply (ε := ε) (hC := det_rootMat_phi3)
      (hCp := rootMat_phi3_pow_three) (t := fun i => (f i).toAdd)
    exact h
  have ht3 : ((ggCommonJRowLinTwo_torus ε) f) ^ 3 = 1 := by
    rw [hτ]
    exact SLNS.nsSL_pow_p ε det_rootMat_phi3 rootMat_phi3_pow_three k
  have ht'3 : (e ((ggCommonJRowLinTwo_torus ε) f)) ^ 3 = 1 := by
    rw [← map_pow, ht3, map_one]
  have hnat : e ((ggCommonJRowLinTwo_torus ε) f) = SLNS.nsSL ε' det_rootMat_phi3 k := by
    rw [hτ]
    exact (nsSL_reindexSL ε φ k).symm
  have hsupp : supp (e ((ggCommonJRowLinTwo_torus ε) f)) = 2 * kc := by
    rw [hnat, GGHalf.supp_nsSL]
    have hfilter : (Finset.univ.filter fun i : Fin m => k i % 3 ≠ 0) =
        (Finset.univ.filter fun i : Fin m => f i ≠ 1) := by
      apply Finset.filter_congr
      intro i _
      have hlt : k i < 3 := ZMod.val_lt (f i).toAdd
      rw [Nat.mod_eq_of_lt hlt, ZMod.val_ne_zero]
      exact not_congr toAdd_eq_zero
    rw [hfilter, hkc]
  have hcomp := ggCommonJRowLinTwo_hcompCount hd hm ε f hJ
  dsimp only at hcomp
  have hJ' : IsComponentOf (J.map e.toMonoidHom)
      (Subgroup.centralizer ({e ((ggCommonJRowLinTwo_torus ε) f)} :
        Set (Matrix.SpecialLinearGroup (Fin (d - 1 + 1)) F2))) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ
      e.toMonoidHom e.injective
    rwa [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e
      ((ggCommonJRowLinTwo_torus ε) f)] at h
  obtain ⟨Z, Λ, hZiso, hΛiso, -, -, -, hcover⟩ :=
    sl6b_centralizer_blocks_equiv (n := d - 1)
      (t := e ((ggCommonJRowLinTwo_torus ε) f)) ht'3
  rcases hcover (J.map e.toMonoidHom) hJ' with hJZ | hJΛ
  · obtain ⟨eZ⟩ := hZiso
    have hindex : (d - 1 + 1) - supp (e ((ggCommonJRowLinTwo_torus ε) f)) =
        d - 2 * kc := by
      rw [hsupp, hdN]
    have hiso : Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin (d - 2 * kc)) F2) :=
      ⟨(Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).trans
        ((MulEquiv.subgroupCongr hJZ).trans (eZ.trans
          (CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL (finCongr hindex))))⟩
    have hcountZ := hcomp.1 hiso
    rw [← hkc] at hcountZ
    have h3k : 3 ^ kc = 3 := by rw [← hcountZ, hcard]
    have hkc1 : kc = 1 := by
      have hinj : Function.Injective fun n : ℕ => 3 ^ n :=
        pow_right_injective₀ (by norm_num : 0 < 3) (by norm_num : 3 ≠ 1)
      exact hinj (by show 3 ^ kc = 3 ^ 1; rw [h3k, pow_one])
    left
    refine ⟨?_, ?_⟩
    · unfold GGCoordSparse
      have hcard1 : (Finset.univ.filter fun i : Fin m => f i ≠ 1).card = 1 := by
        rw [← hkc]
        exact hkc1
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
      refine ⟨i, fun j hj => ?_⟩
      by_contra hfj
      have hmem : j ∈ Finset.univ.filter fun t : Fin m => f t ≠ 1 := by
        simp [hfj]
      rw [hi, Finset.mem_singleton] at hmem
      exact hj hmem
    · rw [hkc1] at hiso
      simpa using hiso
  · obtain ⟨eΛ⟩ := hΛiso
    have hhalf : supp (e ((ggCommonJRowLinTwo_torus ε) f)) / 2 = kc := by
      rw [hsupp]
      omega
    have hiso : Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin kc) (GaloisField 2 2)) :=
      ⟨(Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).trans
        ((MulEquiv.subgroupCongr hJΛ).trans (eΛ.trans
          (CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL (finCongr hhalf))))⟩
    have hcountΛ := hcomp.2 hiso
    rw [← hkc] at hcountΛ
    have h3m : 3 ^ (m - kc + 1) = 3 := by rw [← hcountΛ, hcard]
    have hExp : m - kc + 1 = 1 := by
      have hinj : Function.Injective fun n : ℕ => 3 ^ n :=
        pow_right_injective₀ (by norm_num : 0 < 3) (by norm_num : 3 ≠ 1)
      exact hinj (by show 3 ^ (m - kc + 1) = 3 ^ 1; rw [h3m, pow_one])
    have hle : kc ≤ m := by
      rw [hkc]
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m))
        (fun i : Fin m => f i ≠ 1)
    have hkm : kc = m := by omega
    right
    refine ⟨?_, ?_⟩
    · unfold GGCoordDense
      have hall : ∀ i : Fin m, f i ≠ 1 := by
        intro i
        have hfilter_univ :
            (Finset.univ.filter fun j : Fin m => f j ≠ 1) = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
          rw [Finset.card_univ]
          have hc : (Finset.univ.filter fun j : Fin m => f j ≠ 1).card =
              Fintype.card (Fin m) := by
            rw [← hkc, hkm, Fintype.card_fin]
          omega
        have hi : i ∈ Finset.univ.filter fun j : Fin m => f j ≠ 1 := by
          rw [hfilter_univ]
          exact Finset.mem_univ i
        simpa using hi
      have hz : ∀ a b : Multiplicative (ZMod 3), a ≠ 1 → b ≠ 1 →
          b = a ∨ b = a⁻¹ := by decide
      intro i
      exact ⟨hall i, fun j => hz (f i) (f j) (hall i) (hall j)⟩
    · rw [hkm] at hiso
      exact hiso

end CFSG.StandardType.CommonJRowLinTwo

end
