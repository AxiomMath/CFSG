module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMFix
public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFourTwoFrame

public section

namespace CFSG.StandardType.QTwo

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType

theorem qTwoFrontM_centralizer_solvable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {s : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))} (hs1 : s ≠ 1) (hs3 : s ^ 3 = 1) :
    Group.IsSolvable ↥(Subgroup.centralizer
      ({s} : Set (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))))) := by
  classical
  have hE : IsElemAbelian 3 (Subgroup.zpowers s) := by
    refine ⟨Subgroup.zpowers_isMulCommutative s, ?_⟩
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn, ← _root_.zpow_natCast (s ^ n) 3, ← _root_.zpow_mul]
    rw [_root_.zpow_mul', _root_.zpow_natCast, hs3, _root_.one_zpow]
  obtain ⟨φ, hφ, hdiag⟩ := exists_model_diag_psuFourTwo hK hE
  obtain ⟨s', ⟨t, hst⟩, hsx⟩ := hdiag s (Subgroup.mem_zpowers s)
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hφ.ker (a * b⁻¹) h1
    have h2 : a * b⁻¹ = 1 := eq_one_of_scalar_suFourTwo hK hc
    calc a = a * b⁻¹ * b := by group
      _ = b := by rw [h2, one_mul]
  have ht : ∀ i : Fin 4, t i ≠ 0 := by
    have hprod : (∏ i : Fin 4, t i) = 1 := by
      have hdet := ((mem_unitarySU_iff hφ.field).mp s'.2).1
      rw [hst, Matrix.det_diagonal] at hdet
      exact hdet
    intro i h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at hprod
    exact zero_ne_one hprod
  have hnc : ∃ i j, t i ≠ t j := by
    by_contra h
    have hconst : ∀ i j : Fin 4, t i = t j := by
      intro i j
      by_contra hij
      exact h ⟨i, j, hij⟩
    have hscal : ((s' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal (fun _ => t 0) := by
      rw [hst]
      exact Matrix.diagonal_eq_diagonal_iff.mpr (fun i => hconst i 0)
    have hs'1 : s' = 1 := eq_one_of_scalar_suFourTwo hK hscal
    apply hs1
    rw [← hsx, hs'1, map_one]
  let δ : MulAut ↥(unitarySU 2 1 K 4) := MulAut.conj s'
  have hδ : ∀ g : ↥(unitarySU 2 1 K 4),
      (((δ g : ↥(unitarySU 2 1 K 4)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) * diagonal t =
        diagonal t * (((g : ↥(unitarySU 2 1 K 4)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) := by
    intro g
    have h : (δ g) * s' = s' * g := by
      show MulAut.conj s' g * s' = s' * g
      rw [MulAut.conj_apply]
      group
    have hm := congrArg (fun x : ↥(unitarySU 2 1 K 4) =>
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
    simpa only [Subgroup.coe_mul, Units.val_mul, hst] using hm
  have hsol : Group.IsSolvable ↥(ggFix δ) :=
    qTwoFrontM_ggFix_solvable hφ.field ht hnc δ hδ
  let f : ↥(ggFix δ) →* ↥(Subgroup.centralizer
      ({s} : Set (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))))) :=
    { toFun := fun g =>
        ⟨φ g, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hgfix : δ (g : ↥(unitarySU 2 1 K 4)) = (g : ↥(unitarySU 2 1 K 4)) := g.2
          have hcomm : (g : ↥(unitarySU 2 1 K 4)) * s' =
              s' * (g : ↥(unitarySU 2 1 K 4)) := by
            have h : s' * (g : ↥(unitarySU 2 1 K 4)) * s'⁻¹ =
                (g : ↥(unitarySU 2 1 K 4)) := by
              simpa [δ, MulAut.conj_apply] using hgfix
            calc (g : ↥(unitarySU 2 1 K 4)) * s'
                = (s' * (g : ↥(unitarySU 2 1 K 4)) * s'⁻¹) * s' := by rw [h]
              _ = s' * (g : ↥(unitarySU 2 1 K 4)) := by group
          rw [← hsx, ← map_mul, ← map_mul, hcomm]⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := hφ.surj
      (y : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))
    have hmem : g ∈ ggFix δ := by
      rw [mem_ggFix]
      have hcomm : g * s' = s' * g := by
        apply hinj
        rw [map_mul, map_mul, hsx, hg]
        exact Subgroup.mem_centralizer_singleton_iff.mp y.2
      have h : s' * g * s'⁻¹ = g := by
        calc s' * g * s'⁻¹ = (g * s') * s'⁻¹ := by rw [hcomm]
          _ = g := by group
      simpa [δ, MulAut.conj_apply] using h
    refine ⟨⟨g, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hg
  haveI : Group.IsSolvable ↥(ggFix δ) := hsol
  exact Group.isSolvable_of_surjective (f := f) hsurj

end CFSG.StandardType.QTwo

end
