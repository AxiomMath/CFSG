module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFourTwoFrame
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkClass
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Root
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

private theorem ker_le_center {d n : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφ : UnitTB.Model φ) :
    φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro g hg
  obtain ⟨c, hc⟩ := hφ.ker g hg
  have hcomm : ∀ M : Matrix (Fin d) (Fin d) K,
      diagonal (fun _ => c) * M = M * diagonal (fun _ => c) := by
    intro M
    show Matrix.scalar (Fin d) c * M = M * Matrix.scalar (Fin d) c
    exact Matrix.scalar_comm c (fun r' => mul_comm c r') M
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc]
  first
    | exact hcomm _
    | exact (hcomm _).symm

private theorem isSolvable_blockSU_small {K : Type} [Field K] [Finite K] {d : ℕ}
    (h : UnitaryFieldData 2 1 K) {I : Finset (Fin d)} (h1 : 1 ≤ I.card)
    (h3 : I.card ≤ 3) :
    Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := 1) I) := by
  haveI : Group.IsSolvable ↥(unitarySU 2 1 K I.card) :=
    SmallU.isSolvable_unitarySU_small h h1 h3
  let e := TableBUE.blockSUEquiv (K := K) (n := 1) I h
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom)
    (fun x y hxy => e.symm.injective hxy)

theorem ggTorusCompGenSC_psuFourTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    GGTorusCompGenSC 3 (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) := by
  intro E hE h3 hsc x hx hx1 J hJ
  exfalso
  obtain ⟨φ, hφ, hdiag⟩ := exists_model_diag_psuFourTwo hK hE
  obtain ⟨s, ⟨t, hst⟩, hsx⟩ := hdiag x hx
  classical
  let δ : MulAut ↥(unitarySU 2 1 K 4) := MulAut.conj s
  let a : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) := MulAut.conj x
  have hcompat : ∀ g : ↥(unitarySU 2 1 K 4), a (φ g) = φ (δ g) := by
    intro g
    show MulAut.conj x (φ g) = φ (MulAut.conj s g)
    simp only [MulAut.conj_apply, ← hsx, map_mul, map_inv]
  have ht : ∀ i : Fin 4, t i ≠ 0 := by
    have hprod : (∏ i : Fin 4, t i) = 1 := by
      have hdet := ((mem_unitarySU_iff hφ.field).mp s.2).1
      rw [hst, Matrix.det_diagonal] at hdet
      exact hdet
    intro i h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at hprod
    exact zero_ne_one hprod
  have hδ : ∀ g : ↥(unitarySU 2 1 K 4),
      (((δ g : ↥(unitarySU 2 1 K 4)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) * diagonal t =
        diagonal t * (((g : ↥(unitarySU 2 1 K 4)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) := by
    intro g
    have h : (δ g) * s = s * g := by
      show MulAut.conj s g * s = s * g
      rw [MulAut.conj_apply]
      group
    have hm := congrArg (fun x : ↥(unitarySU 2 1 K 4) =>
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
    simpa only [Subgroup.coe_mul, Units.val_mul, hst] using hm
  have hfix : ggFix a =
      Subgroup.centralizer ({x} : Set (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))) := by
    ext g
    dsimp only [a]
    rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc g * x = x * g * x⁻¹ * x := by rw [h]
        _ = x * g := by group
    · intro h
      rw [← h]
      group
  have hJ' : IsComponentOf J (ggFix a) := by
    rw [hfix]
    exact hJ
  have hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K 4) := ker_le_center hφ
  obtain ⟨Q, hQ, hQmap⟩ := SCFourCover.exists_isComponentOf_map_eq (ψ := φ) hφ.surj hker
    (a := δ) (φ := a) hcompat hJ'
  obtain ⟨i₀, hcard, hQeq⟩ :=
    eq_blockSU_of_isComponentOf_ggFix_diag hφ.field ht δ hδ hQ
  set I : Finset (Fin 4) := Finset.univ.filter (fun i => t i = t i₀) with hI
  have hcardI : 2 ≤ I.card := by simpa [hI] using hcard
  have hQeq' : Q = TableBUE.blockSU (K := K) (n := 1) I := by
    simpa [hI] using hQeq
  have hI4 : I.card < 4 := by
    have hle : I.card ≤ 4 := by
      have h := Finset.card_le_card (Finset.subset_univ I)
      simpa using h
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hIuniv : I = Finset.univ := Finset.eq_univ_of_card I (by simpa using h)
      have htconst : ∀ i : Fin 4, t i = t i₀ := by
        intro i
        have hi : i ∈ I := by rw [hIuniv]; exact Finset.mem_univ i
        simpa [hI] using hi
      have hscal : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          diagonal (fun _ => t i₀) := by
        rw [hst]
        exact Matrix.diagonal_eq_diagonal_iff.mpr htconst
      have hs1 : s = 1 := eq_one_of_scalar_suFourTwo hK hscal
      exact hx1 (by rw [← hsx, hs1, map_one])
  have hsolQ : Group.IsSolvable ↥Q := by
    rw [hQeq']
    exact isSolvable_blockSU_small hφ.field (by omega) (by omega)
  have hsolJ : Group.IsSolvable ↥J := by
    haveI : Group.IsSolvable ↥Q := hsolQ
    have hres := Group.isSolvable_of_surjective
      (f := (φ.comp Q.subtype).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype, hQmap] at hres
  have hperf : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  haveI : Group.IsPerfect ↥J := hperf
  haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
  haveI : Nontrivial ↥J :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  exact Group.IsPerfect.not_isSolvable ↥J hsolJ

end CFSG.StandardType
