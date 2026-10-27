module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The `D₆` intersection transfer

Restriction (6) gives an index-six intersection `D/(D ∩ VU)`.  This module
transfers the ambient quotient `Ĥ/VU ≃ D₆` to the intersection itself.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- If `D = Ĥ ∩ Ĥʸ` has index six over `D ∩ VU`, then its quotient by that
intersection is the dihedral group of order six.  The normality instance in
the binder is needed only to make the quotient type available to Lean; it is
also reproved internally from normality of `VU` in `Ĥ`. -/
public theorem firstCase_klein_intersection_quotient_d6
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (_hy : IsInvolution y) (_hyH : y ∉ c.Hhat)
    (hindex :
      let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      (N.subgroupOf D).index = 6)
    [_hNnormal : let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      (N.subgroupOf D).Normal] :
    Nonempty (((c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G) ⧸
      ((c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G) ⊓
        (twoCoreOf c.Hhat ⊔ c.U)).subgroupOf
          (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) ≃*
      DihedralGroup 3) := by
  classical
  let A : Subgroup G := c.Hhat
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let D : Subgroup G := A ⊓ conjugateSubgroup A y
  let N : Subgroup G := D ⊓ B
  let B0 : Subgroup (↥A) := B.subgroupOf A
  have hBleA : B ≤ A := by
    have h26 := theorem_2_6 hmin c
    have hUeq : c.U = oddCoreOf c.Hhat := h26.1
    dsimp [A, B]
    apply sup_le
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · rw [hUeq]
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hBnorm : IsNormalIn B A := firstCase_klein_VU_normal_in_Hhat hmin c
  have hB0norm : B0.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hBleA).2
    intro a ha b hb
    exact hBnorm.2 ha hb a b
  let Bjoin : Subgroup (↥A) := pCore 2 A ⊔ pPrimeCore 2 A
  have hBjoinmap : Bjoin.map A.subtype = B := by
    have h26 := theorem_2_6 hmin c
    have hUeq : c.U = oddCoreOf c.Hhat := h26.1
    dsimp [A, B, Bjoin]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  have hBjoin0 : Bjoin = B0 := by
    ext z
    constructor
    · intro hz
      apply (Subgroup.mem_subgroupOf).2
      rw [← hBjoinmap]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    · intro hz
      have hzB : (z : G) ∈ B := (Subgroup.mem_subgroupOf).1 hz
      rw [← hBjoinmap] at hzB
      rcases Subgroup.mem_map.mp hzB with ⟨w, hw, hwz⟩
      have hweq : w = z := by
        apply Subtype.ext
        simpa using hwz
      simpa [hweq] using hw
  have hqcard : Nat.card (A ⧸ B0) = 6 := by
    obtain ⟨e⟩ := firstCase_klein_quotient_d6 hmin c hfirst hklein
    calc
      Nat.card (A ⧸ B0) = Nat.card (A ⧸ Bjoin) := by rw [hBjoin0]
      _ = Nat.card (DihedralGroup 3) := by
        simpa [A, Bjoin] using Nat.card_congr e.toEquiv
      _ = 6 := by rw [DihedralGroup.nat_card]
  let D0 : Subgroup (↥A) := D.subgroupOf A
  let fD0 : D0 →* (A ⧸ B0) := (QuotientGroup.mk' B0).comp D0.subtype
  let Q : Subgroup (A ⧸ B0) := fD0.range
  have hker : fD0.ker = B0.subgroupOf D0 := by
    ext z
    simpa [fD0, Subgroup.mem_subgroupOf] using
      (QuotientGroup.eq_one_iff (N := B0) (D0.subtype z))
  have hidxQ : (B0.subgroupOf D0).index = Nat.card Q := by
    rw [← hker]
    simpa [Q] using Subgroup.index_ker fD0
  have hNsubeq : B.subgroupOf D = N.subgroupOf D := by
    ext z
    change (z : G) ∈ B ↔ (z : G) ∈ D ∧ (z : G) ∈ B
    simp
  have hNnorm : (N.subgroupOf D).Normal := by
    apply (Subgroup.normal_subgroupOf_iff (show N ≤ D from inf_le_left)).2
    intro n d hn hd
    change d * n * d⁻¹ ∈ N
    refine ⟨?_, ?_⟩
    · exact D.mul_mem (D.mul_mem hd ((show N ≤ D from inf_le_left) hn))
        (D.inv_mem hd)
    · exact hBnorm.2 d ((show D ≤ A from inf_le_left) hd) n
        ((show N ≤ B from inf_le_right) hn)
  let : (N.subgroupOf D).Normal := hNnorm
  have hindex' : (B0.subgroupOf D0).index = 6 := by
    have hrel : (B0.subgroupOf D0).index = (N.subgroupOf D).index := by
      change (B.subgroupOf A).relIndex (D.subgroupOf A) = (N.subgroupOf D).index
      calc
        (B.subgroupOf A).relIndex (D.subgroupOf A) = B.relIndex D :=
          Subgroup.relIndex_subgroupOf (H := B) (K := D) (L := A)
            (by dsimp [D, A]; exact inf_le_left)
        _ = (N.subgroupOf D).index := by
          simpa [Subgroup.relIndex, hNsubeq]
    calc
      (B0.subgroupOf D0).index = (N.subgroupOf D).index := hrel
      _ = 6 := by simpa [A, B, D, N] using hindex
  have hQcard : Nat.card Q = 6 := by
    calc
      Nat.card Q = (B0.subgroupOf D0).index := hidxQ.symm
      _ = 6 := hindex'
  have hQtop : Q = ⊤ := Subgroup.eq_top_of_card_eq Q (by
    calc
      Nat.card Q = 6 := hQcard
      _ = Nat.card (A ⧸ B0) := hqcard.symm)
  let eRange : Q ≃* (A ⧸ B0) :=
    (MulEquiv.subgroupCongr hQtop).trans Subgroup.topEquiv
  obtain ⟨eA0⟩ := firstCase_klein_quotient_d6 hmin c hfirst hklein
  let eAjoin : (A ⧸ Bjoin) ≃* DihedralGroup 3 := by
    simpa [A, Bjoin] using eA0
  let eA : (A ⧸ B0) ≃* DihedralGroup 3 :=
    (QuotientGroup.quotientMulEquivOfEq hBjoin0.symm).trans eAjoin
  let eRange0 : Q ≃* (A ⧸ B0) := eRange
  let eD0 : (D0 ⧸ fD0.ker) ≃* DihedralGroup 3 :=
    (QuotientGroup.quotientKerEquivRange fD0).trans (eRange0.trans eA)
  let eDA : D ≃* D0 :=
    (Subgroup.subgroupOfEquivOfLe (show D ≤ A from inf_le_left)).symm
  let fD : D →* (A ⧸ B0) := fD0.comp eDA.toMonoidHom
  have hfker : fD.ker = N.subgroupOf D := by
    ext z
    change fD0 (eDA z) = 1 ↔ (z : G) ∈ N
    rw [← MonoidHom.mem_ker]
    rw [hker]
    have hzD0 : eDA z ∈ B0.subgroupOf D0 ↔ z ∈ B.subgroupOf D := by
      change (eDA z : G) ∈ B ↔ (z : G) ∈ B
      rfl
    rw [hzD0, hNsubeq]
    rfl
  have hfDsurj : Function.Surjective fD := by
    intro q
    obtain ⟨q0, hq0⟩ := (MonoidHom.range_eq_top.mp
      (show fD0.range = ⊤ by exact hQtop)) q
    obtain ⟨z, hz⟩ := eDA.surjective q0
    exact ⟨z, by simpa [fD, hz] using hq0⟩
  let eRangeD : fD.range ≃* (⊤ : Subgroup (A ⧸ B0)) :=
    MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hfDsurj)
  let e0 : D ⧸ fD.ker ≃* DihedralGroup 3 :=
    (QuotientGroup.quotientKerEquivRange fD).trans
      (eRangeD.trans (Subgroup.topEquiv.trans eA))
  have hquot : Nonempty (D ⧸ (N.subgroupOf D) ≃* DihedralGroup 3) := by
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hfker.symm).trans e0⟩
  simpa [A, B, D, N] using hquot

end CFSG.GorensteinWalter
