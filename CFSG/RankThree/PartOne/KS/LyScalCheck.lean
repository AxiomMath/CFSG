module

public import Certificates.Certificate14986
public import CFSG.RankThree.PartOne.KS.ScalFiveCheck
public import CFSG.Sporadic.Ly

public section

namespace CFSG.RankThree.PartOne.KS.LyScal

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ CFSG.Sporadic.Ly
  CFSG.RankThree.PartOne.KS.ScalFive
open scoped Matrix

theorem lyScal_check : lyScalCheck = true :=
  Certificates.certificate14986

theorem exM_lt : ∀ i j, lyData.exM i j < 5 := by decide +kernel

theorem exS_lt : ∀ i j, lyData.exS i j < 5 := by decide +kernel

theorem rT_lt : lyData.rT < 5 := by decide

theorem exM_zero_one : lyData.exM 0 1 = 1 := by decide

theorem iQ_lt : ∀ j, lyData.iQ j < lyData.nreg := by decide +kernel

theorem iZ_lt : lyData.iZ < lyData.nreg := by decide

theorem iS_lt : lyData.iS < lyData.nreg := by decide

theorem iT_lt : lyData.iT < lyData.nreg := by decide

@[expose] def Minv : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 4, 1, 3; 1, 0, 0, 0; 4, 0, 0, 4; 2, 0, 1, 0]

theorem Mm_mul_Minv : lyData.Mm * Minv = 1 := by decide +kernel

theorem Mm_isUnit_det : IsUnit lyData.Mm.det := Matrix.isUnit_det_of_right_inverse Mm_mul_Minv

theorem Sm_ne_one : lyData.Sm ≠ 1 := by decide +kernel

theorem rT_sq : ((lyData.rT : ℕ) : ZMod 5) ^ 2 ≠ 1 := by decide +kernel

theorem rT_cube : ((lyData.rT : ℕ) : ZMod 5) ^ 3 ≠ 1 := by decide +kernel

theorem factorization_card_Ly_five :
    (Nat.card NativeSporadic.Ly).factorization 5 = 6 := by
  rw [CFSG.Sporadic.Ly.card_Ly,
    show 51765179004000000 = 5 ^ 6 * 3312971456256 by norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Inst


abbrev φLy : GL (Fin 111) (ZMod 5) →* Matrix (Fin 111) (Fin 111) (ZMod 5) := Units.coeHom _

theorem φLy_injective : Function.Injective φLy := Units.val_injective

theorem φ_gA : φLy gA = mA := rfl

theorem φ_gB : φLy gB = mB := rfl

theorem gA_mul_self : gA * gA = 1 := Units.ext (by
  show mA * mA = 1
  exact mA_sq)

theorem gA_inv : gA⁻¹ = gA := inv_eq_of_mul_eq_one_right gA_mul_self

theorem gB_pow : gB ^ 5 = 1 := Units.ext (by
  rw [Units.val_pow_eq_pow_val]
  exact mB_pow)

theorem gB_inv : gB⁻¹ = gB ^ 4 := inv_eq_of_mul_eq_one_right (by
  rw [← pow_succ']
  exact gB_pow)

theorem rep_gA : Rep (specP 5 111) φLy gA
    ((opsP 5 111).decode NativeSporadic.LySeed1, (opsP 5 111).decode NativeSporadic.LySeed1) := by
  have hw := (specP 5 111).decode_wf NativeSporadic.LySeed1
  refine rep_of hw hw ?_ ?_
  · rw [(specP 5 111).toMat_decode, φ_gA]
  · rw [(specP 5 111).toMat_decode, gA_inv, φ_gA]

theorem rep_gB : Rep (specP 5 111) φLy gB
    ((opsP 5 111).decode NativeSporadic.LySeed2,
      (opsP 5 111).pow ((opsP 5 111).decode NativeSporadic.LySeed2) 4) := by
  have hw := (specP 5 111).decode_wf NativeSporadic.LySeed2
  refine rep_of hw ((specP 5 111).pow_spec hw 4).1 ?_ ?_
  · rw [(specP 5 111).toMat_decode, φ_gB]
  · rw [((specP 5 111).pow_spec hw 4).2, (specP 5 111).toMat_decode, gB_inv, map_pow, φ_gB]

@[expose] noncomputable def Rg : ℕ → GL (Fin 111) (ZMod 5) :=
  runProg (initRegs gA gB) lyData.prog

theorem Rg_mem (r : ℕ) : Rg r ∈ J := by
  have hgA : gA ∈ J := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgB : gB ∈ J := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact runProg_mem J lyData.prog (initRegs_mem J hgA hgB) r

theorem lyScal_regsRep (h : lyScalCheck = true) :
    RegsRep (specP 5 111) φLy lyData.nreg Rg lyRegs := by
  have hprog : lyData.prog.all (Instr.lt lyData.nreg) = true := by
    simp only [lyScalCheck, Bool.and_eq_true] at h
    exact h.1
  exact regsRep_runProg lyData.prog hprog (regsRep_initRegs rep_gA rep_gB)

theorem lyScal_rel :
    ScalRel (fun j => Rg (lyData.iQ j)) (Rg lyData.iZ) (Rg lyData.iS) (Rg lyData.iT) lyData.Mm
      lyData.Sm 0 1 lyData.cs ((lyData.rT : ℕ) : ZMod 5) lyData.ct := by
  have h : lyScalCheck = true := lyScal_check
  have hrels : relsOK (opsP 5 111) lyData lyRegs = true := by
    simp only [lyScalCheck, Bool.and_eq_true] at h
    exact h.2
  exact relsOK_sound lyData φLy_injective (lyScal_regsRep h).2 iQ_lt iZ_lt iS_lt iT_lt exM_lt
    exS_lt rT_lt Mm_isUnit_det exM_zero_one hrels

theorem lyKernelTrivial :
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* NativeSporadic.Ly),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 5 π.ker → π.ker = ⊥ := by
  intro E _ _ _ π hπ hC hpg
  let e : NativeSporadic.Ly ≃* J := lyEquivJ
  let ι : NativeSporadic.Ly →* GL (Fin 111) (ZMod 5) := J.subtype.comp (e : NativeSporadic.Ly →* J)
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιe : ∀ r, ι (e.symm ⟨Rg r, Rg_mem r⟩) = Rg r := fun r => by
    show ((e (e.symm ⟨Rg r, Rg_mem r⟩) : J) : GL (Fin 111) (ZMod 5)) = Rg r
    rw [MulEquiv.apply_symm_apply]
  have hrel : ScalRel (fun j => e.symm ⟨Rg (lyData.iQ j), Rg_mem _⟩)
      (e.symm ⟨Rg lyData.iZ, Rg_mem _⟩) (e.symm ⟨Rg lyData.iS, Rg_mem _⟩)
      (e.symm ⟨Rg lyData.iT, Rg_mem _⟩) lyData.Mm lyData.Sm 0 1 lyData.cs
      ((lyData.rT : ℕ) : ZMod 5) lyData.ct := by
    apply ScalRel.of_injective ι hι
    simp only [hιe]
    exact lyScal_rel
  have hfin : Finite NativeSporadic.Ly :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Ly.card_Ly]; norm_num)
  exact hrel.kernelTrivial Sm_ne_one rT_sq rT_cube factorization_card_Ly_five.le π hπ hC hpg

end Inst

end CFSG.RankThree.PartOne.KS.LyScal
