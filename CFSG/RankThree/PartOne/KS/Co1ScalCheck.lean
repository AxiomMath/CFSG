module

public import Certificates.Certificate14987
public import CFSG.RankThree.PartOne.KS.ScalFiveCheck
public import CFSG.Sporadic.Co1

public section

namespace CFSG.RankThree.PartOne.KS.Co1Scal

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
  CFSG.Sporadic.GLQ CFSG.RankThree.PartOne.KS.ScalFive
open scoped Matrix

theorem co1Scal_check : co1ScalCheck = true :=
  Certificates.certificate14987

theorem exM_lt : ∀ i j, co1Data.exM i j < 5 := by decide +kernel

theorem exS_lt : ∀ i j, co1Data.exS i j < 5 := by decide +kernel

theorem rT_lt : co1Data.rT < 5 := by decide

theorem exM_zero_one : co1Data.exM 0 1 = 1 := by decide

theorem iQ_lt : ∀ j, co1Data.iQ j < co1Data.nreg := by decide +kernel

theorem iZ_lt : co1Data.iZ < co1Data.nreg := by decide

theorem iS_lt : co1Data.iS < co1Data.nreg := by decide

theorem iT_lt : co1Data.iT < co1Data.nreg := by decide

@[expose] def Minv : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 4; 1, 0]

theorem Mm_mul_Minv : co1Data.Mm * Minv = 1 := by decide +kernel

theorem Mm_isUnit_det : IsUnit co1Data.Mm.det := Matrix.isUnit_det_of_right_inverse Mm_mul_Minv

theorem Sm_ne_one : co1Data.Sm ≠ 1 := by decide +kernel

theorem rT_sq : ((co1Data.rT : ℕ) : ZMod 5) ^ 2 ≠ 1 := by decide +kernel

theorem rT_cube : ((co1Data.rT : ℕ) : ZMod 5) ^ 3 ≠ 1 := by decide +kernel

theorem factorization_card_Co1_five :
    (Nat.card NativeSporadic.Co1).factorization 5 = 4 := by
  rw [CFSG.Sporadic.Co1.card_Co1,
    show 4157776806543360000 = 5 ^ 4 * 6652442890469376 by norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Inst


abbrev SM : Submonoid (Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
  NativeSporadic.seedMonoid 2 24 1 NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2

abbrev mA : Matrix (Fin 24) (Fin 24) (ZMod 2) := NativeSporadic.decode 2 24 1 NativeSporadic.Co1Seed1

abbrev mB : Matrix (Fin 24) (Fin 24) (ZMod 2) := NativeSporadic.decode 2 24 1 NativeSporadic.Co1Seed2

theorem hA_check : powOK (ops2 24) ((ops2 24).decode NativeSporadic.Co1Seed1) 2 = true := by
  have h : co1ScalCheck = true := co1Scal_check
  simp only [co1ScalCheck, Bool.and_eq_true] at h
  exact h.1.1.2

theorem hB_check : powOK (ops2 24) ((ops2 24).decode NativeSporadic.Co1Seed2) 3 = true := by
  have h : co1ScalCheck = true := co1Scal_check
  simp only [co1ScalCheck, Bool.and_eq_true] at h
  exact h.1.2

theorem mA_sq : mA ^ 2 = 1 := by
  have h := (spec2 24).pow_eq_one_of_check ((spec2 24).decode_wf _) hA_check
  rwa [(spec2 24).toMat_decode] at h

theorem mB_cube : mB ^ 3 = 1 := by
  have h := (spec2 24).pow_eq_one_of_check ((spec2 24).decode_wf _) hB_check
  rwa [(spec2 24).toMat_decode] at h

theorem mA_mem : mA ∈ SM := Submonoid.subset_closure (Set.mem_insert _ _)

theorem mB_mem : mB ∈ SM := Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def gA : SMˣ := unitOf SM mA_mem two_ne_zero mA_sq

@[expose] noncomputable def gB : SMˣ := unitOf SM mB_mem three_ne_zero mB_cube

theorem gA_sq : gA ^ 2 = 1 := unitOf_pow SM _ _ _

theorem gB_cube : gB ^ 3 = 1 := unitOf_pow SM _ _ _

theorem φ_gA : valHom SM gA = mA := valHom_unitOf SM _ _ _

theorem φ_gB : valHom SM gB = mB := valHom_unitOf SM _ _ _

theorem φ_gA_inv : valHom SM gA⁻¹ = mA := by
  rw [valHom_inv_of_pow SM two_ne_zero gA_sq, φ_gA]
  simp

theorem φ_gB_inv : valHom SM gB⁻¹ = mB ^ 2 := by
  rw [valHom_inv_of_pow SM three_ne_zero gB_cube, φ_gB]

theorem rep_gA : Rep (spec2 24) (valHom SM) gA
    ((ops2 24).decode NativeSporadic.Co1Seed1, (ops2 24).decode NativeSporadic.Co1Seed1) :=
  rep_of ((spec2 24).decode_wf _) ((spec2 24).decode_wf _)
    (by rw [(spec2 24).toMat_decode, φ_gA]) (by rw [(spec2 24).toMat_decode, φ_gA_inv])

theorem rep_gB : Rep (spec2 24) (valHom SM) gB
    ((ops2 24).decode NativeSporadic.Co1Seed2,
      (ops2 24).pow ((ops2 24).decode NativeSporadic.Co1Seed2) 2) :=
  rep_of ((spec2 24).decode_wf _) ((spec2 24).pow_spec ((spec2 24).decode_wf _) 2).1
    (by rw [(spec2 24).toMat_decode, φ_gB])
    (by rw [((spec2 24).pow_spec ((spec2 24).decode_wf _) 2).2, (spec2 24).toMat_decode, φ_gB_inv])

@[expose] noncomputable def Rg : ℕ → SMˣ := runProg (initRegs gA gB) co1Data.prog

theorem co1Scal_regsRep (h : co1ScalCheck = true) :
    RegsRep (spec2 24) (valHom SM) co1Data.nreg Rg co1Regs := by
  have hprog : co1Data.prog.all (Instr.lt co1Data.nreg) = true := by
    simp only [co1ScalCheck, Bool.and_eq_true] at h
    exact h.1.1.1
  exact regsRep_runProg co1Data.prog hprog (regsRep_initRegs rep_gA rep_gB)

theorem co1Scal_rel :
    ScalRel (fun j => Rg (co1Data.iQ j)) (Rg co1Data.iZ) (Rg co1Data.iS) (Rg co1Data.iT)
      co1Data.Mm co1Data.Sm 0 1 co1Data.cs ((co1Data.rT : ℕ) : ZMod 5) co1Data.ct := by
  have h : co1ScalCheck = true := co1Scal_check
  have hrels : relsOK (ops2 24) co1Data co1Regs = true := by
    simp only [co1ScalCheck, Bool.and_eq_true] at h
    exact h.2
  exact relsOK_sound co1Data (valHom_injective SM) (co1Scal_regsRep h).2 iQ_lt iZ_lt iS_lt iT_lt
    exM_lt exS_lt rT_lt Mm_isUnit_det exM_zero_one hrels

theorem co1KernelTrivial :
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* NativeSporadic.Co1),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 5 π.ker → π.ker = ⊥ := by
  intro E _ _ _ π hπ hC hpg
  have hfin : Finite NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  exact co1Scal_rel.kernelTrivial Sm_ne_one rT_sq rT_cube factorization_card_Co1_five.le π hπ hC hpg

end Inst

end CFSG.RankThree.PartOne.KS.Co1Scal
