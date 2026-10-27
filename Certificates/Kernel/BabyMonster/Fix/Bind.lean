module

public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.ForallLt
public import Certificates.Kernel.BabyMonster.ForallApply
public import Certificates.Kernel.BabyMonster.Facts3106
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.All
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check9
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check24
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Check9
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Check0
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Check1
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Check2

public section

namespace CertificateChecks.KernelBM.Fix

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.KC.BSeed CFSG.KC.BM.Lat CFSG.KC.BM.Dy CFSG.KC.YModel
open scoped Matrix

@[expose] noncomputable def blkLens (L : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun s => Nat.beq s (nat_lit 69))
    (fun blk _ ih s => andB (Nat.beq (lenL blk) (rowsSn (nat_lit 4371) s)) (ih (Nat.succ s))) L

theorem blkLens_sound : ∀ {L : List (List Nat)} {s : Nat}, blkLens L s = true →
    s + lenLL L = 69 ∧ ∀ t < lenLL L, lenL (lgetL L t) = rowsSn 4371 (s + t)
  | [], s, h => ⟨Nat.eq_of_beq_eq_true h, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | blk :: L, s, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨ih1, ih2⟩ := blkLens_sound h2
    have e : lenLL (blk :: L) = lenLL L + 1 := rfl
    refine ⟨by rw [e]; omega, fun t ht => ?_⟩
    rcases t with _ | t
    · exact Nat.eq_of_beq_eq_true h1
    · have e2 : lgetL (blk :: L) (t + 1) = lgetL L t := rfl
      rw [e2, ih2 t (by rw [e] at ht; omega)]
      congr 1
      omega

theorem lens_of {C : List (List Nat)} (h : blkLens C 0 = true) :
    lenLL C = 69 ∧ ∀ s < 69, lenL (lgetL C s) = rowsSn 4371 s := by
  obtain ⟨h1, h2⟩ := blkLens_sound h
  refine ⟨by omega, fun s hs => ?_⟩
  rw [h2 s (by omega), Nat.zero_add]

theorem lensC0 : blkLens FixedLine.C0.rows 0 = true := by quickRfl
theorem lensC1 : blkLens FixedLine.C1.rows 0 = true := by quickRfl
theorem lensC2 : blkLens FixedLine.C2.rows 0 = true := by quickRfl
theorem lensC3 : blkLens FixedLine.C3.rows 0 = true := by quickRfl
theorem lensC4 : blkLens FixedLine.C4.rows 0 = true := by quickRfl
theorem lensC5 : blkLens FixedLine.C5.rows 0 = true := by quickRfl
theorem lensC6 : blkLens FixedLine.C6.rows 0 = true := by quickRfl
theorem lensC7 : blkLens FixedLine.C7.rows 0 = true := by quickRfl
theorem lensC8 : blkLens FixedLine.C8.rows 0 = true := by quickRfl
theorem lensC9 : blkLens FixedLine.C9.rows 0 = true := by quickRfl
theorem lensC10 : blkLens FixedLine.C10.rows 0 = true := by quickRfl
theorem lensC11 : blkLens FixedLine.C11.rows 0 = true := by quickRfl
theorem lensC12 : blkLens FixedLine.C12.rows 0 = true := by quickRfl
theorem lensC13 : blkLens FixedLine.C13.rows 0 = true := by quickRfl
theorem lensC14 : blkLens FixedLine.C14.rows 0 = true := by quickRfl
theorem lensC15 : blkLens FixedLine.C15.rows 0 = true := by quickRfl
theorem lensC16 : blkLens FixedLine.C16.rows 0 = true := by quickRfl
theorem lensC17 : blkLens FixedLine.C17.rows 0 = true := by quickRfl
theorem lensC18 : blkLens FixedLine.C18.rows 0 = true := by quickRfl
theorem lensC19 : blkLens FixedLine.C19.rows 0 = true := by quickRfl
theorem lensC20 : blkLens FixedLine.C20.rows 0 = true := by quickRfl
theorem lensC21 : blkLens FixedLine.C21.rows 0 = true := by quickRfl
theorem lensC22 : blkLens FixedLine.C22.rows 0 = true := by quickRfl
theorem lensC23 : blkLens FixedLine.C23.rows 0 = true := by quickRfl
theorem lensC24 : blkLens FixedLine.C24.rows 0 = true := by quickRfl
theorem lensC25 : blkLens FixedLine.C25.rows 0 = true := by quickRfl

theorem lensAll : ∀ g < 26, blkLens (Dy.Ck.getD g []) 0 = true := by
  forall_lt_consts CertificateChecks.KernelBM.Fix.lensC 26

theorem f_eq : FixedLine.f = CFSG.Monster.B.Binary.Native.fixedVector := by
  have h : Nat.beq FixedLine.f CFSG.Monster.B.Binary.Native.fixedVector = true := by quickRfl
  exact Nat.eq_of_beq_eq_true h

theorem fixAt (g : ℕ) {C : List (List Nat)}
    (h : Nat.beq (vecMul C FixedLine.f) FixedLine.f = true) (hl : blkLens C 0 = true)
    (hC : C = Dy.Ck.getD g []) :
    vecOf FixedLine.f ᵥ* rowsMat 4371 (recOf (Dy.Ck.getD g [])) = vecOf FixedLine.f := by
  subst hC
  obtain ⟨hn, hl'⟩ := lens_of hl
  have hv := vecMul_sound hn hl' FixedLine.f
  rw [Nat.eq_of_beq_eq_true h] at hv
  exact hv.symm

theorem fix : ∀ g < 26,
    vecOf FixedLine.f ᵥ* rowsMat 4371 (recOf (Dy.Ck.getD g [])) = vecOf FixedLine.f := by
  forall_lt_vecmul CFSG.KC.BM.FixedLine.fix CertificateChecks.KernelBM.Fix.lensC 26
    CertificateChecks.KernelBM.Fix.fixAt


theorem msum : ∀ s < 69, eqL (xorBlocks (rowsSn 4371 s) (Dy.Ck.map fun C => lgetL C s))
    (lgetL FixedLine.M.rows s) = true := by
  forall_lt_consts CFSG.KC.BM.FixedLine.msum 69

theorem rows_M : rowsMat 4371 (recOf FixedLine.M.rows) = stripMatn FixedLine.M :=
  rowsMat_eq_stripMatn (R := FixedLine.M.rows) (S := FixedLine.M)
    (by bm_blocksn CFSG.KC.BM.FixedLine.rows_M 69) FixedLine.wf_M

theorem rows_C25 : rowsMat 4371 (recOf FixedLine.C25.rows) = stripMatn FixedLine.C25 :=
  rowsMat_eq_stripMatn (R := FixedLine.C25.rows) (S := FixedLine.C25)
    (by bm_blocksn CFSG.KC.BM.FixedLine.rows_C25 69) FixedLine.wf_C25

theorem rkM : stripMatn FixedLine.PM * stripMatn FixedLine.M = stripMatn FixedLine.QM := by
  have h := stripMatn_mul_of_allStrips (Ws := [FixedLine.M]) (A := FixedLine.PM)
    (C := FixedLine.QM)
    (by
      intro W hW
      rw [List.mem_singleton] at hW
      rw [hW]
      exact FixedLine.wf_M)
    FixedLine.wf_PM (by bm_stripsn CFSG.KC.BM.FixedLine.rkM 69)
  rw [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at h
  exact h

theorem shapeM : LinearIndependent (ZMod 2)
    (fun i : {i : Fin 4371 // i.val < 4370} => stripMatn FixedLine.QM i) :=
  shapeOKn_sound FixedLine.wf_QM FixedLine.shapeM

theorem rc : stripMatn FixedLine.R * stripMatn FixedLine.C25 = stripMatn FixedLine.RC := by
  have h := stripMatn_mul_of_allStrips (Ws := [FixedLine.C25]) (A := FixedLine.R)
    (C := FixedLine.RC)
    (by
      intro W hW
      rw [List.mem_singleton] at hW
      rw [hW]
      exact FixedLine.wf_C25)
    FixedLine.wf_R (by bm_stripsn CFSG.KC.BM.FixedLine.rc 69)
  rw [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at h
  exact h

theorem mp : stripMatn FixedLine.Mp =
    stripMatn FixedLine.M + stripMatn FixedLine.RC + stripMatn FixedLine.R := by
  refine xorStrips_sound ?_
  forall_lt_consts CFSG.KC.BM.FixedLine.mp 69

theorem mpinv : stripMatn FixedLine.Mp * stripMatn FixedLine.Mpi = 1 := by
  have h := stripMatn_mul_eq_one (Ws := [FixedLine.Mpi]) (A := FixedLine.Mp)
    (by
      intro W hW
      rw [List.mem_singleton] at hW
      rw [hW]
      exact FixedLine.wf_Mpi)
    FixedLine.wf_Mp (by bm_stripsn CFSG.KC.BM.FixedLine.mpinv 69)
  rw [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at h
  exact h

theorem quot0 : ∀ k < 4370, recOf FixedLine.Q0.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C0.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens0 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot0_ 69)

theorem quot25 : ∀ k < 4370, recOf FixedLine.Q25.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C25.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens25 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot25_ 69)

theorem rowsQ0 : rowsMat 4370 (recOf FixedLine.Q0.rows) = stripMat NativePair.Q0 := by
  have e : FixedLine.Q0.rows = NativePair.Q0.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q0.rows) (S := NativePair.Q0)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q0 69) NativePair24.wf_Q0

theorem rowsQ25 : rowsMat 4370 (recOf FixedLine.Q25.rows) = stripMat NativePair.Q25 := by
  have e : FixedLine.Q25.rows = NativePair.Q25.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q25.rows) (S := NativePair.Q25)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q25 69) NativePair24.wf_Q25

theorem rkQ0 : stripMat FixedLine.PQ0 * (stripMat NativePair.Q0 + 1) = stripMat FixedLine.QQ0 :=
  stripMat_mul_add_one NativePair24.wf_Q0 FixedLine.wf_PQ0
    (by bm_stripsx CFSG.KC.BM.FixedLine.rkQ0_ 69)

theorem rkQ25 :
    stripMat FixedLine.PQ25 * (stripMat NativePair.Q25 + 1) = stripMat FixedLine.QQ25 :=
  stripMat_mul_add_one NativePair24.wf_Q25 FixedLine.wf_PQ25
    (by bm_stripsx CFSG.KC.BM.FixedLine.rkQ25_ 69)

theorem shapeQ0 :
    LinearIndependent (ZMod 2)
        (fun i : {i : Fin 4370 // i.val < 1860} => stripMat FixedLine.QQ0 i) ∧
      ∀ i : Fin 4370, 1860 ≤ i.val → stripMat FixedLine.QQ0 i = 0 :=
  shapeOK_sound FixedLine.wf_QQ0 FixedLine.shapeQ0

theorem shapeQ25 :
    LinearIndependent (ZMod 2)
        (fun i : {i : Fin 4370 // i.val < 2862} => stripMat FixedLine.QQ25 i) ∧
      ∀ i : Fin 4370, 2862 ≤ i.val → stripMat FixedLine.QQ25 i = 0 :=
  shapeOK_sound FixedLine.wf_QQ25 FixedLine.shapeQ25

theorem echQ0 :
    LinearIndependent (ZMod 2)
      (fun i : {i : Fin 4370 // 1860 ≤ i.val} => stripMat FixedLine.PQ0 i) :=
  echFrom_sound FixedLine.wf_PQ0 FixedLine.echQ0

theorem echQ25 :
    LinearIndependent (ZMod 2)
      (fun i : {i : Fin 4370 // 2862 ≤ i.val} => stripMat FixedLine.PQ25 i) :=
  echFrom_sound FixedLine.wf_PQ25 FixedLine.echQ25

theorem q0sq : stripMat NativePair.Q0 * stripMat NativePair.Q0 = 1 := by
  have h := stripMat_mul_eq_one (Ws := [NativePair.Q0]) (A := NativePair.Q0)
    (by
      intro W hW
      rw [List.mem_singleton] at hW
      rw [hW]
      exact NativePair24.wf_Q0)
    NativePair24.wf_Q0 (by bm_strips CFSG.KC.BM.CTIB.sq1 69)
  rw [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at h
  exact h

theorem q25cube :
    stripMat NativePair.Q25 * stripMat NativePair.Q25 * stripMat NativePair.Q25 = 1 := by
  have h := stripMat_mul_eq_one (Ws := [NativePair.Q25, NativePair.Q25]) (A := NativePair.Q25)
    (by
      intro W hW
      rw [List.mem_cons, List.mem_singleton, or_self] at hW
      rw [hW]
      exact NativePair24.wf_Q25)
    NativePair24.wf_Q25 (by bm_strips CFSG.KC.BM.NativePair24.bcube 69)
  rw [List.map_cons, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_cons,
    List.foldl_nil] at h
  exact h

end CertificateChecks.KernelBM.Fix

end
