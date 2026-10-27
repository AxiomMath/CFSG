module

public import Certificates.Kernel.BabyMonster.Stab.Integral
public import Certificates.Kernel.BabyMonster.Ck
public import Certificates.Kernel.BabyMonster.Stab.Mono0
public import Certificates.Kernel.BabyMonster.Stab.Mono1
public import Certificates.Kernel.BabyMonster.Stab.Mono2
public import Certificates.Kernel.BabyMonster.Stab.Sparse
public import Certificates.Kernel.BabyMonster.ChainN
public import CFSG.Certificates.Kernel.BabyMonster.DyConjUse
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Lab
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Bind0
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Bind1
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Bind2
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Bind3
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Bind4
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel11
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel14
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel15
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel16
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel17
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel18
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel20
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel22
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Rel23
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.All

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt CFSG.KC.BM.Fix CFSG.KC.BM.Ln
  CFSG.Monster.B.Dyadic CFSG.Monster.B.Dyadic.Native CFSG.KC.BSeed CertificateChecks.KernelBM.Pkt
open scoped Matrix

set_option maxRecDepth 100000

@[expose] noncomputable def Sg (g : ℕ) : Matrix (Fin 4371) (Fin 4371) (ZMod 2) := rowsMat 4371 (recOf (Ck.getD g []))

@[expose] noncomputable def cjMs : List (List ℕ) :=
  [CFSG.KC.BM.Dyadic.M0.b0, CFSG.KC.BM.Dyadic.M1.b0, CFSG.KC.BM.Dyadic.M2.b0, CFSG.KC.BM.Dyadic.M3.b0,
    CFSG.KC.BM.Dyadic.M4.b0, CFSG.KC.BM.Dyadic.M5.b0, CFSG.KC.BM.Dyadic.M6.b0, CFSG.KC.BM.Dyadic.M7.b0,
    CFSG.KC.BM.Dyadic.M8.b0, CFSG.KC.BM.Dyadic.M9.b0, CFSG.KC.BM.Dyadic.M10.b0, CFSG.KC.BM.Dyadic.M11.b0,
    CFSG.KC.BM.Dyadic.M12.b0, CFSG.KC.BM.Dyadic.M13.b0, CFSG.KC.BM.Dyadic.M14.b0, CFSG.KC.BM.Dyadic.M15.b0,
    CFSG.KC.BM.Dyadic.M16.b0, CFSG.KC.BM.Dyadic.M17.b0, CFSG.KC.BM.Dyadic.M18.b0, CFSG.KC.BM.Dyadic.M19.b0,
    CFSG.KC.BM.Dyadic.M20.b0, CFSG.KC.BM.Dyadic.M21.b0, CFSG.KC.BM.Dyadic.M22.b0, CFSG.KC.BM.Dyadic.M23.b0]

@[expose] noncomputable def cjGs : List (List ℕ) :=
  [CFSG.KC.BM.Dyadic.G0.b0, CFSG.KC.BM.Dyadic.G1.b0, CFSG.KC.BM.Dyadic.G2.b0, CFSG.KC.BM.Dyadic.G3.b0,
    CFSG.KC.BM.Dyadic.G4.b0, CFSG.KC.BM.Dyadic.G5.b0, CFSG.KC.BM.Dyadic.G6.b0, CFSG.KC.BM.Dyadic.G7.b0,
    CFSG.KC.BM.Dyadic.G8.b0, CFSG.KC.BM.Dyadic.G9.b0, CFSG.KC.BM.Dyadic.G10.b0, CFSG.KC.BM.Dyadic.G11.b0,
    CFSG.KC.BM.Dyadic.G12.b0, CFSG.KC.BM.Dyadic.G13.b0, CFSG.KC.BM.Dyadic.G14.b0, CFSG.KC.BM.Dyadic.G15.b0,
    CFSG.KC.BM.Dyadic.G16.b0, CFSG.KC.BM.Dyadic.G17.b0, CFSG.KC.BM.Dyadic.G18.b0, CFSG.KC.BM.Dyadic.G19.b0,
    CFSG.KC.BM.Dyadic.G20.b0, CFSG.KC.BM.Dyadic.G21.b0, CFSG.KC.BM.Dyadic.G22.b0, CFSG.KC.BM.Dyadic.G23.b0]

@[expose] noncomputable def ltr (g : ℕ) : Letter :=
  (nthLL cjMs g, nthN (nthLL cjGs g) 1, nthN (nthLL cjGs g) 0)

theorem monoOK : ∀ g < 24, MonoOK (ltr g).1 (ltr g).2.2 (ltr g).2.1 := by
  intro g hg
  unfold MonoOK
  interval_cases g <;> refine ⟨?_, ?_, ?_⟩ <;> quickRfl

theorem monoOK_list : ∀ gs : List ℕ, (∀ g ∈ gs, g < 24) →
    ∀ l ∈ gs.map ltr, MonoOK l.1 l.2.2 l.2.1 := by
  intro gs hgs l hl
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hl
  exact monoOK g (hgs g hg)

theorem bzq_unit : IsUnit Bzq.det := by
  obtain ⟨-, hdiag, hlow, -, -⟩ := fact3102_of
  have hU : Bzq.IsUpperTriangular := fun i j hij => by
    simp only [Bzq]
    rw [hlow i j hij]
    simp
  rw [Matrix.det_of_isUpperTriangular hU]
  refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  simp only [Bzq]
  rw [hdiag i]
  positivity

theorem cnum_cn (g : Fin 26) (hg : (g : ℕ) < 24) : Cnum g = Cn Bzq (mkMat (ltr g).2.2) := by
  unfold Cnum Cn
  congr 2
  ext t u
  unfold Mq mkMat
  rw [numer_eq g t u t.2 u.2, Nk, ite_eq_left hg]
  have : nthN monoTs g = nthN (nthLL cjGs g) 0 := by
    rcases g with ⟨g, hg'⟩
    simp only at hg ⊢
    interval_cases g <;> rfl
  rw [this]
  rfl

theorem rep_of_stab (g : Fin 26) {N : ℕ → ℕ → ℤ} {r : ℕ → ℕ}
    (hst : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs N (r i) i)
    (hnum : ∀ t u : ℕ, t < 4371 → u < 4371 → numer g t u = N t u) :
    IntRep (Cnum g) (rowsMat 4371 r) := by
  obtain ⟨C, hC, hp⟩ := cnum_int g hst hnum
  refine ⟨C, hC, ?_⟩
  ext i t
  rw [Matrix.map_apply, eq_intCast, ← ZMod.intCast_mod, Nat.cast_ofNat, hp i t]
  unfold rowsMat
  split <;> simp

theorem rep0 : IntRep (Cnum 0) (Sg 0) := rep_of_stab 0 stab0 (numer_eq 0)
theorem rep1 : IntRep (Cnum 1) (Sg 1) := rep_of_stab 1 stab1 (numer_eq 1)
theorem rep2 : IntRep (Cnum 2) (Sg 2) := rep_of_stab 2 stab2 (numer_eq 2)
theorem rep3 : IntRep (Cnum 3) (Sg 3) := rep_of_stab 3 stab3 (numer_eq 3)
theorem rep4 : IntRep (Cnum 4) (Sg 4) := rep_of_stab 4 stab4 (numer_eq 4)
theorem rep5 : IntRep (Cnum 5) (Sg 5) := rep_of_stab 5 stab5 (numer_eq 5)
theorem rep6 : IntRep (Cnum 6) (Sg 6) := rep_of_stab 6 stab6 (numer_eq 6)
theorem rep7 : IntRep (Cnum 7) (Sg 7) := rep_of_stab 7 stab7 (numer_eq 7)
theorem rep8 : IntRep (Cnum 8) (Sg 8) := rep_of_stab 8 stab8 (numer_eq 8)
theorem rep9 : IntRep (Cnum 9) (Sg 9) := rep_of_stab 9 stab9 (numer_eq 9)
theorem rep10 : IntRep (Cnum 10) (Sg 10) := rep_of_stab 10 stab10 (numer_eq 10)
theorem rep12 : IntRep (Cnum 12) (Sg 12) := rep_of_stab 12 stab12 (numer_eq 12)
theorem rep13 : IntRep (Cnum 13) (Sg 13) := rep_of_stab 13 stab13 (numer_eq 13)
theorem rep19 : IntRep (Cnum 19) (Sg 19) := rep_of_stab 19 stab19 (numer_eq 19)
theorem rep21 : IntRep (Cnum 21) (Sg 21) := rep_of_stab 21 stab21 (numer_eq 21)
theorem rep24 : IntRep (Cnum 24) (Sg 24) := rep_of_stab 24 stab24 (numer_eq 24)
theorem rep25 : IntRep (Cnum 25) (Sg 25) := rep_of_stab 25 stab25 (numer_eq 25)

theorem lenC (g : ℕ) (hg : g < 26) : (Ck.getD g []).length = 69 := by
  rw [← dyLenLL_eq]
  interval_cases g <;> decide

theorem bind1 : Sg 1 = stripMatn CFSG.KC.BM.DyConj.S1 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b1_ 69) (lenC 1 (by decide)) CFSG.KC.BM.DyConj.wf1
theorem bind2 : Sg 2 = stripMatn CFSG.KC.BM.DyConj.S2 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b2_ 69) (lenC 2 (by decide)) CFSG.KC.BM.DyConj.wf2
theorem bind3 : Sg 3 = stripMatn CFSG.KC.BM.DyConj.S3 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b3_ 69) (lenC 3 (by decide)) CFSG.KC.BM.DyConj.wf3
theorem bind4 : Sg 4 = stripMatn CFSG.KC.BM.DyConj.S4 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b4_ 69) (lenC 4 (by decide)) CFSG.KC.BM.DyConj.wf4
theorem bind5 : Sg 5 = stripMatn CFSG.KC.BM.DyConj.S5 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b5_ 69) (lenC 5 (by decide)) CFSG.KC.BM.DyConj.wf5
theorem bind6 : Sg 6 = stripMatn CFSG.KC.BM.DyConj.S6 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b6_ 69) (lenC 6 (by decide)) CFSG.KC.BM.DyConj.wf6
theorem bind7 : Sg 7 = stripMatn CFSG.KC.BM.DyConj.S7 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b7_ 69) (lenC 7 (by decide)) CFSG.KC.BM.DyConj.wf7
theorem bind9 : Sg 9 = stripMatn CFSG.KC.BM.DyConj.S9 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b9_ 69) (lenC 9 (by decide)) CFSG.KC.BM.DyConj.wf9
theorem bind10 : Sg 10 = stripMatn CFSG.KC.BM.DyConj.S10 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b10_ 69) (lenC 10 (by decide)) CFSG.KC.BM.DyConj.wf10
theorem bind11 : Sg 11 = stripMatn CFSG.KC.BM.DyConj.S11 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b11_ 69) (lenC 11 (by decide)) CFSG.KC.BM.DyConj.wf11
theorem bind12 : Sg 12 = stripMatn CFSG.KC.BM.DyConj.S12 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b12_ 69) (lenC 12 (by decide)) CFSG.KC.BM.DyConj.wf12
theorem bind13 : Sg 13 = stripMatn CFSG.KC.BM.DyConj.S13 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b13_ 69) (lenC 13 (by decide)) CFSG.KC.BM.DyConj.wf13
theorem bind14 : Sg 14 = stripMatn CFSG.KC.BM.DyConj.S14 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b14_ 69) (lenC 14 (by decide)) CFSG.KC.BM.DyConj.wf14
theorem bind15 : Sg 15 = stripMatn CFSG.KC.BM.DyConj.S15 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b15_ 69) (lenC 15 (by decide)) CFSG.KC.BM.DyConj.wf15
theorem bind16 : Sg 16 = stripMatn CFSG.KC.BM.DyConj.S16 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b16_ 69) (lenC 16 (by decide)) CFSG.KC.BM.DyConj.wf16
theorem bind17 : Sg 17 = stripMatn CFSG.KC.BM.DyConj.S17 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b17_ 69) (lenC 17 (by decide)) CFSG.KC.BM.DyConj.wf17
theorem bind18 : Sg 18 = stripMatn CFSG.KC.BM.DyConj.S18 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b18_ 69) (lenC 18 (by decide)) CFSG.KC.BM.DyConj.wf18
theorem bind20 : Sg 20 = stripMatn CFSG.KC.BM.DyConj.S20 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b20_ 69) (lenC 20 (by decide)) CFSG.KC.BM.DyConj.wf20
theorem bind21 : Sg 21 = stripMatn CFSG.KC.BM.DyConj.S21 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b21_ 69) (lenC 21 (by decide)) CFSG.KC.BM.DyConj.wf21
theorem bind22 : Sg 22 = stripMatn CFSG.KC.BM.DyConj.S22 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b22_ 69) (lenC 22 (by decide)) CFSG.KC.BM.DyConj.wf22
theorem bind23 : Sg 23 = stripMatn CFSG.KC.BM.DyConj.S23 :=
  rows_eq_strips (by forall_lt_consts CFSG.KC.BM.DyConj.b23_ 69) (lenC 23 (by decide)) CFSG.KC.BM.DyConj.wf23

@[expose] def RepC (g : ℕ) : Prop := IntRep (Cn Bzq (mkMat (ltr g).2.2)) (Sg g)

theorem repC_of {g : ℕ} (hg : g < 24) (h : IntRep (Cnum ⟨g, by omega⟩) (Sg g)) : RepC g := by
  unfold RepC
  rw [← cnum_cn ⟨g, by omega⟩ hg]
  exact h

theorem rep_of_C {g : ℕ} (hg : g < 24) (h : RepC g) : IntRep (Cnum ⟨g, by omega⟩) (Sg g) := by
  rw [cnum_cn ⟨g, by omega⟩ hg]
  exact h

theorem repC1 : RepC 1 := repC_of (g := 1) (by decide) rep1
theorem repC2 : RepC 2 := repC_of (g := 2) (by decide) rep2
theorem repC3 : RepC 3 := repC_of (g := 3) (by decide) rep3
theorem repC4 : RepC 4 := repC_of (g := 4) (by decide) rep4
theorem repC5 : RepC 5 := repC_of (g := 5) (by decide) rep5
theorem repC6 : RepC 6 := repC_of (g := 6) (by decide) rep6
theorem repC7 : RepC 7 := repC_of (g := 7) (by decide) rep7
theorem repC9 : RepC 9 := repC_of (g := 9) (by decide) rep9
theorem repC10 : RepC 10 := repC_of (g := 10) (by decide) rep10
theorem repC12 : RepC 12 := repC_of (g := 12) (by decide) rep12
theorem repC13 : RepC 13 := repC_of (g := 13) (by decide) rep13
theorem repC21 : RepC 21 := repC_of (g := 21) (by decide) rep21

theorem rep14 : IntRep (Cnum 14) (Sg 14) := by
  refine rep_of_C (by decide) (derive_y bzq_unit (Ly := ltr 14) (Lx := ltr 13) (Lu := [ltr 9, ltr 10])
    (monoOK_list [14, 9, 10, 13] (by decide)) CFSG.KC.BM.DyConj.lab14 (Su := [Sg 9, Sg 10])
    (List.Forall₂.cons repC9 (List.Forall₂.cons repC10 List.Forall₂.nil)) repC13 ?_)
  rw [bind9, bind10, bind13, bind14]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S10]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf14, DyConj.wf9, DyConj.wf10, DyConj.wf13, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r14 69)

theorem rep15 : IntRep (Cnum 15) (Sg 15) := by
  refine rep_of_C (by decide) (derive_x bzq_unit (Ly := ltr 13) (Lx := ltr 15) (Lu := [ltr 3, ltr 1])
    (monoOK_list [13, 3, 1, 15] (by decide)) CFSG.KC.BM.DyConj.lab15 (Su := [Sg 3, Sg 1])
    (List.Forall₂.cons repC3 (List.Forall₂.cons repC1 List.Forall₂.nil)) repC13 ?_)
  rw [bind1, bind3, bind13, bind15]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S1]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf13, DyConj.wf3, DyConj.wf1, DyConj.wf15, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r15 69)

theorem rep16 : IntRep (Cnum 16) (Sg 16) := by
  refine rep_of_C (by decide) (derive_x bzq_unit (Ly := ltr 13) (Lx := ltr 16) (Lu := [ltr 4, ltr 10])
    (monoOK_list [13, 4, 10, 16] (by decide)) CFSG.KC.BM.DyConj.lab16 (Su := [Sg 4, Sg 10])
    (List.Forall₂.cons repC4 (List.Forall₂.cons repC10 List.Forall₂.nil)) repC13 ?_)
  rw [bind4, bind10, bind13, bind16]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S10]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf13, DyConj.wf4, DyConj.wf10, DyConj.wf16, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r16 69)

theorem rep17 : IntRep (Cnum 17) (Sg 17) := by
  refine rep_of_C (by decide) (derive_y bzq_unit (Ly := ltr 17) (Lx := ltr 16) (Lu := [ltr 2, ltr 9])
    (monoOK_list [17, 2, 9, 16] (by decide)) CFSG.KC.BM.DyConj.lab17 (Su := [Sg 2, Sg 9])
    (List.Forall₂.cons repC2 (List.Forall₂.cons repC9 List.Forall₂.nil)) (repC_of (g := 16) (by decide) rep16) ?_)
  rw [bind2, bind9, bind16, bind17]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S9]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf17, DyConj.wf2, DyConj.wf9, DyConj.wf16, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r17 69)

theorem rep18 : IntRep (Cnum 18) (Sg 18) := by
  refine rep_of_C (by decide) (derive_x bzq_unit (Ly := ltr 21) (Lx := ltr 18) (Lu := [ltr 10, ltr 2])
    (monoOK_list [21, 10, 2, 18] (by decide)) CFSG.KC.BM.DyConj.lab18 (Su := [Sg 10, Sg 2])
    (List.Forall₂.cons repC10 (List.Forall₂.cons repC2 List.Forall₂.nil)) repC21 ?_)
  rw [bind2, bind10, bind18, bind21]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S2]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf21, DyConj.wf10, DyConj.wf2, DyConj.wf18, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r18 69)

theorem rep22 : IntRep (Cnum 22) (Sg 22) := by
  refine rep_of_C (by decide) (derive_x bzq_unit (Ly := ltr 21) (Lx := ltr 22) (Lu := [ltr 9, ltr 10])
    (monoOK_list [21, 9, 10, 22] (by decide)) CFSG.KC.BM.DyConj.lab22 (Su := [Sg 9, Sg 10])
    (List.Forall₂.cons repC9 (List.Forall₂.cons repC10 List.Forall₂.nil)) repC21 ?_)
  rw [bind9, bind10, bind21, bind22]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S10]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf21, DyConj.wf9, DyConj.wf10, DyConj.wf22, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r22 69)

theorem rep20 : IntRep (Cnum 20) (Sg 20) := by
  refine rep_of_C (by decide) (derive_x bzq_unit (Ly := ltr 18) (Lx := ltr 20) (Lu := [ltr 1, ltr 3, ltr 2])
    (monoOK_list [18, 1, 3, 2, 20] (by decide)) CFSG.KC.BM.DyConj.lab20 (Su := [Sg 1, Sg 3, Sg 2])
    (List.Forall₂.cons repC1 (List.Forall₂.cons repC3 (List.Forall₂.cons repC2 List.Forall₂.nil)))
    (repC_of (g := 18) (by decide) rep18) ?_)
  rw [bind1, bind2, bind3, bind18, bind20]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S3, CFSG.KC.BM.DyConj.S2]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf18, DyConj.wf1, DyConj.wf3, DyConj.wf2, DyConj.wf20, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r20 69)

theorem rep23 : IntRep (Cnum 23) (Sg 23) := by
  refine rep_of_C (by decide) (derive_x bzq_unit (Ly := ltr 18) (Lx := ltr 23)
    (Lu := [ltr 4, ltr 5, ltr 7, ltr 7])
    (monoOK_list [18, 4, 5, 7, 7, 23] (by decide)) CFSG.KC.BM.DyConj.lab23 (Su := [Sg 4, Sg 5, Sg 7, Sg 7])
    (List.Forall₂.cons repC4 (List.Forall₂.cons repC5 (List.Forall₂.cons repC7
      (List.Forall₂.cons repC7 List.Forall₂.nil)))) (repC_of (g := 18) (by decide) rep18) ?_)
  rw [bind4, bind5, bind7, bind18, bind23]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S5, CFSG.KC.BM.DyConj.S7, CFSG.KC.BM.DyConj.S7]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf18, DyConj.wf4, DyConj.wf5, DyConj.wf7, DyConj.wf7, DyConj.wf23, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r23 69)

theorem rep11 : IntRep (Cnum 11) (Sg 11) := by
  refine rep_of_C (by decide) (derive_x bzq_unit (Ly := ltr 2) (Lx := ltr 11)
    (Lu := [ltr 4, ltr 12, ltr 6, ltr 4, ltr 10, ltr 10])
    (monoOK_list [2, 4, 12, 6, 4, 10, 10, 11] (by decide)) CFSG.KC.BM.DyConj.lab11
    (Su := [Sg 4, Sg 12, Sg 6, Sg 4, Sg 10, Sg 10])
    (List.Forall₂.cons repC4 (List.Forall₂.cons repC12 (List.Forall₂.cons repC6 (List.Forall₂.cons repC4
      (List.Forall₂.cons repC10 (List.Forall₂.cons repC10 List.Forall₂.nil)))))) repC2 ?_)
  rw [bind2, bind4, bind6, bind10, bind11, bind12]
  exact strip_rel (Us := [CFSG.KC.BM.DyConj.S12, CFSG.KC.BM.DyConj.S6, CFSG.KC.BM.DyConj.S4,
      CFSG.KC.BM.DyConj.S10, CFSG.KC.BM.DyConj.S10]) (by
      simp only [List.forall_mem_cons, List.cons_append, List.nil_append]
      exact ⟨DyConj.wf2, DyConj.wf4, DyConj.wf12, DyConj.wf6, DyConj.wf4, DyConj.wf10, DyConj.wf10,
        DyConj.wf11, fun _ h => nomatch h⟩)
    (by bm_stripsn CFSG.KC.BM.DyConj.r11 69)

theorem cnumRep : ∀ g : Fin 26, IntRep (Cnum g) (Sg g) := by
  intro g
  fin_cases g
  exacts [rep0, rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8, rep9, rep10, rep11, rep12, rep13, rep14,
    rep15, rep16, rep17, rep18, rep19, rep20, rep21, rep22, rep23, rep24, rep25]

end CertificateChecks.KernelBM.Dy

end
