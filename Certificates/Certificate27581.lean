module

public import Certificates.Data.TitsAschbacherE32
public import Certificates.Kernel.EvenBN.Lists
public import Certificates.Kernel.SporSch.Tits.Inv2266
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27581

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCentral
open CertificateChecks.KernelSporSch.TitsHelp
open CertificateChecks.KernelSporSch.TitsInv CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
open Certificates.TitsAschbacherE32

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def cj (g x y : Nat) : Bool := Nat.beq (pc g x) (pc y g)

@[expose] noncomputable def MG : List Nat := (List.range 4).map TitsN.S ++ [Pi]

@[expose] noncomputable def eOK (e : Nat × Nat × List Nat) : Bool :=
  hLetters e.2.2 &&
    (if e.2.1 = 0 then Nat.beq (EL.getD e.1 0) (V 12)
    else if e.2.1 = 1 then cj (wP TitsH.S e.2.2) (V 11) (EL.getD e.1 0)
    else cj (wP TitsH.S e.2.2) (V 10) (EL.getD e.1 0))

@[expose] noncomputable def fOK (e : Nat × Nat × List Nat) : Bool :=
  nLetters e.2.2 &&
    (if e.2.1 = 1 then cj (wP TitsN.S e.2.2) (V 12) (FL.getD e.1 0)
    else if e.2.1 = 2 then cj (wP TitsN.S e.2.2) (V 10) (FL.getD e.1 0)
    else cj (wP TitsN.S e.2.2) (V 9) (FL.getD e.1 0)) &&
    (UL.any (Nat.beq (FL.getD e.1 0)) == decide (e.2.1 ≤ 2))

@[expose] noncomputable def cOK (e : Nat × List Nat × List Nat) : Bool :=
  hLetters e.2.1 && hLetters e.2.2 &&
    Nat.beq (pc (wP TitsH.S e.2.1) (wP TitsH.S e.2.2))
      (pc (pc (V e.1) (wP TitsH.S e.2.2)) (wP TitsH.S e.2.1))

theorem kAll : (eOrbData.all eOK && fOrbData.all fOK &&
    eGenData.all (fun e => Nat.beq (EL.getD e.1 0) (pc (EL.getD e.2.1 0) (EL.getD e.2.2 0))) &&
    MG.all (fun g => fIdx.all fun i => strictB (pc g (V i)) fun y => FL.any fun f => Nat.beq y (pc f g)) &&
    MG.all (fun g => [10, 11, 12].all fun i =>
      strictB (pc g (V i)) fun y => UL.any fun u => Nat.beq y (pc u g)) &&
    UL.all (fun a => UL.all fun b => strictB (pc a b) fun y => UL.any fun c => Nat.beq y c) &&
    (List.range 32).all (fun a => (List.range 32).all fun b =>
      a == b || !Nat.beq (FL.getD a 0) (FL.getD b 0)) &&
    cj (wP TitsN.S n0Word) TitsT (V 10) &&
    fCommData.all cOK) = true := by quickRfl

theorem mGens_eq : mGens = MG.map (unpack 1755 11) ∧ ∀ x ∈ MG, C x := by
  refine ⟨?_, fun x hx => ?_⟩
  · have e : (List.range 4).map (fun i => titsNArrs[i]!) =
        (List.range 4).map (unpack 1755 11 ∘ TitsN.S) :=
      List.map_congr_left fun i hi => bindsN.2.2.2.2.1 i (by simp at hi; omega)
    unfold mGens MG
    rw [List.map_append, List.map_map, pi_eq, e, List.map_cons, List.map_nil]
  · unfold MG at hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
      exact allN_spec canN i (by simp at hi; omega)
    · rw [List.mem_singleton.1 h]
      exact cPi

theorem cj_eq {g x y : Nat} (cg : C g) (cx : C x) (cy : C y) :
    conjToA (unpack 1755 11 g) (unpack 1755 11 x) (unpack 1755 11 y) = cj g x y := by
  unfold conjToA cj pc
  rw [cmpU cg cx, cmpU cy cg, eqU (cmpC cg cx) (cmpC cy cg)]

theorem vE {i : Nat} (hi : i < 13) : vA i = unpack 1755 11 (V i) ∧ C (V i) := v_eq hi

theorem E_get {i : Nat} (hi : i < 32) :
    (EL.map (unpack 1755 11)).getD i #[] = unpack 1755 11 (EL.getD i 0) ∧ C (EL.getD i 0) :=
  ⟨getD_mapU (by rw [EL_len]; exact hi), eArrs_eq.2 _ (getD_mem (by rw [EL_len]; exact hi))⟩

theorem F_get {i : Nat} (hi : i < 32) :
    (FL.map (unpack 1755 11)).getD i #[] = unpack 1755 11 (FL.getD i 0) ∧ C (FL.getD i 0) :=
  ⟨getD_mapU (by rw [FL_len]; exact hi), fArrs_eq.2 _ (getD_mem (by rw [FL_len]; exact hi))⟩

theorem p1 : eOrbData.all (eOrbOK (EL.map (unpack 1755 11))) = eOrbData.all eOK := by
  refine all_congr_mem fun e he => ?_
  have h1 : e.1 < 32 := by revert e; decide
  obtain ⟨hg, cg⟩ := E_get h1
  unfold eOrbOK eOK
  cases hl : hLetters e.2.2
  · rfl
  · obtain ⟨hh, ch⟩ := hW hl
    obtain ⟨h12, c12⟩ := vE (i := 12) (by decide)
    obtain ⟨h11, c11⟩ := vE (i := 11) (by decide)
    obtain ⟨h10, c10⟩ := vE (i := 10) (by decide)
    rw [hg, hh, h12, h11, h10, cj_eq ch c11 cg, cj_eq ch c10 cg, eqU cg c12]

theorem p2 : fOrbData.all (fOrbOK (FL.map (unpack 1755 11)) (UL.map (unpack 1755 11))) =
    fOrbData.all fOK := by
  refine all_congr_mem fun e he => ?_
  have h1 : e.1 < 32 := by revert e; decide
  obtain ⟨hg, cg⟩ := F_get h1
  unfold fOrbOK fOK
  cases hl : nLetters e.2.2
  · rfl
  · obtain ⟨hh, ch⟩ := nW hl
    obtain ⟨h12, c12⟩ := vE (i := 12) (by decide)
    obtain ⟨h10, c10⟩ := vE (i := 10) (by decide)
    obtain ⟨h9, c9⟩ := vE (i := 9) (by decide)
    rw [hg, hh, h12, h10, h9, cj_eq ch c12 cg, cj_eq ch c10 cg, cj_eq ch c9 cg,
      any_mapU (f := eqA 1755 (unpack 1755 11 (FL.getD e.1 0))) (g := Nat.beq (FL.getD e.1 0))
        u10Arrs_eq.2 fun x cx => eqU cg cx]

theorem p3 : eGenData.all (fun e => eqA 1755 ((EL.map (unpack 1755 11)).getD e.1 #[])
      (compA 1755 ((EL.map (unpack 1755 11)).getD e.2.1 #[])
        ((EL.map (unpack 1755 11)).getD e.2.2 #[]))) =
    eGenData.all (fun e => Nat.beq (EL.getD e.1 0) (pc (EL.getD e.2.1 0) (EL.getD e.2.2 0))) := by
  refine all_congr_mem fun e he => ?_
  have h : e.1 < 32 ∧ e.2.1 < 32 ∧ e.2.2 < 32 := by revert e; decide
  obtain ⟨g1, c1⟩ := E_get h.1
  obtain ⟨g2, c2⟩ := E_get h.2.1
  obtain ⟨g3, c3⟩ := E_get h.2.2
  rw [g1, g2, g3, cmpU c2 c3, eqU c1 (cmpC c2 c3)]
  rfl

theorem p4 : mGens.all (fun g => fIdx.all fun i => (FL.map (unpack 1755 11)).any fun f =>
      conjToA g (vA i) f) = MG.all (fun g => fIdx.all fun i =>
        strictB (pc g (V i)) fun y => FL.any fun f => Nat.beq y (pc f g)) := by
  rw [mGens_eq.1]
  refine all_mapU mGens_eq.2 fun g cg => all_congr_mem fun i hi => ?_
  have hi' : i < 13 := by revert i; decide
  obtain ⟨hv, cv⟩ := vE hi'
  rw [hv, strictB_app]
  exact any_mapU fArrs_eq.2 fun f cf => cj_eq cg cv cf

theorem p5 : mGens.all (fun g => [10, 11, 12].all fun i => (UL.map (unpack 1755 11)).any fun u =>
      conjToA g (vA i) u) = MG.all (fun g => [10, 11, 12].all fun i =>
        strictB (pc g (V i)) fun y => UL.any fun u => Nat.beq y (pc u g)) := by
  rw [mGens_eq.1]
  refine all_mapU mGens_eq.2 fun g cg => all_congr_mem fun i hi => ?_
  have hi' : i < 13 := by revert i; decide
  obtain ⟨hv, cv⟩ := vE hi'
  rw [hv, strictB_app]
  exact any_mapU u10Arrs_eq.2 fun f cf => cj_eq cg cv cf

theorem p6 : (UL.map (unpack 1755 11)).all (fun a => (UL.map (unpack 1755 11)).all fun b =>
      (UL.map (unpack 1755 11)).any (eqA 1755 (compA 1755 a b))) =
    UL.all (fun a => UL.all fun b => strictB (pc a b) fun y => UL.any fun c => Nat.beq y c) := by
  refine all_mapU u10Arrs_eq.2 fun a ca => all_mapU u10Arrs_eq.2 fun b cb => ?_
  rw [strictB_app]
  refine any_mapU u10Arrs_eq.2 fun c cc => ?_
  rw [cmpU ca cb, eqU (cmpC ca cb) cc]
  rfl

theorem p7 : (List.range 32).all (fun a => (List.range 32).all fun b =>
      a == b || !eqA 1755 ((FL.map (unpack 1755 11)).getD a #[])
        ((FL.map (unpack 1755 11)).getD b #[])) =
    (List.range 32).all (fun a => (List.range 32).all fun b =>
      a == b || !Nat.beq (FL.getD a 0) (FL.getD b 0)) := by
  refine all_congr_mem fun a ha => all_congr_mem fun b hb => ?_
  obtain ⟨ga, ca⟩ := F_get (List.mem_range.1 ha)
  obtain ⟨gb, cb⟩ := F_get (List.mem_range.1 hb)
  rw [ga, gb, eqU ca cb]

theorem p8 : (nLetters n0Word && conjToA (nArr n0Word) titsTArr (vA 10)) =
    cj (wP TitsN.S n0Word) TitsT (V 10) := by
  obtain ⟨hh, ch⟩ := nW (w := n0Word) (by decide)
  obtain ⟨hv, cv⟩ := vE (i := 10) (by decide)
  rw [hh, hv, t_eq, cj_eq ch cT cv]
  rfl

theorem p9 : fCommData.all (fun e => hLetters e.2.1 && hLetters e.2.2 &&
      eqA 1755 (compA 1755 (hArr e.2.1) (hArr e.2.2))
        (compA 1755 (compA 1755 (vA e.1) (hArr e.2.2)) (hArr e.2.1))) = fCommData.all cOK := by
  refine all_congr_mem fun e he => ?_
  have hi : e.1 < 13 := by revert e; decide
  obtain ⟨hv, cv⟩ := vE hi
  unfold cOK
  cases h1 : hLetters e.2.1
  · rfl
  · cases h2 : hLetters e.2.2
    · rfl
    · obtain ⟨ha, ca⟩ := hW h1
      obtain ⟨hb, cb⟩ := hW h2
      rw [ha, hb, hv, cmpU ca cb, cmpU cv cb, cmpU (cmpC cv cb) ca,
        eqU (cmpC ca cb) (cmpC (cmpC cv cb) ca)]
      rfl

theorem tits_e32_orb_check_0 : orbCheck () = true := by
  unfold orbCheck
  simp only []
  rw [eArrs_eq.1, fArrs_eq.1, u10Arrs_eq.1, p1, p2, p3, p4, p5, p6, p7, Bool.and_assoc _ (nLetters _),
    p8, p9]
  exact kAll

end CertificateChecks.Batch27581

namespace Certificates

open CertificateChecks

theorem certificate27581 : Certificates.TitsAschbacherE32.orbCheck () = true := by
  exact CertificateChecks.Batch27581.tits_e32_orb_check_0

end Certificates
