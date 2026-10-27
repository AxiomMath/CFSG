module

public import CFSG.RankThree.PartOne.SPOR.Co1PlanesData
public import Certificates.Kernel.Co1Planes.Checks
public import Certificates.Kernel.Co1ThreeK.GlueCensus
public import Certificates.Kernel.Co1B.Iota
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Planes

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.KC.Co1Census
  CFSG.KC.Co1Planes CFSG.RankThree.PartOne.SPOR CertificateChecks.KernelCo1ThreeK

theorem validRows_unpackW (X : Nat) :
    CFSG.Sporadic.Co1.InvNative.validRows (unpack 24 24 X) = true := by
  rw [← unpackR_eq_unpack]
  exact CFSG.KC.Co1F2.validRows_unpackR _

theorem getD_unpackK {M : Nat → Nat} {N : Nat} (k : Nat) :
    ((List.range N).map (fun i => unpack 24 24 (M i))).getD k (unpack 24 24 CFSG.KC.Co1B.oneK) =
      unpack 24 24 (getK M N k) := by
  rw [← one_unpack]
  exact getD_unpack k

theorem inv_one_unpack : inv (unpack 24 24 CFSG.KC.Co1B.oneK) = unpack 24 24 CFSG.KC.Co1B.oneK :=
  (invOKW_sound (X := CFSG.KC.Co1B.oneK) (Y := CFSG.KC.Co1B.oneK) (by quickRfl)).2

section Rows

variable {M MI : Nat → Nat} {N : Nat} (hinv : ∀ i < N, inv (unpack 24 24 (M i)) = unpack 24 24 (MI i))

include hinv in
theorem inv_getK (j : Nat) : inv (unpack 24 24 (getK M N j)) = unpack 24 24 (getK MI N j) := by
  unfold getK
  split
  · exact hinv j (by assumption)
  · exact inv_one_unpack

include hinv in
theorem conjProd_eq (T : Nat) : ∀ ws : List Nat,
    co1ConjProd ((List.range N).map fun i => unpack 24 24 (M i)) (unpack 24 24 T) ws =
      unpack 24 24 (conjProdK M MI N T ws)
  | [] => by rw [co1ConjProd, conjProdK, List.foldr_nil, List.foldr_nil, one_unpack]
  | k :: ws => by
    have ih := conjProd_eq T ws
    unfold co1ConjProd conjProdK at ih ⊢
    rw [List.foldr_cons, List.foldr_cons, ih, getD_unpack, inv_getK hinv, mul_unpackW,
      mul_unpackW, mul_unpackW]

include hinv in
theorem line_eq (T p X : Nat) (ws : List Nat) (ex : Nat) :
    co1LineOK ((List.range N).map fun i => unpack 24 24 (M i)) (unpack 24 24 T) p
      (unpack 24 24 X) ws ex = lineK M MI N T p X ws ex := by
  rw [Bool.eq_iff_iff]
  simp only [co1LineOK, lineK, conjProd_eq hinv, getD_unpack, getD_unpackK, inv_getK hinv,
    mul_unpackW,
    pow_unpackW, one_unpack, beq_unpackW, bne, validRows_unpackW, List.length_map,
    List.length_range, Bool.true_and, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    and_true, true_and]

include hinv in
theorem block1_eq (T : Nat) :
    co1Block1OK ((List.range N).map fun i => unpack 24 24 (M i)) (unpack 24 24 T) =
      block1K M MI N T := by
  funext b
  rw [Bool.eq_iff_iff]
  simp only [co1Block1OK, block1K, line_eq hinv, getD_unpack, getD_unpackK, mul_unpackW,
    pow_unpackW,
    one_unpack, beq_unpackW, bne, validRows_unpackW, List.length_map, List.length_range,
    Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and]

include hinv in
theorem block2_eq (T : Nat) :
    co1Block2OK ((List.range N).map fun i => unpack 24 24 (M i)) (unpack 24 24 T) =
      block2K M MI N T := by
  funext b
  rw [Bool.eq_iff_iff]
  simp only [co1Block2OK, block2K, line_eq hinv, getD_unpack, getD_unpackK, mul_unpackW,
    pow_unpackW,
    one_unpack, beq_unpackW, bne, validRows_unpackW, List.length_map, List.length_range,
    Bool.true_and, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_true, true_and]

include hinv in
theorem class_of (c : Co1PlaneClass)
    (hD : dag co1PlaneBase c.derivs = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true))
    (h : classK M MI N c = true) : co1ClassOK c = true := by
  have hlen : co1PlaneBase.length = 4 := rfl
  unfold co1ClassOK
  rw [hD]
  unfold classK at h
  simp only [getD_unpack, getD_unpackK, block1_eq hinv, block2_eq hinv, hlen, Bool.true_and] at h ⊢
  exact h

end Rows

theorem base_eq (P : Nat → Nat)
    (h : (Nat.beq (P 0) CFSG.KD.Co1B.SA && Nat.beq (P 1) CFSG.KD.Co1B.SB &&
      Nat.beq (P 2) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK CFSG.KD.Co1B.IRS 23) &&
      Nat.beq (P 3) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK CFSG.KD.Co1B.IRS 51)) = true) :
    co1PlaneBase = (List.range 4).map fun i => unpack 24 24 (P i) := by
  simp only [Bool.and_eq_true] at h
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  have ha : CertificateChecks.KernelSporSch.Co1Packed.PA = CFSG.KD.Co1B.SA := rfl
  have hb : CertificateChecks.KernelSporSch.Co1Packed.PB = CFSG.KD.Co1B.SB := rfl
  rw [co1PlaneBase, hr, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    CertificateChecks.KernelSporSch.Co1Packed.aR_u, CertificateChecks.KernelSporSch.Co1Packed.bR_u,
    CertificateChecks.KernelCo1B.iotaA_eq, CertificateChecks.KernelCo1B.iotaC_eq,
    unpackR_eq_unpack, unpackR_eq_unpack, Nat.eq_of_beq_eq_true h.1.1.1,
    Nat.eq_of_beq_eq_true h.1.1.2, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2, ha, hb]

theorem hinvOf {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)}
    (h : dagWK M MI nb N ws = true) :
    ∀ i < N, inv (unpack 24 24 (M i)) = unpack 24 24 (MI i) :=
  fun i hi => (invOKW_sound (dagWK_inv h i hi)).2

theorem okA : co1ClassOK co1PlaneA = true := by
  have hD : dag co1PlaneBase co1PlaneA.derivs = ((List.range 49).map fun i => unpack 24 24 (DA.M i),
      (List.range 49).map fun i => unpack 24 24 (DA.MI i), true) := by
    have e : co1PlaneA.derivs = CP.KWA.map decWord := kWA.symm
    rw [e]
    exact dagWK_sound (base_eq DA.M kBA) kDA
  exact class_of (hinvOf kDA) co1PlaneA hD kA

theorem okC : co1ClassOK co1PlaneC = true := by
  have hD : dag co1PlaneBase co1PlaneC.derivs = ((List.range 39).map fun i => unpack 24 24 (DC.M i),
      (List.range 39).map fun i => unpack 24 24 (DC.MI i), true) := by
    have e : co1PlaneC.derivs = CP.KWC.map decWord := kWC.symm
    rw [e]
    exact dagWK_sound (base_eq DC.M kBC) kDC
  exact class_of (hinvOf kDC) co1PlaneC hD kC

theorem okB : co1ClassOK co1PlaneB = true := by
  have hD : dag co1PlaneBase co1PlaneB.derivs = ((List.range 57).map fun i => unpack 24 24 (DB.M i),
      (List.range 57).map fun i => unpack 24 24 (DB.MI i), true) := by
    have e : co1PlaneB.derivs = CP.KWB.map decWord := kWB.symm
    rw [e]
    exact dagWK_sound (base_eq DB.M kBB) kDB
  exact class_of (hinvOf kDB) co1PlaneB hD kB

open Certificates in
open CFSG.RankThree.PartOne.SPOR in
theorem c14960 : co1ClassOK co1PlaneA = true ∧ co1ClassOK co1PlaneC = true ∧
    co1ClassOK co1PlaneB = true := ⟨okA, okC, okB⟩

end CertificateChecks.KernelCo1Planes

end
