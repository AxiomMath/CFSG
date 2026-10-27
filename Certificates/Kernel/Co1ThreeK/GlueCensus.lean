module

public import Certificates.Data.TabCo1Census
public meta import Certificates.Data.TabCo1Census
public import Certificates.Kernel.Co1ThreeK.CensusK
public import Certificates.Kernel.Co1ThreeK.GlueMoore

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.KC.Co1Moore
  CFSG.KC.Co1Census CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.HardMathSupport.Dickson.I271.TabCo1Census

theorem ndI_unpack {MI : Nat → Nat} {N : Nat} {L : List Rows} {b : Bool} (i : Nat) :
    ndI (L, (List.range N).map (fun k => unpack 24 24 (MI k)), b) i =
      unpack 24 24 (ndK MI N i) := by
  unfold ndI ndK
  dsimp only
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]
  · rename_i h
    rw [List.getD_eq_default _ _ (by simpa using h), one_unpack]

theorem getD_unpack {M : Nat → Nat} {N : Nat} (k : Nat) :
    ((List.range N).map (fun i => unpack 24 24 (M i))).getD k (one ()) =
      unpack 24 24 (getK M N k) := by
  unfold getK
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]
  · rename_i h
    rw [List.getD_eq_default _ _ (by simpa using h), one_unpack]

theorem a0Row_unpack {M : Nat → Nat} {N : Nat} (k : Nat) :
    Timmesfeld.Co1Five.a0Row ((List.range N).map (fun i => unpack 24 24 (M i))) k =
      unpack 24 24 (a0K (getK M N (Timmesfeld.Co1Five.idxD.getD 0 0))
        (getK M N (Timmesfeld.Co1Five.idxD.getD 1 0))
        (getK M N (Timmesfeld.Co1Five.idxD.getD 2 0)) k) := by
  unfold Timmesfeld.Co1Five.a0Row Timmesfeld.Co1Five.rowAt a0K
  rw [getD_unpack, getD_unpack, getD_unpack, pow_unpackW, pow_unpackW, pow_unpackW, mul_unpackW,
    mul_unpackW]

theorem chainOK_unpack {M MI G : Nat → Nat} {N NG : Nat} {b : Bool} :
    ∀ (steps : List (Nat × Nat × Nat)) (cov : List Nat),
    chainOK ((List.range N).map (fun k => unpack 24 24 (M k)),
        (List.range N).map (fun k => unpack 24 24 (MI k)), b)
      ((List.range NG).map (fun k => unpack 24 24 (G k))) cov steps =
    chainK (ndK M N) (ndK MI N) (a0K (getK G NG (Timmesfeld.Co1Five.idxD.getD 0 0))
        (getK G NG (Timmesfeld.Co1Five.idxD.getD 1 0))
        (getK G NG (Timmesfeld.Co1Five.idxD.getD 2 0))) cov steps
  | [], _ => by rw [chainOK]; rfl
  | s :: rest, cov => by
    rw [chainOK, chainOK_unpack rest]
    change _ = (stepK _ _ _ cov s && chainK _ _ _ (s.1 :: cov) rest)
    congr 1
    unfold stepOK stepK
    rw [nd_unpack, ndI_unpack, a0Row_unpack, a0Row_unpack, mul_unpackW, mul_unpackW, beq_unpackW]

theorem rep_of {P : Nat} {R : Rows} (h : bindListK 24 24 P R.toList = true) :
    R = unpack 24 24 P := by
  have e := toArray_eq_of_bindListK h
  rwa [Array.toArray_toList] at e

theorem census_of {M MI G GI : Nat → Nat} {NG P₀ P₁ PZ : Nat}
    (hD : kDag ext = ((List.range 90).map (fun k => unpack 24 24 (M k)),
      (List.range 90).map (fun k => unpack 24 24 (MI k)), true))
    (hG : Timmesfeld.Co1Five.gDag aR bR = ((List.range NG).map (fun k => unpack 24 24 (G k)),
      (List.range NG).map (fun k => unpack 24 24 (GI k)), true))
    (h₀ : repD0 = unpack 24 24 P₀) (h₁ : repD1 = unpack 24 24 P₁) (hZ : repZ = unpack 24 24 PZ)
    (h : censusK (ndK M 90) (ndK MI 90)
      (a0K (getK G NG (Timmesfeld.Co1Five.idxD.getD 0 0))
        (getK G NG (Timmesfeld.Co1Five.idxD.getD 1 0))
        (getK G NG (Timmesfeld.Co1Five.idxD.getD 2 0))) P₀ P₁ PZ steps = true) :
    censusCheck () = true := by
  unfold censusCheck
  rw [hD, hG, h₀, h₁, hZ]
  unfold censusK at h
  simp only [a0Row_unpack, chainOK_unpack, beq_unpackW, Bool.true_and, Bool.and_eq_true] at h ⊢
  exact h

theorem KC_base : [aR, bR] = (List.range 2).map fun i => unpack 24 24 (KC.M i) := by
  have h := kCB
  simp only [Bool.and_eq_true] at h
  have e0 : KC.M 0 = CertificateChecks.KernelSporSch.Co1Packed.PA :=
    (Nat.eq_of_beq_eq_true h.1).trans
      (Nat.eq_of_beq_eq_true CertificateChecks.KernelCo1B.Cent2045.kb0)
  have e1 : KC.M 1 = CertificateChecks.KernelSporSch.Co1Packed.PB :=
    (Nat.eq_of_beq_eq_true h.2).trans
      (Nat.eq_of_beq_eq_true CertificateChecks.KernelCo1B.Cent2045.kb1)
  have hr : List.range 2 = [0, 1] := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_nil, e0, e1,
    ← CertificateChecks.KernelSporSch.Co1Packed.aR_u,
    ← CertificateChecks.KernelSporSch.Co1Packed.bR_u]

theorem KG_base : [aR, bR] = (List.range 2).map fun i => unpack 24 24 (KG.M i) := by
  have h := kGB
  simp only [Bool.and_eq_true] at h
  have e0 : KG.M 0 = CertificateChecks.KernelSporSch.Co1Packed.PA :=
    (Nat.eq_of_beq_eq_true h.1).trans
      (Nat.eq_of_beq_eq_true CertificateChecks.KernelCo1B.Cent2045.kb0)
  have e1 : KG.M 1 = CertificateChecks.KernelSporSch.Co1Packed.PB :=
    (Nat.eq_of_beq_eq_true h.2).trans
      (Nat.eq_of_beq_eq_true CertificateChecks.KernelCo1B.Cent2045.kb1)
  have hr : List.range 2 = [0, 1] := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_nil, e0, e1,
    ← CertificateChecks.KernelSporSch.Co1Packed.aR_u,
    ← CertificateChecks.KernelSporSch.Co1Packed.bR_u]

theorem kDagC_eq : kDag ext = ((List.range 90).map fun i => unpack 24 24 (KC.M i),
    (List.range 90).map fun i => unpack 24 24 (KC.MI i), true) := by
  rw [kDag, ← kCW]
  exact dagWK_sound KC_base kKC

theorem gDag_eq : Timmesfeld.Co1Five.gDag aR bR =
    ((List.range KG.N).map fun i => unpack 24 24 (KG.M i),
      (List.range KG.N).map fun i => unpack 24 24 (KG.MI i), true) := by
  rw [Timmesfeld.Co1Five.gDag]
  exact dagWK_sound KG_base kKG

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1Census in
theorem c17327 : censusCheck () = true :=
  census_of kDagC_eq gDag_eq (rep_of kP0) (rep_of kP1) (rep_of kPZ) kC

end CertificateChecks.KernelCo1ThreeK

end
