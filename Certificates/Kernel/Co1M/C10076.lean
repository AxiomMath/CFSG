
module

public import CFSG.Sporadic.Co1.Module.Forms
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public import Certificates.Kernel.Co1M.Scan10076
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Certificates.Kernel.Co1M.BfsTreeSound
public import CFSG.Certificates.Kernel.VecKRegs
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Co1.Module.Orbits
public import CFSG.Sporadic.Co1.Module.FormsInputs
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co1.Module.OrbitsInputs
public import CFSG.Sporadic.Co1.Module.PairsCheckBase
public import CFSG.Certificates.Kernel.VecKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.Loop CFSG.KC.BfsT CFSG.KC.Co1M CFSG.KC.VecK CFSG.KD.Co1M
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CertificateChecks.KernelCo1Cover CFSG.Blueprint

theorem inO76 (w : Nat) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
  cm_orb_inPts w

theorem pt76 {p : Nat} (hp : p < 98280) :
    (orbitOf 2 98280).pts[p]! = lk CertificateChecks.KernelVec.Co1.Pt 32 p :=
  cm_orb_twin.2.1 p hp

theorem tyLab76 (w : Nat) :
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      if w = 0 then 0 else if q0N w then 2 else
        if orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w then 3 else 1 := by
  unfold tyLab
  rw [inO76]

theorem pairs_pts0 : (orbitOf 2 98280).pts[0]! = 2 :=
  (pt76 (by norm_num)).trans (Nat.eq_of_beq_eq_true (by quickRfl))

theorem pairs_wit : witnessCheck = true := by
  unfold witnessCheck
  dsimp only
  rw [tyLab76, tyLab76]
  quickRfl

theorem rep_labs : ∀ j < 4, tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
    ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[dat.subReps[j]!]!) = j := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · have e : dat.subReps[0]! = 0 := by decide +kernel
    rw [e, pt76 (by norm_num), tyLab76]
    exact Nat.eq_of_beq_eq_true (by quickRfl)
  · have e : dat.subReps[1]! = 1 := by decide +kernel
    rw [e, pt76 (by norm_num), pt76 (by norm_num), tyLab76]
    exact Nat.eq_of_beq_eq_true (by quickRfl)
  · have e : dat.subReps[2]! = 4 := by decide +kernel
    rw [e, pt76 (by norm_num), pt76 (by norm_num), tyLab76]
    exact Nat.eq_of_beq_eq_true (by quickRfl)
  · have e : dat.subReps[3]! = 60 := by decide +kernel
    rw [e, pt76 (by norm_num), pt76 (by norm_num), tyLab76]
    exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem tyOrbC_smul (g : NativeSporadic.Co1) {j : Nat} {z : Vec24} (hz : z ∈ tyOrbC j) :
    g • z ∈ tyOrbC j := by
  match j, hz with
  | 0, hz =>
    rw [tyOrbC, Set.mem_singleton_iff] at hz ⊢
    rw [hz, smul_zero]
  | 1, hz => exact orbit_smul_mem g hz
  | 2, hz => exact orbit_smul_mem g hz
  | _ + 3, hz => exact orbit_smul_mem g hz

theorem pt_lt76 {p : Nat} (hp : p < 98280) : (orbitOf 2 98280).pts[p]! < 2 ^ 24 :=
  ((vOrbitOK_facts orbitOK_v₂).2 p hp).1

theorem xor_lt76 {p : Nat} (hp : p < 98280) :
    (orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[p]! < 2 ^ 24 :=
  Nat.xor_lt_two_pow (pt_lt76 (by norm_num)) (pt_lt76 hp)

theorem labs76 : ∀ p < 98280, (labs dat)[p]! =
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[p]!) := by
  intro p hp
  have hF := CFSG.Sporadic.Co1.co1Facts
  have hB := co1BaseFacts
  have hsz : dat.subReps.size = 4 := by decide +kernel
  have hjs : (labs dat)[p]! < dat.subReps.size := hF.labs_lt p hp
  have hj4 : (labs dat)[p]! < 4 := hsz ▸ hjs
  have hTF := subTreeFacts hF hjs
  have hr := hTF.r_lt
  have hlr : (labs dat)[dat.subReps[(labs dat)[p]!]!]! = (labs dat)[p]! := by
    have h := hF.labs_pts _ hjs 0 hTF.size_pos
    rwa [hTF.root] at h
  obtain ⟨g, hg1, hg⟩ := subLab_orb hF (k := 3) hsz ⟨_, hr⟩ ⟨p, hp⟩ (Fin.ext hlr)
  have h1 : P dat (g • (⟨_, hr⟩ : Fin dat.n)).val = g • P dat dat.subReps[(labs dat)[p]!]! :=
    P_smul hB g ⟨_, hr⟩
  rw [hg] at h1
  have h0 : g • root hF = root hF := lvl_one_fix hF hg1
  have h2 : P dat (g • root hF).val = g • P dat 0 := P_smul hB g (root hF)
  rw [h0] at h2
  obtain ⟨g', hg'⟩ := exists_co1_of_mem_Jmat g
  let g₁ : Jmat := g
  have hconv : ∀ v : Vec24, g' • v = g₁ • v := fun v => by
    rw [smul_eq_mulVec, ← hg']; rfl
  set r := dat.subReps[(labs dat)[p]!]! with hrdef
  have hrl : r < 98280 := hr
  have e2 : g₁ • toVecD 24 (orbitOf 2 98280).pts[0]! = toVecD 24 (orbitOf 2 98280).pts[0]! :=
    h2.symm
  have e1 : g₁ • toVecD 24 (orbitOf 2 98280).pts[r]! = toVecD 24 (orbitOf 2 98280).pts[p]! :=
    h1.symm
  have hz : g' • toVecD 24 ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[r]!) =
      toVecD 24 ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[p]!) := by
    rw [toVecD_xor, toVecD_xor, smul_add, hconv, hconv, e2, e1]
  have hrep := rep_labs _ hj4
  rw [← hrdef] at hrep
  have hmem := (tyLab_spec _ (xor_lt76 hrl) _ hj4).1 hrep
  rw [← tyOrbC_eq] at hmem
  have hmem' := tyOrbC_smul g' hmem
  rw [hz, tyOrbC_eq] at hmem'
  exact ((tyLab_spec _ (xor_lt76 hp) _ hj4).2 hmem').symm

theorem pairs_lab : labCheck dat = true := by
  unfold labCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  exact labs76

@[expose] noncomputable def mclRegsK : Nat → Nat := fun r =>
  if r = 1 then R0 else if r = 2 then R1 else idF 24

@[expose] noncomputable def mclRunK : Nat → Nat := runWith (mulF 24) (powK 24) mclProg mclRegsK

theorem mclRun_eq (r : Nat) : mclRun r = unpackR 24 (mclRunK r) := by
  have h := runWith_map (mulF 24) (powK 24) (mulRows 24) (powRows 24) (unpackR 24)
    (fun a b => (CFSG.KC.F2W.mulRows_unpackR 24 a b).symm)
    (fun a e => (powRows_unpackR 24 a e).symm) mclProg mclRegsK r
  have e : (fun s => unpackR 24 (mclRegsK s)) = mclRegs := by
    funext s
    unfold mclRegsK mclRegs
    split_ifs
    · exact rowsA_eq.symm
    · exact rowsB_eq.symm
    · exact unpackR_idF 24
  rw [e] at h
  exact h.symm

theorem mclRunK1 : mclRunK 1 = MC1 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem mclRunK2 : mclRunK 2 = MC2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem bfs76 : bfsTree (mclAct (unpackR 24 MC1) (unpackR 24 MC2)) 4473570 400 =
    (ML.toArray, MP.toArray, MB.toArray) :=
  bfsTree_sound (by quickRfl)

theorem scan76 : ∀ p < 98280, mclF76 p = true :=
  allS_cover (S := 256) (ns := 384) CertificateChecks.KernelCo1M.Scan76.all (by norm_num)

theorem pairs_mcl : mclCheck = true := by
  unfold mclCheck mclCheckOf
  rw [mclRun_eq, mclRun_eq, mclRunK1, mclRunK2, bfs76]
  unfold mclCheckT
  dsimp only
  simp only [inO76]
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · quickRfl
  · rw [List.all_eq_true]
    intro p hp
    rw [List.mem_range] at hp
    rw [pt76 hp, List.contains_toArray]
    exact scan76 p hp

theorem c10076_neg :
    (!bfsK (mclAct (unpackR 24 MC1) (unpackR 24 MC2)) 4473570 400 ML (MP.set 5 0) MB &&
      !bfsK (mclAct (unpackR 24 MC1) (unpackR 24 MC2)) 4473570 200 ML MP MB &&
      !orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17
        (2 ^^^ lk CertificateChecks.KernelVec.Co1.Pt 32 1) &&
      !(!(orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17
          (16663704 ^^^ lk CertificateChecks.KernelVec.Co1.Pt 32 245) &&
        orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17
          (lk CertificateChecks.KernelVec.Co1.Pt 32 245 ^^^ (16663704 ^^^ 4852818))) ||
        ([] : List Nat).contains (lk CertificateChecks.KernelVec.Co1.Pt 32 245))) = true := by
  quickRfl

open Certificates in
open CFSG.Sporadic.Co1.Module.Pairs in
theorem c10076 :
    pairsCheck = true := by
  unfold pairsCheck
  rw [pairs_pts0, pairs_wit, pairs_mcl, pairs_lab]
  rfl

end CertificateChecks.KernelCo1M

end
