module

public import Certificates.Kernel.Co3Tw.Checks
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.PermWitSound
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.RankThree.Native.Co3FiveCentralizers

public section

namespace CertificateChecks.KernelCo3Tw

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.B3S3K CFSG.KC.PermWit CFSG.KC.Co3Tw

theorem szW : szOK 276 9 = true := by decide +kernel

theorem ng6 : EP.ng = 6 := Nat.eq_of_beq_eq_true szP.1

theorem okP : bfsK 276 9 EP.ng EP.G EP.N EP.T EP.E EP.S = true :=
  bfsK_of_slices (L := 243) (K := 9) (C := EP.C) (by decide) (by norm_num) szW EP.g EP.csAll EP.t0
    EP.dist (Nat.eq_of_beq_eq_true EP.c0) (Nat.eq_of_beq_eq_true EP.cK) EP.rsAll

@[expose] noncomputable def gsP : Array (Array ℕ) := Array.ofFn (n := 6) fun k => unpack 276 9 (EP.G k)

noncomputable abbrev P : Subgroup (Equiv.Perm (Fin 276)) := Subgroup.closure (permsA 276 gsP)

theorem gsP_size : gsP.size = 6 := by simp [gsP]

theorem gsP_get {k : ℕ} (hk : k < 6) : gsP[k]! = unpack 276 9 (EP.G k) := by
  rw [getElem!_pos gsP k (by rw [gsP_size]; exact hk)]
  simp [gsP]

theorem pGk : ∀ k < EP.ng, CFSG.KC.Misc.ArrEnum.permB 276 9 (EP.G k) = true := fun k hk =>
  Orb.allN_iff.1 pGP k (by rw [ng6] at hk; exact hk)

theorem bindP : BindA 276 9 gsP EP.ng EP.G :=
  ⟨by rw [gsP_size, ng6], fun j hj => gsP_get (by rw [ng6] at hj; exact hj)⟩

theorem base_lt : ∀ p ∈ co3ChainBaseArr.toList, p < 276 := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
  have hbl := Orb.base_lt_of_levels CertificateChecks.KernelSpor.Co3C.binds
    CertificateChecks.KernelSpor.Co3C.hl
  have hsz : co3ChainBaseArr.size = 7 := CertificateChecks.KernelSpor.Co3C.binds.2.2.2.2.2.1
  have ht' : t < co3ChainBaseArr.size := by simpa using ht
  have h := hbl t (by rw [← hsz]; exact ht')
  rw [getElem!_pos co3ChainBaseArr t ht'] at h
  simpa using h

theorem enumP : enumOK 276 gsP co3ChainBaseArr.toList (enumBfs 276 gsP co3ChainBaseArr.toList 3000) = true ∧
    (enumBfs 276 gsP co3ChainBaseArr.toList 3000).pts.size = EP.N ∧
    ∀ i < EP.N, (enumBfs 276 gsP co3ChainBaseArr.toList 3000).pts[i]! = unpack 276 9 (EP.T i) :=
  enum_of bindP pGk okP base_lt EP.keys (by rw [Nat.eq_of_beq_eq_true szP.2]; norm_num)

theorem card_P : Nat.card P = 2187 := by
  rw [(enumOK_spec base_lt enumP.1).2.1, enumP.2.1, Nat.eq_of_beq_eq_true szP.2]

theorem P_le_co3P : P ≤ co3P := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk6 : k < 6 := by
    rw [Set.mem_setOf_eq, gsP_size] at hk
    exact hk
  have hp := pGk k (by rw [ng6]; exact hk6)
  have hs : siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0
      (unpack 276 9 (EP.G k)) = true :=
    siftR_sound CertificateChecks.KernelSpor.Co3C.binds CertificateChecks.KernelSpor.Co3C.perm
      CertificateChecks.KernelSpor.Co3C.hl (Orb.allN_iff.1 siftP k hk6)
  change permOfArr 276 gsP[k]! ∈ co3P
  rw [gsP_get hk6]
  exact mem_co3P_of_sift (rep_of_validA (validA_of hp)) hs

end CertificateChecks.KernelCo3Tw

end
