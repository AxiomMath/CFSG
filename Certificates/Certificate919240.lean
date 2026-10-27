module

public import Certificates.Data.Foote82J3SylInvol
import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3
import Certificates.Kernel.Sporadic.J3C.GlueS
import Certificates.Kernel.Sporadic.J3C.SqOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Certificates CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.J3Proof CFSG.ClassicalInvolution.J3Data
  CFSG.CGT.Foote82.Proof511.J3Syl
  CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.CentReg CertificateChecks.KernelSpor.J3C
  CertificateChecks.KernelSpor.J3CGlue

namespace CertificateChecks.Batch919240

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Certificates CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.J3Proof CFSG.ClassicalInvolution.J3Data
  CFSG.CGT.Foote82.Proof511.J3Syl
  CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.CentReg CertificateChecks.KernelSpor.J3C
  CertificateChecks.KernelSpor.J3CGlue

theorem invoOK_iff_sq {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    invoOK n T = true ↔ g ^ 2 = 1 := by
  constructor
  · intro h
    refine perm_faithful _ fun i => Fin.ext ?_
    have := idx_sq_of_invoOK hT h i.val i.2
    rw [idx_of_lt _ i.2] at this
    exact this
  · intro h
    rw [invoOK, allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hT i hi, hT _ (idx_lt g hi), ← idx_mul, ← pow_two, h, idx_one]

theorem card_eq_sqOneCount :
    Nat.card {x : sChain.originalSubgroup // (x : Equiv.Perm (Fin 20520)) ^ 2 = 1} =
      sqOneCount () := by
  have hQ : ValidSchreier sChain := ofArrays_valid (by norm_num) sChain_ok
  have hn : (20520 : ℕ) < 2 ^ 32 := by norm_num
  have hcount : Nat.card {x : sChain.originalSubgroup // (x : Equiv.Perm (Fin 20520)) ^ 2 = 1} =
      countProducts 20520 (invoOK 20520) (levelTables sChain) (idT 20520) := by
    rw [countProducts_spec (fun T g hT => invoOK_iff_sq hT) (forall₂_levelTables hn sChain)
        (Rep.idT hn),
      card_subtype_eq_countP sChain.originalSubgroup (enumeration sChain)
        (enumeration_nodup sChain hQ) (mem_enumeration_iff sChain hQ)
        fun g : Equiv.Perm (Fin 20520) => g ^ 2 = 1]
    simp only [one_mul, List.map_id']
    rfl
  rw [hcount, sChain, ofArrays_levelTables sChain_ok]
  rfl

theorem sq_iff (k : ℕ) (hk : k < TS.cnt) :
    sqTest k = true ↔ (CFSG.KS.PC.tw ς TS.PAR TS.LAB k) ^ 2 = 1 := by
  have hpt := tw_pt repTS actS k hk
  have hlt : r32 TS.PTS k < 20520 := by
    rw [← hpt]
    exact actN_lt _ (by norm_num)
  have hw := walkF_tw repTS actS k k hk le_rfl [r32 TS.PTS k] (by simpa using hlt)
  unfold sqTest walkK
  rw [hw, List.map_cons, List.map_nil]
  change Nat.beq (actN _ (r32 TS.PTS k)) 0 = true ↔ _
  rw [Nat.beq_eq, ← hpt, ← actN_mul, ← pow_two]
  constructor
  · intro h
    refine kFree.2.2 _ (sK (J3Groups.S.pow_mem (tw_mem repTS ςS k hk) 2)) ?_
    exact Fin.ext ((actN_of_lt _ (root_lt repTK)).symm.trans h)
  · intro h
    rw [h, actN_one]

theorem card_sq_S : Nat.card {x : J3Groups.S // (x : Equiv.Perm (Fin 20520)) ^ 2 = 1} = 36 := by
  have hc : TS.cnt = 128 := Nat.eq_of_beq_eq_true tsCnt
  have hlt : ∀ k : Fin 128, k.val < TS.cnt := fun k => by
    rw [hc]
    exact k.2
  let e : Fin 128 → J3Groups.S := fun k => ⟨CFSG.KS.PC.tw ς TS.PAR TS.LAB k,
    tw_mem repTS ςS k (hlt k)⟩
  have hsurj : Function.Surjective e := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, -, rfl⟩ := sFree.2 g hg
    exact ⟨⟨k, by rw [← hc]; exact hk⟩, rfl⟩
  have hb : Function.Bijective e := hsurj.bijective_of_nat_card_le (by simp [sCard])
  have h1 : Nat.card {x : J3Groups.S // (x : Equiv.Perm (Fin 20520)) ^ 2 = 1} =
      Nat.card {k : Fin 128 // sqTest k = true} :=
    Nat.card_congr ((Equiv.ofBijective e hb).subtypeEquiv fun k => sq_iff k (hlt k)).symm
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Nat.eq_of_beq_eq_true sqOne_ok,
    cntN_eq, hc]
  refine Finset.card_bij (fun a _ => a.val) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at ha ⊢
    exact ⟨a.2, ha⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simpa using hb.2, rfl⟩

theorem card_of_eq (H : Subgroup (Equiv.Perm (Fin 20520))) (hH : H = J3Groups.S) :
    Nat.card {x : H // (x : Equiv.Perm (Fin 20520)) ^ 2 = 1} = 36 := by
  subst hH
  exact card_sq_S

theorem sqOneCount_eq : sqOneCount () = 36 := by
  have hSS : sChain.originalSubgroup = J3Groups.S := by
    rw [sChain, ofArrays_originalSubgroup]
    rfl
  rw [← card_eq_sqOneCount]
  exact card_of_eq _ hSS

end CertificateChecks.Batch919240

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.Proof511.J3Syl in
theorem certificate919240 : sqOneCount () = 36 :=
  CertificateChecks.Batch919240.sqOneCount_eq

end Certificates

end
