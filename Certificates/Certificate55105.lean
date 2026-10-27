module

public import CFSG.Sporadic.SmallOddCore.J3Data
public import Certificates.Kernel.J3Four.Checks
public import CFSG.Certificates.Kernel.J3FourSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

set_option maxRecDepth 400000

namespace CFSG.KD.J3Four

open Subgroup CFSG.Sporadic.SmallOddCore CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.OddCore CFSG.Sporadic.Th.Native

theorem prep_cent {k : ℕ} (hk : k < 31) :
    PRep 6156 (J3CentP k) (tp 6156 (j3CentTbl k)) ∧
      PRep 6156 (J3CentI k) (tp 6156 (j3CentTbl k))⁻¹ := by
  obtain ⟨-, h2⟩ := CFSG.KS.Prim.invEqK_sound (n := 6156) (w := 13) (j3_perm hk)
  obtain ⟨r1, r2⟩ := CFSG.Monster.B.Co2.rep_permOfArr h2
  have e : tp 6156 (j3CentTbl k) =
      CFSG.Monster.B.Co2.permOfArr 6156 (CFSG.KS.Raw.unpack 6156 13 (J3CentP k)) := by
    change CFSG.Monster.B.Co2.permOfArr 6156 (Native.natArr (j3CentTbl k)) = _
    rw [j3CentTbl_eq hk]
  rw [e]
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · rw [← CFSG.KS.Raw.Orb.unpack_get hq]
    exact r1 ⟨q, hq⟩
  · rw [← CFSG.KS.Raw.Orb.unpack_get hq]
    exact r2 ⟨q, hq⟩

theorem closure_tp_eq (L : List Table) :
    closure (tp 6156 '' {x | x ∈ L.toArray}) =
      closure ((fun i => tp 6156 L[i]!) '' {i | i < L.length}) := by
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toArray.mp hx)
    refine ⟨i, hi, ?_⟩
    change tp 6156 L[i]! = tp 6156 L[i]
    rw [getElem!_pos L i hi]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨L[i]!, ?_, rfl⟩
    rw [getElem!_pos L i hi]
    exact List.mem_toArray.mpr (List.getElem_mem hi)

@[expose] noncomputable def L1 : List Table :=
  [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14]

@[expose] noncomputable def L2 : List Table := [j3CentTbl 22, j3CentTbl 23, j3CentTbl 24]

theorem getN_cons_zero (a : ℕ) (L : List ℕ) : getN (a :: L) 0 = a := rfl

theorem getN_cons_succ (a : ℕ) (L : List ℕ) (i : ℕ) : getN (a :: L) (i + 1) = getN L i := rfl

theorem prep_list : ∀ ks : List ℕ, (∀ k ∈ ks, k < 31) → ∀ i < ks.length,
    PRep 6156 (getN (ks.map J3CentP) i) (tp 6156 (ks.map j3CentTbl)[i]!) ∧
      PRep 6156 (getN (ks.map J3CentI) i) (tp 6156 (ks.map j3CentTbl)[i]!)⁻¹
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k :: ks, hks, 0, _ => by
    rw [List.map_cons, List.map_cons, List.map_cons, getN_cons_zero, getN_cons_zero,
      List.getElem!_cons_zero]
    exact prep_cent (hks k (List.mem_cons_self ..))
  | k :: ks, hks, i + 1, hi => by
    rw [List.map_cons, List.map_cons, List.map_cons, getN_cons_succ, getN_cons_succ,
      List.getElem!_cons_succ]
    exact prep_list ks (fun k' hk' => hks k' (List.mem_cons_of_mem k hk')) i
      (Nat.lt_of_succ_lt_succ hi)

theorem prep_g1 : ∀ i < g1.length, PRep 6156 (getN g1 i) (tp 6156 L1[i]!) ∧
    PRep 6156 (getN g1i i) (tp 6156 L1[i]!)⁻¹ := by
  have e1 : g1 = [10, 11, 12, 13, 14].map J3CentP := rfl
  have e2 : g1i = [10, 11, 12, 13, 14].map J3CentI := rfl
  have e3 : L1 = [10, 11, 12, 13, 14].map j3CentTbl := rfl
  rw [e1, e2, e3]
  exact prep_list [10, 11, 12, 13, 14] (by decide)

theorem prep_g2 : ∀ i < g2.length, PRep 6156 (getN g2 i) (tp 6156 L2[i]!) ∧
    PRep 6156 (getN g2i i) (tp 6156 L2[i]!)⁻¹ := by
  have e1 : g2 = [22, 23, 24].map J3CentP := rfl
  have e2 : g2i = [22, 23, 24].map J3CentI := rfl
  have e3 : L2 = [22, 23, 24].map j3CentTbl := rfl
  rw [e1, e2, e3]
  exact prep_list [22, 23, 24] (by decide)

theorem row1_four
    (hcard : Nat.card (closure ((fun i => tp 6156 L1[i]!) '' {i | i < 5})) = 1920) :
    ∀ w ∈ closure ((fun i => tp 6156 L1[i]!) '' {i | i < 5}), w * w = 1 → w ≠ 1 →
      w ≠ tp 6156 (j3CentTbl 9) →
      Nat.card ↥(closure ((fun i => tp 6156 L1[i]!) '' {i | i < 5}) ⊓
        centralizer ({w} : Set (Equiv.Perm (Fin 6156)))) ∣ 2 ^ 30 * 3 ^ 30 := by
  have hg : g1.length = 5 := rfl
  rw [← hg] at hcard ⊢
  have hT := (prep_cent (k := 9) (by decide)).1
  have hT0 : tp 6156 (j3CentTbl 9) = tp 6156 L1[0]! :=
    (prep_eq hT (prep_g1 0 (by decide)).1).mp rep1_ok
  have hTK : tp 6156 (j3CentTbl 9) ∈
      closure ((fun i => tp 6156 L1[i]!) '' {i | i < g1.length}) := by
    rw [hT0]
    exact subset_closure ⟨0, by decide, rfl⟩
  exact four_of_rowK_central (G := g1) (Gi := g1i) (a := 7) (b := 1) rfl (fun i hi => (prep_g1 i hi).1)
    (fun i hi => (prep_g1 i hi).2) (by decide) row1_ok Nat.prime_five (by decide) (by decide)
    (by decide) (by decide) (hcard.trans (by norm_num)) (hcard.trans (by norm_num)).le hT
    cent1_ok hTK

theorem row2_four
    (hcard : Nat.card (closure ((fun i => tp 6156 L2[i]!) '' {i | i < 3})) = 2448) :
    ∀ w ∈ closure ((fun i => tp 6156 L2[i]!) '' {i | i < 3}), w * w = 1 → w ≠ 1 →
      Nat.card ↥(closure ((fun i => tp 6156 L2[i]!) '' {i | i < 3}) ⊓
        centralizer ({w} : Set (Equiv.Perm (Fin 6156)))) ∣ 2 ^ 30 * 3 ^ 30 := by
  have hg : g2.length = 3 := rfl
  rw [← hg] at hcard ⊢
  exact four_of_rowK (G := g2) (Gi := g2i) (a := 4) (b := 2) rfl (fun i hi => (prep_g2 i hi).1)
    (fun i hi => (prep_g2 i hi).2) (by decide) row2_ok (by norm_num) (by decide) (by decide)
    (by decide) (by decide) (hcard.trans (by norm_num)) (hcard.trans (by norm_num)).le

end CFSG.KD.J3Four

namespace Certificates

open CFSG.Sporadic.SmallOddCore CFSG.KD.J3Four

open CFSG.Sporadic.SmallOddCore in
theorem certificate55105 : ∀ r ∈ j3Rows, Nat.card (j3C r) = r.centOrder →
    ∀ w ∈ j3C r, w * w = 1 → w ≠ 1 → w ≠ tp 6156 r.rep →
      Nat.card ↥(j3C r ⊓ Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 6156)))) ∣
        2 ^ 30 * 3 ^ 30 := by
  refine fun r hr hcard w hw hww hw1 hwt => ?_
  have hK : j3C r =
      Subgroup.closure ((fun i => tp 6156 r.centGens[i]!) '' {i | i < r.centGens.length}) :=
    closure_tp_eq r.centGens
  rw [hK] at hcard hw ⊢
  simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hcard hw ⊢
  · exact row1_four hcard w hw hww hw1 hwt
  · exact row2_four hcard w hw hww hw1

end Certificates
