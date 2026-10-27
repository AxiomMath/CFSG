module

public import CFSG.Sporadic.FischerOddCore.Fi22RelBound
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrder
public import CFSG.Sporadic.FischerOddCore.Fi22SearchCheck
public import CFSG.Sporadic.FischerOddCore.SearchSpec

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native
open scoped Pointwise

theorem fi22H0_le_K0 :
    fi22H 0 ≤ fi22K 0 := fun g hg => by
  obtain ⟨hP, hc⟩ := fi22H_le (c := 0) (by norm_num) hg
  exact ⟨fi22R_le_AutG (fi22P_le_R hP), hc⟩

theorem fi22SearchPoolArr_get {j : ℕ} (hj : j < 64) :
    fi22SearchPoolArr[j]! = fi22CentArr (240 + j) := by
  rw [fi22SearchPoolArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem fi22SearchAccArr_get {i : ℕ} (hi : i < 2) :
    fi22SearchAccArr[i]! = fi22CentArr (304 + i) := by
  rw [fi22SearchAccArr, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem rep_fi22SearchPool {j : ℕ} (hj : j < 64) :
    Rep 3510 fi22SearchPoolArr[j]! (fi22SearchPool j) := by
  rw [fi22SearchPoolArr_get hj]
  exact rep_fi22CentPerm (by omega)

theorem rep_fi22SearchAcc {i : ℕ} (hi : i < 2) :
    Rep 3510 fi22SearchAccArr[i]! (fi22SearchAcc i) := by
  rw [fi22SearchAccArr_get hi]
  exact rep_fi22CentPerm (by omega)

theorem fi22SearchPool_mem
    {j : ℕ} (hj : j < 64) : fi22SearchPool j ∈ fi22H 0 := by
  have h := fi22SearchPool_check j hj
  rw [← fi22SearchPoolArr_get hj] at h
  exact (siftA_iff_mem_fi22H (c := 0) (by norm_num) (rep_fi22SearchPool hj)).1 h

theorem fi22K0_cover
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ fi22K 0) :
    ∃ h ∈ fi22H 0, ∃ k < 2, h * σ = fi22SearchAcc k := by
  have hsize : fi22SearchPoolArr.size = 64 := by simp [fi22SearchPoolArr]
  have hasize : fi22SearchAccArr.size = 2 := by simp [fi22SearchAccArr]
  obtain ⟨hadm, hcomm⟩ := fi22K_admissible hσ
  obtain ⟨h, hh, k, hk, heq⟩ := exists_mul_eq_acc_of_searchOK (Pool := fi22SearchPool)
    (Acc := fi22SearchAcc) (H := fi22H 0) fi22Nbr_facts.point
    (rep_fi22ExtRep (k := 0) (by norm_num))
    fi22Cent_check.2.2.2.2.2.2.2.2.2.2.2
    (fun j hj => ⟨rep_fi22SearchPool (by omega), fi22SearchPool_mem (by omega)⟩)
    (fun h hh => fi22K_admissible (fi22H0_le_K0 hh))
    (fun i hi => rep_fi22SearchAcc (by omega)) (by norm_num) fi22Search_check hadm hcomm
  exact ⟨h, hh, k, by omega, heq⟩

theorem card_fi22K0_le :
    Nat.card (fi22K 0) ≤ 2 * Nat.card (fi22H 0) := by
  have hc : ∀ σ : fi22K 0, ∃ q : fi22H 0 × Fin 2,
      ((q.1 : fi22H 0) : Equiv.Perm (Fin 3510)) * σ = fi22SearchAcc q.2 := fun σ => by
    obtain ⟨h, hh, k, hk, e⟩ := fi22K0_cover σ.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), e⟩
  let f : fi22K 0 → fi22H 0 × Fin 2 := fun σ => (hc σ).choose
  have hf : Function.Injective f := by
    intro σ τ hστ
    have e1 := (hc σ).choose_spec
    have e2 := (hc τ).choose_spec
    change (hc σ).choose = (hc τ).choose at hστ
    rw [hστ] at e1
    exact Subtype.ext (mul_left_cancel (e1.trans e2.symm))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, mul_comm] at this

theorem CTUC_Fi22_54_fixed_point_involution_pruned_graph_bound :
    fi22H 0 ≤ fi22K 0 ∧ ((fi22H 0).subgroupOf (fi22K 0)).index ≤ 2 ∧
    Nat.card (fi22K 0) ≤ 3538944 ∧
    (∀ i < 2, fi22SearchAcc i ∈ fi22AutG ∧
      fi22SearchAcc i * fi22ExtRep 0 = fi22ExtRep 0 * fi22SearchAcc i) ∧
    fi22SearchAcc 0 ∈ fi22P ∧ fi22SearchAcc 1 ∈ fi22R ∧ fi22SearchAcc 1 ∉ fi22P := by
  have hH0 : Nat.card (fi22H 0) = 1769472 := card_fi22H (c := 0) (by norm_num)
  have hK := card_fi22K0_le
  obtain ⟨hacc, hP0, hP1, hu1⟩ := fi22SearchAcc_check
  refine ⟨fi22H0_le_K0, ?_, by omega, fun i hi => ?_, ?_, ?_, ?_⟩
  · have h := ((fi22H 0).subgroupOf (fi22K 0)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22H0_le_K0).toEquiv, hH0] at h
    rw [hH0] at hK
    omega
  · obtain ⟨h1, h2⟩ := hacc i hi
    rw [← fi22SearchAccArr_get hi] at h1 h2
    refine ⟨mem_fi22AutG_of_nbrInv (nbrInv_of_img fi22Nbr_facts.point (rep_fi22SearchAcc hi)
      fun x hx => by simpa using allLt_spec h1 hx), eq_of_eqA (rep_compA (rep_fi22SearchAcc hi)
        (rep_fi22ExtRep (by norm_num))) (rep_compA (rep_fi22ExtRep (by norm_num))
          (rep_fi22SearchAcc hi)) h2⟩
  · rw [← show fi22SearchAccArr[0]! = fi22CentArr 304 from fi22SearchAccArr_get (by norm_num)]
      at hP0
    exact (fi22InP_iff (rep_fi22SearchAcc (by norm_num))).1 hP0
  · rw [← show fi22SearchAccArr[1]! = fi22CentArr 305 from fi22SearchAccArr_get (by norm_num)]
      at hu1
    exact (mem_fi22R_iff _).2 (Or.inr ((fi22InP_iff (rep_compA rep_fi22U
      (rep_fi22SearchAcc (by norm_num)))).1 hu1))
  · intro hm
    rw [← show fi22SearchAccArr[1]! = fi22CentArr 305 from fi22SearchAccArr_get (by norm_num)]
      at hP1
    rw [(fi22InP_iff (rep_fi22SearchAcc (by norm_num))).2 hm] at hP1
    exact Bool.noConfusion hP1

end CFSG.Sporadic.FischerOddCore
