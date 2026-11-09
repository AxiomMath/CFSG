
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Certificates.Kernel.Census.CatFacts.OrbPre
public import Certificates.Kernel.Census.CatFacts.C2008Y
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
import Certificates.Kernel.Census.CatFacts.C2008K2

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups

theorem cfQE_ok' : CFSG.Certificates.ValidSchreier cfQE :=
  check_certificate_of _ _ _ _ _ cfQE2008K.1

@[expose] def normE (x : Equiv.Perm (Fin 8)) : Bool :=
  cfEgens.all fun e => siftP cfQE (x * e * x⁻¹) 0

@[expose] def orbF (x : Equiv.Perm (Fin 8)) : Bool :=
  !(normE x) || (decide (x⁻¹ * cfZ * x ∈ cfOz.map Prod.fst) &&
    decide (x⁻¹ * (cfZ * cfTau) * x ∈ cfOzt.map Prod.fst))

theorem gensE : (WH.original.toList.all fun g => cfQE.original.toList.all fun e =>
    siftP cfQE (g * e * g⁻¹) 0 && siftP cfQE (g⁻¹ * e * g⁻¹⁻¹) 0) = true := by decide +kernel

theorem gensO : (WH.original.toList.all fun g =>
    ((cfOz.map Prod.fst).all fun w => decide (g⁻¹ * w * g ∈ cfOz.map Prod.fst) &&
      decide (g⁻¹⁻¹ * w * g⁻¹ ∈ cfOz.map Prod.fst)) &&
    ((cfOzt.map Prod.fst).all fun w => decide (g⁻¹ * w * g ∈ cfOzt.map Prod.fst) &&
      decide (g⁻¹⁻¹ * w * g⁻¹ ∈ cfOzt.map Prod.fst))) = true := by decide +kernel

theorem z_mem : (decide (cfZ ∈ cfOz.map Prod.fst) && decide (cfZ * cfTau ∈ cfOzt.map Prod.fst)) =
    true := by decide +kernel

theorem cfEgens_mem : (cfEgens.all fun e => siftP cfQE e 0) = true := by decide +kernel

theorem WH_len : (elemsV WH).length = 1152 := by decide +kernel

theorem mem_cfQE {z : Equiv.Perm (Fin 8)} (h : siftP cfQE z 0 = true) :
    z ∈ cfQE.originalSubgroup :=
  (mem_iff_sift cfQE cfQE_ok' z).2 ((sift_eq_siftP _ _ _).trans h)

theorem conjE_gen {g : Equiv.Perm (Fin 8)}
    (h : ∀ e ∈ cfQE.original.toList, siftP cfQE (g * e * g⁻¹) 0 = true) {y : Equiv.Perm (Fin 8)}
    (hy : y ∈ cfQE.originalSubgroup) : g * y * g⁻¹ ∈ cfQE.originalSubgroup := by
  refine closure_all cfQE (P := fun y => g * y * g⁻¹ ∈ cfQE.originalSubgroup) ?_ ?_ ?_ hy
  · beta_reduce
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro a b ha hb
    beta_reduce at ha hb ⊢
    have e : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  · intro e he
    refine ⟨mem_cfQE (h e he), ?_⟩
    beta_reduce
    have e' : g * e⁻¹ * g⁻¹ = (g * e * g⁻¹)⁻¹ := by group
    rw [e']
    exact Subgroup.inv_mem _ (mem_cfQE (h e he))

theorem conjE_of_mem {x : Equiv.Perm (Fin 8)} (hx : x ∈ WH.originalSubgroup) :
    ∀ y ∈ cfQE.originalSubgroup, x * y * x⁻¹ ∈ cfQE.originalSubgroup := by
  refine closure_all WH
    (P := fun x => ∀ y ∈ cfQE.originalSubgroup, x * y * x⁻¹ ∈ cfQE.originalSubgroup) ?_ ?_ ?_ hx
  · intro y hy
    rwa [inv_one, mul_one, one_mul]
  · intro a b ha hb y hy
    have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha _ (hb y hy)
  · intro g hg
    have h := List.all_eq_true.1 gensE g hg
    exact ⟨fun y hy => conjE_gen (fun e he => (Bool.and_eq_true_iff.1
        (List.all_eq_true.1 h e he)).1) hy,
      fun y hy => conjE_gen (fun e he => (Bool.and_eq_true_iff.1
        (List.all_eq_true.1 h e he)).2) hy⟩

theorem normE_of_mem {x : Equiv.Perm (Fin 8)} (hx : x ∈ elemsV WH) : normE x = true := by
  rw [← elemsT_eq_elemsV, mem_elemsT WH WH_ok] at hx
  refine List.all_eq_true.2 fun e he => ?_
  have h := conjE_of_mem hx e (mem_cfQE (List.all_eq_true.1 cfEgens_mem e he))
  rw [← sift_eq_siftP]
  exact (mem_iff_sift cfQE cfQE_ok' _).1 h

theorem orb_of_mem {x : Equiv.Perm (Fin 8)} (hx : x ∈ WH.originalSubgroup) :
    (∀ w ∈ cfOz.map Prod.fst, x⁻¹ * w * x ∈ cfOz.map Prod.fst) ∧
      (∀ w ∈ cfOzt.map Prod.fst, x⁻¹ * w * x ∈ cfOzt.map Prod.fst) := by
  refine closure_all WH (P := fun x =>
    (∀ w ∈ cfOz.map Prod.fst, x⁻¹ * w * x ∈ cfOz.map Prod.fst) ∧
      (∀ w ∈ cfOzt.map Prod.fst, x⁻¹ * w * x ∈ cfOzt.map Prod.fst)) ?_ ?_ ?_ hx
  · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rwa [inv_one, one_mul, mul_one]
    · rwa [inv_one, one_mul, mul_one]
  · intro a b ha hb
    have e : ∀ w : Equiv.Perm (Fin 8), (a * b)⁻¹ * w * (a * b) = b⁻¹ * (a⁻¹ * w * a) * b :=
      fun w => by group
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [e]
      exact hb.1 _ (ha.1 w hw)
    · rw [e]
      exact hb.2 _ (ha.2 w hw)
  · intro g hg
    have h := Bool.and_eq_true_iff.1 (List.all_eq_true.1 gensO g hg)
    refine ⟨⟨fun w hw => ?_, fun w hw => ?_⟩, ⟨fun w hw => ?_, fun w hw => ?_⟩⟩
    · exact of_decide_eq_true (Bool.and_eq_true_iff.1 (List.all_eq_true.1 h.1 w hw)).1
    · exact of_decide_eq_true (Bool.and_eq_true_iff.1 (List.all_eq_true.1 h.2 w hw)).1
    · exact of_decide_eq_true (Bool.and_eq_true_iff.1 (List.all_eq_true.1 h.1 w hw)).2
    · exact of_decide_eq_true (Bool.and_eq_true_iff.1 (List.all_eq_true.1 h.2 w hw)).2

theorem memWE_of_normE {x : Equiv.Perm (Fin 8)} (h : normE x = true) : x ∈ elemsV WH := by
  cases hp : preT labH cfEgens x
  · have h0 := all_siftP_false cfQE_ok' labOK_cfQE hp
    unfold normE at h
    rw [h] at h0
    exact absurd h0 Bool.noConfusion
  · have hx := (mem_elemsT WH WH_ok x).2 (memWE hp)
    rwa [elemsT_eq_elemsV] at hx

theorem cfOrb22008K : (elemsV QS8).all (fun x => !(cfEgens.all fun e =>
      siftP cfQE (x * e * x⁻¹) 0) || (decide (x⁻¹ * cfZ * x ∈ cfOz.map Prod.fst) &&
      decide (x⁻¹ * (cfZ * cfTau) * x ∈ cfOzt.map Prod.fst))) = true ∧
    ((elemsV QS8).filter fun x => cfEgens.all fun e => siftP cfQE (x * e * x⁻¹) 0).length =
      1152 := by
  constructor
  · refine List.all_eq_true.2 fun x _ => ?_
    change orbF x = true
    cases hn : normE x
    · unfold orbF
      rw [hn]
      rfl
    · have hx := memWE_of_normE hn
      rw [← elemsT_eq_elemsV, mem_elemsT WH WH_ok] at hx
      have hz := Bool.and_eq_true_iff.1 z_mem
      unfold orbF
      rw [hn, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      exact ⟨decide_eq_true ((orb_of_mem hx).1 _ (of_decide_eq_true hz.1)),
        decide_eq_true ((orb_of_mem hx).2 _ (of_decide_eq_true hz.2))⟩
  · rw [← WH_len]
    refine length_filter_of ?_ (fun x => ?_) ?_ (fun x => ⟨memWE_of_normE, normE_of_mem⟩)
    · rw [← elemsT_eq_elemsV]
      exact nodup_elemsT QS8 QS8_ok
    · rw [← elemsT_eq_elemsV, mem_elemsT QS8 QS8_ok, QS8_eq]
      exact Subgroup.mem_top x
    · rw [← elemsT_eq_elemsV]
      exact nodup_elemsT WH WH_ok

end CertificateChecks.KernelCatFacts
