module

public import Certificates.Kernel.AE6Tri.FactsTA3
public import Certificates.Kernel.AE6Tri.ChecksTAT
public import CFSG.Certificates.Kernel.AE6TriSoundT
public import Certificates.Certificate517533Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KD.AE6TA CFSG.KD.AE6TAT
open CertificateChecks.KernelAE6TriTA
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open Certificates (ae6TriQuat0 ae6RepSwap ae6TriEdgeC)

@[expose] def tblOf (F : Fin 8 → List (Fin 8)) : List (List Nat) :=
  (List.finRange 8).map fun c => (F c).map Fin.val

theorem tbl_get (F : Fin 8 → List (Fin 8)) (c : Fin 8) :
    (tblOf F).getD c.val [] = (F c).map Fin.val := by
  rw [tblOf, List.getD_eq_getElem _ _ (by simp)]
  simp

theorem tv1 (F : Fin 8 → List (Fin 8)) (c : Fin 8) :
    tv gP [tblOf F] c.val = ((ae6Word (F c) : AE6Om) : Equiv.Perm (Fin 360)) := by
  change wv gP ((tblOf F).getD c.val []) = _
  rw [tbl_get, ← coe_ae6Word]

theorem wv_tbl {f : Nat → Equiv.Perm (Fin 360)} {F' : Fin 8 → List (Fin 8)}
    (hf : ∀ c : Fin 8, f c.val = ((ae6Word (F' c) : AE6Om) : Equiv.Perm (Fin 360)))
    (F : Fin 8 → List (Fin 8)) (c : Fin 8) :
    wv f ((tblOf F).getD c.val []) = ((ae6Word ((F c).flatMap F') : AE6Om) : Equiv.Perm (Fin 360)) := by
  rw [tbl_get, wv]
  exact prod_word f hf (F c)

theorem tv2 (F₁ F₂ : Fin 8 → List (Fin 8)) (c : Fin 8) :
    tv gP [tblOf F₁, tblOf F₂] c.val =
      ((ae6Word ((F₂ c).flatMap F₁) : AE6Om) : Equiv.Perm (Fin 360)) := by
  change wv (fun c => wv gP ((tblOf F₁).getD c [])) ((tblOf F₂).getD c.val []) = _
  exact wv_tbl (fun c => tv1 F₁ c) F₂ c

theorem tv3 (F₁ F₂ F₃ : Fin 8 → List (Fin 8)) (c : Fin 8) :
    tv gP [tblOf F₁, tblOf F₂, tblOf F₃] c.val =
      ((ae6Word ((F₃ c).flatMap fun c₂ => (F₂ c₂).flatMap F₁) : AE6Om) : Equiv.Perm (Fin 360)) := by
  change wv (tv gP [tblOf F₁, tblOf F₂]) ((tblOf F₃).getD c.val []) = _
  exact wv_tbl (fun c => tv2 F₁ F₂ c) F₃ c

theorem tA_eq : ∀ e : Fin 2,
    nthD tatA [] (6 * e.val) = [tblOf fun c => (ae6Delta 0 c).map (ae6EdgeMap e.succ)] ∧
    nthD tatA [] (6 * e.val + 1) = [tblOf fun c => (ae6Delta 1 c).map (ae6EdgeMap e.succ)] ∧
    nthD tatA [] (6 * e.val + 2) =
      [tblOf fun c => (ae6Delta 1 c).map (ae6EdgeMap e.succ), tblOf (ae6Delta 0)] ∧
    nthD tatA [] (6 * e.val + 3) =
      [tblOf fun c => (ae6Delta 0 c).map (ae6EdgeMap e.succ), tblOf (ae6Delta 1)] ∧
    nthD tatA [] (6 * e.val + 4) =
      [tblOf fun c => (ae6Delta 0 c).map (ae6EdgeMap e.succ), tblOf (ae6Delta 1),
        tblOf (ae6Delta 0)] := by
  decide

theorem tB_eq : ∀ e : Fin 2,
    nthD tatB [] (6 * e.val) =
      [tblOf fun c => ae6Delta (ae6EdgeL e.succ) (ae6EdgeMap e.succ c)] ∧
    nthD tatB [] (6 * e.val + 1) =
      [tblOf fun c => ae6Delta (ae6EdgeK e.succ) (ae6EdgeMap e.succ c)] ∧
    nthD tatB [] (6 * e.val + 2) =
      [tblOf (ae6Delta (ae6EdgeK e.succ)),
        tblOf fun c => ae6Delta (ae6EdgeL e.succ) (ae6EdgeMap e.succ c)] ∧
    nthD tatB [] (6 * e.val + 3) =
      [tblOf (ae6Delta (ae6EdgeL e.succ)),
        tblOf fun c => ae6Delta (ae6EdgeK e.succ) (ae6EdgeMap e.succ c)] ∧
    nthD tatB [] (6 * e.val + 4) =
      [tblOf (ae6Delta (ae6EdgeK e.succ)), tblOf (ae6Delta (ae6EdgeL e.succ)),
        tblOf fun c => ae6Delta (ae6EdgeK e.succ) (ae6EdgeMap e.succ c)] := by
  decide

theorem tK_eq : ∀ e : Fin 2,
    nthD tatA [] (6 * e.val + 5) =
      [[((ae6KWord 0).map (ae6EdgeMap e.succ) ++ ae6TriEdgeC e.succ).map Fin.val,
        ((ae6KWord 1).map (ae6EdgeMap e.succ) ++ ae6TriEdgeC e.succ).map Fin.val]] ∧
    nthD tatB [] (6 * e.val + 5) =
      [[(ae6TriEdgeC e.succ ++ (ae6KWord 0 ++ ae6KWord 0 ++ ae6KWord 0)).map Fin.val,
        (ae6TriEdgeC e.succ ++ (ae6KWord 0 ++ ae6KWord 1)).map Fin.val]] ∧
    nthD tatCs [] (6 * e.val + 5) = [0, 1] := by
  decide

theorem rows_mem : ∀ e : Fin 2, ∀ t < 5, ∀ c : Fin 8, c ∈ ae6EdgeLetters 0 1 →
    c.val ∈ nthD tatCs [] (6 * e.val + t) := by
  decide

theorem kTat_all : ∀ e : Fin 2, ∀ t < 6,
    tabEq RG (nthD tatA [] (6 * e.val + t)) (nthD tatB [] (6 * e.val + t))
      (nthD tatCs [] (6 * e.val + t)) = true := by
  intro e t ht
  fin_cases e <;> interval_cases t
  exacts [kTat0, kTat1, kTat2, kTat3, kTat4, kTat5, kTat6, kTat7, kTat8, kTat9, kTat10, kTat11]

theorem tat_val (e : Fin 2) (t : Nat) (ht : t < 6) (c : Nat) (hc : c ∈ nthD tatCs [] (6 * e.val + t)) :
    tv gP (nthD tatA [] (6 * e.val + t)) c = tv gP (nthD tatB [] (6 * e.val + t)) c :=
  tabEq_sound gRep (kTat_all e t ht) c hc

theorem rep_tr (e : Fin 2) (j : Nat) (hj : j < 6) (c : Fin 8) (hc : c ∈ ae6EdgeLetters 0 1) :
    ae6Word ((ae6TriRep 0 ⟨j, hj⟩ [c]).map (ae6EdgeMap e.succ)) =
      ae6Word (ae6TriRep e.succ (ae6RepSwap ⟨j, hj⟩) [ae6EdgeMap e.succ c]) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := tA_eq e
  obtain ⟨b0, b1, b2, b3, b4⟩ := tB_eq e
  apply Subtype.ext
  interval_cases j
  · rfl
  · have h := tat_val e 0 (by norm_num) c.val (rows_mem e 0 (by norm_num) c hc)
    rw [Nat.add_zero] at h
    rw [a0, b0, tv1, tv1] at h
    have eL : (ae6TriRep 0 ⟨1, hj⟩ [c]).map (ae6EdgeMap e.succ) =
        (ae6Delta 0 c).map (ae6EdgeMap e.succ) := by
      change (ae6DeltaW 0 [c]).map _ = _
      simp [ae6DeltaW]
    have eR : ae6TriRep e.succ (ae6RepSwap ⟨1, hj⟩) [ae6EdgeMap e.succ c] =
        ae6Delta (ae6EdgeL e.succ) (ae6EdgeMap e.succ c) := by
      change ae6DeltaW (ae6EdgeL e.succ) [ae6EdgeMap e.succ c] = _
      simp [ae6DeltaW]
    rw [eL, eR]
    exact h
  · have h := tat_val e 1 (by norm_num) c.val (rows_mem e 1 (by norm_num) c hc)
    rw [a1, b1, tv1, tv1] at h
    have eL : (ae6TriRep 0 ⟨2, hj⟩ [c]).map (ae6EdgeMap e.succ) =
        (ae6Delta 1 c).map (ae6EdgeMap e.succ) := by
      change (ae6DeltaW 1 [c]).map _ = _
      simp [ae6DeltaW]
    have eR : ae6TriRep e.succ (ae6RepSwap ⟨2, hj⟩) [ae6EdgeMap e.succ c] =
        ae6Delta (ae6EdgeK e.succ) (ae6EdgeMap e.succ c) := by
      change ae6DeltaW (ae6EdgeK e.succ) [ae6EdgeMap e.succ c] = _
      simp [ae6DeltaW]
    rw [eL, eR]
    exact h
  · have h := tat_val e 2 (by norm_num) c.val (rows_mem e 2 (by norm_num) c hc)
    rw [a2, b2, tv2, tv2] at h
    have eL : (ae6TriRep 0 ⟨3, hj⟩ [c]).map (ae6EdgeMap e.succ) =
        (ae6Delta 0 c).flatMap fun c₁ => (ae6Delta 1 c₁).map (ae6EdgeMap e.succ) := by
      change (ae6DeltaW 1 (ae6DeltaW 0 [c])).map _ = _
      simp [ae6DeltaW, List.map_flatMap]
    have eR : ae6TriRep e.succ (ae6RepSwap ⟨3, hj⟩) [ae6EdgeMap e.succ c] =
        (ae6Delta (ae6EdgeL e.succ) (ae6EdgeMap e.succ c)).flatMap (ae6Delta (ae6EdgeK e.succ)) := by
      change ae6DeltaW (ae6EdgeK e.succ) (ae6DeltaW (ae6EdgeL e.succ) [ae6EdgeMap e.succ c]) = _
      simp [ae6DeltaW]
    rw [eL, eR]
    exact h
  · have h := tat_val e 3 (by norm_num) c.val (rows_mem e 3 (by norm_num) c hc)
    rw [a3, b3, tv2, tv2] at h
    have eL : (ae6TriRep 0 ⟨4, hj⟩ [c]).map (ae6EdgeMap e.succ) =
        (ae6Delta 1 c).flatMap fun c₁ => (ae6Delta 0 c₁).map (ae6EdgeMap e.succ) := by
      change (ae6DeltaW 0 (ae6DeltaW 1 [c])).map _ = _
      simp [ae6DeltaW, List.map_flatMap]
    have eR : ae6TriRep e.succ (ae6RepSwap ⟨4, hj⟩) [ae6EdgeMap e.succ c] =
        (ae6Delta (ae6EdgeK e.succ) (ae6EdgeMap e.succ c)).flatMap (ae6Delta (ae6EdgeL e.succ)) := by
      change ae6DeltaW (ae6EdgeL e.succ) (ae6DeltaW (ae6EdgeK e.succ) [ae6EdgeMap e.succ c]) = _
      simp [ae6DeltaW]
    rw [eL, eR]
    exact h
  · have h := tat_val e 4 (by norm_num) c.val (rows_mem e 4 (by norm_num) c hc)
    rw [a4, b4, tv3, tv3] at h
    have eL : (ae6TriRep 0 ⟨5, hj⟩ [c]).map (ae6EdgeMap e.succ) =
        (ae6Delta 0 c).flatMap fun c₂ => (ae6Delta 1 c₂).flatMap fun c₁ =>
          (ae6Delta 0 c₁).map (ae6EdgeMap e.succ) := by
      change (ae6DeltaW 0 (ae6DeltaW 1 (ae6DeltaW 0 [c]))).map _ = _
      simp [ae6DeltaW, List.map_flatMap, List.flatMap_assoc]
    have eR : ae6TriRep e.succ (ae6RepSwap ⟨5, hj⟩) [ae6EdgeMap e.succ c] =
        (ae6Delta (ae6EdgeK e.succ) (ae6EdgeMap e.succ c)).flatMap fun c₂ =>
          (ae6Delta (ae6EdgeL e.succ) c₂).flatMap (ae6Delta (ae6EdgeK e.succ)) := by
      change ae6DeltaW (ae6EdgeK e.succ) (ae6DeltaW (ae6EdgeL e.succ)
        (ae6DeltaW (ae6EdgeK e.succ) [ae6EdgeMap e.succ c])) = _
      simp [ae6DeltaW, List.flatMap_assoc]
    rw [eL, eR]
    exact h

theorem k0_tr (e : Fin 2) (s : Fin 2) :
    ae6Word ((ae6KWord s.castSucc).map (ae6EdgeMap e.succ)) ∈
      conjSub (ae6Word (ae6TriEdgeC e.succ)) ae6ModelK := by
  obtain ⟨a5, b5, r5⟩ := tK_eq e
  have hK0 : ae6Word (ae6KWord 0) ∈ ae6ModelK := Subgroup.subset_closure (Set.mem_insert _ _)
  have hK1 : ae6Word (ae6KWord 1) ∈ ae6ModelK :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have key : ∀ (X U : List (Fin 8)),
      ((ae6Word (X ++ ae6TriEdgeC e.succ) : AE6Om) : Equiv.Perm (Fin 360)) =
        ((ae6Word (ae6TriEdgeC e.succ ++ U) : AE6Om) : Equiv.Perm (Fin 360)) → ae6Word U ∈ ae6ModelK →
      ae6Word X ∈ conjSub (ae6Word (ae6TriEdgeC e.succ)) ae6ModelK := by
    intro X U h hU
    rw [mem_conjSub_iff]
    have h' := Subtype.ext h
    rw [word_append, word_append] at h'
    have e2 : (ae6Word (ae6TriEdgeC e.succ))⁻¹ * ae6Word X * ae6Word (ae6TriEdgeC e.succ) =
        ae6Word U := by
      rw [mul_assoc, h', ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e2]
    exact hU
  fin_cases s
  · have h := tat_val e 5 (by norm_num) 0 (by rw [r5]; simp)
    rw [a5, b5] at h
    change wv gP (((ae6KWord 0).map (ae6EdgeMap e.succ) ++ ae6TriEdgeC e.succ).map Fin.val) =
      wv gP ((ae6TriEdgeC e.succ ++ (ae6KWord 0 ++ ae6KWord 0 ++ ae6KWord 0)).map Fin.val) at h
    rw [← coe_ae6Word, ← coe_ae6Word] at h
    refine key _ _ h ?_
    rw [word_append, word_append]
    exact ae6ModelK.mul_mem (ae6ModelK.mul_mem hK0 hK0) hK0
  · have h := tat_val e 5 (by norm_num) 1 (by rw [r5]; simp)
    rw [a5, b5] at h
    change wv gP (((ae6KWord 1).map (ae6EdgeMap e.succ) ++ ae6TriEdgeC e.succ).map Fin.val) =
      wv gP ((ae6TriEdgeC e.succ ++ (ae6KWord 0 ++ ae6KWord 1)).map Fin.val) at h
    rw [← coe_ae6Word, ← coe_ae6Word] at h
    refine key _ _ h ?_
    rw [word_append]
    exact ae6ModelK.mul_mem hK0 hK1

end CertificateChecks.KernelAE6Tri

end
