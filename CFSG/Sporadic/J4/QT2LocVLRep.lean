module

public import CFSG.Sporadic.J4.QT2LocGenLem
public import CFSG.Sporadic.J4.QT2LocVLClassNative
public import CFSG.Sporadic.J4.QT2LocVLBasic

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A Matrix

@[expose] def vrMats (A : Array (Array V2)) : Set (Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  {N | ∃ M ∈ A, rowsMatrix M = N}

theorem vrMats_eq (A : Array (Array V2)) :
    vrMats A = rowsMatrix '' ((A.toList.toFinset : Finset (Array V2)) : Set (Array V2)) := by
  ext N
  simp [vrMats]

theorem vrMats_finite (A : Array (Array V2)) : (vrMats A).Finite := by
  rw [vrMats_eq]
  exact (Finset.finite_toSet _).image _

theorem vrMats_ncard_le (A : Array (Array V2)) : (vrMats A).ncard ≤ A.size := by
  rw [vrMats_eq]
  calc _ ≤ ((A.toList.toFinset : Finset (Array V2)) : Set (Array V2)).ncard :=
        Set.ncard_image_le (Finset.finite_toSet _)
    _ = A.toList.toFinset.card := Set.ncard_coe_finset _
    _ ≤ A.toList.length := List.toFinset_card_le _
    _ = A.size := by simp

structure VrClosed (A : Array (Array V2)) : Prop where
  one : ∃ K ∈ A, eqRows idRows K = true
  sq : ∀ M ∈ A, eqRows (mulRows M M) idRows = true
  mul : ∀ M ∈ A, ∀ N ∈ A, ∃ K ∈ A, eqRows (mulRows M N) K = true

theorem VrClosed.of_check {A : Array (Array V2)} (h : vrClosedB A = true) : VrClosed A := by
  unfold vrClosedB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [Array.any_eq_true'] at h1
  rw [Array.all_eq_true_iff_forall_mem] at h2
  refine ⟨?_, fun M hM => ?_, fun M hM N hN => ?_⟩
  · obtain ⟨K, hK, hk⟩ := h1
    exact ⟨K, hK, hk⟩
  · have := h2 M hM
    rw [Bool.and_eq_true] at this
    exact this.1
  · have := h2 M hM
    rw [Bool.and_eq_true] at this
    have h3 := (Array.all_eq_true_iff_forall_mem.1 this.2) N hN
    rw [Array.any_eq_true'] at h3
    obtain ⟨K, hK, hk⟩ := h3
    exact ⟨K, hK, hk⟩

theorem VrClosed.mats_one {A : Array (Array V2)} (h : VrClosed A) :
    (1 : Matrix (Fin 112) (Fin 112) (ZMod 2)) ∈ vrMats A := by
  obtain ⟨K, hK, hk⟩ := h.one
  exact ⟨K, hK, by rw [← eqRows_iff.1 hk, rowsMatrix_idRows]⟩

theorem VrClosed.mats_mul {A : Array (Array V2)} (h : VrClosed A) :
    ∀ a ∈ vrMats A, ∀ b ∈ vrMats A, a * b ∈ vrMats A := by
  rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
  obtain ⟨K, hK, hk⟩ := h.mul M hM N hN
  exact ⟨K, hK, by rw [← eqRows_iff.1 hk, rowsMatrix_mulRows]⟩

theorem VrClosed.mats_sq {A : Array (Array V2)} (h : VrClosed A) :
    ∀ a ∈ vrMats A, a * a = 1 := by
  rintro _ ⟨M, hM, rfl⟩
  rw [← rowsMatrix_mulRows, eqRows_iff.1 (h.sq M hM), rowsMatrix_idRows]

@[expose] noncomputable def vrSub {A : Array (Array V2)} (h : VrClosed A) : Subgroup J :=
  msSubgroup Mx Mx_injective (vrMats A) h.mats_one h.mats_mul h.mats_sq

theorem closure_card
    {A : Array (Array V2)} (h : VrClosed A) (hA : A.size ≤ 16) (ts : ℕ → J)
    (gs : Array (Array V2)) (hgs : ∀ i < 4, Mx (ts i) = rowsMatrix gs[i]!)
    (hwf : ∀ i < 4, wfRows gs[i]! = true) (hgm : ∀ i < 4, ∃ K ∈ A, eqRows gs[i]! K = true)
    (hdist : ∀ m < 16, ∀ m' < 16, eqRows (vlSubsetProd gs m) (vlSubsetProd gs m') = true →
      m = m') :
    Nat.card (Subgroup.closure (ts '' {i | i < 4})) = 16 ∧
      Subgroup.closure (ts '' {i | i < 4}) ≤ vrSub h := by
  have hle : Subgroup.closure (ts '' {i | i < 4}) ≤ vrSub h := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨K, hK, hk⟩ := hgm i hi
    exact ⟨K, hK, by rw [← eqRows_iff.1 hk, ← hgs i hi]⟩
  refine ⟨?_, hle⟩
  have hts : ∀ i < 4, ts i ∈ Subgroup.closure (ts '' {i | i < 4}) := fun i hi =>
    Subgroup.subset_closure ⟨i, hi, rfl⟩
  refine card_eq_of_cover Mx Mx_injective (vrMats A) (vrMats_finite A)
    ((vrMats_ncard_le A).trans hA) (fun u hu => hle hu)
    (fun m : Fin 16 => vlSubJ ts m) (fun m => vlSubJ_mem hts m) ?_
  intro m m' hmm
  have hMm := Mx_vlSubJ hgs m
  have hMm' := Mx_vlSubJ hgs m'
  have hw1 := wfRows_vlSubsetProd hwf m
  have hw2 := wfRows_vlSubsetProd hwf m'
  have heq : rowsMatrix (vlSubsetProd gs m) = rowsMatrix (vlSubsetProd gs m') := by
    rw [← hMm, ← hMm']
    exact congrArg Mx hmm
  have := hdist m m.2 m' m'.2 (eqRows_of_mx hw1 hw2 heq)
  exact Fin.ext this

theorem eq_conj_of_matrices {W U : Subgroup J} (hW16 : Nat.card W = 16)
    (hU16 : Nat.card U = 16) {Ag Ar : Array (Array V2)} (hAg : Ag.size ≤ 16)
    (hW : ∀ w ∈ W, ∃ M ∈ Ag, Mx w = rowsMatrix M)
    (hU : ∀ u ∈ U, ∃ M ∈ Ar, Mx u = rowsMatrix M) {c : J} {C Ci : Array V2}
    (hC : Mx c = rowsMatrix C) (hCi : Mx c⁻¹ = rowsMatrix Ci)
    (hconj : ∀ M ∈ Ar, ∃ M' ∈ Ag, eqRows (mulRows (mulRows C M) Ci) M' = true) :
    W = U.map (MulAut.conj c).toMonoidHom := by
  refine subgroup_eq_of_images Mx Mx_injective (vrMats Ag) (vrMats_finite Ag)
    ((vrMats_ncard_le Ag).trans hAg) (fun w hw => ?_)
    (conj_images Mx (vrMats Ag) c U (fun u hu => ?_)) hW16 ?_
  · obtain ⟨M, hM, e⟩ := hW w hw
    exact ⟨M, hM, e.symm⟩
  · obtain ⟨M, hM, e⟩ := hU u hu
    obtain ⟨M', hM', hk⟩ := hconj M hM
    refine ⟨M', hM', ?_⟩
    rw [e, hC, hCi, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 hk]
  · rw [card_map_conj]
    exact hU16

end CFSG.Sporadic.J4.QT2
