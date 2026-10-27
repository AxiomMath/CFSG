module

public import Certificates.Data.TwoDepSmallLow
public import CFSG.LocalAnalysis.StandardType.GGTWNatWord

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggTWLMatWF (d : ℕ) (A : List (List ℕ)) : Prop :=
  A.length = d ∧ ∀ c ∈ A, c.length = d

@[expose] noncomputable def ggTWLMatLin (p d : ℕ) (A : List (List ℕ)) :
    Module.End (ZMod p) (GGDepAE p d) :=
  ∑ k : Fin d, (LinearMap.proj k : GGDepAE p d →ₗ[ZMod p] ZMod p).smulRight
    (ggDepANToZ p d (A.getD k.val []))

private lemma l05nLM_basis_length (d k : ℕ) : (ggTWLBasis d k).length = d := by
  simp [ggTWLBasis]

private lemma l05nLM_toZ_basis (p d : ℕ) (k : Fin d) :
    ggDepANToZ p d (ggTWLBasis d k.val) = Pi.single k 1 := by
  funext j
  simp only [ggDepANToZ]
  rw [show ggTWLBasis d k.val = (List.range d).map (fun j => if j = k.val then 1 else 0)
      from rfl]
  have hlen : j.val < ((List.range d).map (fun j => if j = k.val then 1 else 0)).length := by
    simp [j.isLt]
  rw [List.getD_eq_getElem _ 0 hlen, List.getElem_map]
  have hrange : (List.range d)[j.val] = j.val := List.getElem_range (by simpa using j.isLt)
  rw [hrange]
  by_cases h : j.val = k.val
  · rw [if_pos h]
    have hjk : j = k := Fin.ext h
    rw [hjk, Pi.single_eq_same]
    simp
  · rw [if_neg h]
    have hjk : j ≠ k := fun hh => h (congrArg Fin.val hh)
    rw [Pi.single_eq_of_ne hjk]
    simp

private lemma l05nLM_lin_apply (p d : ℕ) (A : List (List ℕ)) (v : GGDepAE p d) :
    ggTWLMatLin p d A v = ∑ k : Fin d, v k • ggDepANToZ p d (A.getD k.val []) := by
  simp only [ggTWLMatLin, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

private lemma l05nLM_lin_single (p d : ℕ) (A : List (List ℕ)) (k : Fin d) :
    ggTWLMatLin p d A (Pi.single k 1) = ggDepANToZ p d (A.getD k.val []) := by
  rw [l05nLM_lin_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg hb, zero_smul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma l05nLM_ext_pi_single {p d : ℕ} {f g : Module.End (ZMod p) (GGDepAE p d)}
    (h : ∀ k : Fin d, f (Pi.single k 1) = g (Pi.single k 1)) : f = g := by
  apply LinearMap.pi_ext
  intro i x
  have hsingle : Pi.single i x = x • (Pi.single i (1 : ZMod p)) := by
    funext j
    by_cases hj : j = i
    · rw [hj]; simp
    · simp [Pi.single_apply, hj]
  rw [hsingle, map_smul, map_smul, h i]

private lemma l05nLM_getD_map_range {α : Type} (f : ℕ → α) (d : ℕ) (k : Fin d) (dflt : α) :
    ((List.range d).map f).getD k.val dflt = f k.val := by
  have hlen : k.val < ((List.range d).map f).length := by simp
  rw [List.getD_eq_getElem ((List.range d).map f) dflt hlen, List.getElem_map]
  congr 1
  exact List.getElem_range (by simpa using k.isLt)

private lemma l05nLM_refl_length {p d : ℕ} {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = d) (hv : v.length = d) : (ggTWNRefl p q v).length = d := by
  rw [ggTWNRefl]
  exact l05nNC_sub_length hv (l05nNC_smul_length hq1)

private lemma l05nLM_toZ_refl {p d : ℕ} [Fact p.Prime] {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = d) (hq2 : q.2.length = d) (hv : v.length = d) :
    ggDepANToZ p d (ggTWNRefl p q v) =
      ggDepARefl (ggDepANToZ p d q.1) (ggDepANToZ p d q.2) (ggDepANToZ p d v) := by
  unfold ggTWNRefl
  rw [l05nNC_toZ_sub hv (l05nNC_smul_length hq1), l05nNC_toZ_smul hq1,
    ggDepANDot_cast q.2 v hq2 hv]
  rw [l05nNC_refl_apply]

private lemma l05nLM_getD_ofPair (p d : ℕ) (q : GGDepANPair) (k : Fin d) :
    (ggTWLMatOfPair p d q).getD k.val [] = ggTWNRefl p q (ggTWLBasis d k.val) := by
  rw [ggTWLMatOfPair]
  exact l05nLM_getD_map_range (fun k => ggTWNRefl p q (ggTWLBasis d k)) d k []

theorem ggTWLMatOfPair_lin {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} (hq : GGTWNValid p N q) :
    ggTWLMatWF (N - 1) (ggTWLMatOfPair p (N - 1) q) ∧
      ggTWLMatLin p (N - 1) (ggTWLMatOfPair p (N - 1) q) = ggTWNRflOf p N q := by
  constructor
  · constructor
    · rw [ggTWLMatOfPair, List.length_map, List.length_range]
    · intro c hc
      rw [ggTWLMatOfPair] at hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨k, _hk, rfl⟩ := hc
      exact l05nLM_refl_length hq.1 (l05nLM_basis_length (N - 1) k)
  · apply l05nLM_ext_pi_single
    intro k
    rw [l05nLM_lin_single, l05nLM_getD_ofPair,
      l05nLM_toZ_refl hq.1 hq.2.1 (l05nLM_basis_length (N - 1) k.val), l05nLM_toZ_basis]

private lemma l05nLM_getD_one (d : ℕ) (k : Fin d) :
    (ggTWLMatOne d).getD k.val [] = ggTWLBasis d k.val := by
  rw [ggTWLMatOne]
  exact l05nLM_getD_map_range (ggTWLBasis d) d k []

theorem ggTWLMatOne_lin {p d : ℕ} [Fact p.Prime] :
    ggTWLMatWF d (ggTWLMatOne d) ∧ ggTWLMatLin p d (ggTWLMatOne d) = 1 := by
  constructor
  · constructor
    · rw [ggTWLMatOne, List.length_map, List.length_range]
    · intro c hc
      rw [ggTWLMatOne] at hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨k, _hk, rfl⟩ := hc
      exact l05nLM_basis_length d k
  · apply l05nLM_ext_pi_single
    intro k
    rw [l05nLM_lin_single, l05nLM_getD_one, l05nLM_toZ_basis]
    simp

private lemma l05nLM_vecEq_iff_getD (p : ℕ) (u v : List ℕ) :
    ggTWLVecEq p u v = true ↔
      u.length = v.length ∧ ∀ i, i < u.length → u.getD i 0 % p = v.getD i 0 % p := by
  unfold ggTWLVecEq
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hlen : u.length = v.length := decide_eq_true_eq.mp h1
    refine ⟨hlen, ?_⟩
    intro i hi
    have hlt : i < (List.zipWith (fun a b => a % p == b % p) u v).length := by
      rw [List.length_zipWith, ← hlen, min_self]; exact hi
    have hv := (List.all_eq_true.mp h2) ((List.zipWith (fun a b => a % p == b % p) u v)[i])
      (List.getElem_mem hlt)
    rw [List.getElem_zipWith] at hv
    simp only [id_eq] at hv
    rw [beq_iff_eq] at hv
    have hiv : i < v.length := by rw [← hlen]; exact hi
    rw [List.getD_eq_getElem u 0 hi, List.getD_eq_getElem v 0 hiv]
    exact hv
  · rintro ⟨hlen, hmod⟩
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true_eq.mpr hlen, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    change x = true
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, hix⟩ := hx
    rw [← hix, List.getElem_zipWith, beq_iff_eq]
    have hiA : i < u.length := List.lt_length_left_of_zipWith hi
    have hiv : i < v.length := by rw [← hlen]; exact hiA
    have hthis := hmod i hiA
    rwa [List.getD_eq_getElem u 0 hiA, List.getD_eq_getElem v 0 hiv] at hthis

private lemma l05nLM_vecEq_iff (p d : ℕ) [Fact p.Prime] {u v : List ℕ}
    (hu : u.length = d) (hv : v.length = d) :
    ggTWLVecEq p u v = true ↔ ggDepANToZ p d u = ggDepANToZ p d v := by
  rw [l05nLM_vecEq_iff_getD]
  constructor
  · rintro ⟨_, hmod⟩
    funext j
    have hju : j.val < u.length := by rw [hu]; exact j.isLt
    simp only [ggDepANToZ]
    exact (ZMod.natCast_eq_natCast_iff' (u.getD j.val 0) (v.getD j.val 0) p).mpr (hmod j.val hju)
  · intro h
    constructor
    · rw [hu, hv]
    · intro i hi
      have hid : i < d := by rw [← hu]; exact hi
      have hcomp := congrFun h (⟨i, hid⟩ : Fin d)
      simp only [ggDepANToZ, Fin.val_mk] at hcomp
      exact (ZMod.natCast_eq_natCast_iff' (u.getD i 0) (v.getD i 0) p).mp hcomp

private lemma l05nLM_lin_eq_iff (p d : ℕ) (A B : List (List ℕ)) :
    ggTWLMatLin p d A = ggTWLMatLin p d B ↔
      ∀ k : Fin d, ggDepANToZ p d (A.getD k.val []) = ggDepANToZ p d (B.getD k.val []) := by
  constructor
  · intro h k
    rw [← l05nLM_lin_single p d A k, ← l05nLM_lin_single p d B k, h]
  · intro h
    apply l05nLM_ext_pi_single
    intro k
    rw [l05nLM_lin_single p d A k, l05nLM_lin_single p d B k, h k]

private lemma l05nLM_matEq_iff_cols (p d : ℕ) [Fact p.Prime] {A B : List (List ℕ)}
    (hA : ggTWLMatWF d A) (hB : ggTWLMatWF d B) :
    ggTWLMatEq p A B = true ↔
      ∀ k : Fin d, ggDepANToZ p d (A.getD k.val []) = ggDepANToZ p d (B.getD k.val []) := by
  constructor
  · intro h k
    have h1 : (List.zipWith (ggTWLVecEq p) A B).all id = true := by
      have := h
      rw [ggTWLMatEq, Bool.and_eq_true] at this
      exact this.2
    have hkA : k.val < A.length := by rw [hA.1]; exact k.isLt
    have hkB : k.val < B.length := by rw [hB.1]; exact k.isLt
    have hlt : k.val < (List.zipWith (ggTWLVecEq p) A B).length := by
      rw [List.length_zipWith, hA.1, hB.1, min_self]; exact k.isLt
    have hv := (List.all_eq_true.mp h1) ((List.zipWith (ggTWLVecEq p) A B)[k.val])
      (List.getElem_mem hlt)
    rw [List.getElem_zipWith] at hv
    have hAlen : (A[k.val]).length = d := hA.2 _ (List.getElem_mem hkA)
    have hBlen : (B[k.val]).length = d := hB.2 _ (List.getElem_mem hkB)
    have hv' : ggDepANToZ p d (A[k.val]) = ggDepANToZ p d (B[k.val]) :=
      (l05nLM_vecEq_iff p d hAlen hBlen).mp hv
    rw [List.getD_eq_getElem A [] hkA, List.getD_eq_getElem B [] hkB]
    exact hv'
  · intro h
    rw [ggTWLMatEq, Bool.and_eq_true]
    constructor
    · exact decide_eq_true_eq.mpr (by rw [hA.1, hB.1])
    · rw [List.all_eq_true]
      intro x hx
      change x = true
      rw [List.mem_iff_getElem] at hx
      obtain ⟨i, hi, hix⟩ := hx
      rw [← hix, List.getElem_zipWith]
      have hiA : i < A.length := List.lt_length_left_of_zipWith hi
      have hiB : i < B.length := List.lt_length_right_of_zipWith hi
      have hid : i < d := by rw [← hA.1]; exact hiA
      have hcomp : ggDepANToZ p d (A.getD i []) = ggDepANToZ p d (B.getD i []) := h ⟨i, hid⟩
      rw [List.getD_eq_getElem A [] hiA, List.getD_eq_getElem B [] hiB] at hcomp
      have hAlen : (A[i]).length = d := hA.2 _ (List.getElem_mem hiA)
      have hBlen : (B[i]).length = d := hB.2 _ (List.getElem_mem hiB)
      exact (l05nLM_vecEq_iff p d hAlen hBlen).mpr hcomp

theorem ggTWLMatEq_iff {p d : ℕ} [Fact p.Prime] {A B : List (List ℕ)} (hA : ggTWLMatWF d A)
    (hB : ggTWLMatWF d B) :
    ggTWLMatEq p A B = true ↔ ggTWLMatLin p d A = ggTWLMatLin p d B := by
  rw [l05nLM_matEq_iff_cols p d hA hB]
  exact (l05nLM_lin_eq_iff p d A B).symm

end CFSG.StandardType

end
