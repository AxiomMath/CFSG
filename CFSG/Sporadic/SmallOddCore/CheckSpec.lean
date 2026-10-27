module

public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ}

@[expose] noncomputable def hkeyOf (n : ℕ) (g : Equiv.Perm (Fin n)) : UInt64 :=
  Nat.fold n (fun i _ h => (h ^^^ (UInt32.ofNat (idx n g i)).toUInt64) * 1099511628211)
    14695981039346656037

theorem hkey_eq_hkeyOf {T : Table} {g : Equiv.Perm (Fin n)} (h : Rep n T g) :
    hkey n T = hkeyOf n g := by
  unfold hkey hkeyOf
  have hf : (fun i (_ : i < n) (acc : UInt64) => (acc ^^^ (T[i]!).toUInt64) * 1099511628211) =
      fun i (_ : i < n) (acc : UInt64) =>
        (acc ^^^ (UInt32.ofNat (idx n g i)).toUInt64) * 1099511628211 := by
    funext i hi acc
    rw [← h i hi]
    unfold ap
    rw [UInt32.ofNat_toNat]
  rw [hf]

theorem map_hkey_eq {Ts : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) Ts gs) :
    Ts.map (fun T => (hkey n T).toNat) = gs.map (fun g => (hkeyOf n g).toNat) := by
  induction h with
  | nil => rfl
  | cons hT _ ih => rw [List.map_cons, List.map_cons, ih, hkey_eq_hkeyOf hT]

theorem nodup_of_hkeysDistinct {Ts : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) Ts gs) (hk : hkeysDistinct n Ts = true) : gs.Nodup := by
  have hsorted := (pairwise_of_strictlyIncreasing hk).imp (fun hab => Nat.ne_of_lt hab)
  have hkeys : (Ts.map fun T => (hkey n T).toNat).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.1 hsorted
  rw [map_hkey_eq h] at hkeys
  exact List.Nodup.of_map _ hkeys

theorem mulTreeOK_spec (hn : n < 2 ^ 32) (H : Subgroup (Equiv.Perm (Fin n))) {gens : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ gg l ∈ H)
    {elts : Array Table} {par lab : Array ℕ} (h : mulTreeOK n gens elts par lab = true) :
    ∀ k < elts.size, ∃ c ∈ H, Rep n elts[k]! c := by
  simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq, allIn_eq_true] at h
  obtain ⟨⟨_, h0⟩, hk⟩ := h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk'
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, H.one_mem, rep_of_tblEq (Rep.idT hn) h0⟩
    · obtain ⟨⟨hpar, hlab⟩, heq⟩ := hk k hpos hk'
      obtain ⟨c, hc, hrep⟩ := ih _ hpar (hpar.trans hk')
      obtain ⟨hgl, hgH⟩ := hg _ hlab
      exact ⟨c * gg lab[k]!, H.mul_mem hc hgH, rep_of_tblEq (Rep.compT hrep hgl) heq⟩

theorem memT_spec {L : Array Table} {e : ℕ → Equiv.Perm (Fin n)}
    (hL : ∀ k < L.size, Rep n L[k]! (e k)) {x : Table} {g : Equiv.Perm (Fin n)} (hx : Rep n x g)
    (h : memT n L x = true) : ∃ k < L.size, g = e k := by
  rw [memT, Array.any_eq_true] at h
  obtain ⟨k, hk, hxk⟩ := h
  refine ⟨k, hk, ?_⟩
  have hk' := hL k hk
  rw [getElem!_pos L k hk] at hk'
  exact (rep_unique (rep_of_tblEq hk' hxk) hx).symm

theorem closedOK_spec {gens : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} (hg : ∀ l < gens.size, Rep n gens[l]! (gg l))
    (hginv : ∀ l < gens.size, ∃ l' < gens.size, gg l' = (gg l)⁻¹)
    {L : Array Table} {e : ℕ → Equiv.Perm (Fin n)} (hL : ∀ k < L.size, Rep n L[k]! (e k))
    (h1 : ∃ k < L.size, e k = 1) (hc : closedOK n gens L = true) :
    ∀ x ∈ closure (gg '' {l | l < gens.size}), ∃ k < L.size, x = e k := by
  rw [closedOK, Array.all_eq_true] at hc
  have hstep : ∀ k < L.size, ∀ l < gens.size, ∃ k' < L.size, e k * gg l = e k' := by
    intro k hk l hl
    have h2 := hc k hk
    rw [Array.all_eq_true] at h2
    have h3 := h2 l hl
    have hk' := hL k hk
    rw [getElem!_pos L k hk] at hk'
    have hl' := hg l hl
    rw [getElem!_pos gens l hl] at hl'
    exact memT_spec hL (Rep.compT hk' hl') h3
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => obtain ⟨k, hk, hk1⟩ := h1; exact ⟨k, hk, hk1.symm⟩
  | mul_right x _ y hy ih =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨k', hk', e'⟩ := hstep k hk l hl
    exact ⟨k', hk', e'⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨l', hl', hinv⟩ := hginv l hl
    obtain ⟨k', hk', e'⟩ := hstep k hk l' hl'
    exact ⟨k', hk', by rw [← hinv, e']⟩

theorem natArr_getElem! (T : Table) (i : ℕ) : (natArr T)[i]! = ap T i := by
  unfold natArr ap
  by_cases hi : i < T.size
  · rw [getElem!_pos (T.map (·.toNat)) i (by simpa using hi), Array.getElem_map,
      getElem!_pos T i hi]
  · rw [getElem!_neg (T.map (·.toNat)) i (by simpa using hi), getElem!_neg T i hi]
    rfl

theorem co2Rep_natArr_iff {T : Table} {g : Equiv.Perm (Fin n)} :
    CFSG.Monster.B.Co2.Rep n (natArr T) g ↔ Rep n T g := by
  constructor
  · intro h i hi
    rw [← natArr_getElem!, h ⟨i, hi⟩, idx_of_lt g hi]
    rfl
  · intro h x
    rw [natArr_getElem!, h x x.2, idx_of_lt g x.2]
    rfl

theorem rep_permOfArr_natArr {T : Table} {r : Array ℕ}
    (h : CFSG.Monster.B.Co2.Native.isInvA n (natArr T) r = true) :
    Rep n T (CFSG.Monster.B.Co2.permOfArr n (natArr T)) :=
  co2Rep_natArr_iff.1 (CFSG.Monster.B.Co2.rep_permOfArr h).1

end CFSG.Sporadic.SmallOddCore
