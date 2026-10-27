
module

public import CFSG.Monster.B.TwoA.Co2Inv.SixCertInputs
public import Certificates.Kernel.MonsterB.Six3056K
public import CFSG.Certificates.Kernel.MonsterB.QFormSound
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

open CFSG.Monster.B.TwoA.Co2Inv CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.QForm CFSG.KC.Bfs
  CertificateChecks.Six3056

namespace CertificateChecks.Batch3056

set_option maxRecDepth 100000

theorem kMat : ∀ k < 20, mat k = CFSG.KC.U6Orb.packL 22 (cRows k).toList ∧ (cRows k).size = 22 ∧
    ∀ x ∈ (cRows k).toList, x < 2 ^ 22 := by decide +kernel

theorem kRoot : (List.range 6).all (fun t => rowOf root6 t == zBasis[t]!) = true := by
  decide +kernel

theorem orN_succ (m : ℕ) (f : ℕ → ℕ) : orN (m + 1) f = Nat.lor (f m) (orN m f) := rfl

theorem encL_cons (x : ℕ) (L : List ℕ) : encL (x :: L) = x % 2 ^ 22 + 2 ^ 22 * encL L := rfl

theorem encL_snoc (x : ℕ) : ∀ L : List ℕ,
    encL (L ++ [x]) = encL L + 2 ^ (22 * L.length) * (x % 2 ^ 22)
  | [] => by simp [encL_cons, encL]
  | y :: L => by
    rw [List.cons_append, encL_cons, encL_cons, encL_snoc x L, List.length_cons, Nat.mul_succ,
      pow_add]
    ring

theorem encL_lt : ∀ L : List ℕ, encL L < 2 ^ (22 * L.length)
  | [] => by simp [encL]
  | y :: L => by
    have h1 := encL_lt L
    have h2 : y % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by positivity)
    rw [encL_cons, List.length_cons, Nat.mul_succ, pow_add]
    calc y % 2 ^ 22 + 2 ^ 22 * encL L < 2 ^ 22 + 2 ^ 22 * encL L := by omega
      _ = 2 ^ 22 * (encL L + 1) := by ring
      _ ≤ 2 ^ 22 * 2 ^ (22 * L.length) := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (22 * L.length) * 2 ^ 22 := by ring

theorem orN_encL (a : ℕ → ℕ) : ∀ m, (∀ t < m, a t < 2 ^ 22) →
    orN m (fun t => a t <<< (22 * t)) = encL ((List.range m).map a)
  | 0, _ => rfl
  | m + 1, h => by
    have hl := encL_lt ((List.range m).map a)
    rw [List.length_map, List.length_range] at hl
    rw [orN_succ, orN_encL a m (fun t ht => h t (by omega))]
    change a m <<< (22 * m) ||| _ = _
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, encL_snoc, List.length_map, List.length_range,
      Nat.mod_eq_of_lt (h m (by omega)), Nat.shiftLeft_eq]
    ring

theorem encL_orN (a : ℕ → ℕ) (h : ∀ t < 6, a t < 2 ^ 22) :
    encL ((List.range 6).map a) = orN 6 (fun t => Nat.shiftLeft (a t) (Nat.mul 22 t)) :=
  (orN_encL a 6 h).symm

theorem rowOf_lt (n t : ℕ) : rowOf n t < 2 ^ 22 := Nat.mod_lt _ (by positivity)

theorem fget_rowOf (n t : ℕ) : fget n t 22 = rowOf n t := by
  rw [CFSG.KC.U6Orb.fget_eq, rowOf, Nat.shiftRight_eq_div_pow, Nat.mul_comm]

theorem act6R_eq {k : ℕ} (hk : k < 20) (n : ℕ) : act6 k n = act6R k n := by
  obtain ⟨hm, hs, hb⟩ := kMat k hk
  have hrow : ∀ t, CFSG.Monster.B.Co2.Native.actD 22 (cRows k) (rowOf n t) =
      actB TT k (fget n t 22) := fun t => by
    rw [fget_rowOf, actB_eq kTab hk (rowOf_lt n t), hm, CFSG.KC.U6Orb.actD_eq_actK hs hb]
  rw [act6, act6R, encL_orN _ (fun t _ => by
    rw [CFSG.KC.U6Orb.actD_eq_actK hs hb]
    exact actK_lt _ _)]
  simp only [hrow]

theorem reach_iff {r x : ℕ} : Reach act6R 20 r x ↔ Reach act6 20 r x := by
  constructor
  · intro h
    induction h with
    | root => exact Reach.root
    | step k hk _ ih =>
      rw [← act6R_eq hk]
      exact Reach.step k hk ih
  · intro h
    induction h with
    | root => exact Reach.root
    | step k hk _ ih =>
      rw [act6R_eq hk]
      exact Reach.step k hk ih

theorem kTree : treeOK act6R 20 valid6 root6 recS 23040 132 4 15 64 360 = true :=
  treeOK_of_chunks (by decide) (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add none_lt t0 rfl)
    t1 rfl) t2 rfl) t3 rfl) t4 rfl) t5 rfl)

theorem kClose : closeOK act6R 20 recS edgeS 23040 132 64 360 = true := by
  refine closeOK_of_chunks (by decide) ?_
  exact sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add
    (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add
    (sl_add (sl_add none_lt c0 rfl) c1 rfl) c2 rfl) c3 rfl) c4 rfl) c5 rfl) c6 rfl) c7 rfl) c8 rfl)
    c9 rfl) c10 rfl) c11 rfl) c12 rfl) c13 rfl) c14 rfl) c15 rfl) c16 rfl) c17 rfl) c18 rfl)
    c19 rfl) c20 rfl) c21 rfl) c22 rfl) c23 rfl

theorem six : sixCheck = true := by
  obtain ⟨S, hS, hcard, hv, -, -⟩ := orbit_sound (by norm_num) kTree kClose
  obtain ⟨h1, -, h3, -⟩ := natBfs_spec (act := act6) (fuel := 30000) S
    (fun x => reach_iff.symm.trans (hS x)) hv (by rw [hcard]; norm_num)
  simp only [sixCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨h1, h3.trans hcard⟩, kRoot⟩

end CertificateChecks.Batch3056

namespace Certificates

end Certificates
