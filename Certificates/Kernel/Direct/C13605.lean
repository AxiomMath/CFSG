module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE7

namespace CertificateChecks.KernelDirect.C13605

open CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.Blueprint.Chevalley

set_option maxHeartbeats 0
set_option maxRecDepth 100000

section Chunks

variable {τ : Tag}

theorem all_of_keyChunks {α : Type*} (l : List α) (p : α → Bool) (c m : Nat)
    (hlen : l.length ≤ m * c) (h : ∀ j < m, ((l.drop (j * c)).take c).all p = true) :
    l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0
      rw [Nat.mul_zero] at hlen
      omega
    · exact h0
  have hj : i / c < m := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  have h1 := List.all_eq_true.1 (h (i / c) hj)
  apply h1
  have hmod : i % c < c := Nat.mod_lt _ hc
  have hi' : i / c * c + i % c = i := Nat.div_add_mod' i c
  have hlt : i % c < ((l.drop (i / c * c)).take c).length := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [List.mem_iff_getElem]
  refine ⟨i % c, hlt, ?_⟩
  simp only [List.getElem_take, List.getElem_drop, hi']

theorem orbitAux3_append_eq (rows reps : List (List ℕ)) :
    ∀ (l₁ l₂ : List ℕ) (n : ℕ), orbitAux3 τ rows reps n (l₁ ++ l₂) =
      (orbitAux3 τ rows reps n l₁ && orbitAux3 τ rows reps (n + l₁.length) l₂)
  | [], l₂, n => by simp [orbitAux3]
  | e :: l₁, l₂, n => by
    rw [List.cons_append, orbitAux3, orbitAux3, orbitAux3_append_eq rows reps l₁ l₂ (n + 1),
      List.length_cons, Nat.add_right_comm n 1, Nat.add_assoc]
    simp only [Bool.and_assoc]

theorem orbitAux3_of_orbChunks (rows reps : List (List ℕ)) (c : ℕ) :
    ∀ (m n : ℕ) (l : List ℕ), l.length ≤ m * c →
      (∀ j < m, orbitAux3 τ rows reps (n + j * c) ((l.drop (j * c)).take c) = true) →
      orbitAux3 τ rows reps n l = true
  | 0, n, l, hlen, _ => by
    rw [Nat.zero_mul, Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen
    simp [orbitAux3]
  | m + 1, n, l, hlen, h => by
    rw [← List.take_append_drop c l, orbitAux3_append_eq]
    have h0 := h 0 (by omega)
    rw [Nat.zero_mul, Nat.add_zero, List.drop_zero] at h0
    rw [h0, Bool.true_and]
    by_cases hc : c ≤ l.length
    · rw [List.length_take, Nat.min_eq_left hc]
      refine orbitAux3_of_orbChunks rows reps c m (n + c) (l.drop c) ?_ fun j hj => ?_
      · rw [List.length_drop]
        rw [Nat.succ_mul] at hlen
        omega
      · have := h (j + 1) (by omega)
        have e1 : (j + 1) * c = c + j * c := by rw [Nat.succ_mul, Nat.add_comm]
        rw [e1, ← Nat.add_assoc] at this
        rwa [List.drop_drop]
    · rw [List.drop_eq_nil_of_le (by omega)]
      simp [orbitAux3]

def stabKeyStep (C : RootCertificate τ) (S : StabCert3) (k : ℕ) : Bool :=
  (List.range τ.rank).all fun i =>
    StabCert3.stepAux τ (RootTables.ofCert C)
      (S.simple.map fun β => (RootTables.ofCert C).vecs.getD β []) (KTree.ofSorted S.keys)
      (imgL (RootTables.ofCert C) i (decodeT τ.rank k))

def stabHead (C : RootCertificate τ) (S : StabCert3) : Bool :=
  (KTree.ofSorted S.keys).mem (encodeT (List.range τ.rank)) &&
  decide (decodeT τ.rank (encodeT (List.range τ.rank)) = List.range τ.rank) &&
  S.simple.all (fun β => decide (β < C.roots.length) && decide (0 < height (C.root β)) &&
    decide (triPairing (vec3 (τ := τ) S.vec) (C.root β) = 0))

theorem stab_check_of_keyChunks (C : RootCertificate τ) (S : StabCert3) (c m : ℕ)
    (hhead : stabHead C S = true) (hlen : S.keys.length ≤ m * c)
    (h : ∀ j < m, ((S.keys.drop (j * c)).take c).all (stabKeyStep C S) = true) :
    S.check C = true := by
  unfold StabCert3.check StabCert3.checkWith
  rw [Bool.and_eq_true_iff]
  exact ⟨hhead, all_of_keyChunks _ _ c m hlen h⟩

end Chunks

theorem e7OrbHead : (decide (e7ThreeOrbit.length = 3 ^ Tag.E7.rank) &&
    e7ThreeReps.all fun b => decide (b.length = Tag.E7.rank)) = true := by
  decide +kernel

theorem e7OrbC0 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 0 * 160)
    ((e7ThreeOrbit.drop (0 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC1 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 1 * 160)
    ((e7ThreeOrbit.drop (1 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC2 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 2 * 160)
    ((e7ThreeOrbit.drop (2 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC3 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 3 * 160)
    ((e7ThreeOrbit.drop (3 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC4 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 4 * 160)
    ((e7ThreeOrbit.drop (4 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC5 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 5 * 160)
    ((e7ThreeOrbit.drop (5 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC6 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 6 * 160)
    ((e7ThreeOrbit.drop (6 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC7 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 7 * 160)
    ((e7ThreeOrbit.drop (7 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC8 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 8 * 160)
    ((e7ThreeOrbit.drop (8 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC9 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 9 * 160)
    ((e7ThreeOrbit.drop (9 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC10 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 10 * 160)
    ((e7ThreeOrbit.drop (10 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC11 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 11 * 160)
    ((e7ThreeOrbit.drop (11 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC12 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 12 * 160)
    ((e7ThreeOrbit.drop (12 * 160)).take 160) = true := by decide +kernel
theorem e7OrbC13 : orbitAux3 .E7 (negCartanRows .E7) e7ThreeReps (0 + 13 * 160)
    ((e7ThreeOrbit.drop (13 * 160)).take 160) = true := by decide +kernel

theorem e7S2Head : stabHead e7Certificate e7ThreeStab2 = true := by decide +kernel
theorem e7S2Pass : decide ((e7ThreeStab2.passing e7Certificate).length ≤ 1) = true := by
  decide +kernel
theorem e7S2C0 : ((e7ThreeStab2.keys.drop (0 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab2) = true := by decide +kernel
theorem e7S2C1 : ((e7ThreeStab2.keys.drop (1 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab2) = true := by decide +kernel
theorem e7S2C2 : ((e7ThreeStab2.keys.drop (2 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab2) = true := by decide +kernel
theorem e7S2C3 : ((e7ThreeStab2.keys.drop (3 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab2) = true := by decide +kernel
theorem e7S2C4 : ((e7ThreeStab2.keys.drop (4 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab2) = true := by decide +kernel
theorem e7S2C5 : ((e7ThreeStab2.keys.drop (5 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab2) = true := by decide +kernel

theorem e7S4Head : stabHead e7Certificate e7ThreeStab4 = true := by decide +kernel
theorem e7S4Pass : decide ((e7ThreeStab4.passing e7Certificate).length ≤ 1) = true := by
  decide +kernel
theorem e7S4C0 : ((e7ThreeStab4.keys.drop (0 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab4) = true := by decide +kernel
theorem e7S4C1 : ((e7ThreeStab4.keys.drop (1 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab4) = true := by decide +kernel
theorem e7S4C2 : ((e7ThreeStab4.keys.drop (2 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab4) = true := by decide +kernel
theorem e7S4C3 : ((e7ThreeStab4.keys.drop (3 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab4) = true := by decide +kernel
theorem e7S4C4 : ((e7ThreeStab4.keys.drop (4 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab4) = true := by decide +kernel
theorem e7S4C5 : ((e7ThreeStab4.keys.drop (5 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab4) = true := by decide +kernel
theorem e7S4C6 : ((e7ThreeStab4.keys.drop (6 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab4) = true := by decide +kernel

theorem e7S5Head : stabHead e7Certificate e7ThreeStab5 = true := by decide +kernel
theorem e7S5Pass : decide ((e7ThreeStab5.passing e7Certificate).length ≤ 1) = true := by
  decide +kernel
theorem e7S5C0 : ((e7ThreeStab5.keys.drop (0 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel
theorem e7S5C1 : ((e7ThreeStab5.keys.drop (1 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel
theorem e7S5C2 : ((e7ThreeStab5.keys.drop (2 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel
theorem e7S5C3 : ((e7ThreeStab5.keys.drop (3 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel
theorem e7S5C4 : ((e7ThreeStab5.keys.drop (4 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel
theorem e7S5C5 : ((e7ThreeStab5.keys.drop (5 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel
theorem e7S5C6 : ((e7ThreeStab5.keys.drop (6 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel
theorem e7S5C7 : ((e7ThreeStab5.keys.drop (7 * 96)).take 96).all
    (stabKeyStep e7Certificate e7ThreeStab5) = true := by decide +kernel

public section

theorem e7ThreeOrbitOK : orbitCheck3 .E7 e7ThreeReps e7ThreeOrbit = true := by
  unfold orbitCheck3
  rw [e7OrbHead, Bool.true_and]
  refine orbitAux3_of_orbChunks _ _ 160 14 0 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact e7OrbC0
  | 1, _ => exact e7OrbC1
  | 2, _ => exact e7OrbC2
  | 3, _ => exact e7OrbC3
  | 4, _ => exact e7OrbC4
  | 5, _ => exact e7OrbC5
  | 6, _ => exact e7OrbC6
  | 7, _ => exact e7OrbC7
  | 8, _ => exact e7OrbC8
  | 9, _ => exact e7OrbC9
  | 10, _ => exact e7OrbC10
  | 11, _ => exact e7OrbC11
  | 12, _ => exact e7OrbC12
  | 13, _ => exact e7OrbC13
  | j + 14, h => exact absurd h (by omega)

theorem e7StabOK0 : (e7ThreeStab0.check e7Certificate &&
    decide ((e7ThreeStab0.passing e7Certificate).length ≤ 1)) = true := by
  decide +kernel

theorem e7StabOK1 : (e7ThreeStab1.check e7Certificate &&
    decide ((e7ThreeStab1.passing e7Certificate).length ≤ 1)) = true := by
  decide +kernel

theorem e7StabOK2 : (e7ThreeStab2.check e7Certificate &&
    decide ((e7ThreeStab2.passing e7Certificate).length ≤ 1)) = true := by
  rw [Bool.and_eq_true_iff]
  refine ⟨stab_check_of_keyChunks _ _ 96 6 e7S2Head (by decide +kernel) fun j hj => ?_, e7S2Pass⟩
  match j, hj with
  | 0, _ => exact e7S2C0
  | 1, _ => exact e7S2C1
  | 2, _ => exact e7S2C2
  | 3, _ => exact e7S2C3
  | 4, _ => exact e7S2C4
  | 5, _ => exact e7S2C5
  | j + 6, h => exact absurd h (by omega)

theorem e7StabOK3 : (e7ThreeStab3.check e7Certificate &&
    decide ((e7ThreeStab3.passing e7Certificate).length ≤ 1)) = true := by
  decide +kernel

theorem e7StabOK4 : (e7ThreeStab4.check e7Certificate &&
    decide ((e7ThreeStab4.passing e7Certificate).length ≤ 1)) = true := by
  rw [Bool.and_eq_true_iff]
  refine ⟨stab_check_of_keyChunks _ _ 96 7 e7S4Head (by decide +kernel) fun j hj => ?_, e7S4Pass⟩
  match j, hj with
  | 0, _ => exact e7S4C0
  | 1, _ => exact e7S4C1
  | 2, _ => exact e7S4C2
  | 3, _ => exact e7S4C3
  | 4, _ => exact e7S4C4
  | 5, _ => exact e7S4C5
  | 6, _ => exact e7S4C6
  | j + 7, h => exact absurd h (by omega)

theorem e7StabOK5 : (e7ThreeStab5.check e7Certificate &&
    decide ((e7ThreeStab5.passing e7Certificate).length ≤ 1)) = true := by
  rw [Bool.and_eq_true_iff]
  refine ⟨stab_check_of_keyChunks _ _ 96 8 e7S5Head (by decide +kernel) fun j hj => ?_, e7S5Pass⟩
  match j, hj with
  | 0, _ => exact e7S5C0
  | 1, _ => exact e7S5C1
  | 2, _ => exact e7S5C2
  | 3, _ => exact e7S5C3
  | 4, _ => exact e7S5C4
  | 5, _ => exact e7S5C5
  | 6, _ => exact e7S5C6
  | 7, _ => exact e7S5C7
  | j + 8, h => exact absurd h (by omega)

theorem e7ThreeCheck_eq_true : e7ThreeCheck () = true := by
  simp only [e7ThreeCheck, List.all_cons, List.all_nil, e7ThreeOrbitOK, e7StabOK0, e7StabOK1,
    e7StabOK2, e7StabOK3, e7StabOK4, e7StabOK5, Bool.and_true]

end

end CertificateChecks.KernelDirect.C13605
