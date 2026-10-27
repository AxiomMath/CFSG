module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusNat
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNatSimplePart1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg
open Matrix
open scoped Matrix

section Helpers

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type} [Field k] [CharP k 2]

private theorem c2slomqns_weylD_e_lt {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val + 1 < n) :
    spinAction (quadPlus n F) (weylD F hn s) (plusVec n F s true) =
      plusVec n F ⟨s.val + 1, hs⟩ true := by
  rw [spinAction_weylD, rootIdxD_of_lt n hs, rootIdxD'_of_lt n hs, rootSignD_of_lt n hs]
  simp [CharTwo.neg_eq]

private theorem c2slomqns_weylD_f_lt {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val + 1 < n) :
    spinAction (quadPlus n F) (weylD F hn s) (plusVec n F ⟨s.val + 1, hs⟩ false) =
      plusVec n F s false := by
  rw [spinAction_weylD, rootIdxD_of_lt n hs, rootIdxD'_of_lt n hs, rootSignD_of_lt n hs]
  rw [longWeylSign_of_ne (m := ⟨s.val + 1, hs⟩) (Fin.ne_of_val_ne (by simp))]
  simp

private theorem c2slomqns_weylD_e_last {n : ℕ} (hn : 3 ≤ n) :
    spinAction (quadPlus n F) (weylD F hn (⟨n - 1, by omega⟩ : Fin n))
      (plusVec n F (⟨n - 2, by omega⟩ : Fin n) true) =
      plusVec n F (⟨n - 1, by omega⟩ : Fin n) false := by
  rw [weylD_eq_of_not_lt F hn (k := ⟨n - 1, by omega⟩) (by simp; omega)
    (i := ⟨n - 2, by omega⟩) (j := ⟨n - 1, by omega⟩) rfl rfl
    (Fin.ne_of_val_ne (by simp; omega))]
  rw [show plusVec n F (⟨n - 2, by omega⟩ : Fin n) true =
      (plusFrame n F hn).vec (⟨n - 2, by omega⟩ : Fin n) true from rfl,
    HypFrame.spinAction_longWeyl_vec (F := plusFrame n F hn)]
  simp [longWeylBool, longWeylSign, CharTwo.neg_eq]

private theorem c2slomqns_weylD_e_lt_rep {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) {s : Fin n}
    (hs : s.val + 1 < n) :
    (omPlusNatRep n φ) (weylD F hn s) (Pi.single (Sum.inl s) (1 : k)) =
      Pi.single (Sum.inl ⟨s.val + 1, hs⟩) (1 : k) := by
  rw [show Pi.single (Sum.inl s) (1 : k) = fun a => φ (plusVec n F s true a) from by
    rw [← c2slomqns_phi_single φ (Sum.inl s)]
    rfl]
  rw [c2slomqns_mapVec, c2slomqns_weylD_e_lt (F := F) hn hs]
  simpa using c2slomqns_phi_single φ (Sum.inl ⟨s.val + 1, hs⟩)

private theorem c2slomqns_weylD_f_lt_rep {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) {s : Fin n}
    (hs : s.val + 1 < n) :
    (omPlusNatRep n φ) (weylD F hn s) (Pi.single (Sum.inr ⟨s.val + 1, hs⟩) (1 : k)) =
      Pi.single (Sum.inr s) (1 : k) := by
  rw [show Pi.single (Sum.inr ⟨s.val + 1, hs⟩) (1 : k) =
      fun a => φ (plusVec n F ⟨s.val + 1, hs⟩ false a) from by
    rw [← c2slomqns_phi_single φ (Sum.inr ⟨s.val + 1, hs⟩)]
    rfl]
  rw [c2slomqns_mapVec, c2slomqns_weylD_f_lt (F := F) hn hs]
  simpa using c2slomqns_phi_single φ (Sum.inr s)

private theorem c2slomqns_weylD_e_last_rep {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) :
    (omPlusNatRep n φ) (weylD F hn (⟨n - 1, by omega⟩ : Fin n))
      (Pi.single (Sum.inl (⟨n - 2, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inr (⟨n - 1, by omega⟩ : Fin n)) (1 : k) := by
  rw [show Pi.single (Sum.inl (⟨n - 2, by omega⟩ : Fin n)) (1 : k) =
      fun a => φ (plusVec n F (⟨n - 2, by omega⟩ : Fin n) true a) from by
    rw [← c2slomqns_phi_single φ (Sum.inl (⟨n - 2, by omega⟩ : Fin n))]
    rfl]
  rw [c2slomqns_mapVec, c2slomqns_weylD_e_last (F := F) hn]
  simpa using c2slomqns_phi_single φ (Sum.inr (⟨n - 1, by omega⟩ : Fin n))

private theorem c2slomqns_e_mem_orbit {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) (i : Fin n) :
    Pi.single (Sum.inl i) (1 : k) ∈
      orbitSpan (omPlusNatRep n φ) (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) := by
  have key : ∀ (j : ℕ) (hj : j < n),
      (Pi.single (Sum.inl (⟨j, hj⟩ : Fin n)) (1 : k)) ∈
        orbitSpan (omPlusNatRep n φ) (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using mem_orbitSpan_self (omPlusNatRep n φ)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
    | succ j ih =>
      intro hj
      have hj' : j < n := by omega
      rw [← c2slomqns_weylD_e_lt_rep (F := F) hn φ (s := ⟨j, hj'⟩) hj]
      exact orbitSpan_stable (omPlusNatRep n φ)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) (weylD F hn ⟨j, hj'⟩) (ih hj')
  exact key i.val i.isLt

private theorem c2slomqns_f_mem_orbit {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) (i : Fin n) :
    Pi.single (Sum.inr i) (1 : k) ∈
      orbitSpan (omPlusNatRep n φ) (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) := by
  have key : ∀ j : ℕ, j ≤ n - 1 → ∀ (hj : n - 1 - j < n),
      (Pi.single (Sum.inr (⟨n - 1 - j, hj⟩ : Fin n)) (1 : k)) ∈
        orbitSpan (omPlusNatRep n φ) (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj hj'
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have h := orbitSpan_stable (omPlusNatRep n φ)
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
          (weylD F hn (⟨n - 1, by omega⟩ : Fin n))
          (c2slomqns_e_mem_orbit hn φ (⟨n - 2, by omega⟩ : Fin n))
        rw [c2slomqns_weylD_e_last_rep (F := F) hn φ] at h
        have hidx : (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 1 - 0, hj'⟩ := Fin.ext (by simp)
        rwa [hidx] at h
      · have hprev := ih (j - 1) (by omega) (by omega) (by omega : n - 1 - (j - 1) < n)
        have hs : (⟨n - 1 - j, by omega⟩ : Fin n).val + 1 < n := by simp; omega
        have hidx : (⟨(⟨n - 1 - j, by omega⟩ : Fin n).val + 1, hs⟩ : Fin n) =
            ⟨n - 1 - (j - 1), by omega⟩ := Fin.ext (by simp; omega)
        rw [← hidx] at hprev
        have h := orbitSpan_stable (omPlusNatRep n φ)
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
          (weylD F hn ⟨n - 1 - j, by omega⟩) hprev
        have hstep := c2slomqns_weylD_f_lt_rep (F := F) hn φ
          (s := ⟨n - 1 - j, by omega⟩) hs
        rw [hstep] at h
        exact h
  have h := key (n - 1 - i.val) (by omega) (by omega : n - 1 - (n - 1 - i.val) < n)
  have hidx : (⟨n - 1 - (n - 1 - i.val), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
  rw [hidx] at h
  exact h

private theorem c2slomqns_orbitSpan_top {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) :
    orbitSpan (omPlusNatRep n φ) (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun k (Fin n ⊕ Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  rw [Pi.basisFun_apply]
  rcases b with i | i
  · exact c2slomqns_e_mem_orbit hn φ i
  · exact c2slomqns_f_mem_orbit hn φ i

end Helpers

theorem omq_isSimpleRep_omPlusNatRep_embedding {n : ℕ} (hn : 3 ≤ n) {F k : Type} [Field F]
    [Finite F] [CharP F 2] [Field k] (φ : F →+* k) :
    CFSG.Quasithin.SmithCurtis.IsSimpleRep (omPlusNatRep n φ) := by
  haveI : CharP k 2 := charP_of_injective_ringHom φ.injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (Fin n ⊕ Fin n → k) :=
    ⟨0, Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) 1, fun h => by
      have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin n))
      simpa using this⟩
  exact (omPlusCurtisDatum n F hn).isSimpleRep_of_fixU (omPlusNatRep n φ)
    (c2slomqns_fixU_mem hn φ) (c2slomqns_orbitSpan_top hn φ)

end CFSG.LocalAnalysis.WeakClosure81
