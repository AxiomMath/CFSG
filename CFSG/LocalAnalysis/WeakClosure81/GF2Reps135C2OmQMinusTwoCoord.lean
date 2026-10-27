module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private lemma c2slomqmtc_injective_four {α : Type*} {v0 v1 v2 v3 : α}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    Function.Injective ![v0, v1, v2, v3] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private lemma c2slomqmtc_inOrbit_single {l m h : ℕ} (hl : 3 ≤ l) {z p c : Fin l}
    (hzp : z ≠ p) (hzc : z ≠ c) {A B : ZMod m} {e e' : ℤ}
    (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1) :
    OmqMinusInOrbit
      ((Pi.single z A + Pi.single p B : Fin l → ZMod m), (0 : ZMod h))
      ((Pi.single z ((e : ZMod m) * A) + Pi.single c ((e' : ZMod m) * B) : Fin l → ZMod m),
        (0 : ZMod h)) := by
  obtain ⟨π', s', hsp, hprod, hact⟩ :=
    omq_exists_signed_perm_two_coord hl hzp hzc he he' A B
  unfold OmqMinusInOrbit
  refine ⟨π', s', hsp, ?_⟩
  unfold omqMinusAct
  rw [hact, hprod]
  simp

theorem omq_minus_exists_four_two_coord {l : ℕ} (hl : 3 ≤ l) {m h : ℕ} (hm : Odd m)
    {A B : ZMod m} (hA : A ≠ 0) (hB : B ≠ 0) {π : Equiv.Perm (Fin l)} {s : Fin l → ℤ}
    (hs : SpIsSign s) (hsh : OmqMinusShape (by omega : 2 ≤ l) π s) :
    ∃ u : Fin 4 → OmqMinusLat l m h, Function.Injective u ∧
      (∀ i, OmqMinusInOrbit
        ((Pi.single ⟨0, by omega⟩ A + Pi.single ⟨1, by omega⟩ B : Fin l → ZMod m),
          (0 : ZMod h)) (u i)) ∧
      ∀ i i', u i ≠ omqMinusAct π s (u i') := by
  have hAneg : A ≠ -A := ZMod.ne_neg_self hm hA
  have hBneg : B ≠ -B := ZMod.ne_neg_self hm hB
  unfold OmqMinusShape at hsh
  rcases hsh with ⟨hs1, hππ, hπ0, hπ1⟩ | ⟨hπ, hs0, hodd⟩
  ·
    let z : Fin l := ⟨0, by omega⟩
    let p : Fin l := ⟨1, by omega⟩
    let q : Fin l := ⟨2, by omega⟩
    have hzp : z ≠ p := by simp [z, p]
    have hzq : z ≠ q := by simp [z, q]
    have hpq : p ≠ q := by simp [p, q]
    have hqz : q ≠ z := hzq.symm
    have hqp : q ≠ p := hpq.symm
    let v0 : Fin l → ZMod m := Pi.single z A + Pi.single q B
    let v1 : Fin l → ZMod m := Pi.single z (-A) + Pi.single q B
    let v2 : Fin l → ZMod m := Pi.single z A + Pi.single q (-B)
    let v3 : Fin l → ZMod m := Pi.single z (-A) + Pi.single q (-B)
    let u : Fin 4 → OmqMinusLat l m h :=
      ![(v0, (0 : ZMod h)), (v1, (0 : ZMod h)), (v2, (0 : ZMod h)), (v3, (0 : ZMod h))]
    have hv01 : v0 ≠ v1 := by
      intro hh
      have hc := congrFun hh z
      simp only [v0, v1, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc
    have hv02 : v0 ≠ v2 := by
      intro hh
      have hc := congrFun hh q
      simp only [v0, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzq,
        zero_add] at hc
      exact hBneg hc
    have hv03 : v0 ≠ v3 := by
      intro hh
      have hc := congrFun hh z
      simp only [v0, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc
    have hv12 : v1 ≠ v2 := by
      intro hh
      have hc := congrFun hh z
      simp only [v1, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc.symm
    have hv13 : v1 ≠ v3 := by
      intro hh
      have hc := congrFun hh q
      simp only [v1, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzq,
        zero_add] at hc
      exact hBneg hc
    have hv23 : v2 ≠ v3 := by
      intro hh
      have hc := congrFun hh z
      simp only [v2, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc
    refine ⟨u, ?_, ?_, ?_⟩
    · exact c2slomqmtc_injective_four
        (fun hh => hv01 (Prod.ext_iff.mp hh).1)
        (fun hh => hv02 (Prod.ext_iff.mp hh).1)
        (fun hh => hv03 (Prod.ext_iff.mp hh).1)
        (fun hh => hv12 (Prod.ext_iff.mp hh).1)
        (fun hh => hv13 (Prod.ext_iff.mp hh).1)
        (fun hh => hv23 (Prod.ext_iff.mp hh).1)
    · intro i
      fin_cases i
      · simpa [u, v0] using
          c2slomqmtc_inOrbit_single hl hzp hzq (A := A) (B := B) (Or.inl rfl) (Or.inl rfl)
      · simpa [u, v1] using
          c2slomqmtc_inOrbit_single hl hzp hzq (A := A) (B := B) (Or.inr rfl) (Or.inl rfl)
      · simpa [u, v2] using
          c2slomqmtc_inOrbit_single hl hzp hzq (A := A) (B := B) (Or.inl rfl) (Or.inr rfl)
      · simpa [u, v3] using
          c2slomqmtc_inOrbit_single hl hzp hzq (A := A) (B := B) (Or.inr rfl) (Or.inr rfl)
    · intro i i' heq
      have hzval : ∀ k, (u k).1 z ≠ 0 := by
        intro k
        fin_cases k <;>
          simp [u, v0, v1, v2, v3, Pi.single_eq_of_ne' hqz, hA, neg_ne_zero]
      have hsymm : π.symm z = p := (Equiv.symm_apply_eq π).2 hπ1.symm
      have hxuz : ∀ k, (omqSignedAct π s (u k).1) z = 0 := by
        intro k
        have hp0 : (u k).1 p = 0 := by
          fin_cases k <;>
            simp [u, v0, v1, v2, v3, Pi.single_eq_of_ne' hzp, Pi.single_eq_of_ne' hqp]
        simp only [omqSignedAct]
        rw [hsymm, hp0, mul_zero]
      have hc : (u i).1 z = (omqSignedAct π s (u i').1) z := by
        have h1 := congrFun (congrArg Prod.fst heq) z
        simpa [omqMinusAct] using h1
      rw [hxuz i'] at hc
      exact hzval i hc
  ·
    let z : Fin l := ⟨0, by omega⟩
    let p : Fin l := ⟨1, by omega⟩
    let q : Fin l := ⟨2, by omega⟩
    have hzp : z ≠ p := by simp [z, p]
    have hzq : z ≠ q := by simp [z, q]
    have hpq : p ≠ q := by simp [p, q]
    have hpz : p ≠ z := hzp.symm
    have hqz : q ≠ z := hzq.symm
    let v0 : Fin l → ZMod m := Pi.single z A + Pi.single p B
    let v1 : Fin l → ZMod m := Pi.single z A + Pi.single p (-B)
    let v2 : Fin l → ZMod m := Pi.single z A + Pi.single q B
    let v3 : Fin l → ZMod m := Pi.single z A + Pi.single q (-B)
    let u : Fin 4 → OmqMinusLat l m h :=
      ![(v0, (0 : ZMod h)), (v1, (0 : ZMod h)), (v2, (0 : ZMod h)), (v3, (0 : ZMod h))]
    have hv01 : v0 ≠ v1 := by
      intro hh
      have hc := congrFun hh p
      simp only [v0, v1, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        zero_add] at hc
      exact hBneg hc
    have hv02 : v0 ≠ v2 := by
      intro hh
      have hc := congrFun hh p
      simp only [v0, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB hc
    have hv03 : v0 ≠ v3 := by
      intro hh
      have hc := congrFun hh p
      simp only [v0, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB hc
    have hv12 : v1 ≠ v2 := by
      intro hh
      have hc := congrFun hh p
      simp only [v1, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB (neg_eq_zero.mp hc)
    have hv13 : v1 ≠ v3 := by
      intro hh
      have hc := congrFun hh p
      simp only [v1, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB (neg_eq_zero.mp hc)
    have hv23 : v2 ≠ v3 := by
      intro hh
      have hc := congrFun hh q
      simp only [v2, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzq,
        zero_add] at hc
      exact hBneg hc
    refine ⟨u, ?_, ?_, ?_⟩
    · exact c2slomqmtc_injective_four
        (fun hh => hv01 (Prod.ext_iff.mp hh).1)
        (fun hh => hv02 (Prod.ext_iff.mp hh).1)
        (fun hh => hv03 (Prod.ext_iff.mp hh).1)
        (fun hh => hv12 (Prod.ext_iff.mp hh).1)
        (fun hh => hv13 (Prod.ext_iff.mp hh).1)
        (fun hh => hv23 (Prod.ext_iff.mp hh).1)
    · intro i
      fin_cases i
      · simpa [u, v0] using
          c2slomqmtc_inOrbit_single hl hzp hzp (A := A) (B := B) (Or.inl rfl) (Or.inl rfl)
      · simpa [u, v1] using
          c2slomqmtc_inOrbit_single hl hzp hzp (A := A) (B := B) (Or.inl rfl) (Or.inr rfl)
      · simpa [u, v2] using
          c2slomqmtc_inOrbit_single hl hzp hzq (A := A) (B := B) (Or.inl rfl) (Or.inl rfl)
      · simpa [u, v3] using
          c2slomqmtc_inOrbit_single hl hzp hzq (A := A) (B := B) (Or.inl rfl) (Or.inr rfl)
    · intro i i' heq
      have hzval : ∀ k, (u k).1 z = A := by
        intro k
        fin_cases k <;>
          simp [u, v0, v1, v2, v3, Pi.single_eq_of_ne' hpz, Pi.single_eq_of_ne' hqz]
      subst hπ
      have h1z : (1 : Equiv.Perm (Fin l)).symm z = z := rfl
      have hxuz : ∀ k, (omqSignedAct 1 s (u k).1) z = -A := by
        intro k
        simp only [omqSignedAct]
        rw [h1z, hzval k, hs0]
        simp
      have hc : (u i).1 z = (omqSignedAct 1 s (u i').1) z := by
        have h1 := congrFun (congrArg Prod.fst heq) z
        simpa [omqMinusAct] using h1
      rw [hxuz i'] at hc
      rw [hzval i] at hc
      exact hAneg hc

end CFSG.LocalAnalysis.WeakClosure81
