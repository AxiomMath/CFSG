module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusSigned

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private lemma c2slomqtc_ne_neg_self {m : ℕ} (hm : Odd m) {A : ZMod m} (hA : A ≠ 0) :
    A ≠ -A := by
  intro h
  have hAA : A + A = 0 := (eq_neg_iff_add_eq_zero).1 h
  have h2 : (2 : ZMod m) * A = 0 := by simpa [two_mul] using hAA
  exact hA ((IsUnit.mul_right_eq_zero
    ((ZMod.isUnit_iff_coprime 2 m).2 hm.coprime_two_right.symm)).1 h2)

private lemma c2slomqtc_intCast_mul_ne_zero {m : ℕ} {A : ZMod m} (hA : A ≠ 0) {e f : ℤ}
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1) :
    ((e : ZMod m) * ((f : ZMod m) * A)) ≠ 0 := by
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> simp [hA]

private lemma c2slomqtc_injective_four {α : Type*} {v0 v1 v2 v3 : α}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    Function.Injective ![v0, v1, v2, v3] := by
  intro i l h
  fin_cases i <;> fin_cases l <;> simp_all

theorem omq_exists_four_orbit_two_coord {n : ℕ} (hn : 3 ≤ n) {m : ℕ} (hm : Odd m)
    {A B : ZMod m} (hA : A ≠ 0) (hB : B ≠ 0) {a b : Fin n} (hab : a ≠ b)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hs : SpIsSign s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ u : Fin 4 → Fin n → ZMod m, Function.Injective u ∧
      (∀ i, ∃ (π' : Equiv.Perm (Fin n)) (s' : Fin n → ℤ), SpIsSign s' ∧ ∏ c, s' c = 1 ∧
        omqSignedAct π' s' (Pi.single a A + Pi.single b B) = u i) ∧
      ∀ i l, u i ≠ omqSignedAct π s (u l) := by
  have hAneg : A ≠ -A := c2slomqtc_ne_neg_self hm hA
  have hBneg : B ≠ -B := c2slomqtc_ne_neg_self hm hB
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ01, hπ10, hs01⟩
  ·
    let z : Fin n := ⟨0, by omega⟩
    let p : Fin n := ⟨1, by omega⟩
    let q : Fin n := ⟨2, by omega⟩
    have hpz : p ≠ z := by simp [p, z]
    have hqz : q ≠ z := by simp [q, z]
    have hpq : p ≠ q := by simp [p, q]
    have hzp : z ≠ p := hpz.symm
    have hzq : z ≠ q := hqz.symm
    let v0 : Fin n → ZMod m := Pi.single z A + Pi.single p B
    let v1 : Fin n → ZMod m := Pi.single z A + Pi.single p (-B)
    let v2 : Fin n → ZMod m := Pi.single z A + Pi.single q B
    let v3 : Fin n → ZMod m := Pi.single z A + Pi.single q (-B)
    have hv01 : v0 ≠ v1 := by
      intro h
      have hc := congrFun h p
      simp only [v0, v1, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        zero_add] at hc
      exact hBneg hc
    have hv02 : v0 ≠ v2 := by
      intro h
      have hc := congrFun h p
      simp only [v0, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB hc
    have hv03 : v0 ≠ v3 := by
      intro h
      have hc := congrFun h p
      simp only [v0, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB hc
    have hv12 : v1 ≠ v2 := by
      intro h
      have hc := congrFun h p
      simp only [v1, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB (neg_eq_zero.mp hc)
    have hv13 : v1 ≠ v3 := by
      intro h
      have hc := congrFun h p
      simp only [v1, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzp,
        Pi.single_eq_of_ne' hpq.symm, zero_add] at hc
      exact hB (neg_eq_zero.mp hc)
    have hv23 : v2 ≠ v3 := by
      intro h
      have hc := congrFun h q
      simp only [v2, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzq,
        zero_add] at hc
      exact hBneg hc
    have huzall : ∀ i, ![v0, v1, v2, v3] i z = A := by
      intro i
      fin_cases i <;>
        simp [v0, v1, v2, v3, Pi.single_eq_of_ne hzp, Pi.single_eq_of_ne hzq]
    have hsymm : π.symm z = z := (Equiv.symm_apply_eq π).2 hπ0.symm
    have hxuz : ∀ l, omqSignedAct π s (![v0, v1, v2, v3] l) z = -A := by
      intro l
      unfold omqSignedAct
      rw [hsymm, huzall l, hs0]
      simp
    refine ⟨![v0, v1, v2, v3], c2slomqtc_injective_four hv01 hv02 hv03 hv12 hv13 hv23,
      ?_, ?_⟩
    · intro i
      fin_cases i
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := p) (e := 1) (e' := 1) hn hab hzp (Or.inl rfl) (Or.inl rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v0]⟩
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := p) (e := 1) (e' := -1) hn hab hzp (Or.inl rfl) (Or.inr rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v1]⟩
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := q) (e := 1) (e' := 1) hn hab hzq (Or.inl rfl) (Or.inl rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v2]⟩
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := q) (e := 1) (e' := -1) hn hab hzq (Or.inl rfl) (Or.inr rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v3]⟩
    · intro i l heq
      have hc := congrFun heq z
      rw [huzall i, hxuz l] at hc
      exact hAneg hc
  ·
    let z : Fin n := ⟨0, by omega⟩
    let o : Fin n := ⟨1, by omega⟩
    let q : Fin n := ⟨2, by omega⟩
    have hzo : z ≠ o := by simp [z, o]
    have hoz : o ≠ z := hzo.symm
    have hzq : z ≠ q := by simp [z, q]
    have hqz : q ≠ z := hzq.symm
    have hoq : o ≠ q := by simp [o, q]
    have hqo : q ≠ o := hoq.symm
    let v0 : Fin n → ZMod m := Pi.single z A + Pi.single q B
    let v1 : Fin n → ZMod m := Pi.single z (-A) + Pi.single q B
    let v2 : Fin n → ZMod m := Pi.single z A + Pi.single q (-B)
    let v3 : Fin n → ZMod m := Pi.single z (-A) + Pi.single q (-B)
    have hv01 : v0 ≠ v1 := by
      intro h
      have hc := congrFun h z
      simp only [v0, v1, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc
    have hv02 : v0 ≠ v2 := by
      intro h
      have hc := congrFun h q
      simp only [v0, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzq,
        zero_add] at hc
      exact hBneg hc
    have hv03 : v0 ≠ v3 := by
      intro h
      have hc := congrFun h z
      simp only [v0, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc
    have hv12 : v1 ≠ v2 := by
      intro h
      have hc := congrFun h z
      simp only [v1, v2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc.symm
    have hv13 : v1 ≠ v3 := by
      intro h
      have hc := congrFun h q
      simp only [v1, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hzq,
        zero_add] at hc
      exact hBneg hc
    have hv23 : v2 ≠ v3 := by
      intro h
      have hc := congrFun h z
      simp only [v2, v3, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hqz,
        add_zero] at hc
      exact hAneg hc
    have huzero : ∀ i, ![v0, v1, v2, v3] i o = 0 := by
      intro i
      fin_cases i <;>
        simp [v0, v1, v2, v3, Pi.single_eq_of_ne hoz, Pi.single_eq_of_ne hoq]
    have hlz : ∀ l, ![v0, v1, v2, v3] l z = A ∨ ![v0, v1, v2, v3] l z = -A := by
      intro l
      fin_cases l <;>
        simp [v0, v1, v2, v3, Pi.single_eq_same, Pi.single_eq_of_ne' hqz]
    have hsymm : π.symm o = z := (Equiv.symm_apply_eq π).2 hπ01.symm
    have hne : ∀ l, ((s z : ℤ) : ZMod m) * (![v0, v1, v2, v3] l z) ≠ 0 := by
      intro l
      rcases hlz l with h | h
      · rw [h]
        simpa using c2slomqtc_intCast_mul_ne_zero hA (hs z) (Or.inl rfl)
      · rw [h]
        have hkey := c2slomqtc_intCast_mul_ne_zero (A := A) hA (hs z)
          (Or.inr (rfl : (-1 : ℤ) = -1))
        simpa using hkey
    refine ⟨![v0, v1, v2, v3], c2slomqtc_injective_four hv01 hv02 hv03 hv12 hv13 hv23,
      ?_, ?_⟩
    · intro i
      fin_cases i
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := q) (e := 1) (e' := 1) hn hab hzq (Or.inl rfl) (Or.inl rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v0]⟩
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := q) (e := -1) (e' := 1) hn hab hzq (Or.inr rfl) (Or.inl rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v1]⟩
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := q) (e := 1) (e' := -1) hn hab hzq (Or.inl rfl) (Or.inr rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v2]⟩
      · obtain ⟨π', s', hsp, hprod, hact⟩ :=
          omq_exists_signed_perm_two_coord (n := n) (m := m) (a := a) (b := b) (a' := z)
            (b' := q) (e := -1) (e' := -1) hn hab hzq (Or.inr rfl) (Or.inr rfl) A B
        exact ⟨π', s', hsp, hprod, by rw [hact]; simp [v3]⟩
    · intro i l heq
      have hc := congrFun heq o
      have hxuo : omqSignedAct π s (![v0, v1, v2, v3] l) o =
          ((s z : ℤ) : ZMod m) * ![v0, v1, v2, v3] l z := by
        unfold omqSignedAct
        rw [hsymm]
      rw [huzero i, hxuo] at hc
      exact hne l hc.symm

end CFSG.LocalAnalysis.WeakClosure81
