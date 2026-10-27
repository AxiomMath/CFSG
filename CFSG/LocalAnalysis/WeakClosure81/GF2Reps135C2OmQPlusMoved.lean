module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusSigned

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private def c2slomqmv_sgn (i : Fin 7) : ℤ := if i.val % 2 = 0 then 1 else -1

private def c2slomqmv_sgn2 (i : Fin 7) : ℤ := if (i.val / 2) % 2 = 0 then 1 else -1

private def c2slomqmv_c1 (n : ℕ) (hn : 5 ≤ n) (i : Fin 7) : Fin n :=
  ⟨1 + i.val / 2, by
    have hi : i.val ≤ 6 := by omega
    have h : i.val / 2 ≤ 3 := by
      calc i.val / 2 ≤ 6 / 2 := Nat.div_le_div_right hi
        _ = 3 := by norm_num
    omega⟩

private def c2slomqmv_c2 (n : ℕ) (hn : 5 ≤ n) (i : Fin 7) : Fin n :=
  ⟨2 + i.val / 4, by
    have hi : i.val ≤ 6 := by omega
    have h : i.val / 4 ≤ 1 := by
      calc i.val / 4 ≤ 6 / 4 := Nat.div_le_div_right hi
        _ = 1 := by norm_num
    omega⟩

private lemma c2slomqmv_one_ne_neg_one {m : ℕ} (hm3 : 3 ≤ m) : (1 : ZMod m) ≠ -1 := by
  intro h
  rcases (ZMod.neg_one_eq_one_iff.mp h.symm) with h1 | h2 <;> omega

private lemma c2slomqmv_one_ne_zero {m : ℕ} (hm3 : 3 ≤ m) : (1 : ZMod m) ≠ 0 := by
  intro h
  exact absurd (ZMod.one_eq_zero_iff.mp h) (by omega)

private lemma c2slomqmv_neg_one_ne_zero {m : ℕ} (hm3 : 3 ≤ m) : (-1 : ZMod m) ≠ 0 :=
  neg_ne_zero.mpr (c2slomqmv_one_ne_zero hm3)

private lemma c2slomqmv_pm_cast_ne_zero {m : ℕ} (hm3 : 3 ≤ m) {z : ℤ}
    (hz : z = 1 ∨ z = -1) : (z : ZMod m) ≠ 0 := by
  rcases hz with h | h <;> rw [h]
  · simpa using c2slomqmv_one_ne_zero hm3
  · simpa using c2slomqmv_neg_one_ne_zero hm3

private lemma c2slomqmv_sgn_eq (i : Fin 7) :
    c2slomqmv_sgn i = 1 ∨ c2slomqmv_sgn i = -1 := by
  unfold c2slomqmv_sgn; split_ifs <;> simp

private lemma c2slomqmv_sgn2_eq (i : Fin 7) :
    c2slomqmv_sgn2 i = 1 ∨ c2slomqmv_sgn2 i = -1 := by
  unfold c2slomqmv_sgn2; split_ifs <;> simp

private lemma c2slomqmv_mul_pm {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;> norm_num

private lemma c2slomqmv_intCast_mul_self {m : ℕ} {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) :
    (δ : ZMod m) * (δ : ZMod m) = 1 := by
  rcases hδ with h | h <;> rw [h] <;> norm_num

private lemma c2slomqmv_cast_mul {m : ℕ} {σ δ : ℤ} (hδ : δ = 1 ∨ δ = -1) :
    ((σ * δ : ℤ) : ZMod m) * (δ : ZMod m) = (σ : ZMod m) := by
  rw [Int.cast_mul]
  calc (σ : ZMod m) * (δ : ZMod m) * (δ : ZMod m)
      = (σ : ZMod m) * ((δ : ZMod m) * (δ : ZMod m)) := by ring
    _ = (σ : ZMod m) * 1 := by rw [c2slomqmv_intCast_mul_self hδ]
    _ = (σ : ZMod m) := by ring

private lemma c2slomqmv_pm_mul_cast_ne_zero {m : ℕ} (hm3 : 3 ≤ m) {a b : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : (a : ZMod m) * (b : ZMod m) ≠ 0 := by
  rw [← Int.cast_mul]
  exact c2slomqmv_pm_cast_ne_zero hm3 (c2slomqmv_mul_pm ha hb)

private lemma c2slomqmv_pair1_inj :
    Function.Injective (fun i : Fin 7 => (i.val / 2, i.val % 2)) := by decide

private lemma c2slomqmv_pair2_inj :
    Function.Injective (fun i : Fin 7 => (i.val / 4, i.val % 2, (i.val / 2) % 2)) := by
  decide

private lemma c2slomqmv_mod2_eq_of_sgn {m : ℕ} (hm3 : 3 ≤ m) {a b : ℕ}
    (h : ((if a % 2 = 0 then (1 : ℤ) else -1 : ℤ) : ZMod m) =
      ((if b % 2 = 0 then (1 : ℤ) else -1 : ℤ) : ZMod m)) :
    a % 2 = b % 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · omega
  · exfalso
    exact c2slomqmv_one_ne_neg_one hm3 (by simpa [ha, hb] using h)
  · exfalso
    exact c2slomqmv_one_ne_neg_one hm3 (by simpa [ha, hb] using h.symm)
  · omega

private lemma c2slomqmv_c1_ne_zero (n : ℕ) (hn : 5 ≤ n) (i : Fin 7) :
    c2slomqmv_c1 n hn i ≠ (⟨0, by omega⟩ : Fin n) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [c2slomqmv_c1, Fin.val_mk] at hv
  omega

private lemma c2slomqmv_c2_ne_zero (n : ℕ) (hn : 5 ≤ n) (i : Fin 7) :
    c2slomqmv_c2 n hn i ≠ (⟨0, by omega⟩ : Fin n) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [c2slomqmv_c2, Fin.val_mk] at hv
  omega

private lemma c2slomqmv_c2_ne_one (n : ℕ) (hn : 5 ≤ n) (i : Fin 7) :
    c2slomqmv_c2 n hn i ≠ (⟨1, by omega⟩ : Fin n) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [c2slomqmv_c2, Fin.val_mk] at hv
  omega

theorem omq_exists_seven_orbit_roots {n : ℕ} (hn : 5 ≤ n) {m : ℕ} (hm3 : 3 ≤ m)
    {a b : Fin n} (hab : a ≠ b) {δ δ' : ℤ} (hδ : δ = 1 ∨ δ = -1) (hδ' : δ' = 1 ∨ δ' = -1)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hs : SpIsSign s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ u : Fin 7 → Fin n → ZMod m, Function.Injective u ∧
      (∀ i, ∃ (π' : Equiv.Perm (Fin n)) (s' : Fin n → ℤ), SpIsSign s' ∧ ∏ c, s' c = 1 ∧
        omqSignedAct π' s' (Pi.single a (δ : ZMod m) + Pi.single b (δ' : ZMod m)) = u i) ∧
      ∀ i l, u i ≠ omqSignedAct π s (u l) := by
  have hn3 : 3 ≤ n := by omega
  let z0 : Fin n := ⟨0, by omega⟩
  let z1 : Fin n := ⟨1, by omega⟩
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ01, hπ10, hs01⟩
  ·
    let c : Fin 7 → Fin n := c2slomqmv_c1 n hn
    let u : Fin 7 → Fin n → ZMod m := fun i =>
      Pi.single z0 (1 : ZMod m) + Pi.single (c i) ((c2slomqmv_sgn i : ℤ) : ZMod m)
    have hπ0' : π z0 = z0 := hπ0
    have hs0' : s z0 = -1 := hs0
    refine ⟨u, ?_, ?_, ?_⟩
    · intro i j h
      have hci : c i ≠ z0 := c2slomqmv_c1_ne_zero n hn i
      have h1 : (c2slomqmv_sgn i : ZMod m) =
          (if c i = c j then (c2slomqmv_sgn j : ZMod m) else 0) := by
        have hcongr := congrFun h (c i)
        simpa [u, Pi.single_apply, hci] using hcongr
      have hσi : (c2slomqmv_sgn i : ZMod m) ≠ 0 :=
        c2slomqmv_pm_cast_ne_zero hm3 (c2slomqmv_sgn_eq i)
      have hcd : c i = c j := by
        by_contra hne
        rw [if_neg hne] at h1
        exact hσi h1
      have hsgn : (c2slomqmv_sgn i : ZMod m) = (c2slomqmv_sgn j : ZMod m) := by
        rw [hcd, if_pos rfl] at h1
        exact h1
      have hdiv : i.val / 2 = j.val / 2 := by
        have hv := congrArg Fin.val hcd
        simp only [c, c2slomqmv_c1, Fin.val_mk] at hv
        omega
      have hmod : i.val % 2 = j.val % 2 :=
        c2slomqmv_mod2_eq_of_sgn hm3 (by simpa [c2slomqmv_sgn] using hsgn)
      exact c2slomqmv_pair1_inj (by simp only [hdiv, hmod])
    · intro i
      have hzi : z0 ≠ c i := (c2slomqmv_c1_ne_zero n hn i).symm
      obtain ⟨π', s', hs', hprod, hact⟩ :=
        omq_exists_signed_perm_two_coord (n := n) (m := m) (hn := hn3)
          (a := a) (b := b) (a' := z0) (b' := c i) hab hzi
          (e := δ) (he := hδ) (e' := c2slomqmv_sgn i * δ')
          (he' := c2slomqmv_mul_pm (c2slomqmv_sgn_eq i) hδ')
          (δ : ZMod m) (δ' : ZMod m)
      refine ⟨π', s', hs', hprod, ?_⟩
      rw [hact]
      have h1 : ((δ : ℤ) : ZMod m) * (δ : ZMod m) = 1 := by
        simpa using c2slomqmv_cast_mul (σ := (1 : ℤ)) hδ
      have h2 : ((c2slomqmv_sgn i * δ' : ℤ) : ZMod m) * (δ' : ZMod m) =
          (c2slomqmv_sgn i : ZMod m) :=
        c2slomqmv_cast_mul (σ := c2slomqmv_sgn i) hδ'
      rw [h1, h2]
    · intro i l h
      have hz : u i z0 = (1 : ZMod m) := by
        simp only [u, c, z0, Pi.add_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne' (c2slomqmv_c1_ne_zero n hn i), add_zero]
      have hz' : omqSignedAct π s (u l) z0 = (-1 : ZMod m) := by
        have hsymm : π.symm z0 = z0 := by
          conv_lhs => rw [← hπ0']
          rw [Equiv.symm_apply_apply]
        simp only [omqSignedAct, hsymm, hs0']
        have hul : u l z0 = (1 : ZMod m) := by
          simp only [u, c, z0, Pi.add_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne' (c2slomqmv_c1_ne_zero n hn l), add_zero]
        rw [hul]
        simp
      have hne : (1 : ZMod m) = -1 := hz.symm.trans ((congrFun h z0).trans hz')
      exact c2slomqmv_one_ne_neg_one hm3 hne
  ·
    let c : Fin 7 → Fin n := c2slomqmv_c2 n hn
    let u : Fin 7 → Fin n → ZMod m := fun i =>
      Pi.single z0 ((c2slomqmv_sgn i : ℤ) : ZMod m) +
        Pi.single (c i) ((c2slomqmv_sgn2 i : ℤ) : ZMod m)
    have hπ01' : π z0 = z1 := hπ01
    refine ⟨u, ?_, ?_, ?_⟩
    · intro i j h
      have hci : c i ≠ z0 := c2slomqmv_c2_ne_zero n hn i
      have h2 : (c2slomqmv_sgn2 i : ZMod m) =
          (if c i = c j then (c2slomqmv_sgn2 j : ZMod m) else 0) := by
        have hcongr := congrFun h (c i)
        simpa [u, Pi.single_apply, hci] using hcongr
      have hσ2 : (c2slomqmv_sgn2 i : ZMod m) ≠ 0 :=
        c2slomqmv_pm_cast_ne_zero hm3 (c2slomqmv_sgn2_eq i)
      have hcc : c i = c j := by
        by_contra hne
        rw [if_neg hne] at h2
        exact hσ2 h2
      have hsgn2 : (c2slomqmv_sgn2 i : ZMod m) = (c2slomqmv_sgn2 j : ZMod m) := by
        rw [hcc, if_pos rfl] at h2
        exact h2
      have h1 : (c2slomqmv_sgn i : ZMod m) = (c2slomqmv_sgn j : ZMod m) := by
        have hcongr := congrFun h z0
        simpa [u, c, z0, Pi.single_apply, hci.symm,
          (c2slomqmv_c2_ne_zero n hn j).symm] using hcongr
      have hdiv4 : i.val / 4 = j.val / 4 := by
        have hv := congrArg Fin.val hcc
        simp only [c, c2slomqmv_c2, Fin.val_mk] at hv
        omega
      have hmod : i.val % 2 = j.val % 2 :=
        c2slomqmv_mod2_eq_of_sgn hm3 (by simpa [c2slomqmv_sgn] using h1)
      have hdivmod : (i.val / 2) % 2 = (j.val / 2) % 2 :=
        c2slomqmv_mod2_eq_of_sgn hm3 (by simpa [c2slomqmv_sgn2] using hsgn2)
      exact c2slomqmv_pair2_inj (by simp only [hdiv4, hmod, hdivmod])
    · intro i
      have hzi : z0 ≠ c i := (c2slomqmv_c2_ne_zero n hn i).symm
      obtain ⟨π', s', hs', hprod, hact⟩ :=
        omq_exists_signed_perm_two_coord (n := n) (m := m) (hn := hn3)
          (a := a) (b := b) (a' := z0) (b' := c i) hab hzi
          (e := c2slomqmv_sgn i * δ) (he := c2slomqmv_mul_pm (c2slomqmv_sgn_eq i) hδ)
          (e' := c2slomqmv_sgn2 i * δ') (he' := c2slomqmv_mul_pm (c2slomqmv_sgn2_eq i) hδ')
          (δ : ZMod m) (δ' : ZMod m)
      refine ⟨π', s', hs', hprod, ?_⟩
      rw [hact]
      have h1 : ((c2slomqmv_sgn i * δ : ℤ) : ZMod m) * (δ : ZMod m) =
          (c2slomqmv_sgn i : ZMod m) :=
        c2slomqmv_cast_mul (σ := c2slomqmv_sgn i) hδ
      have h2 : ((c2slomqmv_sgn2 i * δ' : ℤ) : ZMod m) * (δ' : ZMod m) =
          (c2slomqmv_sgn2 i : ZMod m) :=
        c2slomqmv_cast_mul (σ := c2slomqmv_sgn2 i) hδ'
      rw [h1, h2]
    · intro i l h
      have hz : u i z1 = 0 := by
        simp only [u, c, z0, z1, Pi.add_apply,
          Pi.single_eq_of_ne' (show z0 ≠ z1 by simp [z0, z1]),
          Pi.single_eq_of_ne' (c2slomqmv_c2_ne_one n hn i), add_zero]
      have hz' : omqSignedAct π s (u l) z1 =
          (s z0 : ZMod m) * (c2slomqmv_sgn l : ZMod m) := by
        have hsymm : π.symm z1 = z0 := by
          conv_lhs => rw [← hπ01']
          rw [Equiv.symm_apply_apply]
        simp only [omqSignedAct, hsymm]
        have hul : u l z0 = (c2slomqmv_sgn l : ZMod m) := by
          simp only [u, c, z0, Pi.add_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne' (c2slomqmv_c2_ne_zero n hn l), add_zero]
        rw [hul]
      have hne : (0 : ZMod m) = (s z0 : ZMod m) * (c2slomqmv_sgn l : ZMod m) :=
        hz.symm.trans ((congrFun h z1).trans hz')
      exact c2slomqmv_pm_mul_cast_ne_zero hm3 (hs z0) (c2slomqmv_sgn_eq l) hne.symm

end CFSG.LocalAnalysis.WeakClosure81
