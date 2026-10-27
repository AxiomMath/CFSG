module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinCent
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinModule
import Mathlib.Data.Matrix.Basis

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

private theorem nor_zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : x.val ≤ 1 := by
    have := ZMod.val_lt x
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · left
    have := ZMod.natCast_zmod_val x
    rw [h0] at this
    simpa using this.symm
  · right
    have := ZMod.natCast_zmod_val x
    rw [h1] at this
    simpa using this.symm

private theorem nor_two_pow_N_sub_one_lt (r m N : ℕ) (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hN : 2 * r + m = N) : 2 ^ (N - 1) < 2 ^ (r * m + r * r) := by
  rw [Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)]
  have hmain : N ≤ r * m + r * r := by
    rw [← hN]
    have h1 : m ≤ r * m := Nat.le_mul_of_pos_left m (by omega)
    have h2 : 2 * r ≤ r * r := by
      have := Nat.mul_le_mul_left r hr
      simpa [Nat.mul_comm] using this
    omega
  have hNpos : 1 ≤ N := by omega
  omega

private theorem nor_zSub_le_of_prod_mem (r m : ℕ) (hm : 1 ≤ m)
    (D : Subgroup (GL (BlkIdx r m) (ZMod 2)))
    (hprod : ∀ (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2)),
      uGL 0 0 (a * b) ∈ D) :
    zSub r m ≤ D := by
  intro x hx
  obtain ⟨c, rfl⟩ := hx
  have key : ∀ c : Matrix (Fin r) (Fin r) (ZMod 2), uGL 0 0 c ∈ D := by
    intro c
    refine Matrix.induction_on' c ?_ ?_ ?_
    · rw [uGL_zero]
      exact D.one_mem
    · intro p q hp hq
      have hmem : uGL 0 0 p * uGL 0 0 q ∈ D := D.mul_mem hp hq
      simpa [uGL_mul] using hmem
    · intro i j xx
      rcases nor_zmod_two_eq_zero_or_one xx with h0 | h1
      · rw [h0, Matrix.single_zero, uGL_zero]
        exact D.one_mem
      · rw [h1]
        have hk : Matrix.single i (⟨0, by omega⟩ : Fin m) (1 : ZMod 2) *
            Matrix.single (⟨0, by omega⟩ : Fin m) j (1 : ZMod 2) =
            Matrix.single i j (1 : ZMod 2) := by
          simp
        rw [← hk]
        exact hprod _ _
  exact key c

private theorem nor_contra_of_Ma (r m N : ℕ) (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hN : 2 * r + m = N)
    (D : Subgroup (GL (BlkIdx r m) (ZMod 2)))
    (hDn : ∀ g ∈ Cent r m, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hE : ∀ E : Subgroup (GL (BlkIdx r m) (ZMod 2)), E ≤ D → (∀ x ∈ E, x * x = 1) →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ 2 ^ (N - 1))
    (hMa : ∀ a : Matrix (Fin r) (Fin m) (ZMod 2), ∃ c : Matrix (Fin r) (Fin r) (ZMod 2),
      uGL a 0 c ∈ D) : False := by
  have hzD : zSub r m ≤ D := by
    refine nor_zSub_le_of_prod_mem r m hm D ?_
    intro a b
    obtain ⟨c, hc⟩ := hMa a
    have hb : uGL (0 : Matrix (Fin r) (Fin m) (ZMod 2)) b
        (0 : Matrix (Fin r) (Fin r) (ZMod 2)) ∈ Cent r m :=
      uSub_le_cent r m ⟨0, b, 0, rfl⟩
    have hconj : uGL 0 b 0 * uGL a 0 c * (uGL 0 b 0)⁻¹ ∈ D := hDn _ hb _ hc
    have hmem : uGL 0 b 0 * uGL a 0 c * (uGL 0 b 0)⁻¹ * (uGL a 0 c)⁻¹ ∈ D :=
      D.mul_mem hconj (D.inv_mem hc)
    have hcomm := uGL_commutator (r := r) (m := m)
      (0 : Matrix (Fin r) (Fin m) (ZMod 2)) a b
      (0 : Matrix (Fin m) (Fin r) (ZMod 2)) (0 : Matrix (Fin r) (Fin r) (ZMod 2)) c
    rw [hcomm] at hmem
    simpa using hmem
  let E : Subgroup (GL (BlkIdx r m) (ZMod 2)) :=
    { carrier := {x | ∃ (a : Matrix (Fin r) (Fin m) (ZMod 2))
          (c : Matrix (Fin r) (Fin r) (ZMod 2)), x = uGL a 0 c}
      one_mem' := ⟨0, 0, uGL_zero.symm⟩
      mul_mem' := by
        rintro x y ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
        exact ⟨a + a', c + c', by rw [uGL_mul]; simp⟩
      inv_mem' := by
        rintro x ⟨a, c, rfl⟩
        exact ⟨-a, -c, by rw [uGL_inv]; simp⟩ }
  have hED : E ≤ D := by
    rintro x ⟨a, c, rfl⟩
    obtain ⟨ca, hca⟩ := hMa a
    have hz : uGL 0 0 (c + ca) ∈ D := hzD ⟨c + ca, rfl⟩
    have hmul : uGL a 0 ca * uGL 0 0 (c + ca) = uGL a 0 c := by
      rw [uGL_mul]
      have h2 : ca + ca = 0 := by
        ext i j
        simpa using CharTwo.add_self_eq_zero (ca i j)
      have hcc : ca + (c + ca) = c := by
        rw [add_comm c ca, ← add_assoc, h2, zero_add]
      simp [hcc]
    rw [← hmul]
    exact D.mul_mem hca hz
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro x ⟨a, c, rfl⟩
    rw [uGL_mul]
    have haa : a + a = 0 := by ext i j; simpa using CharTwo.add_self_eq_zero (a i j)
    have hcc : c + c = 0 := by ext i j; simpa using CharTwo.add_self_eq_zero (c i j)
    rw [haa, hcc]
    simpa using uGL_zero
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro x ⟨a, c, rfl⟩ y ⟨a', c', rfl⟩
    rw [uGL_mul, uGL_mul]
    simp only [Matrix.mul_zero, add_zero]
    rw [add_comm a a', add_comm c c']
  have hcardE : Nat.card E = 2 ^ (r * m + r * r) := by
    let f : (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin r) (Fin r) (ZMod 2)) → E :=
      fun p => ⟨uGL p.1 0 p.2, p.1, p.2, rfl⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨a, c⟩ ⟨a', c'⟩ h
        have h' : (uGL a 0 c : GL (BlkIdx r m) (ZMod 2)) = uGL a' 0 c' := by
          have := congrArg Subtype.val h
          simpa [f] using this
        obtain ⟨ha, _, hc⟩ := uGL_injective h'
        simp [ha, hc]
      · rintro ⟨x, hx⟩
        obtain ⟨a, c, rfl⟩ := hx
        exact ⟨(a, c), rfl⟩
    have hcard1 : Nat.card E =
        Nat.card (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin r) (Fin r) (ZMod 2)) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    simp only [hcard1, Nat.card_prod, Matrix.card_matrix, Nat.card_fin, Nat.card_zmod,
      ← pow_add]
    rw [Nat.mul_comm m r]
  have hle := hE E hED hEsq hEcomm
  rw [hcardE] at hle
  exact absurd hle (not_le.mpr (nor_two_pow_N_sub_one_lt r m N hr hm hN))

private theorem nor_contra_of_Mb (r m N : ℕ) (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hN : 2 * r + m = N)
    (D : Subgroup (GL (BlkIdx r m) (ZMod 2)))
    (hDn : ∀ g ∈ Cent r m, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hE : ∀ E : Subgroup (GL (BlkIdx r m) (ZMod 2)), E ≤ D → (∀ x ∈ E, x * x = 1) →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ 2 ^ (N - 1))
    (hMb : ∀ b : Matrix (Fin m) (Fin r) (ZMod 2), ∃ c : Matrix (Fin r) (Fin r) (ZMod 2),
      uGL 0 b c ∈ D) : False := by
  have hzD : zSub r m ≤ D := by
    refine nor_zSub_le_of_prod_mem r m hm D ?_
    intro a b
    obtain ⟨c, hc⟩ := hMb b
    have ha : uGL a (0 : Matrix (Fin m) (Fin r) (ZMod 2))
        (0 : Matrix (Fin r) (Fin r) (ZMod 2)) ∈ Cent r m :=
      uSub_le_cent r m ⟨a, 0, 0, rfl⟩
    have hconj : uGL a 0 0 * uGL 0 b c * (uGL a 0 0)⁻¹ ∈ D := hDn _ ha _ hc
    have hmem : uGL a 0 0 * uGL 0 b c * (uGL a 0 0)⁻¹ * (uGL 0 b c)⁻¹ ∈ D :=
      D.mul_mem hconj (D.inv_mem hc)
    have hcomm := uGL_commutator (r := r) (m := m) a
      (0 : Matrix (Fin r) (Fin m) (ZMod 2))
      (0 : Matrix (Fin m) (Fin r) (ZMod 2)) b (0 : Matrix (Fin r) (Fin r) (ZMod 2)) c
    rw [hcomm] at hmem
    simpa using hmem
  let E : Subgroup (GL (BlkIdx r m) (ZMod 2)) :=
    { carrier := {x | ∃ (b : Matrix (Fin m) (Fin r) (ZMod 2))
          (c : Matrix (Fin r) (Fin r) (ZMod 2)), x = uGL 0 b c}
      one_mem' := ⟨0, 0, uGL_zero.symm⟩
      mul_mem' := by
        rintro x y ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
        exact ⟨b + b', c + c', by rw [uGL_mul]; simp⟩
      inv_mem' := by
        rintro x ⟨b, c, rfl⟩
        exact ⟨-b, -c, by rw [uGL_inv]; simp⟩ }
  have hED : E ≤ D := by
    rintro x ⟨b, c, rfl⟩
    obtain ⟨cb, hcb⟩ := hMb b
    have hz : uGL 0 0 (c + cb) ∈ D := hzD ⟨c + cb, rfl⟩
    have hmul : uGL 0 b cb * uGL 0 0 (c + cb) = uGL 0 b c := by
      rw [uGL_mul]
      have h2 : cb + cb = 0 := by
        ext i j
        simpa using CharTwo.add_self_eq_zero (cb i j)
      have hcc : cb + (c + cb) = c := by
        rw [add_comm c cb, ← add_assoc, h2, zero_add]
      simp [hcc]
    rw [← hmul]
    exact D.mul_mem hcb hz
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro x ⟨b, c, rfl⟩
    rw [uGL_mul]
    have hbb : b + b = 0 := by ext i j; simpa using CharTwo.add_self_eq_zero (b i j)
    have hcc : c + c = 0 := by ext i j; simpa using CharTwo.add_self_eq_zero (c i j)
    rw [hbb, hcc]
    simpa using uGL_zero
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro x ⟨b, c, rfl⟩ y ⟨b', c', rfl⟩
    rw [uGL_mul, uGL_mul]
    simp only [Matrix.zero_mul, add_zero]
    rw [add_comm b b', add_comm c c']
  have hcardE : Nat.card E = 2 ^ (r * m + r * r) := by
    let f : (Matrix (Fin m) (Fin r) (ZMod 2) × Matrix (Fin r) (Fin r) (ZMod 2)) → E :=
      fun p => ⟨uGL 0 p.1 p.2, p.1, p.2, rfl⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨b, c⟩ ⟨b', c'⟩ h
        have h' : (uGL 0 b c : GL (BlkIdx r m) (ZMod 2)) = uGL 0 b' c' := by
          have := congrArg Subtype.val h
          simpa [f] using this
        obtain ⟨_, hb, hc⟩ := uGL_injective h'
        simp [hb, hc]
      · rintro ⟨x, hx⟩
        obtain ⟨b, c, rfl⟩ := hx
        exact ⟨(b, c), rfl⟩
    have hcard1 : Nat.card E =
        Nat.card (Matrix (Fin m) (Fin r) (ZMod 2) × Matrix (Fin r) (Fin r) (ZMod 2)) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    simp only [hcard1, Nat.card_prod, Matrix.card_matrix, Nat.card_fin, Nat.card_zmod,
      ← pow_add]
  have hle := hE E hED hEsq hEcomm
  rw [hcardE] at hle
  exact absurd hle (not_le.mpr (nor_two_pow_N_sub_one_lt r m N hr hm hN))

theorem le_zSub_of_normal_of_le_uSub (r m N : ℕ) (hr : 2 ≤ r) (hm : 1 ≤ m)
    (h3 : 3 ≤ r ∨ 3 ≤ m) (hN : 2 * r + m = N)
    (D : Subgroup (GL (BlkIdx r m) (ZMod 2))) (hDU : D ≤ uSub r m)
    (hDn : ∀ g ∈ Cent r m, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hE : ∀ E : Subgroup (GL (BlkIdx r m) (ZMod 2)), E ≤ D → (∀ x ∈ E, x * x = 1) →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ 2 ^ (N - 1)) :
    D ≤ zSub r m := by
  let W : AddSubgroup
      (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)) :=
    { carrier := {w | ∃ c : Matrix (Fin r) (Fin r) (ZMod 2), uGL w.1 w.2 c ∈ D}
      zero_mem' := ⟨0, by
        change uGL (0 : Matrix (Fin r) (Fin m) (ZMod 2))
          (0 : Matrix (Fin m) (Fin r) (ZMod 2)) (0 : Matrix (Fin r) (Fin r) (ZMod 2)) ∈ D
        rw [uGL_zero]
        exact D.one_mem⟩
      add_mem' := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, hc⟩ ⟨c', hc'⟩
        refine ⟨c + c' + a * b', ?_⟩
        change uGL (a + a') (b + b') (c + c' + a * b') ∈ D
        rw [← uGL_mul]
        exact D.mul_mem hc hc'
      neg_mem' := by
        rintro ⟨a, b⟩ ⟨c, hc⟩
        refine ⟨a * b - c, ?_⟩
        change uGL (-a) (-b) (a * b - c) ∈ D
        rw [← uGL_inv]
        exact D.inv_mem hc }
  have hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W := by
    rintro P R ⟨a, b⟩ ⟨c, hc⟩
    refine ⟨(P : Matrix (Fin r) (Fin r) (ZMod 2)) * c *
        ((P⁻¹ : GL (Fin r) (ZMod 2)) : Matrix (Fin r) (Fin r) (ZMod 2)), ?_⟩
    have hmem := hDn (levi P R) (levi_mem_cent r m P R) (uGL a b c) hc
    rw [levi_conj_uGL r m P R a b c] at hmem
    simpa only [actA, actB] using hmem
  rcases eq_bot_or_actA_or_actB r m h3 W hW with hbot | hMa | hMb
  · intro d hd
    obtain ⟨a, b, c, rfl⟩ := hDU hd
    have hab : (a, b) ∈ W := ⟨c, hd⟩
    rw [hbot] at hab
    have hab0 : (a, b) = 0 := AddSubgroup.mem_bot.mp hab
    have ha : a = 0 := congrArg Prod.fst hab0
    have hb : b = 0 := congrArg Prod.snd hab0
    exact ⟨c, by rw [ha, hb]⟩
  · exact (nor_contra_of_Ma r m N hr hm hN D hDn hE hMa).elim
  · exact (nor_contra_of_Mb r m N hr hm hN D hDn hE hMb).elim

end CFSG.StandardType.FF81.RootFusionLin

end
