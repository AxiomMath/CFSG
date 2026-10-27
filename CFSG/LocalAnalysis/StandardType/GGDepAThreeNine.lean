module

public import CFSG.LocalAnalysis.StandardType.GGDepAOdd
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepThreeChain
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
import CFSG.LocalAnalysis.StandardType.GGCartanATypeArith
import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenCoreA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggA8Tail (a : Fin 8 → ZMod 3) (i : Fin 9) : ZMod 3 :=
  ∑ l : Fin 8, if (i : ℕ) ≤ (l : ℕ) then a l else 0

theorem ggA8Tail_last (a : Fin 8 → ZMod 3) : ggA8Tail a 8 = 0 := by
  simp only [ggA8Tail]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp

theorem ggA8Tail_sub_succ (a : Fin 8 → ZMod 3) (l : Fin 8) :
    ggA8Tail a l.castSucc - ggA8Tail a l.succ = a l := by
  simp only [ggA8Tail, Fin.val_castSucc, Fin.val_succ]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single l]
  · rw [if_pos le_rfl, if_neg (Nat.not_succ_le_self (l : ℕ))]
    exact sub_zero (a l)
  · intro k _ hk
    have hne : (l : ℕ) ≠ (k : ℕ) := fun h => hk (Fin.ext h.symm)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · rw [if_pos hlt.le, if_pos (by omega : (l : ℕ) + 1 ≤ (k : ℕ)), sub_self]
    · rw [if_neg (by omega : ¬ (l : ℕ) ≤ (k : ℕ)),
        if_neg (by omega : ¬ (l : ℕ) + 1 ≤ (k : ℕ)), sub_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem ggA8Tail_quad (m : Fin 8 → ZMod 3) :
    (∑ s : Fin 8, m s * ∑ t : Fin 8, (CartanMatrix.A 8 s t : ZMod 3) * m t) =
      ∑ i : Fin 9,
        ggA8Tail (fun l => ∑ t : Fin 8, (CartanMatrix.A 8 l t : ZMod 3) * m t) i ^ 2 := by
  set aFun : Fin 8 → ZMod 3 :=
    fun l => ∑ t : Fin 8, (CartanMatrix.A 8 l t : ZMod 3) * m t with haFun
  have ha0 : aFun 0 = 2 * m 0 - m 1 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha1 : aFun 1 = -m 0 + 2 * m 1 - m 2 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha2 : aFun 2 = -m 1 + 2 * m 2 - m 3 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha3 : aFun 3 = -m 2 + 2 * m 3 - m 4 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha4 : aFun 4 = -m 3 + 2 * m 4 - m 5 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha5 : aFun 5 = -m 4 + 2 * m 5 - m 6 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha6 : aFun 6 = -m 5 + 2 * m 6 - m 7 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha7 : aFun 7 = -m 6 + 2 * m 7 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
  change (∑ s : Fin 8, m s * aFun s) = ∑ i : Fin 9, ggA8Tail aFun i ^ 2
  conv_lhs => rw [Fin.sum_univ_eight]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [ggA8Tail, Fin.sum_univ_eight, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]
  simp
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination (-3 * m 7 ^ 2) * h3

theorem ggA8Tail_sum_cartan (m : Fin 8 → ZMod 3) :
    ∑ i : Fin 9, ggA8Tail (fun l => ∑ t : Fin 8, (CartanMatrix.A 8 l t : ZMod 3) * m t) i = 0 := by
  set aFun : Fin 8 → ZMod 3 :=
    fun l => ∑ t : Fin 8, (CartanMatrix.A 8 l t : ZMod 3) * m t with haFun
  have ha0 : aFun 0 = 2 * m 0 - m 1 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha1 : aFun 1 = -m 0 + 2 * m 1 - m 2 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha2 : aFun 2 = -m 1 + 2 * m 2 - m 3 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha3 : aFun 3 = -m 2 + 2 * m 3 - m 4 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha4 : aFun 4 = -m 3 + 2 * m 4 - m 5 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha5 : aFun 5 = -m 4 + 2 * m 5 - m 6 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha6 : aFun 6 = -m 5 + 2 * m 6 - m 7 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
    ring
  have ha7 : aFun 7 = -m 6 + 2 * m 7 := by
    simp only [haFun]
    simp [Fin.sum_univ_eight, CartanMatrix.A, Matrix.of_apply]
  change ∑ i : Fin 9, ggA8Tail aFun i = 0
  conv_lhs => rw [Fin.sum_univ_castSucc]
  simp only [ggA8Tail, Fin.sum_univ_eight, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]
  simp
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination (3 * m 7) * h3

private lemma sum_zmod3 {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) :
    ∑ c : ZMod 3, f c = f 0 + f 1 + f 2 := by
  have h : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [h]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [add_assoc]

private lemma zmod3_sum_mul (f : ZMod 3 → ZMod 3) :
    ∑ c : ZMod 3, f c * c = f 1 + 2 * f 2 := by
  rw [sum_zmod3 (fun c => f c * c)]
  simp [mul_comm]

private lemma zmod3_sum_sq (f : ZMod 3 → ZMod 3) :
    ∑ c : ZMod 3, f c * c ^ 2 = f 1 + f 2 := by
  rw [sum_zmod3 (fun c => f c * c ^ 2)]
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  simp [h2]

private lemma zmod3_cases {P : ZMod 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ c, P c := by
  intro c
  have h : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide
  rcases h with rfl | rfl | rfl <;> assumption

private lemma fiber_card_sub (g : Fin 9 → ZMod 3) (a c : ZMod 3) :
    (Finset.univ.filter (fun i : Fin 9 => a - g i = c)).card =
      (Finset.univ.filter (fun i : Fin 9 => g i = a - c)).card := by
  have h : Finset.univ.filter (fun i : Fin 9 => a - g i = c) =
      Finset.univ.filter (fun i : Fin 9 => g i = a - c) := by
    apply Finset.filter_congr
    intro i _
    rw [sub_eq_iff_eq_add, eq_sub_iff_add_eq]
    exact ⟨fun h => by simpa [add_comm] using h.symm, fun h => by simpa [add_comm] using h.symm⟩
  rw [h]

private lemma zmod3_fiber_cases :
    ∀ n0 n1 n2 : Fin 10, n0.val + n1.val + n2.val = 9 →
      n0.val % 3 = n1.val % 3 → n1.val % 3 = n2.val % 3 →
      n1.val % 3 ≠ 0 → n0 = n1 ∨ n0 = n2 ∨ n1 = n2 := by
  decide

private lemma exists_perm_of_fiber (g : Fin 9 → ZMod 3) (a : ZMod 3)
    (hfix : ∀ c : ZMod 3,
      (Finset.univ.filter (fun i : Fin 9 => g i = a - c)).card =
        (Finset.univ.filter (fun i : Fin 9 => g i = c)).card) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, g (σ i) = a - g i := by
  let e : ∀ c : ZMod 3, {i : Fin 9 // a - g i = c} ≃ {j : Fin 9 // g j = c} :=
    fun c => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      rw [fiber_card_sub g a c]
      exact hfix c)
  exact ⟨Equiv.ofFiberEquiv e, fun i => Equiv.ofFiberEquiv_map e i⟩

theorem ggA8_fiber_involution (g : Fin 9 → ZMod 3) (hsum : ∑ i, g i = 0)
    (hsq : ∑ i, g i ^ 2 ≠ 0) : ∃ (σ : Equiv.Perm (Fin 9)) (a : ZMod 3), ∀ i, g (σ i) = a - g i := by
  classical
  let n : ZMod 3 → ℕ := fun c => (Finset.univ.filter (fun i : Fin 9 => g i = c)).card
  have hpart : n 0 + n 1 + n 2 = 9 := by
    have h := Finset.sum_fiberwise (s := (Finset.univ : Finset (Fin 9))) (g := g)
      (f := fun _ : Fin 9 => (1 : ℕ))
    have h' : ∑ c : ZMod 3, n c = ∑ i : Fin 9, (1 : ℕ) := by
      simpa [n, Finset.sum_const, nsmul_eq_mul, mul_one] using h
    rw [sum_zmod3] at h'
    simpa using h'
  have hlin : (n 1 : ZMod 3) + 2 * (n 2 : ZMod 3) = 0 := by
    have hid : ∑ c : ZMod 3, (n c : ZMod 3) * c = ∑ i : Fin 9, g i := by
      have h := Finset.sum_fiberwise' (s := (Finset.univ : Finset (Fin 9))) (g := g)
        (f := fun c : ZMod 3 => c)
      simpa [n, Finset.sum_const, nsmul_eq_mul] using h
    rw [zmod3_sum_mul (fun c => (n c : ZMod 3))] at hid
    rw [hsum] at hid
    exact hid
  have hsq2 : (n 1 : ZMod 3) + (n 2 : ZMod 3) ≠ 0 := by
    have hid : ∑ c : ZMod 3, (n c : ZMod 3) * c ^ 2 = ∑ i : Fin 9, g i ^ 2 := by
      have h := Finset.sum_fiberwise' (s := (Finset.univ : Finset (Fin 9))) (g := g)
        (f := fun c : ZMod 3 => c ^ 2)
      simpa [n, Finset.sum_const, nsmul_eq_mul] using h
    rw [zmod3_sum_sq (fun c => (n c : ZMod 3))] at hid
    rw [hid]
    exact hsq
  have h12 : (n 1 : ZMod 3) = (n 2 : ZMod 3) := by
    have h3 : (3 : ZMod 3) = 0 := by decide
    calc (n 1 : ZMod 3) = (n 1 : ZMod 3) + 3 * (n 2 : ZMod 3) := by
          rw [h3, zero_mul, add_zero]
      _ = (n 1 : ZMod 3) + 2 * (n 2 : ZMod 3) + (n 2 : ZMod 3) := by ring
      _ = 0 + (n 2 : ZMod 3) := by rw [hlin]
      _ = (n 2 : ZMod 3) := zero_add _
  have h01 : (n 0 : ZMod 3) = (n 1 : ZMod 3) := by
    have hpartcast : (n 0 : ZMod 3) + (n 1 : ZMod 3) + (n 2 : ZMod 3) = 0 := by
      have h := congrArg (fun m : ℕ => (m : ZMod 3)) hpart
      push_cast at h
      have h9 : (9 : ZMod 3) = 0 := by decide
      simpa [h9] using h
    have h := hpartcast
    rw [← h12] at h
    have h3 : (3 : ZMod 3) = 0 := by decide
    calc (n 0 : ZMod 3) = (n 0 : ZMod 3) + 3 * (n 1 : ZMod 3) := by
          rw [h3, zero_mul, add_zero]
      _ = (n 0 : ZMod 3) + (n 1 : ZMod 3) + (n 1 : ZMod 3) + (n 1 : ZMod 3) := by ring
      _ = 0 + (n 1 : ZMod 3) := by rw [h]
      _ = (n 1 : ZMod 3) := zero_add _
  have hn1ne : (n 1 : ZMod 3) ≠ 0 := by
    intro h
    apply hsq2
    rw [h]
    have h2 : (n 2 : ZMod 3) = 0 := h12 ▸ h
    rw [h2, zero_add]
  have hmod01 : n 0 % 3 = n 1 % 3 :=
    (ZMod.natCast_eq_natCast_iff' (n 0) (n 1) 3).mp h01
  have hmod12 : n 1 % 3 = n 2 % 3 :=
    (ZMod.natCast_eq_natCast_iff' (n 1) (n 2) 3).mp h12
  have hmod1ne : n 1 % 3 ≠ 0 := by
    rw [← ZMod.val_natCast 3 (n 1)]
    intro h0
    exact hn1ne ((ZMod.val_eq_zero ((n 1 : ZMod 3))).mp h0)
  have hcases : n 0 = n 1 ∨ n 0 = n 2 ∨ n 1 = n 2 := by
    let m0 : Fin 10 := ⟨n 0, by omega⟩
    let m1 : Fin 10 := ⟨n 1, by omega⟩
    let m2 : Fin 10 := ⟨n 2, by omega⟩
    have hf := zmod3_fiber_cases m0 m1 m2 (by simpa [m0, m1, m2] using hpart)
      (by simpa [m0, m1] using hmod01) (by simpa [m1, m2] using hmod12)
      (by simpa [m1] using hmod1ne)
    rcases hf with h | h | h
    · left
      have := congrArg Fin.val h
      simpa [m0, m1] using this
    · right; left
      have := congrArg Fin.val h
      simpa [m0, m2] using this
    · right; right
      have := congrArg Fin.val h
      simpa [m1, m2] using this
  rcases hcases with h01n | h02n | h12n
  · have hfix : ∀ c : ZMod 3, n (1 - c) = n c := by
      refine zmod3_cases ?_ ?_ ?_
      · simpa using h01n.symm
      · simpa using h01n
      · have h2 : (1 : ZMod 3) - 2 = 2 := by decide
        rw [h2]
    have hfix' : ∀ c : ZMod 3,
        (Finset.univ.filter (fun i : Fin 9 => g i = 1 - c)).card =
          (Finset.univ.filter (fun i : Fin 9 => g i = c)).card := by
      intro c
      simpa [n] using hfix c
    obtain ⟨σ, hσ⟩ := exists_perm_of_fiber g 1 hfix'
    exact ⟨σ, 1, hσ⟩
  · have hfix : ∀ c : ZMod 3, n (2 - c) = n c := by
      refine zmod3_cases ?_ ?_ ?_
      · have h2 : (2 : ZMod 3) - 0 = 2 := by decide
        rw [h2]
        exact h02n.symm
      · have h2 : (2 : ZMod 3) - 1 = 1 := by decide
        rw [h2]
      · have h2 : (2 : ZMod 3) - 2 = 0 := by decide
        rw [h2]
        exact h02n
    have hfix' : ∀ c : ZMod 3,
        (Finset.univ.filter (fun i : Fin 9 => g i = 2 - c)).card =
          (Finset.univ.filter (fun i : Fin 9 => g i = c)).card := by
      intro c
      simpa [n] using hfix c
    obtain ⟨σ, hσ⟩ := exists_perm_of_fiber g 2 hfix'
    exact ⟨σ, 2, hσ⟩
  · have hfix : ∀ c : ZMod 3, n (0 - c) = n c := by
      refine zmod3_cases ?_ ?_ ?_
      · have h0 : (0 : ZMod 3) - 0 = 0 := by decide
        rw [h0]
      · have h0 : (0 : ZMod 3) - 1 = 2 := by decide
        rw [h0]
        exact h12n.symm
      · have h0 : (0 : ZMod 3) - 2 = 1 := by decide
        rw [h0]
        exact h12n
    have hfix' : ∀ c : ZMod 3,
        (Finset.univ.filter (fun i : Fin 9 => g i = 0 - c)).card =
          (Finset.univ.filter (fun i : Fin 9 => g i = c)).card := by
      intro c
      simpa [n] using hfix c
    obtain ⟨σ, hσ⟩ := exists_perm_of_fiber g 0 hfix'
    exact ⟨σ, 0, hσ⟩

private lemma ggA8Tail_cartan_sum (k : Fin 8) (i : Fin 9) :
    (∑ l : Fin 8, if (i : ℕ) ≤ (l : ℕ) then (CartanMatrix.A 8 l k : ZMod 3) else 0) =
      (if i = k.castSucc then 1 else 0) - (if i = k.succ then 1 else 0) +
        (if k = 7 then 1 else 0) := by
  fin_cases k <;> fin_cases i <;> decide

theorem ggA8Tail_refl {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {h : Fin 8 → V}
    {α : Fin 8 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 8 i j : ZMod 3)) (k : Fin 8) (w : V)
    (i : Fin 9) :
    ggA8Tail (fun l => α l (w - α k w • h k)) i =
      ggA8Tail (fun l => α l w) (Equiv.swap k.castSucc k.succ i) -
        (if k = 7 then α k w else 0) := by
  have hfun : (fun l => α l (w - α k w • h k)) =
      fun l => α l w - α k w * (CartanMatrix.A 8 l k : ZMod 3) := by
    funext l
    rw [map_sub, map_smul, hpair, smul_eq_mul]
  have hsplit : ggA8Tail (fun l => α l (w - α k w • h k)) i =
      ggA8Tail (fun l => α l w) i -
        α k w * ∑ l : Fin 8, if (i : ℕ) ≤ (l : ℕ) then
          (CartanMatrix.A 8 l k : ZMod 3) else 0 := by
    rw [hfun]
    simp only [ggA8Tail]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro l _
    split_ifs <;> ring
  have hcs : k.castSucc ≠ k.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hlast : (if k = 7 then α k w else 0) =
      α k w * (if k = 7 then 1 else 0) := by
    split_ifs <;> ring
  rw [hsplit, ggA8Tail_cartan_sum, hlast]
  have hsub : ggA8Tail (fun l => α l w) k.castSucc =
      α k w + ggA8Tail (fun l => α l w) k.succ := by
    have := ggA8Tail_sub_succ (fun l => α l w) k
    rwa [sub_eq_iff_eq_add] at this
  by_cases h1 : i = k.castSucc
  · rw [h1, Equiv.swap_apply_left]
    simp only [hcs, if_true, if_false]
    rw [hsub]
    ring
  · by_cases h2 : i = k.succ
    · rw [h2, Equiv.swap_apply_right]
      have hsc : k.succ ≠ k.castSucc := hcs.symm
      simp only [hsc, if_true, if_false]
      rw [hsub]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [h1, h2, if_false]
      ring

theorem ggA8Tail_perm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {h : Fin 8 → V}
    {α : Fin 8 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 8 i j : ZMod 3))
    (ρ : Equiv.Perm (Fin 9) →* (V ≃ₗ[ZMod 3] V))
    (hρ : ∀ (k : Fin 8) (w : V), ρ (Equiv.swap k.castSucc k.succ) w = w - α k w • h k)
    (σ : Equiv.Perm (Fin 9)) (w : V) :
    ∃ c : ZMod 3, ∀ i, ggA8Tail (fun l => α l (ρ σ w)) i =
      ggA8Tail (fun l => α l w) (σ⁻¹ i) + c := by
  have hgen : σ ∈ Submonoid.closure (Set.range fun i : Fin 8 =>
      Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top σ
  have hmain : ∀ w : V, ∃ c : ZMod 3, ∀ i,
      ggA8Tail (fun l => α l (ρ σ w)) i =
        ggA8Tail (fun l => α l w) (σ⁻¹ i) + c := by
    refine Submonoid.closure_induction
      (motive := fun τ _ => ∀ w : V, ∃ c : ZMod 3, ∀ i,
        ggA8Tail (fun l => α l (ρ τ w)) i =
          ggA8Tail (fun l => α l w) (τ⁻¹ i) + c) ?_ ?_ ?_ hgen
    · rintro x ⟨k, rfl⟩ w
      refine ⟨-(if k = 7 then α k w else 0), ?_⟩
      intro i
      have h := ggA8Tail_refl hpair k w i
      rw [hρ k w, Equiv.swap_inv]
      simpa [sub_eq_add_neg] using h
    · intro w
      refine ⟨0, ?_⟩
      intro i
      simp
    · intro a b _ _ hPa hPb w
      obtain ⟨c₂, h₂⟩ := hPb w
      obtain ⟨c₁, h₁⟩ := hPa (ρ b w)
      refine ⟨c₁ + c₂, ?_⟩
      intro i
      rw [map_mul, LinearEquiv.mul_apply, h₁ i, h₂ (a⁻¹ i), mul_inv_rev,
        Equiv.Perm.mul_apply]
      ring
  exact hmain w

theorem ggDepA9_exists_neg {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V} {x : V}
    (F : GGDepAFrame 3 9 h α x)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    {ha : V} (hH : ha ∈ Submodule.span (ZMod 3) (Set.range h))
    (hsq : ∑ i : Fin 9, ggA8Tail (fun l => α l ha) i ^ 2 ≠ 0) :
    ∃ u ∈ Subgroup.closure (Set.range r), u ha = -ha ∧ u x = x := by
  classical
  have hpair : ∀ i j : Fin 8, α i (h j) = (CartanMatrix.A 8 i j : ZMod 3) := F.pair
  obtain ⟨ρ, hρ, hρA, hρx, -⟩ :=
    ggDepAOdd_perm_embed (p := 3) (N := 9) (by norm_num) (by norm_num) F r hr
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hH
  have hαha : (fun l => α l ha) =
      fun l => ∑ t : Fin 8, (CartanMatrix.A 8 l t : ZMod 3) * m t := by
    funext l
    rw [← hm, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, hpair, smul_eq_mul, mul_comm]
  have hsum : ∑ i, ggA8Tail (fun l => α l ha) i = 0 := by
    rw [hαha]
    exact ggA8Tail_sum_cartan m
  obtain ⟨σ, a, hσ⟩ := ggA8_fiber_involution _ hsum hsq
  have hρ' : ∀ (k : Fin 8) (w : V), ρ (Equiv.swap k.castSucc k.succ) w = w - α k w • h k := by
    intro k w
    have hsw : (Equiv.swap k.castSucc k.succ : Equiv.Perm (Fin 9)) =
        Equiv.swap (ggDepALeft 9 k) (ggDepARight 9 k) := rfl
    rw [hsw, hρ k, hr]
  obtain ⟨c, hc⟩ := ggA8Tail_perm hpair ρ hρ' σ⁻¹ ha
  have hc' : ∀ i, ggA8Tail (fun l => α l (ρ σ⁻¹ ha)) i =
      a - ggA8Tail (fun l => α l ha) i + c := by
    intro i
    rw [hc i, inv_inv, hσ i]
  have hac : a + c = 0 := by
    have h8 := hc' 8
    rw [ggA8Tail_last, ggA8Tail_last] at h8
    linear_combination -h8
  have hneg : ∀ l : Fin 8, α l (ρ σ⁻¹ ha + ha) = 0 := by
    intro l
    have h1 := ggA8Tail_sub_succ (fun l => α l (ρ σ⁻¹ ha)) l
    have h2 := ggA8Tail_sub_succ (fun l => α l ha) l
    simp only [hc'] at h1
    rw [map_add, ← h1, ← h2]
    ring
  have hfixv := F.fix _ hneg
  have hHu : ρ σ⁻¹ ha ∈ Submodule.span (ZMod 3) (Set.range h) := by
    have h1 := ggTen_sub_mem_span h α r hr (Subgroup.closure (Set.range r)) rfl (ρ σ⁻¹)
      (hρA σ⁻¹) ha
    have h2 := Submodule.add_mem _ h1 hH
    rwa [sub_add_cancel] at h2
  have hsumH : ρ σ⁻¹ ha + ha ∈ Submodule.span (ZMod 3) (Set.range h) :=
    Submodule.add_mem _ hHu hH
  have hzero : ρ σ⁻¹ ha + ha = 0 := by
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hfixv
    by_contra hne
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hd
      exact hne hd.symm
    have hxH : x ∈ Submodule.span (ZMod 3) (Set.range h) := by
      have h1 := Submodule.smul_mem _ d⁻¹ hsumH
      rwa [← hd, smul_smul, inv_mul_cancel₀ hd0, one_smul] at h1
    exact (ggDepA_relation F).2.1 hxH
  exact ⟨ρ σ⁻¹, hρA σ⁻¹, eq_neg_of_add_eq_zero_left hzero, hρx σ⁻¹⟩

private theorem l9_transv_false {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ A) {v : V} {ψ : Module.Dual (ZMod 3) V} {z : V}
    (hv : v ≠ 0) (hψv : ψ v = 0) (hψz : ψ z ≠ 0) (hform : ∀ w, g w = w - ψ w • v) : False := by
  have hmove : ggLinMove g = Submodule.span (ZMod 3) {v} := by
    refine le_antisymm (fun y hy => ?_) ?_
    · simp only [ggLinMove, LinearMap.mem_range] at hy
      obtain ⟨w, rfl⟩ := hy
      rw [Submodule.mem_span_singleton]
      refine ⟨-ψ w, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hform w]
      module
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      simp only [ggLinMove, SetLike.mem_coe, LinearMap.mem_range]
      refine ⟨-(ψ z)⁻¹ • z, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hform, map_smul,
        smul_eq_mul, neg_mul, inv_mul_cancel₀ hψz]
      module
  refine hnt g hg ⟨?_, fun w => ?_⟩
  · rw [hmove]
    exact finrank_span_singleton hv
  · have hw : g w - w = -ψ w • v := by
      rw [hform w]
      module
    rw [hw, hform, map_smul, hψv, smul_zero, zero_smul, sub_zero]

theorem ggDepA9_caseII_false {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V} {x : V}
    (F : GGDepAFrame 3 9 h α x)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod 3] V) (ha : V) (αa : Module.Dual (ZMod 3) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hH : ha ∈ Submodule.span (ZMod 3) (Set.range h)) : False := by
  classical
  let A : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range r ∪ {ra})
  have hrA : ∀ l, r l ∈ A := fun l => Subgroup.subset_closure (Or.inl ⟨l, rfl⟩)
  have hraA : ra ∈ A := Subgroup.subset_closure (Or.inr rfl)
  have hpair : ∀ i j : Fin 8, α i (h j) = (CartanMatrix.A 8 i j : ZMod 3) := F.pair
  obtain ⟨κ, hκ⟩ := ggIndep_p3_affine h α F.pair A hnt r hr hrA ra hraA ha αa hra hαa
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hH
  have hαha : (fun l => α l ha) =
      fun l => ∑ t : Fin 8, (CartanMatrix.A 8 l t : ZMod 3) * m t := by
    funext l
    rw [← hm, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, hpair, smul_eq_mul, mul_comm]
  have h2 : αa ha = κ * ∑ s : Fin 8, m s * ∑ t : Fin 8, (CartanMatrix.A 8 s t : ZMod 3) * m t := by
    conv_lhs => rw [← hm]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, hκ, smul_eq_mul, ← congrFun hαha s]
    ring
  have hsq : ∑ i : Fin 9, ggA8Tail (fun l => α l ha) i ^ 2 ≠ 0 := by
    intro h0
    rw [hαha, ← ggA8Tail_quad m] at h0
    rw [h0, mul_zero, hαa] at h2
    exact absurd h2 (by decide)
  obtain ⟨u, huA, hu, hux⟩ := ggDepA9_exists_neg F r hr hH hsq
  have huA' : u ∈ A := Subgroup.closure_mono Set.subset_union_left huA
  have huinv : ∀ w, u (u⁻¹ w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
  have huha : u⁻¹ ha = -ha := u.injective (by rw [huinv, map_neg, hu, neg_neg])
  have hux' : u⁻¹ x = x := u.injective (by rw [huinv, hux])
  let ψ : Module.Dual (ZMod 3) V := αa + αa ∘ₗ (u⁻¹ : V ≃ₗ[ZMod 3] V).toLinearMap
  have hψ : ∀ w, ψ w = αa w + αa (u⁻¹ w) := fun w => rfl
  have hg : ra * (u * ra * u⁻¹) ∈ A :=
    A.mul_mem hraA (A.mul_mem (A.mul_mem huA' hraA) (A.inv_mem huA'))
  have hform : ∀ w, (ra * (u * ra * u⁻¹)) w = w - ψ w • ha := by
    intro w
    have ht : (u * ra * u⁻¹) w = w + αa (u⁻¹ w) • ha := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hra, map_sub, map_smul, huinv, hu,
        smul_neg, sub_neg_eq_add]
    rw [LinearEquiv.mul_apply, ht, hra, hψ, map_add, map_smul, hαa, smul_eq_mul]
    module
  have hψha : ψ ha = 0 := by
    rw [hψ, huha, map_neg, hαa]
    ring
  have hψx : ψ x ≠ 0 := by
    rw [hψ, hux', ← two_mul]
    exact mul_ne_zero (by decide) hw
  have ha0 : ha ≠ 0 := by
    rintro rfl
    rw [map_zero] at hαa
    exact absurd hαa (by decide)
  exact l9_transv_false A hnt hg ha0 hψha hψx hform

theorem ggDepA_absIrred_of_not_mem {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 3 ≤ N)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hjoin : ∃ c, αa (h c) ≠ 0)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hdim : Module.finrank (ZMod p) V = N - 1)
    (hnH : ha ∉ Submodule.span (ZMod p) (Set.range h)) :
    ZS.AbsIrred p (Subgroup.closure (Set.range r ∪ {ra})) := by
  classical
  let z : Fin (N - 1) := ⟨0, by omega⟩
  let h' : Option (Fin (N - 1)) → V := fun o =>
    match o with
    | none => ha
    | some i => h i
  let α' : Option (Fin (N - 1)) → Module.Dual (ZMod p) V := fun o =>
    match o with
    | none => αa
    | some i => α i
  let g : Option (Fin (N - 1)) → (V ≃ₗ[ZMod p] V) := fun o =>
    match o with
    | none => ra
    | some i => r i
  have hg : ∀ o w, g o w = w - α' o w • h' o := by
    intro o w
    cases o with
    | none => exact hra w
    | some i => exact hr i w
  have hαdiag : ∀ i, α i (h i) = 2 := by
    intro i
    rw [F.pair i i]
    have hdiag : CartanMatrix.A (N - 1) i i = 2 := by
      simp [CartanMatrix.A, Matrix.of_apply]
    rw [hdiag]
    norm_num
  have hα : ∀ o, α' o (h' o) = 2 := by
    intro o
    cases o with
    | none => exact hαa
    | some i => exact hαdiag i
  have hspan : Submodule.span (ZMod p) (Set.range h') = ⊤ := by
    let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
    have hrel := ggDepA_relation F
    have hdimH : Module.finrank (ZMod p) H = N - 2 := hrel.2.2
    have hinf : H ⊓ Submodule.span (ZMod p) ({ha} : Set V) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨hvH, hvS⟩ := hv
      rw [Submodule.mem_span_singleton] at hvS
      obtain ⟨c, hc⟩ := hvS
      by_cases hc0 : c = 0
      · rw [hc0, zero_smul] at hc
        exact hc.symm
      · exfalso
        apply hnH
        have hha : ha = c⁻¹ • (c • ha) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hc] at hha
        rw [hha]
        exact H.smul_mem c⁻¹ hvH
    have hspan1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({ha} : Set V)) = 1 := by
      rw [finrank_span_singleton]
      intro hha0
      exact hnH (by rw [hha0]; exact H.zero_mem)
    have hdimsup : Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) ({ha} : Set V)) = N - 1 := by
      change Module.finrank (ZMod p)
        ↥(H ⊔ Submodule.span (ZMod p) ({ha} : Set V)) = N - 1
      have h := Submodule.finrank_sup_add_finrank_inf_eq H
        (Submodule.span (ZMod p) ({ha} : Set V))
      rw [hinf, finrank_bot, add_zero, hdimH, hspan1] at h
      omega
    have hrange : Set.range h' = Set.range h ∪ ({ha} : Set V) := by
      ext v
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact Or.inr rfl
        | some i => exact Or.inl ⟨i, rfl⟩
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨some i, rfl⟩
        · exact ⟨none, rfl⟩
    rw [hrange, Submodule.span_union]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hdimsup, hdim]
  have hker : ∀ w, (∀ o, α' o w = 0) → w = 0 := by
    intro w hw0
    have hfix := F.fix w (fun i => hw0 (some i))
    rw [Submodule.mem_span_singleton] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hcz : c = 0 := by
      have h0 : c * αa x = 0 := by
        have h1 : αa w = 0 := hw0 none
        rw [← hc, map_smul, smul_eq_mul] at h1
        exact h1
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hw
    rw [← hc, hcz, zero_smul]
  let R : Option (Fin (N - 1)) → Option (Fin (N - 1)) → Prop :=
    fun a b => α' a (h' b) ≠ 0 ∧ α' b (h' a) ≠ 0
  have hsymmMod : ∀ a b : Fin (N - 1),
      ggCartanAMod (N - 1) p a b = ggCartanAMod (N - 1) p b a := by
    intro a b
    have h := congrFun (congrFun (CartanMatrix.A_transpose (N - 1)) a) b
    simp only [Matrix.transpose_apply] at h
    simp only [ggCartanAMod]
    rw [h]
  have hstep : ∀ a b : Fin (N - 1),
      ggCartanAMod (N - 1) p a b ≠ 0 → R (some a) (some b) := by
    intro a b hab
    have h1 : α a (h b) = ggCartanAMod (N - 1) p a b := by
      simpa [ggCartanAMod] using F.pair a b
    have h2 : α b (h a) = ggCartanAMod (N - 1) p b a := by
      simpa [ggCartanAMod] using F.pair b a
    exact ⟨by rw [h1]; exact hab, by rw [h2, ← hsymmMod a b]; exact hab⟩
  have hchain : ∀ j : Fin (N - 1),
      Relation.ReflTransGen R (some z) (some j) := by
    intro j
    exact Relation.ReflTransGen.lift (p := R) some hstep z j
      (ggCartanAMod_conn (N - 1) p z j)
  let S : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hraS : ra ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  have hrS : ∀ i, r i ∈ Subgroup.closure S := fun i =>
    Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  obtain ⟨c, hc⟩ := hjoin
  have hRc_none : R (some c) none := by
    refine ⟨?_, ?_⟩
    · show α c ha ≠ 0
      intro h0
      exact hc (ggDepA_pair_zero_symm hp2 (Subgroup.closure S) hnt
        (hrS c) hraS (hr c) hra (hαdiag c) hαa h0)
    · show αa (h c) ≠ 0
      exact hc
  have hsymm : ∀ {a b : Option (Fin (N - 1))},
      Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact (Relation.ReflTransGen.single ⟨hbc.2, hbc.1⟩).trans ih
  have hnone_c : Relation.ReflTransGen R none (some c) :=
    Relation.ReflTransGen.single ⟨hRc_none.2, hRc_none.1⟩
  have hconn : ∀ o o' : Option (Fin (N - 1)), Relation.ReflTransGen R o o' := by
    intro o o'
    cases o with
    | none =>
      cases o' with
      | none => exact Relation.ReflTransGen.refl
      | some j => exact hnone_c.trans ((hsymm (hchain c)).trans (hchain j))
    | some i =>
      cases o' with
      | none =>
        exact hsymm (hnone_c.trans ((hsymm (hchain c)).trans (hchain i)))
      | some j =>
        exact (hsymm (hnone_c.trans ((hsymm (hchain c)).trans (hchain i)))).trans
          (hnone_c.trans ((hsymm (hchain c)).trans (hchain j)))
  have hrange : Set.range g = Set.range r ∪ ({ra} : Set (V ≃ₗ[ZMod p] V)) := by
    ext t
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr rfl
      | some i => exact Or.inl ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨none, rfl⟩
  have hA : Subgroup.closure (Set.range r ∪ {ra}) = Subgroup.closure (Set.range g) := by
    rw [hrange]
  exact ggRC_absIrred_of_connected hp2 g h' α' hg hα hspan hker hconn _ hA

end CFSG.StandardType

end
