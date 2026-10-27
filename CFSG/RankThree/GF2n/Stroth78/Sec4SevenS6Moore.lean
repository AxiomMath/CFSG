module


import CFSG.Sporadic.SchreierLemmas.MoorePresentation
import CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

open Equiv Equiv.Perm CFSG.Sporadic.SchreierLemmas

variable {X : Type} [Group X] {D : Set X}

private theorem comm_lift (Ψ : X →* Perm (Fin 6)) (hker : Ψ.ker ≤ Subgroup.center X)
    (hodd : Odd (Nat.card Ψ.ker)) (hself : ∀ x ∈ D, x * x = 1)
    (h3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ)) {e e' : X} (he : e ∈ D)
    (he' : e' ∈ D) (h : Ψ e * Ψ e' = Ψ e' * Ψ e) : e * e' = e' * e :=
  CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid.commute_of_pi_commute hker hodd hself
    h3 he he' h

private theorem cube_lift (Ψ : X →* Perm (Fin 6))
    (h3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ)) {e e' : X} (he : e ∈ D)
    (he' : e' ∈ D) (hc : orderOf (Ψ e * Ψ e') = 3) : (e * e') ^ 3 = 1 := by
  have h1 : orderOf (Ψ (e * e')) ∣ orderOf (e * e') := orderOf_map_dvd Ψ _
  rw [map_mul, hc] at h1
  have h2 := h3 e he e' he'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
  have h4 : orderOf (e * e') = 3 := by
    rcases h2 with h | h | h
    · rw [h] at h1; omega
    · rw [h] at h1; omega
    · exact h
  rw [← h4]
  exact pow_orderOf_eq_one _

private theorem sq_mul_of_commute {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h : a * b = b * a) : (a * b) ^ 2 = 1 := by
  calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
    _ = a * (a * b) * b := by rw [h]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]


private theorem orderOf_three_of {p : Perm (Fin 6)} (h3 : p ^ 3 = 1) (h1 : p ≠ 1) :
    orderOf p = 3 := orderOf_eq_prime h3 h1

theorem injective_of_closure_eq_top_of_moore {X : Type} [Group X] {D : Set X}
    (Ψ : X →* Perm (Fin 6)) (hgen : Subgroup.closure D = ⊤)
    (hker : Ψ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card Ψ.ker))
    (hself : ∀ x ∈ D, x * x = 1)
    (h3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    (hconj : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ ∈ D)
    (hswap : ∀ x ∈ D, (Ψ x).IsSwap)
    (hlift : ∀ p : Perm (Fin 6), p.IsSwap → ∃ x ∈ D, Ψ x = p) :
    Function.Injective Ψ := by
  classical
  obtain ⟨e0, he0, hΨ0⟩ := hlift (swap 0 1) ⟨0, 1, by decide, rfl⟩
  obtain ⟨e1, he1, hΨ1⟩ := hlift (swap 1 2) ⟨1, 2, by decide, rfl⟩
  obtain ⟨e2, he2, hΨ2⟩ := hlift (swap 2 3) ⟨2, 3, by decide, rfl⟩
  obtain ⟨e3, he3, hΨ3⟩ := hlift (swap 3 4) ⟨3, 4, by decide, rfl⟩
  obtain ⟨e4, he4, hΨ4⟩ := hlift (swap 4 5) ⟨4, 5, by decide, rfl⟩
  have s0 := hself e0 he0
  have s1 := hself e1 he1
  have s2 := hself e2 he2
  have s3 := hself e3 he3
  have s4 := hself e4 he4
  have c02 : e0 * e2 = e2 * e0 :=
    comm_lift Ψ hker hodd hself h3 he0 he2 (by rw [hΨ0, hΨ2]; decide)
  have c03 : e0 * e3 = e3 * e0 :=
    comm_lift Ψ hker hodd hself h3 he0 he3 (by rw [hΨ0, hΨ3]; decide)
  have c04 : e0 * e4 = e4 * e0 :=
    comm_lift Ψ hker hodd hself h3 he0 he4 (by rw [hΨ0, hΨ4]; decide)
  have c13 : e1 * e3 = e3 * e1 :=
    comm_lift Ψ hker hodd hself h3 he1 he3 (by rw [hΨ1, hΨ3]; decide)
  have c14 : e1 * e4 = e4 * e1 :=
    comm_lift Ψ hker hodd hself h3 he1 he4 (by rw [hΨ1, hΨ4]; decide)
  have c24 : e2 * e4 = e4 * e2 :=
    comm_lift Ψ hker hodd hself h3 he2 he4 (by rw [hΨ2, hΨ4]; decide)
  have t01 : (e0 * e1) ^ 3 = 1 :=
    cube_lift Ψ h3 he0 he1 (by
      rw [hΨ0, hΨ1]; exact orderOf_three_of (by decide) (by decide))
  have t23 : (e2 * e3) ^ 3 = 1 :=
    cube_lift Ψ h3 he2 he3 (by
      rw [hΨ2, hΨ3]; exact orderOf_three_of (by decide) (by decide))
  have t34 : (e3 * e4) ^ 3 = 1 :=
    cube_lift Ψ h3 he3 he4 (by
      rw [hΨ3, hΨ4]; exact orderOf_three_of (by decide) (by decide))
  have e0inv : e0⁻¹ = e0 := inv_eq_of_mul_eq_one_left s0
  have hf : e0 * e1 * e0⁻¹ ∈ D := hconj e0 he0 e1 he1
  have t12 : (e0 * e1 * e0⁻¹ * e2) ^ 3 = 1 :=
    cube_lift Ψ h3 hf he2 (by
      rw [map_mul, map_mul, map_inv, hΨ0, hΨ1, hΨ2]
      exact orderOf_three_of (by decide) (by decide))
  have m02 : (e0 * e2) * (e0 * e2) = 1 := by
    calc (e0 * e2) * (e0 * e2) = (e0 * e0) * (e2 * e2) := by
          rw [mul_assoc, ← mul_assoc e2, ← c02]; group
      _ = 1 := by rw [s0, s2, one_mul]
  have comm_mul : ∀ a b c : X, a * a = 1 → a * b = b * a → (a * b) * (a * c) = b * c := by
    intro a b c ha hab
    calc (a * b) * (a * c) = (b * a) * (a * c) := by rw [hab]
      _ = b * (a * a) * c := by group
      _ = b * c := by rw [ha, mul_one]
  let x : ℕ → X := fun i => if i = 1 then e0 * e1 else if i = 2 then e0 * e2 else
    if i = 3 then e0 * e3 else if i = 4 then e0 * e4 else 1
  have hx1 : x 1 = e0 * e1 := by simp [x]
  have hx2 : x 2 = e0 * e2 := by simp [x]
  have hx3 : x 3 = e0 * e3 := by simp [x]
  have hx4 : x 4 = e0 * e4 := by simp [x]
  have hf2 : (e0 * e1) * (e0 * e2) = e0 * e1 * e0⁻¹ * e2 := by rw [e0inv]; group
  have hf3 : (e0 * e1) * (e0 * e3) = (e0 * e1 * e0⁻¹) * e3 := by rw [e0inv]; group
  have hf4 : (e0 * e1) * (e0 * e4) = (e0 * e1 * e0⁻¹) * e4 := by rw [e0inv]; group
  have hfe3 : Commute (e0 * e1 * e0⁻¹) e3 :=
    Commute.mul_left (Commute.mul_left c03 c13) (Commute.inv_left c03)
  have hfe4 : Commute (e0 * e1 * e0⁻¹) e4 :=
    Commute.mul_left (Commute.mul_left c04 c14) (Commute.inv_left c04)
  have hM : IsMooreFamily (6 - 2) x := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hx1]; exact t01
    · intro j hj2 hj4
      have hj : j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj with rfl | rfl | rfl
      · rw [hx2]; exact sq_mul_of_commute s0 s2 c02
      · rw [hx3]; exact sq_mul_of_commute s0 s3 c03
      · rw [hx4]; exact sq_mul_of_commute s0 s4 c04
    · intro j hj2 hj4
      have hj : j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj with rfl | rfl | rfl
      · show (x 1 * x 2) ^ 3 = 1
        rw [hx1, hx2, hf2]; exact t12
      · show (x 2 * x 3) ^ 3 = 1
        rw [hx2, hx3, comm_mul e0 e2 e3 s0 c02]; exact t23
      · show (x 3 * x 4) ^ 3 = 1
        rw [hx3, hx4, comm_mul e0 e3 e4 s0 c03]; exact t34
    · intro i j hi hij hj
      have hij' : (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by omega
      rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hx1, hx3, hf3]; exact sq_mul_of_commute (hself _ hf) s3 hfe3.eq
      · rw [hx1, hx4, hf4]; exact sq_mul_of_commute (hself _ hf) s4 hfe4.eq
      · rw [hx2, hx4, comm_mul e0 e2 e4 s0 c02]; exact sq_mul_of_commute s2 s4 c24
  obtain ⟨φ, hφ⟩ := exists_hom_mooreCycle (by norm_num : 3 ≤ 6) x hM
  have hΨφ : Ψ.comp φ = (alternatingGroup (Fin 6)).subtype := by
    refine hom_ext_mooreCycle (by norm_num) ?_
    intro i hi
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      simp only [Set.mem_Icc] at hi; omega
    rw [MonoidHom.comp_apply, hφ i hi, Subgroup.coe_subtype, coe_mooreCycle]
    rcases hi' with rfl | rfl | rfl | rfl
    · rw [hx1, map_mul, hΨ0, hΨ1, moorePerm_one (by norm_num)]; decide
    · rw [hx2, map_mul, hΨ0, hΨ2, moorePerm_of_two_le (by norm_num) (by norm_num)]; decide
    · rw [hx3, map_mul, hΨ0, hΨ3, moorePerm_of_two_le (by norm_num) (by norm_num)]; decide
    · rw [hx4, map_mul, hΨ0, hΨ4, moorePerm_of_two_le (by norm_num) (by norm_num)]; decide
  have hΨφa : ∀ a : alternatingGroup (Fin 6), Ψ (φ a) = (a : Perm (Fin 6)) := fun a => by
    have := congrArg (fun f => f a) hΨφ
    simpa using this
  have hYinj : ∀ y ∈ φ.range, Ψ y = 1 → y = 1 := by
    rintro _ ⟨a, rfl⟩ h
    have h1 : (a : Perm (Fin 6)) = 1 := by rw [← hΨφa a]; exact h
    have h2 : a = 1 := Subtype.ext h1
    rw [h2, map_one]
  have hYgen : φ.range = Subgroup.closure (x '' Set.Icc 1 (6 - 2)) :=
    (moore_alternating_presentation (by norm_num) x hM).2.2.1 φ hφ
  have e1inv : e1⁻¹ = e1 := inv_eq_of_mul_eq_one_left s1
  have hxY : ∀ i ∈ Set.Icc 1 (6 - 2), x i ∈ φ.range := fun i hi =>
    hYgen ▸ Subgroup.subset_closure ⟨i, hi, rfl⟩
  have hnormY : ∀ y ∈ φ.range, e0 * y * e0 ∈ φ.range := by
    have hle : Subgroup.closure (x '' Set.Icc 1 (6 - 2)) ≤
        φ.range.comap (MulAut.conj e0).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        simp only [Set.mem_Icc] at hi; omega
      show e0 * x i * e0⁻¹ ∈ φ.range
      rcases hi' with rfl | rfl | rfl | rfl
      · have : e0 * x 1 * e0⁻¹ = (x 1)⁻¹ := by
          rw [hx1, mul_inv_rev, e1inv, e0inv]
          calc e0 * (e0 * e1) * e0 = (e0 * e0) * e1 * e0 := by group
            _ = e1 * e0 := by rw [s0, one_mul]
        rw [this]; exact inv_mem (hxY 1 hi)
      · have : e0 * x 2 * e0⁻¹ = x 2 := by
          rw [hx2, e0inv]
          calc e0 * (e0 * e2) * e0 = (e0 * e0) * e2 * e0 := by group
            _ = e2 * e0 := by rw [s0, one_mul]
            _ = e0 * e2 := c02.symm
        rw [this]; exact hxY 2 hi
      · have : e0 * x 3 * e0⁻¹ = x 3 := by
          rw [hx3, e0inv]
          calc e0 * (e0 * e3) * e0 = (e0 * e0) * e3 * e0 := by group
            _ = e3 * e0 := by rw [s0, one_mul]
            _ = e0 * e3 := c03.symm
        rw [this]; exact hxY 3 hi
      · have : e0 * x 4 * e0⁻¹ = x 4 := by
          rw [hx4, e0inv]
          calc e0 * (e0 * e4) * e0 = (e0 * e0) * e4 * e0 := by group
            _ = e4 * e0 := by rw [s0, one_mul]
            _ = e0 * e4 := c04.symm
        rw [this]; exact hxY 4 hi
    intro y hy
    have := hle (hYgen ▸ hy)
    simpa [MulAut.conj_apply, e0inv] using this
  have hDQ : ∀ e ∈ D, e ∈ Subgroup.closure ((φ.range : Set X) ∪ {e0}) := by
    intro e he
    obtain ⟨u, v, huv, hp⟩ := hswap e he
    have hsign : sign (Ψ e * swap 0 1) = 1 := by
      rw [map_mul, hp, sign_swap huv, sign_swap (by decide)]; rfl
    let a : alternatingGroup (Fin 6) := ⟨Ψ e * swap 0 1, mem_alternatingGroup.mpr hsign⟩
    have hyY : φ a ∈ φ.range := ⟨a, rfl⟩
    have hΨq : Ψ (φ a * e0) = Ψ e := by
      rw [map_mul, hΨφa, hΨ0]
      simp only [a]
      rw [mul_assoc, swap_mul_self, mul_one]
    have hk : (φ a * e0)⁻¹ * e ∈ Ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΨq, inv_mul_cancel]
    have hkc := hker hk
    have hq2 : (φ a * e0) * (φ a * e0) = 1 := by
      have h1 : (φ a * e0) * (φ a * e0) = φ a * (e0 * φ a * e0) := by group
      have h2 : φ a * (e0 * φ a * e0) ∈ φ.range := mul_mem hyY (hnormY _ hyY)
      refine hYinj _ (h1 ▸ h2) ?_
      rw [map_mul, hΨq, hp, swap_mul_self]
    generalize hqdef : φ a * e0 = q at hΨq hk hkc hq2
    have hek : e = q * (q⁻¹ * e) := by group
    have hqk := Subgroup.mem_center_iff.mp hkc q
    have hkk : (q⁻¹ * e) * (q⁻¹ * e) = 1 := by
      have he2 := hself e he
      calc (q⁻¹ * e) * (q⁻¹ * e) = (q * q) * ((q⁻¹ * e) * (q⁻¹ * e)) := by rw [hq2, one_mul]
        _ = q * (q * (q⁻¹ * e)) * (q⁻¹ * e) := by group
        _ = q * ((q⁻¹ * e) * q) * (q⁻¹ * e) := by rw [hqk]
        _ = (q * (q⁻¹ * e)) * (q * (q⁻¹ * e)) := by group
        _ = e * e := by rw [← hek]
        _ = 1 := he2
    have hk1 : q⁻¹ * e = 1 := by
      have h2 : orderOf (q⁻¹ * e) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hkk)
      have h3 : orderOf (⟨q⁻¹ * e, hk⟩ : Ψ.ker) ∣ Nat.card Ψ.ker :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h3
      have h4 : orderOf (q⁻¹ * e) = 1 :=
        Nat.Coprime.eq_one_of_dvd (hodd.of_dvd_nat h3).coprime_two_right h2
      exact orderOf_eq_one_iff.mp h4
    have heq : e = φ a * e0 := by
      rw [hqdef]
      have := hek; rw [hk1, mul_one] at this; exact this
    rw [heq]
    exact mul_mem (Subgroup.subset_closure (Or.inl hyY)) (Subgroup.subset_closure (Or.inr rfl))
  have hXQ : ∀ g : X, g ∈ Subgroup.closure ((φ.range : Set X) ∪ {e0}) := by
    intro g
    have h1 : Subgroup.closure D ≤ Subgroup.closure ((φ.range : Set X) ∪ {e0}) :=
      (Subgroup.closure_le _).mpr hDQ
    rw [hgen] at h1
    exact h1 (Subgroup.mem_top g)
  have hQ : ∀ q ∈ Subgroup.closure ((φ.range : Set X) ∪ {e0}),
      q ∈ φ.range ∨ ∃ y ∈ φ.range, q = e0 * y := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Or.inl hx
      · rw [Set.mem_singleton_iff] at hx
        exact Or.inr ⟨1, one_mem _, by rw [hx, mul_one]⟩
    | one => exact Or.inl (one_mem _)
    | mul x y _ _ hx hy =>
      rcases hx with hx | ⟨x', hx', rfl⟩ <;> rcases hy with hy | ⟨y', hy', rfl⟩
      · exact Or.inl (mul_mem hx hy)
      · refine Or.inr ⟨(e0 * x * e0) * y', mul_mem (hnormY _ hx) hy', ?_⟩
        calc x * (e0 * y') = (e0 * e0) * x * (e0 * y') := by rw [s0, one_mul]
          _ = e0 * ((e0 * x * e0) * y') := by group
      · exact Or.inr ⟨x' * y, mul_mem hx' hy, by group⟩
      · refine Or.inl ?_
        have : e0 * x' * (e0 * y') = (e0 * x' * e0) * y' := by group
        rw [this]
        exact mul_mem (hnormY _ hx') hy'
    | inv x _ hx =>
      rcases hx with hx | ⟨x', hx', rfl⟩
      · exact Or.inl (inv_mem hx)
      · refine Or.inr ⟨e0 * x'⁻¹ * e0, hnormY _ (inv_mem hx'), ?_⟩
        calc (e0 * x')⁻¹ = x'⁻¹ * e0⁻¹ := mul_inv_rev _ _
          _ = (e0 * e0) * x'⁻¹ * e0 := by rw [e0inv, s0, one_mul]
          _ = e0 * (e0 * x'⁻¹ * e0) := by group
  rw [injective_iff_map_eq_one]
  intro k hk
  rcases hQ k (hXQ k) with hY | ⟨y, hy, rfl⟩
  · exact hYinj k hY hk
  · exfalso
    obtain ⟨a, rfl⟩ := hy
    rw [map_mul, hΨ0, hΨφa] at hk
    have h1 : (a : Perm (Fin 6)) = swap 0 1 := by
      have := congrArg (fun t => swap (0 : Fin 6) 1 * t) hk
      simpa [← mul_assoc, swap_mul_self] using this
    have h2 : sign (a : Perm (Fin 6)) = 1 := mem_alternatingGroup.mp a.2
    rw [h1, sign_swap (by decide)] at h2
    exact absurd h2 (by decide)

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
