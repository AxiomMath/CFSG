module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParAltDef
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv
open Nat
open scoped Nat

private theorem s16t3_alt_four_mul_div_add_mod (n : ℕ) :
    4 * (n / 4) + n % 4 = n :=
  Nat.div_add_mod n 4

private theorem s16t3_alt_eq_four_mul_div_add_mod (n : ℕ) :
    n = 4 * (n / 4) + n % 4 :=
  (s16t3_alt_four_mul_div_add_mod n).symm

private theorem s16t3_alt_div_mul_add_mod (n : ℕ) :
    n / 4 * 4 + n % 4 = n := by
  rw [Nat.mul_comm]
  exact s16t3_alt_four_mul_div_add_mod n

private def s16t3_alt_f (n : ℕ) (i : Fin n) : Fin (n / 4 + 1) :=
  ⟨(i : ℕ) / 4, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.isLt))⟩

private def s16t3_alt_ext (n : ℕ) (π : Perm (Fin (n / 4))) (b : Fin (n / 4 + 1)) :
    Fin (n / 4 + 1) :=
  if h : (b : ℕ) < n / 4 then (π ⟨b, h⟩).castLE (Nat.le_succ (n / 4)) else b

private noncomputable def s16t3_alt_φ (n : ℕ) :
    (Fin (n / 4) × Fin 4) ⊕ Fin (n % 4) ≃ Fin n :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin (n % 4)))).trans
    (finSumFinEquiv.trans (finCongr (s16t3_alt_div_mul_add_mod n)))

private theorem s16t3_alt_φ_inl_val (n : ℕ) (a : Fin (n / 4)) (j : Fin 4) :
    ((s16t3_alt_φ n (Sum.inl (a, j)) : Fin n) : ℕ) = (j : ℕ) + 4 * (a : ℕ) := by
  simp [s16t3_alt_φ, finProdFinEquiv]

private theorem s16t3_alt_φ_inr_val (n : ℕ) (y : Fin (n % 4)) :
    ((s16t3_alt_φ n (Sum.inr y) : Fin n) : ℕ) = n / 4 * 4 + (y : ℕ) := by
  simp [s16t3_alt_φ]

private noncomputable def s16t3_alt_inner (n : ℕ) :
    Perm (Fin (n / 4)) →* Perm ((Fin (n / 4) × Fin 4) ⊕ Fin (n % 4)) where
  toFun π := Equiv.sumCongr (Equiv.prodCongr π (Equiv.refl (Fin 4))) (Equiv.refl (Fin (n % 4)))
  map_one' := by
    ext x
    rcases x with ⟨⟨a, j⟩ | y⟩ <;> rfl
  map_mul' π ρ := by
    ext x
    rcases x with ⟨⟨a, j⟩ | y⟩ <;> rfl

private noncomputable def s16t3_alt_sHom (n : ℕ) :
    Perm (Fin (n / 4)) →* Perm (Fin n) :=
  (Equiv.permCongrHom (s16t3_alt_φ n)).toMonoidHom.comp (s16t3_alt_inner n)

private theorem s16t3_alt_sHom_apply (n : ℕ) (π : Perm (Fin (n / 4))) (i : Fin n) :
    s16t3_alt_sHom n π i
      = s16t3_alt_φ n (s16t3_alt_inner n π ((s16t3_alt_φ n).symm i)) := rfl

private theorem s16t3_alt_sHom_injective (n : ℕ) :
    Function.Injective (s16t3_alt_sHom n) := by
  have hinj : Function.Injective (s16t3_alt_inner n) := by
    intro π ρ h
    ext a
    have := congrArg (fun e : Perm ((Fin (n / 4) × Fin 4) ⊕ Fin (n % 4)) =>
      e (Sum.inl (a, 0))) h
    simpa [s16t3_alt_inner, Equiv.sumCongr_apply, Equiv.prodCongr, Fin.ext_iff] using this
  intro π ρ h
  change (Equiv.permCongrHom (s16t3_alt_φ n)).toMonoidHom (s16t3_alt_inner n π)
      = (Equiv.permCongrHom (s16t3_alt_φ n)).toMonoidHom (s16t3_alt_inner n ρ) at h
  exact hinj ((Equiv.permCongrHom (s16t3_alt_φ n)).injective h)

private theorem s16t3_alt_f_φ_inl (n : ℕ) (a : Fin (n / 4)) (j : Fin 4) :
    s16t3_alt_f n (s16t3_alt_φ n (Sum.inl (a, j)))
      = a.castLE (Nat.le_succ (n / 4)) := by
  apply Fin.ext
  simp only [s16t3_alt_f, Fin.val_castLE]
  rw [s16t3_alt_φ_inl_val, Nat.add_mul_div_left (j : ℕ) (a : ℕ) (by norm_num : 0 < 4),
    Nat.div_eq_of_lt j.isLt, Nat.zero_add]

private theorem s16t3_alt_f_φ_inr (n : ℕ) (y : Fin (n % 4)) :
    s16t3_alt_f n (s16t3_alt_φ n (Sum.inr y)) = Fin.last (n / 4) := by
  apply Fin.ext
  simp only [s16t3_alt_f, Fin.val_last]
  rw [s16t3_alt_φ_inr_val, Nat.mul_comm (n / 4) 4, Nat.mul_add_div (by norm_num : 0 < 4)]
  have hy : (y : ℕ) < 4 :=
    lt_of_lt_of_le y.isLt (Nat.le_of_lt (Nat.mod_lt n (by norm_num)))
  rw [Nat.div_eq_of_lt hy, Nat.add_zero]

private theorem s16t3_alt_ext_castSucc (n : ℕ) (π : Perm (Fin (n / 4))) (a : Fin (n / 4)) :
    s16t3_alt_ext n π (a.castLE (Nat.le_succ (n / 4)))
      = (π a).castLE (Nat.le_succ (n / 4)) := by
  unfold s16t3_alt_ext
  rw [dif_pos (by simpa using a.isLt)]
  exact congrArg (fun y : Fin (n / 4) => (π y).castLE (Nat.le_succ (n / 4)))
    (Fin.ext (by simp))

private theorem s16t3_alt_ext_last (n : ℕ) (π : Perm (Fin (n / 4))) :
    s16t3_alt_ext n π (Fin.last (n / 4)) = Fin.last (n / 4) := by
  unfold s16t3_alt_ext
  rw [dif_neg (by simpa using lt_irrefl (n / 4))]

private theorem s16t3_alt_f_s (n : ℕ) (π : Perm (Fin (n / 4))) (i : Fin n) :
    s16t3_alt_f n (s16t3_alt_sHom n π i)
      = s16t3_alt_ext n π (s16t3_alt_f n i) := by
  rcases hs : (s16t3_alt_φ n).symm i with ⟨a, j⟩ | y
  · have hi : i = s16t3_alt_φ n (Sum.inl (a, j)) := by
      rw [← Equiv.apply_symm_apply (s16t3_alt_φ n) i, hs]
    rw [hi]
    have hsf : s16t3_alt_sHom n π (s16t3_alt_φ n (Sum.inl (a, j)))
        = s16t3_alt_φ n (Sum.inl (π a, j)) := by
      rw [s16t3_alt_sHom_apply]
      simp only [Equiv.symm_apply_apply]
      rfl
    rw [hsf]
    rw [s16t3_alt_f_φ_inl n (π a) j]
    rw [s16t3_alt_f_φ_inl n a j]
    rw [s16t3_alt_ext_castSucc]
  · have hi : i = s16t3_alt_φ n (Sum.inr y) := by
      rw [← Equiv.apply_symm_apply (s16t3_alt_φ n) i, hs]
    rw [hi]
    have hsf : s16t3_alt_sHom n π (s16t3_alt_φ n (Sum.inr y))
        = s16t3_alt_φ n (Sum.inr y) := by
      rw [s16t3_alt_sHom_apply]
      simp only [Equiv.symm_apply_apply]
      rfl
    rw [hsf, s16t3_alt_f_φ_inr, s16t3_alt_ext_last]

private theorem s16t3_alt_mem_N0_iff (n : ℕ) (σ : Perm (Fin n)) :
    σ ∈ s16t3AltN0 n ↔ ∀ i, s16t3_alt_f n (σ i) = s16t3_alt_f n i := by
  rw [show σ ∈ s16t3AltN0 n ↔
      ∀ i, ((σ i : Fin n) : ℕ) / 4 = ((i : Fin n) : ℕ) / 4 from Iff.rfl]
  constructor
  · intro h i
    exact Fin.ext (h i)
  · intro h i
    exact congrArg Fin.val (h i)

private theorem s16t3_alt_conj_mem_N0 (n : ℕ) (π : Perm (Fin (n / 4))) (σ : Perm (Fin n))
    (hσ : σ ∈ s16t3AltN0 n) :
    s16t3_alt_sHom n π * σ * (s16t3_alt_sHom n π)⁻¹ ∈ s16t3AltN0 n := by
  rw [s16t3_alt_mem_N0_iff] at hσ ⊢
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [s16t3_alt_f_s n π (σ ((s16t3_alt_sHom n π)⁻¹ i)), hσ ((s16t3_alt_sHom n π)⁻¹ i),
    ← s16t3_alt_f_s n π ((s16t3_alt_sHom n π)⁻¹ i)]
  simp

private theorem s16t3_alt_le_normalizer (n : ℕ) :
    (s16t3_alt_sHom n).range ≤ Subgroup.normalizer (s16t3AltN0 n : Set (Perm (Fin n))) := by
  rintro _ ⟨π, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro σ
  constructor
  · intro hσ
    exact s16t3_alt_conj_mem_N0 n π σ hσ
  · intro h
    have h1 := s16t3_alt_conj_mem_N0 n π⁻¹
      (s16t3_alt_sHom n π * σ * (s16t3_alt_sHom n π)⁻¹) h
    have h2 : s16t3_alt_sHom n π⁻¹
          * (s16t3_alt_sHom n π * σ * (s16t3_alt_sHom n π)⁻¹)
          * (s16t3_alt_sHom n π⁻¹)⁻¹ = σ := by
      simp only [map_inv]
      group
    rwa [h2] at h1

private theorem s16t3_alt_inf_range_bot (n : ℕ) :
    s16t3AltN0 n ⊓ (s16t3_alt_sHom n).range = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro g
  rw [Subgroup.mem_inf]
  rintro ⟨hN, hS⟩
  obtain ⟨π, rfl⟩ := hS
  change (s16t3_alt_sHom n π) ∈ s16t3AltN0 n at hN
  rw [s16t3_alt_mem_N0_iff] at hN
  have hπ : π = 1 := by
    ext a
    have h := hN (s16t3_alt_φ n (Sum.inl (a, 0)))
    rw [s16t3_alt_f_s n π (s16t3_alt_φ n (Sum.inl (a, 0))),
      s16t3_alt_f_φ_inl, s16t3_alt_ext_castSucc] at h
    simpa using congrArg Fin.val h
  rw [hπ, map_one]
  simp

private def s16t3_alt_fibreFour (n : ℕ) (b : Fin (n / 4)) :
    {a : Fin n // s16t3_alt_f n a = Fin.castSucc b} ≃ Fin 4 where
  toFun a := ⟨((a : Fin n) : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩
  invFun j :=
    ⟨⟨4 * (b : ℕ) + (j : ℕ), by
        have hb : (b : ℕ) + 1 ≤ n / 4 := Nat.succ_le_of_lt b.isLt
        have h4 : 4 * ((b : ℕ) + 1) ≤ 4 * (n / 4) := Nat.mul_le_mul_left 4 hb
        have hle : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
        have : 4 * (b : ℕ) + (j : ℕ) < 4 * ((b : ℕ) + 1) := by omega
        omega⟩,
      by
        apply Fin.ext
        simp only [s16t3_alt_f, Fin.val_castSucc]
        rw [Nat.mul_add_div (by norm_num : 0 < 4), Nat.div_eq_of_lt j.isLt,
          Nat.add_zero]⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha : ((a : Fin n) : ℕ) / 4 = b := by
      have := congrArg Fin.val a.2
      simpa [s16t3_alt_f, Fin.val_castSucc] using this
    have h := Nat.div_add_mod ((a : Fin n) : ℕ) 4
    rw [ha] at h
    simp only [Fin.val_mk]
    omega
  right_inv j := by
    apply Fin.ext
    simp only [Fin.val_mk]
    rw [show 4 * (b : ℕ) + (j : ℕ) = (j : ℕ) + 4 * (b : ℕ) by omega,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt j.isLt

private def s16t3_alt_fibreLast (n : ℕ) :
    {a : Fin n // s16t3_alt_f n a = Fin.last (n / 4)} ≃ Fin (n % 4) where
  toFun a :=
    ⟨((a : Fin n) : ℕ) - 4 * (n / 4), by
      have ha : ((a : Fin n) : ℕ) / 4 = n / 4 := by
        have := congrArg Fin.val a.2
        simpa [s16t3_alt_f, Fin.val_last] using this
      have h := Nat.div_add_mod ((a : Fin n) : ℕ) 4
      rw [ha] at h
      have hone : ((a : Fin n) : ℕ) = 4 * (n / 4) + ((a : Fin n) : ℕ) % 4 := h.symm
      have hn : n = 4 * (n / 4) + n % 4 := s16t3_alt_eq_four_mul_div_add_mod n
      have : ((a : Fin n) : ℕ) % 4 < n % 4 := by omega
      omega⟩
  invFun j :=
    ⟨⟨4 * (n / 4) + (j : ℕ), by
        have hn : n = 4 * (n / 4) + n % 4 := s16t3_alt_eq_four_mul_div_add_mod n
        have hj : (j : ℕ) < n % 4 := j.isLt
        omega⟩,
      by
        apply Fin.ext
        simp only [s16t3_alt_f, Fin.val_last]
        rw [Nat.mul_add_div (by norm_num : 0 < 4),
          Nat.div_eq_of_lt (lt_of_lt_of_le j.isLt
            (Nat.le_of_lt (Nat.mod_lt n (by norm_num)))), Nat.add_zero]⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha : ((a : Fin n) : ℕ) / 4 = n / 4 := by
      have := congrArg Fin.val a.2
      simpa [s16t3_alt_f, Fin.val_last] using this
    have h := Nat.div_add_mod ((a : Fin n) : ℕ) 4
    rw [ha] at h
    have hone : ((a : Fin n) : ℕ) = 4 * (n / 4) + ((a : Fin n) : ℕ) % 4 := h.symm
    simp only [Fin.val_mk]
    omega
  right_inv j := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

private theorem s16t3_alt_fibre_card_four (n : ℕ) (b : Fin (n / 4)) :
    Fintype.card {a : Fin n // s16t3_alt_f n a = Fin.castSucc b} = 4 :=
  (Fintype.card_congr (s16t3_alt_fibreFour n b)).trans (Fintype.card_fin 4)

private theorem s16t3_alt_fibre_card_last (n : ℕ) :
    Fintype.card {a : Fin n // s16t3_alt_f n a = Fin.last (n / 4)} = n % 4 :=
  (Fintype.card_congr (s16t3_alt_fibreLast n)).trans (Fintype.card_fin (n % 4))

private theorem s16t3_alt_prod_fibre (n : ℕ) :
    (∏ i : Fin (n / 4 + 1), (Fintype.card {a : Fin n // s16t3_alt_f n a = i})!)
      = 24 ^ (n / 4) * (n % 4)! := by
  rw [Fin.prod_univ_castSucc]
  have hfirst : (∏ i : Fin (n / 4),
        (Fintype.card {a : Fin n // s16t3_alt_f n a = Fin.castSucc i})!)
      = ∏ _i : Fin (n / 4), (24 : ℕ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [s16t3_alt_fibre_card_four]
    decide
  rw [hfirst, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    s16t3_alt_fibre_card_last]

private theorem s16t3_alt_N0_card (n : ℕ) :
    Nat.card ↥(s16t3AltN0 n) = 24 ^ (n / 4) * (n % 4)! := by
  have hiff : ∀ g : Perm (Fin n),
      g ∈ s16t3AltN0 n ↔ s16t3_alt_f n ∘ g = s16t3_alt_f n := by
    intro g
    rw [s16t3_alt_mem_N0_iff]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  calc Nat.card ↥(s16t3AltN0 n)
      = Nat.card {g : Perm (Fin n) // s16t3_alt_f n ∘ g = s16t3_alt_f n} :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ = Fintype.card {g : Perm (Fin n) // s16t3_alt_f n ∘ g = s16t3_alt_f n} :=
        Nat.card_eq_fintype_card
    _ = 24 ^ (n / 4) * (n % 4)! := by
        rw [DomMulAct.stabilizer_card (s16t3_alt_f n)]
        exact s16t3_alt_prod_fibre n

private theorem s16t3_alt_range_card (n : ℕ) :
    Nat.card ↥(s16t3_alt_sHom n).range = (n / 4)! := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (s16t3_alt_sHom_injective n)).toEquiv,
    Nat.card_perm, Nat.card_fin]

private theorem s16t3_alt_sup_card (n : ℕ) :
    Nat.card ↥(s16t3AltN0 n ⊔ (s16t3_alt_sHom n).range)
      = Nat.card ↥(s16t3AltN0 n) * Nat.card ↥(s16t3_alt_sHom n).range := by
  let N0 := s16t3AltN0 n
  let S := (s16t3_alt_sHom n).range
  have hSN : S ≤ Subgroup.normalizer (N0 : Set (Perm (Fin n))) := s16t3_alt_le_normalizer n
  have hbot : N0 ⊓ S = ⊥ := s16t3_alt_inf_range_bot n
  let F : ↥N0 × ↥S → ↥(N0 ⊔ S) :=
    fun p => ⟨p.1 * p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      have h' : (a1 : Perm (Fin n)) * b1 = a2 * b2 := Subtype.ext_iff.mp h
      have hmem : (a2 : Perm (Fin n))⁻¹ * a1 = b2 * (b1 : Perm (Fin n))⁻¹ := by
        have hc := congrArg (fun x : Perm (Fin n) =>
          (a2 : Perm (Fin n))⁻¹ * x * (b1 : Perm (Fin n))⁻¹) h'
        simpa [mul_assoc] using hc
      have h1 : (a2 : Perm (Fin n))⁻¹ * a1 ∈ N0 ⊓ S := by
        refine ⟨N0.mul_mem (N0.inv_mem a2.2) a1.2, ?_⟩
        rw [hmem]
        exact S.mul_mem b2.2 (S.inv_mem b1.2)
      rw [hbot, Subgroup.mem_bot] at h1
      have ha' : (a1 : Perm (Fin n)) = a2 := by
        have hc := congrArg (fun x : Perm (Fin n) => (a2 : Perm (Fin n)) * x) h1
        simpa [mul_assoc] using hc
      have hb' : (b1 : Perm (Fin n)) = b2 := by
        have h2 : b2 * (b1 : Perm (Fin n))⁻¹ = 1 := by
          rw [← hmem, ha']; simp
        have hc := congrArg (fun x : Perm (Fin n) => x * b1) h2
        simpa [mul_assoc] using hc.symm
      exact Prod.ext (Subtype.ext ha') (Subtype.ext hb')
    · intro x
      have hx : (x : Perm (Fin n)) ∈ (↑(N0 ⊔ S) : Set (Perm (Fin n))) := x.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left N0 S hSN, Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  exact (Nat.card_congr (Equiv.ofBijective F hF).symm).trans (Nat.card_prod _ _)

private theorem s16t3_alt_N1_card (n : ℕ) :
    Nat.card ↥(s16t3AltN0 n ⊔ (s16t3_alt_sHom n).range)
      = 24 ^ (n / 4) * (n % 4)! * (n / 4)! := by
  rw [s16t3_alt_sup_card, s16t3_alt_N0_card, s16t3_alt_range_card]

private theorem s16t3_alt_sum_digits (k r : ℕ) (hr : r < 4) :
    (Nat.digits 2 (4 * k + r)).sum = (Nat.digits 2 k).sum + (Nat.digits 2 r).sum := by
  rcases k with _ | k
  · interval_cases r <;> decide
  · have h1 : 4 * (k + 1) + r = r % 2 + 2 * (2 * (k + 1) + r / 2) := by omega
    rw [h1, Nat.digits_add 2 (by norm_num) (r % 2) (2 * (k + 1) + r / 2) (by omega)
        (Or.inr (by omega)), List.sum_cons]
    rw [show 2 * (k + 1) + r / 2 = r / 2 + 2 * (k + 1) by omega,
      Nat.digits_add 2 (by norm_num) (r / 2) (k + 1) (by omega) (Or.inr (by omega)),
      List.sum_cons]
    have h3 : (Nat.digits 2 r).sum = r % 2 + r / 2 := by
      interval_cases r <;> decide
    rw [h3]
    ring

private theorem s16t3_alt_padic (k r : ℕ) (hr : r < 4) :
    padicValNat 2 ((4 * k + r)!) = 3 * k + padicValNat 2 (r !) + padicValNat 2 (k !) := by
  have hmain := sub_one_mul_padicValNat_factorial (p := 2) (4 * k + r)
  have hk := sub_one_mul_padicValNat_factorial (p := 2) k
  have hr' := sub_one_mul_padicValNat_factorial (p := 2) r
  simp only [Nat.reduceSub, one_mul] at hmain hk hr'
  rw [hmain, hk, hr', s16t3_alt_sum_digits k r hr]
  have hk_le : (Nat.digits 2 k).sum ≤ k := Nat.digit_sum_le 2 k
  have hr_le : (Nat.digits 2 r).sum ≤ r := Nat.digit_sum_le 2 r
  omega

private theorem s16t3_alt_padic_n (n : ℕ) :
    padicValNat 2 (n !) = 3 * (n / 4) + padicValNat 2 ((n % 4)!)
      + padicValNat 2 ((n / 4)!) := by
  conv_lhs => rw [s16t3_alt_eq_four_mul_div_add_mod n]
  exact s16t3_alt_padic (n / 4) (n % 4) (Nat.mod_lt n (by norm_num : 0 < 4))

private theorem s16t3_alt_padicValNat_24 : padicValNat 2 24 = 3 := by
  have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 3)]

private theorem s16t3_alt_padicValNat_le_of_dvd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ∣ b) : padicValNat 2 a ≤ padicValNat 2 b := by
  have h1 : 2 ^ padicValNat 2 a ∣ a := (padicValNat_dvd_iff_le (p := 2) ha).mpr le_rfl
  exact (padicValNat_dvd_iff_le (p := 2) hb).mp (h1.trans h)

theorem s16t3_alt_sylow_normalizing (n : ℕ) :
    ∃ Y : Subgroup (Equiv.Perm (Fin n)), CFSG.ABGLocalTools.IsSylowOf 2 Y ⊤ ∧
      Y ≤ Subgroup.normalizer (s16t3AltN0 n : Set (Equiv.Perm (Fin n))) := by
  let N0 := s16t3AltN0 n
  let S := (s16t3_alt_sHom n).range
  let N1 := N0 ⊔ S
  let M := Subgroup.normalizer (N0 : Set (Perm (Fin n)))
  have hN1M : N1 ≤ M := by
    refine sup_le Subgroup.le_normalizer ?_
    exact s16t3_alt_le_normalizer n
  have hcardN1 : Nat.card ↥N1 = 24 ^ (n / 4) * (n % 4)! * (n / 4)! := s16t3_alt_N1_card n
  have h24 : padicValNat 2 (24 ^ (n / 4) * (n % 4)! * (n / 4)!)
      = 3 * (n / 4) + padicValNat 2 ((n % 4)!) + padicValNat 2 ((n / 4)!) := by
    rw [padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (by positivity) (by positivity), padicValNat.pow,
      s16t3_alt_padicValNat_24]
    ring
  have hN1eq : padicValNat 2 (Nat.card ↥N1)
      = padicValNat 2 (Nat.card (Equiv.Perm (Fin n))) := by
    rw [hcardN1, h24, Nat.card_perm, Nat.card_fin]
    conv_rhs => rw [s16t3_alt_padic_n]
  have hkey : padicValNat 2 (Nat.card ↥M)
      = padicValNat 2 (Nat.card ↥(⊤ : Subgroup (Equiv.Perm (Fin n)))) := by
    refine le_antisymm ?_ ?_
    · have hMtop : Nat.card ↥M ∣ Nat.card ↥(⊤ : Subgroup (Equiv.Perm (Fin n))) :=
        Subgroup.card_dvd_of_le le_top
      exact s16t3_alt_padicValNat_le_of_dvd Nat.card_pos.ne'
        (Nat.card_pos (α := ↥(⊤ : Subgroup (Equiv.Perm (Fin n))))).ne' hMtop
    · have hN1M' : Nat.card ↥N1 ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hN1M
      have h1 : padicValNat 2 (Nat.card ↥N1) ≤ padicValNat 2 (Nat.card ↥M) :=
        s16t3_alt_padicValNat_le_of_dvd Nat.card_pos.ne' Nat.card_pos.ne' hN1M'
      have h2 : padicValNat 2 (Nat.card ↥(⊤ : Subgroup (Equiv.Perm (Fin n))))
          = padicValNat 2 (Nat.card ↥N1) := by
        rw [Subgroup.card_top]
        exact hN1eq.symm
      rw [h2]
      exact h1
  let Q : Sylow 2 ↥M := default
  refine ⟨Q.map M.subtype, ?_, ?_⟩
  · refine CFSG.ABGLocalTools.isSylowOf_of_card (p := 2)
      (P := Q.map M.subtype) (K := ⊤) le_top ?_
    rw [Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity]
    congr 1
    rw [Nat.factorization_def (Nat.card ↥M) Nat.prime_two,
      Nat.factorization_def (Nat.card ↥(⊤ : Subgroup (Equiv.Perm (Fin n)))) Nat.prime_two]
    exact hkey
  · show Q.map M.subtype ≤ M
    exact Subgroup.map_subtype_le (H := M) Q

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
