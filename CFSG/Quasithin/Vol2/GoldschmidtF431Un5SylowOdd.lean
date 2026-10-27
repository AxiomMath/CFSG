module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnSylowOdd

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits Matrix

section Odd

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

theorem exists_diagonal_of_mem_unT5 {t : SU (unitaryInvolution F 2 f) 5}
    (ht : t ∈ unT (F := F) (p := 2) (f := f) 5) :
    ∃ d : Fin 5 → F, mat (unitaryInvolution F 2 f) 5 t = diagonal d :=
  Subgroup.iSup_induction (C := fun y : SU (unitaryInvolution F 2 f) 5 =>
    ∃ d : Fin 5 → F, mat (unitaryInvolution F 2 f) 5 y = diagonal d)
    (fun i => levelTorus (unitaryInvolution F 2 f) i) ht
    (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
    ⟨1, by rw [map_one]; exact diagonal_one.symm⟩ fun y z ⟨d, hd⟩ ⟨d', hd'⟩ =>
      ⟨d * d', by rw [map_mul, hd, hd', diagonal_mul_diagonal]; rfl⟩

theorem pow_card_sub_one_unT5 {t : SU (unitaryInvolution F 2 f) 5}
    (ht : t ∈ unT (F := F) (p := 2) (f := f) 5) : t ^ (Nat.card F - 1) = 1 := by
  obtain ⟨d, hd⟩ := exists_diagonal_of_mem_unT5 ht
  have hdet : ∏ i, d i = 1 := by
    have h := t.2.1
    have h2 : ((t : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = diagonal d := hd
    rw [h2, det_diagonal] at h
    exact h
  have hne : ∀ i, d i ≠ 0 := fun i h0 => by
    have : ∏ i, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  have : Fintype F := Fintype.ofFinite F
  apply mat_injective
  rw [map_pow, hd, diagonal_pow, map_one]
  have hc : Nat.card F - 1 = Fintype.card F - 1 := by rw [Nat.card_eq_fintype_card]
  rw [hc]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [diagonal_apply_eq, FiniteField.pow_card_sub_one_eq_one _ (hne i)]
  · simp [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem odd_card_unT5 (hF : Nat.card F = (2 ^ f) ^ 2) :
    Odd (Nat.card (unT (F := F) (p := 2) (f := f) 5)) := by
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (unT (F := F) (p := 2) (f := f) 5) := by omega
  have : Fintype (unT (F := F) (p := 2) (f := f) 5) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := unT (F := F) (p := 2) (f := f) 5) 2 h2
  have hpow : (x : SU (unitaryInvolution F 2 f) 5) ^ (Nat.card F - 1) = 1 :=
    pow_card_sub_one_unT5 x.2
  have h3 : orderOf (x : SU (unitaryInvolution F 2 f) 5) ∣ Nat.card F - 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hx] at h3
  obtain ⟨k, hk⟩ := odd_card_sub_one hF
  omega

end Odd

end CFSG.Quasithin.H13.F431.Un
