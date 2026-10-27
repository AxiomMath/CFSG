module

public import CFSG.LieType.Universal.Unitary.Extras.Torus
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits Matrix

section Odd

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

theorem exists_diagonal_of_mem_unT {t : SU (unitaryInvolution F 2 f) 4}
    (ht : t ∈ unT (F := F) (p := 2) (f := f) 4) :
    ∃ d : Fin 4 → F, mat (unitaryInvolution F 2 f) 4 t = diagonal d :=
  Subgroup.iSup_induction (C := fun y : SU (unitaryInvolution F 2 f) 4 =>
    ∃ d : Fin 4 → F, mat (unitaryInvolution F 2 f) 4 y = diagonal d)
    (fun i => levelTorus (unitaryInvolution F 2 f) i) ht
    (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
    ⟨1, by rw [map_one]; exact diagonal_one.symm⟩ fun y z ⟨d, hd⟩ ⟨d', hd'⟩ =>
      ⟨d * d', by rw [map_mul, hd, hd', diagonal_mul_diagonal]; rfl⟩

omit [CharP F 2] in
theorem odd_card_sub_one (hF : Nat.card F = (2 ^ f) ^ 2) : Odd (Nat.card F - 1) := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hf : 1 ≤ f := by
    by_contra h
    have : f = 0 := by omega
    rw [this] at hF
    simp at hF
    omega
  have h2 : 2 ∣ Nat.card F := by
    rw [hF]
    exact Dvd.dvd.pow (dvd_pow_self 2 (by omega)) (by norm_num)
  obtain ⟨k, hk⟩ := h2
  exact ⟨k - 1, by omega⟩

theorem pow_card_sub_one_unT {t : SU (unitaryInvolution F 2 f) 4}
    (ht : t ∈ unT (F := F) (p := 2) (f := f) 4) : t ^ (Nat.card F - 1) = 1 := by
  obtain ⟨d, hd⟩ := exists_diagonal_of_mem_unT ht
  have hdet : ∏ i, d i = 1 := by
    have h := t.2.1
    have h2 : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal d := hd
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

theorem odd_card_unT (hF : Nat.card F = (2 ^ f) ^ 2) :
    Odd (Nat.card (unT (F := F) (p := 2) (f := f) 4)) := by
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (unT (F := F) (p := 2) (f := f) 4) := by omega
  have : Fintype (unT (F := F) (p := 2) (f := f) 4) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := unT (F := F) (p := 2) (f := f) 4) 2 h2
  have hpow : (x : SU (unitaryInvolution F 2 f) 4) ^ (Nat.card F - 1) = 1 :=
    pow_card_sub_one_unT x.2
  have h3 : orderOf (x : SU (unitaryInvolution F 2 f) 4) ∣ Nat.card F - 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hx] at h3
  obtain ⟨k, hk⟩ := odd_card_sub_one hF
  omega

end Odd

end CFSG.Quasithin.H13.F431.Un
