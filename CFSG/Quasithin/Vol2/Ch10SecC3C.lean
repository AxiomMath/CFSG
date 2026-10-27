module

public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Background.HL3WrModel
public import CFSG.Quasithin.Background.HSL3Bridge

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem card_le_four_of_elem {E : Subgroup ↥SL32} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  let φ : ↥SL32 ≃* L3.Γ := (H.SL3Pair.slEquiv (ZMod 2)).symm
  set E' : Subgroup L3.Γ := E.map φ.toMonoidHom with hE'
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective φ.injective
  rw [← hcard]
  by_cases hE : E' = ⊥
  · rw [hE, Subgroup.card_bot]
    norm_num
  have hc' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have h2' : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, h2 x hx, map_one]
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE
  have hinv : L3.IsInvol (a : L3.Γ) := ⟨h2' a a.2, fun h => ha1 (Subtype.ext h)⟩
  have hle : E' ≤ Subgroup.centralizer ({(a : L3.Γ)} : Set L3.Γ) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc' x hx _ a.2)
  have hne : E' ≠ Subgroup.centralizer ({(a : L3.Γ)} : Set L3.Γ) := by
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := L3.cent_nonabelian (a : L3.Γ) hinv
    have hmem : ∀ z ∈ L3.cent (a : L3.Γ), z ∈ E' := fun z hz => by
      rw [h, Subgroup.mem_centralizer_singleton_iff]
      simp only [L3.cent, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact hz
    exact hxy (hc' x (hmem x hx) y (hmem y hy))
  have h8 := card_centralizer_L3 hinv
  have hdvd : Nat.card E' ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hle
  have hne8 : Nat.card E' ≠ 8 := fun h => hne (Subgroup.eq_of_le_of_card_ge hle (by omega))
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card E' ∣ 2 ^ 3 from hdvd)
  rw [hk']
  have hk3 : k ≠ 3 := fun h => hne8 (by rw [hk', h]; norm_num)
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 := by norm_num

theorem toAdd_rho_left (c : ↥SL32) (X : WMod) :
    Multiplicative.toAdd (rho (c, 1) X) = mat c * Multiplicative.toAdd X := by
  rw [toAdd_rho]
  simp [mat_one]

theorem toAdd_rho_right (d : ↥SL32) (X : WMod) :
    Multiplicative.toAdd (rho (1, d) X) = Multiplicative.toAdd X * (mat d)ᵀ := by
  rw [toAdd_rho]
  simp [mat_one]

theorem exists_ne_one_entry {c : ↥SL32} (hc : c ≠ 1) :
    ∃ i j, mat c i j ≠ (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
  by_contra h
  push Not at h
  exact hc (Subtype.ext (Units.ext (Matrix.ext h)))

theorem eq_one_of_ne_zero {z : ZMod 2} (hz : z ≠ 0) : z = 1 := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) z with h | h
  · exact absurd h hz
  · exact h

theorem eq_zero_of_fix_pair {c d D : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hcD : c * D = D)
    (hDd : D * dᵀ = D) {i j i' j' : Fin 3}
    (hij : c i j ≠ (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j)
    (hij' : d i' j' ≠ (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i' j')
    (hD : ∀ r k, r ≠ j → k ≠ j' → D r k = 0) : D = 0 := by
  have hN : (c - 1) * D = 0 := by rw [Matrix.sub_mul, hcD, Matrix.one_mul, sub_self]
  have hN' : D * (d - 1)ᵀ = 0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, hDd, Matrix.mul_one, sub_self]
  have hNij : (c - 1) i j = 1 :=
    eq_one_of_ne_zero (by rw [Matrix.sub_apply, sub_ne_zero]; exact hij)
  have hNij' : (d - 1) i' j' = 1 :=
    eq_one_of_ne_zero (by rw [Matrix.sub_apply, sub_ne_zero]; exact hij')
  have hrow : ∀ k, k ≠ j' → D j k = 0 := by
    intro k hk
    have h := congrFun (congrFun hN i) k
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun l _ hl => by rw [hD l k hl hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), hNij, one_mul] at h
    exact h
  have hcol : ∀ r k, k ≠ j' → D r k = 0 := by
    intro r k hk
    by_cases hr : r = j
    · rw [hr]
      exact hrow k hk
    · exact hD r k hr hk
  have hcol' : ∀ r, D r j' = 0 := by
    intro r
    have h := congrFun (congrFun hN' r) i'
    rw [Matrix.mul_apply, Finset.sum_eq_single j' (fun k _ hk => by rw [hcol r k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ j') h), Matrix.transpose_apply, hNij', mul_one] at h
    exact h
  ext r k
  by_cases hk : k = j'
  · rw [hk]
    exact hcol' r
  · exact hcol r k hk

theorem card_fixV_le_sixteen {A : Subgroup (MulAut WMod)} {c d : ↥SL32} (hcA : rho (c, 1) ∈ A)
    (hdA : rho (1, d) ∈ A) (hc : c ≠ 1) (hd : d ≠ 1) : Nat.card ↥(fixV A) ≤ 16 := by
  classical
  obtain ⟨i, j, hij⟩ := exists_ne_one_entry hc
  obtain ⟨i', j', hij'⟩ := exists_ne_one_entry hd
  let φ : ↥(fixV A) → (Fin 2 → Fin 2 → ZMod 2) := fun w r k =>
    Multiplicative.toAdd (w : WMod) (j.succAbove r) (j'.succAbove k)
  have hfixc : ∀ w : ↥(fixV A),
      mat c * Multiplicative.toAdd (w : WMod) = Multiplicative.toAdd (w : WMod) := fun w => by
    exact (toAdd_rho_left c (w : WMod)).symm.trans (congrArg Multiplicative.toAdd (w.2 _ hcA))
  have hfixd : ∀ w : ↥(fixV A),
      Multiplicative.toAdd (w : WMod) * (mat d)ᵀ = Multiplicative.toAdd (w : WMod) := fun w => by
    exact (toAdd_rho_right d (w : WMod)).symm.trans (congrArg Multiplicative.toAdd (w.2 _ hdA))
  have hφ : Function.Injective φ := by
    intro w w' hww
    set D := Multiplicative.toAdd (w : WMod) - Multiplicative.toAdd (w' : WMod) with hD
    have h1 : mat c * D = D := by rw [hD, Matrix.mul_sub, hfixc w, hfixc w']
    have h2 : D * (mat d)ᵀ = D := by rw [hD, Matrix.sub_mul, hfixd w, hfixd w']
    have h3 : ∀ r k, r ≠ j → k ≠ j' → D r k = 0 := by
      intro r k hr hk
      obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hr
      obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hk
      have := congrFun (congrFun hww s) t
      rw [hD, Matrix.sub_apply, sub_eq_zero]
      exact this
    have hD0 := eq_zero_of_fix_pair h1 h2 hij hij' h3
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact sub_eq_zero.mp hD0
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card (Fin 2 → Fin 2 → ZMod 2) = 16 := by
    simp [Nat.card_eq_fintype_card]
  rw [h2] at h1
  exact h1

end CFSG.Quasithin.Vol2.Ch10.C3
