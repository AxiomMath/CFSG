module

public import CFSG.Quasithin.Background.HL3WrNorm

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H13
open scoped Matrix

theorem mem_fixV_zpowers {x : MulAut WMod} {w : WMod} :
    w ∈ fixV (Subgroup.zpowers x) ↔ x w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_fixV_conj (φ x : MulAut WMod) :
    Nat.card ↥(fixV (Subgroup.zpowers (φ * x * φ⁻¹))) = Nat.card ↥(fixV (Subgroup.zpowers x)) :=
  CFSG.Quasithin.card_fixV_zpowers_conj φ x

theorem card_WMod : Nat.card WMod = 2 ^ 9 := by
  have h : Nat.card WMod = Nat.card (Fin 3 → Fin 3 → ZMod 2) := rfl
  rw [h, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  norm_num

theorem eq_zero_of_rows {a b X : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hb : b * b = 1)
    (hX : a * X * bᵀ = X) {i j : Fin 3} (hij : a i j ≠ (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j)
    (hrows : ∀ r, r ≠ j → X r = 0) : X = 0 := by
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hbt : bᵀ * bᵀ = 1 := by rw [← Matrix.transpose_mul, hb, Matrix.transpose_one]
  have haX : a * X = X * bᵀ := by
    calc a * X = a * X * (bᵀ * bᵀ) := by rw [hbt, Matrix.mul_one]
      _ = X * bᵀ := by rw [← Matrix.mul_assoc, hX]
  have hlhs : ∀ k, (a * X) i k = a i j * X j k := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · intro l _ hl
      rw [hrows l hl, Pi.zero_apply, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  by_cases hij' : i = j
  · subst hij'
    have haii : a i i = 0 := by
      rw [Matrix.one_apply_eq] at hij
      rcases h01 (a i i) with h | h
      · exact h
      · exact absurd h hij
    have hrow : ∀ k, (X * bᵀ) i k = 0 := by
      intro k
      rw [← haX, hlhs, haii, zero_mul]
    have hXi : X i = 0 := by
      ext k
      have h1 : (X * bᵀ * bᵀ) i k = 0 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_eq_zero fun l _ => by rw [hrow l, zero_mul]
      rw [Matrix.mul_assoc, hbt, Matrix.mul_one] at h1
      exact h1
    ext r k
    by_cases hr : r = i
    · subst hr
      rw [hXi]
      rfl
    · rw [hrows r hr]
      rfl
  · have haij : a i j = 1 := by
      rw [Matrix.one_apply_ne hij'] at hij
      rcases h01 (a i j) with h | h
      · exact absurd h hij
      · exact h
    have hXj : X j = 0 := by
      ext k
      have h1 : (a * X) i k = (X * bᵀ) i k := by rw [haX]
      rw [hlhs, haij, one_mul, Matrix.mul_apply] at h1
      rw [h1]
      exact Finset.sum_eq_zero fun l _ => by rw [hrows i hij', Pi.zero_apply, zero_mul]
    ext r k
    by_cases hr : r = j
    · subst hr
      rw [hXj]
      rfl
    · rw [hrows r hr]
      rfl

theorem card_fixV_rho_le {a b : ↥SL32} (hb : b * b = 1) (ha1 : a ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) ≤ 64 := by
  classical
  have hne : ∃ i j, mat a i j ≠ (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
    by_contra h
    push Not at h
    apply ha1
    apply Subtype.ext
    apply Units.ext
    exact Matrix.ext h
  obtain ⟨i, j, hij⟩ := hne
  have hbm : mat b * mat b = 1 := by rw [← mat_mul, hb, mat_one]
  let φ : ↥(fixV (Subgroup.zpowers (rho (a, b)))) → (Fin 2 → Fin 3 → ZMod 2) :=
    fun w r => Multiplicative.toAdd (w : WMod) (j.succAbove r)
  have hfix : ∀ w : ↥(fixV (Subgroup.zpowers (rho (a, b)))),
      mat a * Multiplicative.toAdd (w : WMod) * (mat b)ᵀ = Multiplicative.toAdd (w : WMod) := by
    intro w
    have h := mem_fixV_zpowers.mp w.2
    exact congrArg Multiplicative.toAdd h
  have hφ : Function.Injective φ := by
    intro w w' hww
    set D := Multiplicative.toAdd (w : WMod) - Multiplicative.toAdd (w' : WMod) with hD
    have hDfix : mat a * D * (mat b)ᵀ = D := by
      rw [hD, Matrix.mul_sub, Matrix.sub_mul, hfix w, hfix w']
    have hDrows : ∀ r, r ≠ j → D r = 0 := by
      intro r hr
      obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hr
      have := congrFun hww s
      rw [hD]
      ext k
      simp only [Matrix.sub_apply, Pi.zero_apply]
      rw [sub_eq_zero]
      exact congrFun this k
    have hD0 := eq_zero_of_rows hbm hDfix hij hDrows
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact sub_eq_zero.mp hD0
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card (Fin 2 → Fin 3 → ZMod 2) = 64 := by
    simp [Nat.card_eq_fintype_card]
  rw [h2] at h1
  exact h1

theorem card_fixV_rho_tau_le (a : ↥SL32) :
    Nat.card ↥(fixV (Subgroup.zpowers (rho (a, a⁻¹) * tau))) ≤ 64 := by
  classical
  have hfix : ∀ w : ↥(fixV (Subgroup.zpowers (rho (a, a⁻¹) * tau))),
      mat a * (Multiplicative.toAdd (w : WMod))ᵀ * (mat a⁻¹)ᵀ =
        Multiplicative.toAdd (w : WMod) := by
    intro w
    have h := mem_fixV_zpowers.mp w.2
    exact congrArg Multiplicative.toAdd h
  have hsym : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), mat a * Xᵀ * (mat a⁻¹)ᵀ = X →
      (X * (mat a)ᵀ)ᵀ = X * (mat a)ᵀ := by
    intro X hX
    have h1 : mat a * Xᵀ = X * (mat a)ᵀ := by
      calc mat a * Xᵀ = mat a * Xᵀ * ((mat a⁻¹)ᵀ * (mat a)ᵀ) := by
            rw [← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one, Matrix.mul_one]
        _ = X * (mat a)ᵀ := by rw [← Matrix.mul_assoc, hX]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, h1]
  let idx : Fin 6 → Fin 3 × Fin 3 := ![(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]
  let φ : ↥(fixV (Subgroup.zpowers (rho (a, a⁻¹) * tau))) → (Fin 6 → ZMod 2) :=
    fun w p => (Multiplicative.toAdd (w : WMod) * (mat a)ᵀ) (idx p).1 (idx p).2
  have hφ : Function.Injective φ := by
    intro w w' hww
    set D := Multiplicative.toAdd (w : WMod) - Multiplicative.toAdd (w' : WMod) with hD
    have hDfix : mat a * Dᵀ * (mat a⁻¹)ᵀ = D := by
      rw [hD, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul, hfix w, hfix w']
    set Z := D * (mat a)ᵀ with hZ
    have hZs : Zᵀ = Z := hsym D hDfix
    have hZu : ∀ p : Fin 6, Z (idx p).1 (idx p).2 = 0 := by
      intro p
      have h := congrFun hww p
      simp only [φ] at h
      rw [hZ, hD, Matrix.sub_mul, Matrix.sub_apply, h, sub_self]
    have hZ0 : Z = 0 := by
      have e : ∀ r c : Fin 3, Z r c = Z c r := fun r c => by
        rw [← Matrix.transpose_apply Z c r, hZs]
      ext r c
      fin_cases r <;> fin_cases c
      · exact hZu 0
      · exact hZu 1
      · exact hZu 2
      · rw [e]; exact hZu 1
      · exact hZu 3
      · exact hZu 4
      · rw [e]; exact hZu 2
      · rw [e]; exact hZu 4
      · exact hZu 5
    have hD0 : D = 0 := by
      calc D = D * ((mat a)ᵀ * (mat a⁻¹)ᵀ) := by
            rw [← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one, Matrix.mul_one]
        _ = Z * (mat a⁻¹)ᵀ := by rw [hZ, Matrix.mul_assoc]
        _ = 0 := by rw [hZ0, Matrix.zero_mul]
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact sub_eq_zero.mp hD0
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card (Fin 6 → ZMod 2) = 64 := by
    simp [Nat.card_eq_fintype_card]
  rw [h2] at h1
  exact h1

theorem card_fixV_le {s : MulAut WMod} (hs : s ∈ norm) (hs2 : orderOf s = 2) :
    Nat.card ↥(fixV (Subgroup.zpowers s)) ≤ 64 := by
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2, sq] at h
    exact h
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.mp hs
  · have hgg : g * g = 1 := rho_injective (by rw [map_mul, hss, map_one])
    have hg1 : g ≠ 1 := fun h => hs1 (by rw [h, map_one])
    have h2 : g.2 * g.2 = 1 := congrArg Prod.snd hgg
    have h1 : g.1 * g.1 = 1 := congrArg Prod.fst hgg
    by_cases hg1' : g.1 = 1
    · have hg2 : g.2 ≠ 1 := fun h => hg1 (Prod.ext hg1' h)
      rw [← card_fixV_conj tau, tau_conj_rho]
      have e : g.swap = (g.2, g.1) := rfl
      rw [e]
      exact card_fixV_rho_le h1 hg2
    · exact card_fixV_rho_le h2 hg1'
  · have hg : g.1 * g.2 = 1 := by
      have h : rho (g * g.swap) = 1 := by
        rw [map_mul]
        calc rho g * rho g.swap = rho g * (tau * rho g * tau⁻¹) := by rw [tau_conj_rho]
          _ = rho g * tau * (rho g * tau) * (tau⁻¹ * tau⁻¹) := by group
          _ = 1 := by rw [hss, one_mul, tau_inv, tau_mul_self]
      have h' := congrArg Prod.fst (rho_injective (h.trans (map_one rho).symm))
      exact h'
    have hg2 : g.2 = g.1⁻¹ := eq_inv_of_mul_eq_one_right hg
    have e : g = (g.1, g.1⁻¹) := Prod.ext rfl hg2
    rw [e]
    exact card_fixV_rho_tau_le g.1

theorem three_le_mParam {X : Subgroup (MulAut WMod)} (hX2 : X ≤ norm) : 3 ≤ E3.mParam X := by
  classical
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut WMod), t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro n ⟨s, hsX, hs2, rfl⟩
    have h64 := card_fixV_le (hX2 hsX) hs2
    refine SL3Pair.le_rkIdx_of_card_mul_le card_WMod _ ?_
    calc Nat.card ↥(fixV (Subgroup.zpowers s)) * 2 ^ 3 ≤ 64 * 2 ^ 3 :=
          Nat.mul_le_mul_right _ h64
      _ = 2 ^ 9 := by norm_num
  · rw [rk, card_WMod]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.prime_pow]
    norm_num

theorem H44_L3Wreath_mParam {V : Type*} [CommGroup V] {H M : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) : 3 ≤ E3.mParam M := by
  obtain ⟨e, he⟩ := exists_model hreal
  have h2 : M.map (congrHom e) ≤ norm := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut WMod)) :
          Set (MulAut WMod)) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := congrHom e) hMN).trans (le_of_eq h3)
    have h5 := congrArg (fun K : Subgroup (MulAut WMod) => Subgroup.normalizer
      (K : Set (MulAut WMod))) he
    exact h4.trans (le_of_eq h5)
  have h6 := mParam_map_congrHom e M
  rw [← h6]
  exact three_le_mParam h2

end L3Wr

end H

end CFSG.Quasithin
