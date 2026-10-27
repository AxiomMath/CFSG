module

public import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.Transvection.OddModelSU3
import CFSG.Timmesfeld.Transvection.OddSU3Torus

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Universal.SpecialLinear CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)

variable {n : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

private theorem rootHom_inv {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (c : F) :
    (rootHom σ hσ hab ha hb (Multiplicative.ofAdd c))⁻¹ =
      rootHom σ hσ hab ha hb (Multiplicative.ofAdd (-c)) := by
  rw [← MonoidHom.map_inv, ← ofAdd_neg]

theorem shortWeyl_inv_eq_shortWeyl_neg {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (c : F) :
    (shortWeyl σ hσ hab ha hb c)⁻¹ = shortWeyl σ hσ hab ha hb (-c) := by
  rw [shortWeyl_def, shortWeyl_def, _root_.mul_inv_rev, _root_.mul_inv_rev,
    rootHom_inv hσ hab ha hb c, rootHom_inv hσ hab.symm hb ha (-c⁻¹)]
  rw [mul_assoc]
  simp only [inv_neg, neg_neg]

theorem shortTorus_mul {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (hba : b ≠ Fin.rev a) {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    shortTorus σ hσ hab ha hb (c * c') =
      shortTorus σ hσ hab ha hb c * shortTorus σ hσ hab ha hb c' := by
  apply mat_injective
  rw [map_mul, mat_apply, mat_apply, mat_apply,
    coe_shortTorus σ hσ hab ha hb hba (mul_ne_zero hc hc'),
    coe_shortTorus σ hσ hab ha hb hba hc, coe_shortTorus σ hσ hab ha hb hba hc',
    diagonal_mul_diagonal]
  congr 1
  funext s
  simp only [shortTorusFun]
  split_ifs <;> (try simp only [map_mul]) <;> ring

private theorem shortSign_shortTorusFun {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {κ c : F} (hκ : κ ≠ 0) (hc : c ≠ 0) :
    (fun s => shortSign σ a b (-κ)
      ((Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) s) *
        shortSign σ a b (κ * c) s) = shortTorusFun σ b a c := by
  funext s
  have hab' : a ≠ Fin.rev b := fun h => hba (by rw [h, Fin.rev_rev])
  have hb'a : Fin.rev b ≠ a := fun h => hba (by
    have := congrArg Fin.rev h
    simpa using this)
  have hba_ne : b ≠ a := Ne.symm hab
  have hbb : Fin.rev b ≠ b := hb.symm
  have haa : Fin.rev a ≠ a := ha.symm
  have hrev : Fin.rev b ≠ Fin.rev a := fun h => hab (Fin.rev_injective h.symm)
  have ha'b : Fin.rev a ≠ b := Ne.symm hba
  have hp_a : (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) a = b := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne ha hab', Equiv.swap_apply_left]
  have hp_b : (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) b = a := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hba hb, Equiv.swap_apply_right]
  have hp_a' : (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) (Fin.rev a) =
      Fin.rev b := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hb'a hb.symm]
  have hp_b' : (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) (Fin.rev b) =
      Fin.rev a := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne ha.symm (Ne.symm hba)]
  have hσκ : σ κ ≠ 0 := (map_ne_zero σ).mpr hκ
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  by_cases hsa : s = a
  · rw [hsa, hp_a]
    simp only [shortSign, shortTorusFun, hab, hba_ne, ha, haa, hb, hbb, hba, ha'b, hab',
      hb'a, hrev, hrev.symm, ite_true, ite_false]
    field_simp
  by_cases hsb : s = b
  · rw [hsb, hp_b]
    simp only [shortSign, shortTorusFun, hab, hba_ne, ha, haa, hb, hbb, hba, ha'b, hab',
      hb'a, hrev, hrev.symm, ite_true, ite_false]
    field_simp
  by_cases hsa' : s = Fin.rev a
  · rw [hsa', hp_a']
    simp only [shortSign, shortTorusFun, hab, hba_ne, ha, haa, hb, hbb, hba, ha'b, hab',
      hb'a, hrev, hrev.symm, ite_true, ite_false]
    field_simp [hσκ, hσc]
    simp only [map_mul, map_neg]
    ring
  by_cases hsb' : s = Fin.rev b
  · rw [hsb', hp_b']
    simp only [shortSign, shortTorusFun, hab, hba_ne, ha, haa, hb, hbb, hba, ha'b, hab',
      hb'a, hrev, hrev.symm, ite_true, ite_false]
    field_simp [hσκ, hσc]
    simp only [map_mul, map_neg]
    ring
  have hp_s : (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) s = s := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hsa' hsb',
      Equiv.swap_apply_of_ne_of_ne hsa hsb]
  rw [hp_s]
  simp only [shortSign, shortTorusFun, hsa, hsb, hsa', hsb', hba_ne, haa, hbb, hba, ha'b,
    hab', hb'a, hrev, ite_false]
  ring

theorem mat_shortWeyl_inv_mul_shortWeyl {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {κ c : F} (hκ : κ ≠ 0) (hc : c ≠ 0) :
    mat σ n ((shortWeyl σ hσ hab ha hb κ)⁻¹ * shortWeyl σ hσ hab ha hb (κ * c)) =
      Matrix.diagonal (shortTorusFun σ b a c) := by
  rw [shortWeyl_inv_eq_shortWeyl_neg hσ hab ha hb κ, map_mul, mat_apply, mat_apply,
    coe_shortWeyl σ hσ hab ha hb hba (neg_ne_zero.mpr hκ),
    coe_shortWeyl σ hσ hab ha hb hba (mul_ne_zero hκ hc), signedPerm_mul_signedPerm]
  have hp : (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) *
      (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) = 1 :=
    swap_mul_swap_rev_mul_self ha hb hba
  rw [hp, signedPerm_one]
  congr 1
  exact shortSign_shortTorusFun hab ha hb hba hκ hc

theorem shortWeyl_inv_mul_shortWeyl_mul {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {κ c : F} (hκ : κ ≠ 0) (hc : c ≠ 0) :
    (shortWeyl σ hσ hab ha hb κ)⁻¹ * shortWeyl σ hσ hab ha hb (κ * c) =
      (shortWeyl σ hσ hab ha hb 1)⁻¹ * shortWeyl σ hσ hab ha hb c := by
  apply mat_injective
  rw [mat_shortWeyl_inv_mul_shortWeyl hσ hab ha hb hba hκ hc]
  simpa only [one_mul] using
    (mat_shortWeyl_inv_mul_shortWeyl hσ hab ha hb hba one_ne_zero hc).symm

theorem exists_conj_suHeis_eq_pow_three {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hFn : Nat.card F = (2 ^ n) ^ 2) {b : F}
    (hb : unitaryInvolution F 2 n b * b = 1) :
    ∃ h : SU (unitaryInvolution F 2 n) 3,
      (∀ u v : F,
        v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        h * suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v * h⁻¹ =
        suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) (b ^ 3 * u) v) ∧
      ∀ (a : Fin (3 / 2) ⊕ Fin (3 / 2)) (c : F),
        h * suLong (unitaryInvolution F 2 n) a c * h⁻¹ =
          suLong (unitaryInvolution F 2 n) a c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  have hb0 : b ≠ 0 := by
    rintro rfl
    simpa using hb
  have hσb : σ b = b⁻¹ := eq_inv_of_mul_eq_one_left hb
  have hHcard : Nat.card (uc22pwsu3H σ) = Nat.card Fˣ := by
    rw [card_levelTorus_three (p := 2) (f := n) hFn,
      CFSG.ClassicalGroups.Unitary.card_units_of_card hFn]
  obtain ⟨h, -, hmat⟩ := uc22pwsu3H_exists_entry hHcard (Units.mk0 b hb0)
  let d : Fin 3 → F := ![b, σ b / b, (σ b)⁻¹]
  have hmatd : mat σ 3 h = diagonal d := by
    simpa [d, Units.val_mk0] using hmat
  have hd : ∀ s, σ (d s) * d (Fin.rev s) = 1 := by
    intro s
    fin_cases s <;> simp [d, hσ, hσb, hb0] <;> field_simp [hσb, hb0]
  refine ⟨h, ?_, ?_⟩
  · intro u v huv
    rw [conj_suHeis_of_mat_diagonal hσ (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) hmatd hd
      (Sum.inl (0 : Fin (3 / 2))) huv]
    have h1 : d 0 * u * (d 1)⁻¹ = b ^ 3 * u := by
      rw [show d 0 = b by rfl, show d 1 = σ b / b by rfl, hσb]
      field_simp [hb0]
    have h2 : d 0 * v * (d 2)⁻¹ = v := by
      rw [show d 0 = b by rfl, show d 2 = (σ b)⁻¹ by rfl, hσb]
      field_simp [hb0]
    change suHeis σ hσ (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2)))
        (d 0 * u * (d 1)⁻¹) (d 0 * v * (d 2)⁻¹) =
      suHeis σ hσ (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2)))
        (b ^ 3 * u) v
    rw [h1, h2]
  · intro a c
    rw [conj_suLong_of_mat_diagonal hmatd hd a c]
    rcases a with a | a
    · fin_cases a
      change suLong σ (Sum.inl (0 : Fin (3 / 2))) (d 0 * c * (d 2)⁻¹) =
        suLong σ (Sum.inl (0 : Fin (3 / 2))) c
      rw [show d 0 * c * (d 2)⁻¹ = c by
        rw [show d 0 = b by rfl, show d 2 = (σ b)⁻¹ by rfl, hσb]
        field_simp [hb0]]
    · fin_cases a
      change suLong σ (Sum.inr (0 : Fin (3 / 2))) (d 2 * c * (d 0)⁻¹) =
        suLong σ (Sum.inr (0 : Fin (3 / 2))) c
      rw [show d 2 * c * (d 0)⁻¹ = c by
        rw [show d 0 = b by rfl, show d 2 = (σ b)⁻¹ by rfl, hσb]
        field_simp [hb0]]

theorem eq_and_eq_of_map_suHeis_eq {H : Type*} [Group H] {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker)) {u v u' v' : F}
    (h : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    (h' : v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0)
    (he : θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v) =
        θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u' v')) :
    u = u' ∧ v = v' := by
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  have hm : ¬ Even 3 := Nat.not_even_iff_odd.mpr ⟨1, rfl⟩
  have hmem : suHeis σ hσ hm (Sum.inl (0 : Fin (3 / 2))) u v =
      suHeis σ hσ hm (Sum.inl (0 : Fin (3 / 2))) u' v' :=
    CFSG.Timmesfeld.Transvection.eq_of_mem_heis_of_map_eq hFn hθk
      (suHeis_mem hσ hm toStd_three_single u v)
      (suHeis_mem hσ hm toStd_three_single u' v') he
  have hmat := congrArg (mat σ 3) hmem
  constructor
  · have h1 := mat_suHeis_apply_mid hσ hm (a := Sum.inl (0 : Fin (3 / 2))) h
    have h2 := mat_suHeis_apply_mid hσ hm (a := Sum.inl (0 : Fin (3 / 2))) h'
    exact h1.symm.trans ((congrFun (congrFun hmat (crd (Sum.inl (0 : Fin (3 / 2)))))
      (midIdx 3 hm)).trans h2)
  · have h1 := mat_suHeis_apply_swap hσ hm (a := Sum.inl (0 : Fin (3 / 2))) h
    have h2 := mat_suHeis_apply_swap hσ hm (a := Sum.inl (0 : Fin (3 / 2))) h'
    exact h1.symm.trans ((congrFun (congrFun hmat (crd (Sum.inl (0 : Fin (3 / 2)))))
      (crd (Sum.swap (Sum.inl (0 : Fin (3 / 2)))))).trans h2)

end CFSG.Timmesfeld.Transvection.Pres
