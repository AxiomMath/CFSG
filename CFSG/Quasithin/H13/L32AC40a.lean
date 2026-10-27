module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.L32A.C.A5Mod

theorem alt5_not_comm : ∀ e a : alternatingGroup (Fin 5), e * e = 1 → e ≠ 1 → a ^ 3 = 1 →
    a ≠ 1 → e * a ≠ a * e := by
  decide +kernel

theorem alt5_exists_conj : ∀ u : alternatingGroup (Fin 5), u * u = 1 → u ≠ 1 →
    ∃ g : alternatingGroup (Fin 5), (u * (g * u * g⁻¹)) ^ 5 = 1 ∧ u * (g * u * g⁻¹) ≠ 1 := by
  decide +kernel

variable {X : Type*} [CommGroup X]

@[expose] def commHom (σ : MulAut X) : X →* X where
  toFun x := σ x * x⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv]
    rw [mul_mul_mul_comm]

theorem commHom_apply (σ : MulAut X) (x : X) : commHom σ x = σ x * x⁻¹ := rfl

theorem apply_eq_commHom_mul (σ : MulAut X) (x : X) : σ x = commHom σ x * x := by
  rw [commHom_apply, inv_mul_cancel_right]

theorem pow_mem_of_comm_mem {σ : MulAut X} {N : Subgroup X} (hN : ∀ x, commHom σ x ∈ N) (n : ℕ)
    (x : X) : commHom (σ ^ n) x ∈ N := by
  induction n generalizing x with
  | zero => simp [commHom_apply]
  | succ n ih =>
    have e : commHom (σ ^ (n + 1)) x = commHom σ ((σ ^ n) x) * commHom (σ ^ n) x := by
      simp only [commHom_apply, pow_succ', MulAut.mul_apply]
      group
    rw [e]
    exact N.mul_mem (hN _) (ih x)

theorem card_sup_le [Finite X] (A B : Subgroup X) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  let f : ↥A × ↥B →* X := A.subtype.coprod B.subtype
  have hle : A ⊔ B ≤ f.range := by
    refine sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), by simp [f]⟩)
      (fun b hb => ⟨(1, ⟨b, hb⟩), by simp [f]⟩)
  calc Nat.card ↥(A ⊔ B) ≤ Nat.card f.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (↥A × ↥B) := Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

variable [Finite X]

theorem pow_six_apply_of_mem {σ : MulAut X} {N : Subgroup X} (hN4 : Nat.card N ≤ 4)
    (hσN : ∀ y ∈ N, σ y ∈ N) {y : X} (hy : y ∈ N) : (σ ^ 6) y = y := by
  classical
  by_cases hy1 : y = 1
  · rw [hy1, map_one]
  have hmem : ∀ i : ℕ, (σ ^ i) y ∈ N := by
    intro i
    induction i with
    | zero => simpa using hy
    | succ i ih =>
      rw [pow_succ', MulAut.mul_apply]
      exact hσN _ ih
  have hne : ∀ i : ℕ, (σ ^ i) y ≠ 1 := fun i h => hy1 (by
    have := congrArg (σ ^ i).symm h
    simpa using this)
  have : Fintype X := Fintype.ofFinite X
  set t : Finset X := (Finset.univ.filter fun z => z ∈ N).erase 1 with ht
  have hcardN : (Finset.univ.filter fun z => z ∈ N).card = Nat.card N := by
    rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]
  have htc : t.card < (Finset.range 4).card := by
    rw [Finset.card_range, ht, Finset.card_erase_of_mem (by simp [N.one_mem]), hcardN]
    have : 0 < Nat.card N := Nat.card_pos
    omega
  obtain ⟨i, hi, j, hj, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to htc
    (f := fun i : ℕ => (σ ^ i) y) (fun i _ =>
      Finset.mem_erase.mpr ⟨hne i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem i⟩⟩)
  simp only [Finset.mem_range] at hi hj
  have key : ∀ a b : ℕ, a < b → b < 4 → (σ ^ a) y = (σ ^ b) y → (σ ^ 6) y = y := by
    intro a b hab hb hfab
    have hd : (σ ^ (b - a)) y = y := by
      have h1 : (σ ^ b) y = (σ ^ a) ((σ ^ (b - a)) y) := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
      exact ((σ ^ a).injective (hfab.trans h1)).symm
    have hdvd : (b - a) ∣ 6 := by
      have h1 : 0 < b - a := Nat.sub_pos_of_lt hab
      have h2 : b - a < 4 := by omega
      interval_cases (b - a) <;> decide
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    clear hc
    induction c with
    | zero => simp
    | succ c ih => rw [pow_succ, MulAut.mul_apply, hd, ih]
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hj hfij
  · exact key j i h hi hfij.symm

theorem pow_twelve_eq_one (hX : ∀ x : X, x * x = 1) {u v : MulAut X}
    (hu2 : Nat.card (commHom u).range ≤ 2) (hv2 : Nat.card (commHom v).range ≤ 2) :
    (u * v) ^ 12 = 1 := by
  set N := (commHom u).range ⊔ (commHom v).range with hNdef
  have hN4 : Nat.card N ≤ 4 := (card_sup_le _ _).trans (Nat.mul_le_mul hu2 hv2)
  have hcomm : ∀ x, commHom (u * v) x ∈ N := by
    intro x
    have e : commHom (u * v) x = commHom u (v x) * commHom v x := by
      simp only [commHom_apply, MulAut.mul_apply]
      group
    rw [e]
    exact N.mul_mem (Subgroup.mem_sup_left ⟨v x, rfl⟩) (Subgroup.mem_sup_right ⟨x, rfl⟩)
  have hσN : ∀ y ∈ N, (u * v) y ∈ N := fun y hy => by
    rw [apply_eq_commHom_mul]
    exact N.mul_mem (hcomm y) hy
  set t := (u * v) ^ 6 with ht
  have htN : ∀ y ∈ N, t y = y := fun y hy => pow_six_apply_of_mem hN4 hσN hy
  have htc : ∀ x, commHom t x ∈ N := pow_mem_of_comm_mem hcomm 6
  have htt : t * t = 1 := by
    ext x
    rw [MulAut.mul_apply, MulAut.one_apply, apply_eq_commHom_mul t x, map_mul,
      htN _ (htc x), apply_eq_commHom_mul t x, ← mul_assoc, hX, one_mul]
  calc (u * v) ^ 12 = t * t := by rw [ht, ← pow_add]
    _ = 1 := htt

theorem four_le_card_range (hX : ∀ x : X, x * x = 1) {Γ : Subgroup (MulAut X)}
    (e : ↥Γ ≃* alternatingGroup (Fin 5)) {u : MulAut X} (hu : u ∈ Γ) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : 4 ≤ Nat.card (commHom u).range := by
  have hp : IsPGroup 2 X := fun x => ⟨1, by rw [pow_one, pow_two]; exact hX x⟩
  obtain ⟨n, hn⟩ := (hp.to_subgroup (commHom u).range).exists_card_eq
  have hne1 : n ≠ 0 := by
    rintro rfl
    apply hu1
    have hbot : (commHom u).range = ⊥ := Subgroup.card_eq_one.mp (by simpa using hn)
    ext x
    have h1 : commHom u x = 1 := by
      have : commHom u x ∈ (commHom u).range := ⟨x, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    rw [MulAut.one_apply, apply_eq_commHom_mul, h1, one_mul]
  have hne2 : n ≠ 1 := by
    rintro rfl
    set γu : ↥Γ := ⟨u, hu⟩ with hγu
    have hγu2 : γu * γu = 1 := Subtype.ext hu2
    have hγu1 : γu ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
    have hu'2 : e γu * e γu = 1 := by rw [← map_mul, hγu2, map_one]
    have hu'1 : e γu ≠ 1 := fun h => hγu1 (e.injective (h.trans (map_one e).symm))
    obtain ⟨g', hg5, hg1⟩ := alt5_exists_conj (e γu) hu'2 hu'1
    set γg : ↥Γ := e.symm g' with hγg
    set γv : ↥Γ := γg * γu * γg⁻¹ with hγv
    have hv2 : Nat.card (commHom (γv : MulAut X)).range ≤ 2 := by
      have hr : (commHom (γv : MulAut X)).range =
          (commHom u).range.map (γg : MulAut X).toMonoidHom := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨commHom u ((γg : MulAut X)⁻¹ x), ⟨_, rfl⟩, ?_⟩
          simp only [hγv, Subgroup.coe_mul, Subgroup.coe_inv, commHom_apply, MulAut.mul_apply,
            MulEquiv.coe_toMonoidHom, map_mul, map_inv, hγu]
          rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
        · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
          refine ⟨(γg : MulAut X) x, ?_⟩
          simp only [hγv, Subgroup.coe_mul, Subgroup.coe_inv, commHom_apply, MulAut.mul_apply,
            MulEquiv.coe_toMonoidHom, map_mul, map_inv, hγu]
          rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [hr, Subgroup.card_map_of_injective (γg : MulAut X).injective, hn, pow_one]
    have h12 := pow_twelve_eq_one hX (u := u) (v := (γv : MulAut X)) (by rw [hn, pow_one]) hv2
    have h12' : (γu * γv) ^ 12 = 1 := Subtype.ext (by simpa [hγu] using h12)
    have hev : e γv = g' * e γu * g'⁻¹ := by
      rw [hγv, map_mul, map_mul, map_inv, hγg, MulEquiv.apply_symm_apply]
    have hw12 : (e γu * (g' * e γu * g'⁻¹)) ^ 12 = 1 := by
      rw [← hev, ← map_mul, ← map_pow, h12', map_one]
    set w := e γu * (g' * e γu * g'⁻¹) with hw
    have h1 : orderOf w ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg5) (orderOf_dvd_of_pow_eq_one hw12)
      simpa using this
    exact hg1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  rw [hn]
  have : 2 ≤ n := by omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this

end CFSG.Quasithin.H13.L32A.C.A5Mod
