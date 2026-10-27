module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Fan86

@[expose] def shiftHom {A : Type*} [CommGroup A] (σ : MulAut A) : A →* A :=
  MonoidHom.mk' (fun a => σ a * a⁻¹) fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem shiftHom_apply {A : Type*} [CommGroup A] (σ : MulAut A) (a : A) :
    shiftHom σ a = σ a * a⁻¹ := rfl

theorem card_closure_le_thirtytwo {A : Type*} [CommGroup A] (hsq : ∀ a : A, a * a = 1)
    (d : Fin 5 → A) : Nat.card (Subgroup.closure (Set.range d)) ≤ 32 := by
  classical
  let φ : (Fin 5 → ZMod 2) → A := fun e => ∏ k, d k ^ (e k).val
  have hpow : ∀ (a : A) (n : ℕ), a ^ n = a ^ (n % 2) := fun a n => by
    conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, sq, hsq a, one_pow, mul_one]
  have hadd : ∀ e e' : Fin 5 → ZMod 2, φ e * φ e' = φ (e + e') := fun e e' => by
    simp only [φ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, hpow (d k) ((e k).val + (e' k).val), Pi.add_apply, ZMod.val_add]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  have hφsq : ∀ e, φ e * φ e = 1 := fun e => by
    have : e + e = 0 := funext fun k => h2 (e k)
    rw [hadd, this]
    simp [φ]
  have hmem : ∀ g ∈ Subgroup.closure (Set.range d), ∃ e, φ e = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨Pi.single k 1, ?_⟩
      simp only [φ]
      rw [Finset.prod_eq_single k]
      · have : (Pi.single k (1 : ZMod 2) : Fin 5 → ZMod 2) k = 1 := by simp
        rw [this, show (1 : ZMod 2).val = 1 by decide, pow_one]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    | one => exact ⟨0, by simp [φ]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨e, rfl⟩ := hx
      obtain ⟨e', rfl⟩ := hy
      exact ⟨e + e', (hadd e e').symm⟩
    | inv x _ hx =>
      obtain ⟨e, rfl⟩ := hx
      exact ⟨e, eq_inv_of_mul_eq_one_left (hφsq e)⟩
  have hcl : ∀ e, φ e ∈ Subgroup.closure (Set.range d) := fun e =>
    Subgroup.prod_mem _ fun k _ =>
      Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self k)) _
  have hsurj : Function.Surjective
      (fun e : Fin 5 → ZMod 2 => (⟨φ e, hcl e⟩ : Subgroup.closure (Set.range d))) := by
    rintro ⟨g, hg⟩
    obtain ⟨e, he⟩ := hmem g hg
    exact ⟨e, Subtype.ext he⟩
  calc Nat.card (Subgroup.closure (Set.range d)) ≤ Nat.card (Fin 5 → ZMod 2) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = 32 := by simp [Nat.card_eq_fintype_card]

variable {A : Type*} [CommGroup A] (σ : MulAut A) (hσ : σ ^ 5 = 1)
include hσ

theorem norm_shiftHom (a : A) : ∏ k : Fin 5, (σ ^ (k : ℕ)) (shiftHom σ a) = 1 := by
  have h := Finset.prod_range_div (fun i => (σ ^ i) a) 5
  simp only [hσ, pow_zero, MulAut.one_apply, div_self'] at h
  rw [Fin.prod_univ_eq_prod_range (fun k => (σ ^ k) (shiftHom σ a)) 5]
  rw [← h]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [shiftHom_apply, map_mul, map_inv, div_eq_mul_inv, pow_succ, MulAut.mul_apply]

theorem shiftHom_fix (hsq : ∀ a : A, a * a = 1) {v : A} (hv : v ∈ (shiftHom σ).range)
    (hσv : σ v = v) : v = 1 := by
  obtain ⟨a, rfl⟩ := hv
  have h1 := norm_shiftHom σ hσ a
  have h2 : ∀ k : ℕ, (σ ^ k) (shiftHom σ a) = shiftHom σ a := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hσv, ih]
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have e : shiftHom σ a ^ 5 = shiftHom σ a := by
    have hv2 : shiftHom σ a ^ 2 = 1 := by rw [sq]; exact hsq _
    rw [show 5 = 2 + 2 + 1 from rfl, pow_add, pow_add, hv2, one_mul, one_mul, pow_one]
  rw [← e]
  exact h1

omit hσ in
theorem index_ker_shiftHom [Finite A] (hσ : σ ^ 5 = 1) (hsq : ∀ a : A, a * a = 1) (z c : A)
    (hz : σ z = z) (hc : σ c ≠ c)
    (hgen : Subgroup.closure ({z} ∪ Set.range fun k : Fin 5 => (σ ^ (k : ℕ)) c) = ⊤) :
    (shiftHom σ).ker.index = 16 := by
  classical
  rw [Subgroup.index_ker]
  set T := shiftHom σ with hT
  let d : Fin 5 → A := fun k => T ((σ ^ (k : ℕ)) c)
  have hrange : T.range = Subgroup.closure (Set.range d) := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg | hg, rfl⟩
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        have : T g = 1 := by rw [hT, shiftHom_apply, hz, mul_inv_cancel]
        rw [this]
        exact one_mem _
      · obtain ⟨k, rfl⟩ := hg
        exact Subgroup.subset_closure ⟨k, rfl⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨_, rfl⟩
  have hle : Nat.card T.range ≤ 32 := by
    rw [hrange]
    exact card_closure_le_thirtytwo hsq d
  have hne : Nat.card T.range ≠ 1 := by
    intro h
    have hb := Subgroup.card_eq_one.1 h
    have : T c ∈ T.range := ⟨c, rfl⟩
    rw [hb] at this
    have h1 : T c = 1 := Subgroup.mem_bot.1 this
    apply hc
    rw [hT, shiftHom_apply] at h1
    exact (mul_inv_eq_one.1 h1)
  have hmapD : ∀ v ∈ T.range, σ v ∈ T.range := by
    rintro _ ⟨a, rfl⟩
    refine ⟨σ a, ?_⟩
    simp [hT, shiftHom_apply, map_mul, map_inv]
  let f : T.range → T.range := fun v => ⟨σ v, hmapD v v.2⟩
  have hf_inj : Function.Injective f := fun u v h =>
    Subtype.ext (σ.injective (congrArg Subtype.val h))
  let σD : Equiv.Perm T.range := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf_inj)
  have hσD : ∀ (n : ℕ) (v : T.range), ((σD ^ n) v : A) = (σ ^ n) v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hσD5 : σD ^ 5 = 1 := Equiv.ext fun v => Subtype.ext (by rw [hσD, hσ]; rfl)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fintype T.range := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σD)
    (by rw [pow_one]; exact hσD5)
  have hsupp : σD.supportᶜ = {1} := by
    ext v
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro h
      exact Subtype.ext (shiftHom_fix σ hσ hsq v.2 (congrArg Subtype.val h))
    · rintro rfl
      exact Subtype.ext (by simp [σD, f])
  rw [hsupp, Finset.card_singleton, ← Nat.card_eq_fintype_card] at hmod
  have h2 : IsPGroup 2 T.range := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa [pow_two] using hsq g.1)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
  rw [hn] at hle hne hmod ⊢
  have hn6 : n < 6 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
    omega
  interval_cases n <;> simp_all [Nat.ModEq]

end CFSG.Quasithin.Fan86
