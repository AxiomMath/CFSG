module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open Polynomial Module CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem case5_two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  have : ((2 : ℕ) : (ZMod 2)[X]) = 0 := by
    rw [← C_eq_natCast]
    have : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [this, C_0]
  simpa using this

theorem case5_bez1 : (X^3 + X + 1 : (ZMod 2)[X]) * (X^4 + X + 1) + (X^3 + X^2) * (X^4 + X^3 + 1) = 1 := by
  have h := case5_two_eq_zero_poly
  linear_combination (exp := 1) (X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X) * h

theorem case5_bez2 : (1 : (ZMod 2)[X]) * (X^4 + X + 1) + X * (X^3 - 1) = 1 := by
  have h := case5_two_eq_zero_poly
  linear_combination (exp := 1) (X^4) * h

theorem case5_bez3 : (X^3 + X^2 + 1 : (ZMod 2)[X]) * (X^4 + X + 1) + (X^2 + X) * (X^5 - 1) = 1 := by
  have h := case5_two_eq_zero_poly
  linear_combination (exp := 1) (X^7 + X^6 + X^4 + X^3) * h

theorem case5_fac : (X^2 + X + 1 : (ZMod 2)[X]) * (X^4 + X + 1) * (X^4 + X^3 + 1) = X^10 + X^5 + 1 := by
  have h := case5_two_eq_zero_poly
  linear_combination (exp := 1) (X + X^2 + X^3 + 2 * X^4 + 2 * X^5 + 2 * X^6 + X^7 + X^8 + X^9) * h

omit [Finite V] in
theorem case5_pow_apply_eq (u : V ≃ₗ[ZMod 2] V) (n : ℕ) (v : V) :
    (u ^ n) v = ((u : V →ₗ[ZMod 2] V) ^ n) v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    simp [Module.End.mul_apply, ih]

omit [Finite V] in
theorem case5_orbit_free (u : V ≃ₗ[ZMod 2] V) (h15 : u ^ 15 = 1) {w : V}
    (hw : aeval (u : V →ₗ[ZMod 2] V) (X^4 + X + 1 : (ZMod 2)[X]) w = 0) (hw0 : w ≠ 0) :
    Function.Injective (fun k : Fin 15 => (u ^ (k : ℕ)) w) := by
  classical
  have key : ∀ n : ℕ, 1 ≤ n → n < 15 → (u ^ n) w = w → False := by
    intro n hn1 hn15 hfix
    let S := MulAction.stabilizer (V ≃ₗ[ZMod 2] V) w
    have hnS : u ^ n ∈ S := hfix
    have h15S : u ^ 15 ∈ S := by rw [h15]; exact S.one_mem
    have hg : u ^ (Nat.gcd n 15) ∈ S := by
      have : (u ^ (Nat.gcd n 15) : V ≃ₗ[ZMod 2] V) =
          (u ^ n) ^ (Nat.gcdA n 15) * (u ^ 15) ^ (Nat.gcdB n 15) := by
        rw [← zpow_natCast, Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul]
        simp
      rw [this]
      exact S.mul_mem (S.zpow_mem hnS _) (S.zpow_mem h15S _)
    have hcases : Nat.gcd n 15 = 1 ∨ Nat.gcd n 15 = 3 ∨ Nat.gcd n 15 = 5 := by
      interval_cases n <;> simp (config := {decide := true})
    have h35 : u ^ 3 ∈ S ∨ u ^ 5 ∈ S := by
      rcases hcases with h | h | h
      · rw [h, pow_one] at hg
        exact Or.inl (S.pow_mem hg 3)
      · rw [h] at hg; exact Or.inl hg
      · rw [h] at hg; exact Or.inr hg
    set U : Module.End (ZMod 2) V := (u : V →ₗ[ZMod 2] V) with hU
    have hker : w ∈ LinearMap.ker (aeval U (X^4 + X + 1 : (ZMod 2)[X])) := hw
    rcases h35 with h3 | h5
    · have h3' : (U ^ 3) w = w := by rw [← case5_pow_apply_eq]; exact h3
      have hk3 : w ∈ LinearMap.ker (aeval U (X^3 - 1 : (ZMod 2)[X])) := by
        simp [h3']
      have hd := Polynomial.disjoint_ker_aeval_of_isCoprime U
        (show IsCoprime (X^4 + X + 1 : (ZMod 2)[X]) (X^3 - 1) from ⟨1, X, by simpa using case5_bez2⟩)
      exact hw0 ((Submodule.disjoint_def.1 hd) w hker hk3)
    · have h5' : (U ^ 5) w = w := by rw [← case5_pow_apply_eq]; exact h5
      have hk5 : w ∈ LinearMap.ker (aeval U (X^5 - 1 : (ZMod 2)[X])) := by
        simp [h5']
      have hd := Polynomial.disjoint_ker_aeval_of_isCoprime U
        (show IsCoprime (X^4 + X + 1 : (ZMod 2)[X]) (X^5 - 1) from
          ⟨X^3 + X^2 + 1, X^2 + X, by simpa using case5_bez3⟩)
      exact hw0 ((Submodule.disjoint_def.1 hd) w hker hk5)
  have key2 : ∀ i j : ℕ, i < j → j < 15 → (u ^ i) w = (u ^ j) w → False := by
    intro i j hij hj h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine key (n + 1) (by omega) (by omega) ?_
    have h' : (u ^ i) w = (u ^ i) ((u ^ (n + 1)) w) := by
      rw [h]
      have : u ^ (i + n + 1) = u ^ i * u ^ (n + 1) := by rw [← pow_add]; ring_nf
      rw [this]; rfl
    exact ((u ^ i).injective h').symm
  intro a b hab
  by_contra hne
  have hne' : (a : ℕ) ≠ b := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact key2 a b hlt b.2 hab
  · exact key2 b a hlt a.2 hab.symm

theorem case5_finrank_ker_eq_of_adjoint (f : LinearMap.BilinForm (ZMod 2) V) (hf : f.Nondegenerate)
    (T S : Module.End (ZMod 2) V) (h : ∀ v w, f (T v) w = f v (S w)) :
    finrank (ZMod 2) (LinearMap.ker T) = finrank (ZMod 2) (LinearMap.ker S) := by
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let φ := f.toDual hf
  have hφ : ∀ v, φ (T v) = S.dualMap (φ v) := by
    intro v
    ext w
    simp [φ, LinearMap.BilinForm.toDual_def, h]
  have hrange : (LinearMap.range T).map φ.toLinearMap = LinearMap.range S.dualMap := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨φ v, (hφ v).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨φ.symm y, rfl⟩, ?_⟩
      rw [hφ, φ.apply_symm_apply]
  have h1 : finrank (ZMod 2) (LinearMap.range T) = finrank (ZMod 2) (LinearMap.range S) := by
    rw [← LinearMap.finrank_range_dualMap_eq_finrank_range S, ← hrange]
    exact (LinearEquiv.finrank_map_eq _ _).symm
  have h2 := LinearMap.finrank_range_add_finrank_ker S
  have h3 := LinearMap.finrank_range_add_finrank_ker T
  omega


theorem case5_cube_eq_one_of_form (hd : finrank (ZMod 2) V ≤ 7) (f : LinearMap.BilinForm (ZMod 2) V)
    (hf : f.Nondegenerate) (u : V ≃ₗ[ZMod 2] V) (hinv : ∀ v w, f (u v) (u w) = f v w)
    (h15 : u ^ 15 = 1) (hfix : ∀ v, (u ^ 5) v = v → v = 0) : u ^ 3 = 1 := by
  classical
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  set U : Module.End (ZMod 2) V := (u : V →ₗ[ZMod 2] V) with hU
  set Ui : Module.End (ZMod 2) V := ((u⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) with hUi
  have hpowi : ∀ (n : ℕ) (v : V), (u⁻¹ ^ n) v = (Ui ^ n) v := fun n v => case5_pow_apply_eq u⁻¹ n v
  have hadj : ∀ (k : ℕ) (v w : V), f ((u ^ k) v) w = f v ((u⁻¹ ^ k) w) := by
    intro k
    induction k with
    | zero => intro v w; simp
    | succ k ih =>
      intro v w
      have h1 : f ((u ^ (k + 1)) v) w = f (u ((u ^ k) v)) w := by
        rw [pow_succ']; rfl
      have h2 : f (u ((u ^ k) v)) w = f ((u ^ k) v) (u⁻¹ w) := by
        have := hinv ((u ^ k) v) (u⁻¹ w)
        rw [← this]
        simp
      have h3 : (u⁻¹ ^ (k + 1)) w = (u⁻¹ ^ k) (u⁻¹ w) := by
        rw [pow_succ]; rfl
      rw [h1, h2, ih, h3]
  have hTexp : ∀ v, aeval U (X^4 + X + 1 : (ZMod 2)[X]) v = (u ^ 4) v + u v + v := by
    intro v
    have : aeval U (X^4 + X + 1 : (ZMod 2)[X]) = U ^ 4 + U + 1 := by
      simp only [map_add, map_pow, aeval_X, map_one]
    rw [this, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, ← case5_pow_apply_eq u 4 v]
    rfl
  have hSexp : ∀ v, aeval Ui (X^4 + X + 1 : (ZMod 2)[X]) v = (u⁻¹ ^ 4) v + u⁻¹ v + v := by
    intro v
    have : aeval Ui (X^4 + X + 1 : (ZMod 2)[X]) = Ui ^ 4 + Ui + 1 := by
      simp only [map_add, map_pow, aeval_X, map_one]
    rw [this, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, ← hpowi 4 v]
    rfl
  have hT'exp : ∀ v, aeval U (X^4 + X^3 + 1 : (ZMod 2)[X]) v = (u ^ 4) v + (u ^ 3) v + v := by
    intro v
    have : aeval U (X^4 + X^3 + 1 : (ZMod 2)[X]) = U ^ 4 + U ^ 3 + 1 := by
      simp only [map_add, map_pow, aeval_X, map_one]
    rw [this, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
      ← case5_pow_apply_eq u 4 v, ← case5_pow_apply_eq u 3 v]
  have hTS : ∀ v w, f (aeval U (X^4 + X + 1 : (ZMod 2)[X]) v) w =
      f v (aeval Ui (X^4 + X + 1 : (ZMod 2)[X]) w) := by
    intro v w
    rw [hTexp, hSexp]
    simp only [map_add, LinearMap.add_apply]
    have e1 := hadj 4 v w
    have e2 := hadj 1 v w
    simp only [pow_one] at e2
    rw [e1, e2]
  have hmulinv : ∀ k : ℕ, ∀ w : V, (u ^ k) ((u⁻¹ ^ k) w) = w := by
    intro k w
    have : u ^ k * u⁻¹ ^ k = 1 := by rw [inv_pow]; exact mul_inv_cancel _
    simp
  have hrel : ∀ w, aeval U (X^4 + X^3 + 1 : (ZMod 2)[X]) w =
      (u ^ 4) (aeval Ui (X^4 + X + 1 : (ZMod 2)[X]) w) := by
    intro w
    rw [hT'exp, hSexp, map_add, map_add, hmulinv 4 w]
    have a3 : (u ^ 4) (u⁻¹ w) = (u ^ 3) w := by
      have h1 : u ^ 4 * u⁻¹ = u ^ 3 := by
        rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, mul_assoc, mul_inv_cancel, mul_one]
      have h2 := congrArg (fun g : V ≃ₗ[ZMod 2] V => g w) h1
      simpa using h2
    rw [a3]
    abel
  set π₁ : (ZMod 2)[X] := X^4 + X + 1 with hπ₁
  set π₂ : (ZMod 2)[X] := X^4 + X^3 + 1 with hπ₂
  have hcomm : ∀ (p : (ZMod 2)[X]) (k : ℕ) (v : V), aeval U p ((U ^ k) v) = (U ^ k) (aeval U p v) := by
    intro p k v
    have hc : Commute (aeval U p) (U ^ k) := by
      simpa using (Commute.all p (X ^ k)).map (aeval U : (ZMod 2)[X] →ₐ[ZMod 2] _)
    exact congrArg (fun g : Module.End (ZMod 2) V => g v) hc.eq
  have hK : finrank (ZMod 2) (LinearMap.ker (aeval U π₁)) =
      finrank (ZMod 2) (LinearMap.ker (aeval U π₂)) := by
    rw [case5_finrank_ker_eq_of_adjoint f hf (aeval U π₁) (aeval Ui π₁) hTS]
    have hker : LinearMap.ker (aeval Ui π₁) = LinearMap.ker (aeval U π₂) := by
      ext w
      simp only [LinearMap.mem_ker]
      rw [hrel w]
      exact (LinearEquiv.map_eq_zero_iff _).symm
    rw [hker]
  have hdisj : Disjoint (LinearMap.ker (aeval U π₁)) (LinearMap.ker (aeval U π₂)) :=
    Polynomial.disjoint_ker_aeval_of_isCoprime U ⟨X^3 + X + 1, X^3 + X^2, case5_bez1⟩
  have hle : finrank (ZMod 2) (LinearMap.ker (aeval U π₁)) ≤ 3 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval U π₁))
      (LinearMap.ker (aeval U π₂))
    rw [disjoint_iff.1 hdisj, finrank_bot] at h1
    have h2 := Submodule.finrank_le (LinearMap.ker (aeval U π₁) ⊔ LinearMap.ker (aeval U π₂))
    omega
  have hK1 : LinearMap.ker (aeval U π₁) = ⊥ := by
    by_contra hne
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hinj := case5_orbit_free u h15 (w := w) hw hw0
    let φ : Fin 15 → LinearMap.ker (aeval U π₁) := fun k =>
      ⟨(u ^ (k : ℕ)) w, by
        rw [LinearMap.mem_ker, case5_pow_apply_eq u]
        rw [hcomm π₁ (k : ℕ) w]
        rw [LinearMap.mem_ker] at hw
        rw [hw, map_zero]⟩
    have hφ : Function.Injective φ := fun a b hab => hinj (congrArg Subtype.val hab)
    have hc := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hc
    have hcard : Nat.card (LinearMap.ker (aeval U π₁)) =
        2 ^ finrank (ZMod 2) (LinearMap.ker (aeval U π₁)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have : 2 ^ finrank (ZMod 2) (LinearMap.ker (aeval U π₁)) ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by norm_num) hle
    omega
  have hK2 : LinearMap.ker (aeval U π₂) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← hK, hK1, finrank_bot]
  have hTinj : Function.Injective (aeval U π₁) := LinearMap.ker_eq_bot.1 hK1
  have hT'inj : Function.Injective (aeval U π₂) := LinearMap.ker_eq_bot.1 hK2
  have hTsurj : Function.Surjective (aeval U π₁) := LinearMap.injective_iff_surjective.1 hTinj
  have hT'surj : Function.Surjective (aeval U π₂) := LinearMap.injective_iff_surjective.1 hT'inj
  have hU15 : U ^ 15 = 1 := by
    ext v
    have := case5_pow_apply_eq u 15 v
    rw [h15] at this
    simpa using this.symm
  have hρ0 : aeval U (X^10 + X^5 + 1 : (ZMod 2)[X]) = 0 := by
    ext v
    have h1 : aeval U ((X^5 - 1) * (X^10 + X^5 + 1) : (ZMod 2)[X]) = 0 := by
      have : ((X^5 - 1) * (X^10 + X^5 + 1) : (ZMod 2)[X]) = X^15 - 1 := by ring
      rw [this]
      simp [hU15]
    have h2 := congrArg (fun g : Module.End (ZMod 2) V => g v) h1
    simp only [map_mul, Module.End.mul_apply, LinearMap.zero_apply] at h2
    have h3 : (U ^ 5) (aeval U (X^10 + X^5 + 1 : (ZMod 2)[X]) v) =
        aeval U (X^10 + X^5 + 1 : (ZMod 2)[X]) v := by
      have : aeval U (X^5 - 1 : (ZMod 2)[X]) = U ^ 5 - 1 := by
        simp only [map_sub, map_pow, aeval_X, map_one]
      rw [this, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h2
      exact h2
    have h4 : (u ^ 5) (aeval U (X^10 + X^5 + 1 : (ZMod 2)[X]) v) =
        aeval U (X^10 + X^5 + 1 : (ZMod 2)[X]) v := by
      rw [case5_pow_apply_eq]; exact h3
    simpa using hfix _ h4
  have hΦ : ∀ x, aeval U (X^2 + X + 1 : (ZMod 2)[X]) x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := hTsurj x
    obtain ⟨v, rfl⟩ := hT'surj y
    have h1 := congrArg (fun g : Module.End (ZMod 2) V => g v) hρ0
    rw [← case5_fac] at h1
    simp only [map_mul, Module.End.mul_apply, LinearMap.zero_apply] at h1
    exact h1
  have hcube : aeval U (X^3 - 1 : (ZMod 2)[X]) = 0 := by
    ext v
    have : (X^3 - 1 : (ZMod 2)[X]) = (X - 1) * (X^2 + X + 1) := by ring
    rw [this]
    simp only [map_mul, Module.End.mul_apply, LinearMap.zero_apply]
    rw [hΦ, map_zero]
  have hU3 : U ^ 3 = 1 := by
    have : aeval U (X^3 - 1 : (ZMod 2)[X]) = U ^ 3 - 1 := by
      simp only [map_sub, map_pow, aeval_X, map_one]
    rw [this, sub_eq_zero] at hcube
    exact hcube
  ext v
  have := case5_pow_apply_eq u 3 v
  rw [this, hU3]
  rfl


theorem case5_not_selfDual {L : Subgroup (GLV V)} (hd : finrank (ZMod 2) V ≤ 7)
    {z y : GLV V} (hzL : z ∈ L) (hzc : ∀ l ∈ L, z * l = l * z) (hz3 : z ^ 3 = 1)
    (hfp : ∀ v, z v = v → v = 0) (hyL : y ∈ L) (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) :
    ¬ SelfDual L ⊤ := by
  rintro ⟨f, hf, hinv⟩
  set e : (⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] V := Submodule.topEquiv with he
  set f' : LinearMap.BilinForm (ZMod 2) V := LinearMap.BilinForm.congr e f with hf'
  have hf'nd : f'.Nondegenerate := LinearMap.BilinForm.Nondegenerate.congr e hf
  have hf'apply : ∀ v w, f' v w = f ⟨v, trivial⟩ ⟨w, trivial⟩ := fun v w => rfl
  have hinv' : ∀ g ∈ L, ∀ v w, f' (g v) (g w) = f' v w := by
    intro g hg v w
    rw [hf'apply, hf'apply]
    exact hinv g hg ⟨v, trivial⟩ ⟨w, trivial⟩ ⟨g v, trivial⟩ ⟨g w, trivial⟩ rfl rfl
  have hyz : Commute y z := (hzc y hyL).symm
  have hu : ∀ n : ℕ, (y * z) ^ n = y ^ n * z ^ n := fun n => hyz.mul_pow n
  have hy15 : y ^ 15 = 1 := by rw [show (15 : ℕ) = 5 * 3 from rfl, pow_mul, hy5, one_pow]
  have hz15 : z ^ 15 = 1 := by rw [show (15 : ℕ) = 3 * 5 from rfl, pow_mul, hz3, one_pow]
  have hz5 : z ^ 5 = z ^ 2 := by
    rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, hz3, one_mul]
  have hu15 : (y * z) ^ 15 = 1 := by rw [hu, hy15, hz15, one_mul]
  have hu5 : ∀ v, ((y * z) ^ 5) v = v → v = 0 := by
    intro v hv
    rw [hu, hy5, one_mul, hz5] at hv
    apply hfp
    have h1 : (z ^ 2) v = v := hv
    have h3 : (z ^ 3) v = z ((z ^ 2) v) := by rw [pow_succ']; rfl
    rw [hz3, h1] at h3
    exact h3.symm
  have hcube := case5_cube_eq_one_of_form hd f' hf'nd (y * z) (hinv' _ (L.mul_mem hyL hzL)) hu15 hu5
  rw [hu, hz3, mul_one] at hcube
  apply hy1
  have h2 : y ^ 2 = 1 := by
    have : y ^ 5 = y ^ 3 * y ^ 2 := by rw [← pow_add]
    rw [hcube, one_mul] at this
    rw [← this, hy5]
  have : y ^ 3 = y ^ 2 * y := by rw [← pow_succ]
  rw [hcube, h2, one_mul] at this
  exact this.symm

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
