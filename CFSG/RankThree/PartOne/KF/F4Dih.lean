module

public import CFSG.RankThree.PartOne.KF.G2Dih
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K] {θ : ℕ}

@[expose] noncomputable def f4s1 (p : ℕ) (K : Type) [Field K] : MulAut (G2V p K) where
  toFun b := ![(b 0)⁻¹ * b 1, b 1]
  invFun b := ![(b 0)⁻¹ * b 1, b 1]
  left_inv b := by
    refine g2v_ext ?_ rfl
    show ((b 0)⁻¹ * b 1)⁻¹ * b 1 = b 0
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv]
    abel
  right_inv b := by
    refine g2v_ext ?_ rfl
    show ((b 0)⁻¹ * b 1)⁻¹ * b 1 = b 0
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv]
    abel
  map_mul' a b := by
    refine g2v_ext ?_ rfl
    show (a 0 * b 0)⁻¹ * (a 1 * b 1) = (a 0)⁻¹ * a 1 * ((b 0)⁻¹ * b 1)
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv]
    abel

@[expose] noncomputable def f4s2 (p : ℕ) (K : Type) [Field K] (θ : ℕ) : MulAut (G2V p K) where
  toFun b := ![b 0, b 0 ^ (2 * θ + 2) * (b 1)⁻¹]
  invFun b := ![b 0, b 0 ^ (2 * θ + 2) * (b 1)⁻¹]
  left_inv b := by
    refine g2v_ext rfl ?_
    show b 0 ^ (2 * θ + 2) * (b 0 ^ (2 * θ + 2) * (b 1)⁻¹)⁻¹ = b 1
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  right_inv b := by
    refine g2v_ext rfl ?_
    show b 0 ^ (2 * θ + 2) * (b 0 ^ (2 * θ + 2) * (b 1)⁻¹)⁻¹ = b 1
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  map_mul' a b := by
    refine g2v_ext rfl ?_
    show (a 0 * b 0) ^ (2 * θ + 2) * (a 1 * b 1)⁻¹ =
      a 0 ^ (2 * θ + 2) * (a 1)⁻¹ * (b 0 ^ (2 * θ + 2) * (b 1)⁻¹)
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

theorem f4s1_apply_zero (b : G2V p K) : f4s1 p K b 0 = (b 0)⁻¹ * b 1 := rfl

theorem f4s1_apply_one (b : G2V p K) : f4s1 p K b 1 = b 1 := rfl

theorem f4s2_apply_zero (b : G2V p K) : f4s2 p K θ b 0 = b 0 := rfl

theorem f4s2_apply_one (b : G2V p K) : f4s2 p K θ b 1 = b 0 ^ (2 * θ + 2) * (b 1)⁻¹ := rfl

@[expose] noncomputable def f4Dih (p : ℕ) (K : Type) [Field K] (θ : ℕ) :
    Subgroup (MulAut (G2V p K)) :=
  Subgroup.closure {f4s1 p K, f4s2 p K θ}

theorem f4s1_mem_f4Dih : f4s1 p K ∈ f4Dih p K θ := Subgroup.subset_closure (Set.mem_insert _ _)

theorem f4s2_mem_f4Dih : f4s2 p K θ ∈ f4Dih p K θ :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem f4s1_mul_self : f4s1 p K * f4s1 p K = 1 := by
  refine MulEquiv.ext fun b => g2v_ext ?_ rfl
  show ((b 0)⁻¹ * b 1)⁻¹ * b 1 = b 0
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem f4s2_mul_self : f4s2 p K θ * f4s2 p K θ = 1 := by
  refine MulEquiv.ext fun b => g2v_ext rfl ?_
  show b 0 ^ (2 * θ + 2) * (b 0 ^ (2 * θ + 2) * (b 1)⁻¹)⁻¹ = b 1
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

@[expose] def f4ι0 (p : ℕ) (K : Type) [Field K] : rootsOfUnity p K →* G2V p K where
  toFun w := ![w, 1]
  map_one' := g2v_ext rfl rfl
  map_mul' a b := g2v_ext rfl (by simp)

@[expose] def f4ι1 (p : ℕ) (K : Type) [Field K] : rootsOfUnity p K →* G2V p K where
  toFun w := ![1, w]
  map_one' := g2v_ext rfl rfl
  map_mul' a b := g2v_ext (by simp) rfl

theorem f4ι0_apply_zero (w : rootsOfUnity p K) : f4ι0 p K w 0 = w := rfl

theorem f4ι0_apply_one (w : rootsOfUnity p K) : f4ι0 p K w 1 = 1 := rfl

theorem f4ι1_apply_zero (w : rootsOfUnity p K) : f4ι1 p K w 0 = 1 := rfl

theorem f4ι1_apply_one (w : rootsOfUnity p K) : f4ι1 p K w 1 = w := rfl

theorem f4ι0_injective : Function.Injective (f4ι0 p K) := fun _ _ h => congrFun h 0

theorem f4ι1_injective : Function.Injective (f4ι1 p K) := fun _ _ h => congrFun h 1

theorem f4ι_decomp (v : G2V p K) : v = f4ι0 p K (v 0) * f4ι1 p K (v 1) :=
  g2v_ext (mul_one _).symm (one_mul _).symm

theorem f4_pow_self (x : rootsOfUnity p K) : x ^ p = 1 :=
  Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp x.2)

theorem f4_pow_self_V (x : G2V p K) : x ^ p = 1 := funext fun i => f4_pow_self (x i)

theorem f4_rec_four {G : Type*} [CommGroup G] {p : ℕ} (hp : ∀ x : G, x ^ p = 1) {s m : ℤ}
    (hs : s ^ 2 - 2 = p * m) {c0 c1 c2 c3 c4 : G} (h2 : c2 = c1 ^ s * c0⁻¹)
    (h3 : c3 = c2 ^ s * c1⁻¹) (h4 : c4 = c3 ^ s * c2⁻¹) : c4 = c0⁻¹ := by
  have e : c4 * c0 = (c1 ^ s * c0⁻¹) ^ (s ^ 2 - 2) := by
    subst h2 h3 h4
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  have h1 : (c1 ^ s * c0⁻¹) ^ (s ^ 2 - 2) = 1 := by
    rw [hs, zpow_mul, zpow_natCast, hp, one_zpow]
  exact eq_inv_of_mul_eq_one_left (e.trans h1)

theorem f4_mulAut_pow_rec {V : Type*} [Group V] (ρ : MulAut V) (s : ℤ)
    (hCH : ∀ x : V, (ρ ^ 2) x = ρ x ^ s * x⁻¹) (n : ℕ) (x : V) :
    (ρ ^ (n + 2)) x = (ρ ^ (n + 1)) x ^ s * ((ρ ^ n) x)⁻¹ := by
  rw [show n + 2 = 2 + n by omega, pow_add ρ 2 n, MulAut.mul_apply _ (ρ ^ 2) (ρ ^ n) x, hCH,
    pow_succ' ρ n, MulAut.mul_apply _ ρ (ρ ^ n) x]

theorem f4_mulAut_pow_four {V : Type*} [CommGroup V] {p : ℕ} (hp : ∀ x : V, x ^ p = 1)
    (ρ : MulAut V) {s m : ℤ} (hs : s ^ 2 - 2 = p * m)
    (hCH : ∀ x : V, (ρ ^ 2) x = ρ x ^ s * x⁻¹) (x : V) : (ρ ^ 4) x = x⁻¹ := by
  have h : (ρ ^ 4) x = ((ρ ^ 0) x)⁻¹ :=
    f4_rec_four hp hs (f4_mulAut_pow_rec ρ s hCH 0 x) (f4_mulAut_pow_rec ρ s hCH 1 x)
      (f4_mulAut_pow_rec ρ s hCH 2 x)
  rwa [pow_zero, MulAut.one_apply] at h

theorem f4rot_apply_zero (b : G2V p K) :
    (f4s1 p K * f4s2 p K θ) b 0 = (b 0)⁻¹ * (b 0 ^ (2 * θ + 2) * (b 1)⁻¹) := rfl

theorem f4rot_apply_one (b : G2V p K) :
    (f4s1 p K * f4s2 p K θ) b 1 = b 0 ^ (2 * θ + 2) * (b 1)⁻¹ := rfl

theorem f4rot_sq (b : G2V p K) :
    ((f4s1 p K * f4s2 p K θ) ^ 2) b =
      (f4s1 p K * f4s2 p K θ) b ^ (2 * (θ : ℤ)) * b⁻¹ := by
  rw [pow_two, MulAut.mul_apply _ (f4s1 p K * f4s2 p K θ) (f4s1 p K * f4s2 p K θ) b]
  refine g2v_ext ?_ ?_
  · simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, f4rot_apply_zero, f4rot_apply_one]
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    module
  · simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, f4rot_apply_zero, f4rot_apply_one]
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    module

theorem f4_rot_four (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) (b : G2V p K) :
    ((f4s1 p K * f4s2 p K θ) ^ 4) b = b⁻¹ := by
  obtain ⟨k, hk⟩ := hθ
  exact f4_mulAut_pow_four f4_pow_self_V (f4s1 p K * f4s2 p K θ) (s := 2 * (θ : ℤ))
    (m := 2 * k) (by linear_combination 2 * hk) f4rot_sq b

theorem f4_braid (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) : (f4s1 p K * f4s2 p K θ) ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul]
  refine MulEquiv.ext fun b => ?_
  rw [pow_two, MulAut.mul_apply, f4_rot_four hθ, f4_rot_four hθ, inv_inv]
  rfl

theorem f4s1_ne_one (hp : p.Prime) (_h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    f4s1 p K ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
  intro h
  have h1 := congrArg (fun m : MulAut (G2V p K) => m (f4ι1 p K z) 0) h
  simp only [f4s1_apply_zero, MulAut.one_apply, f4ι1_apply_zero, f4ι1_apply_one, inv_one,
    one_mul] at h1
  exact hz h1

theorem f4s2_ne_one (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    f4s2 p K θ ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
  intro h
  have h1 := congrArg (fun m : MulAut (G2V p K) => m (f4ι1 p K z) 1) h
  simp only [f4s2_apply_one, MulAut.one_apply, f4ι1_apply_zero, f4ι1_apply_one, one_pow,
    one_mul] at h1
  exact hz (eq_one_of_inv_eq_self (hp.odd_of_ne_two (by omega)) h1)

theorem orderOf_f4s1 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    orderOf (f4s1 p K) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact f4s1_mul_self) (f4s1_ne_one hp h5 hζ)

theorem orderOf_f4s2 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    orderOf (f4s2 p K θ) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact f4s2_mul_self) (f4s2_ne_one hp h5 hζ)

theorem orderOf_f4rot (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) : orderOf (f4s1 p K * f4s2 p K θ) = 8 := by
  obtain ⟨z, hz⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
  have h4 : ¬ (f4s1 p K * f4s2 p K θ) ^ 4 = 1 := by
    intro h
    have h1 := f4_rot_four hθ (f4ι1 p K z)
    rw [h, MulAut.one_apply] at h1
    have h2 : z = z⁻¹ := congrFun h1 1
    exact hz (eq_one_of_inv_eq_self (hp.odd_of_ne_two (by omega)) h2.symm)
  have h8 : (f4s1 p K * f4s2 p K θ) ^ 2 ^ (2 + 1) = 1 := f4_braid hθ
  exact (orderOf_eq_prime_pow (p := 2) (n := 2) h4 h8).trans (by norm_num)

theorem f4rot_sq_ne_one (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) : (f4s1 p K * f4s2 p K θ) ^ 2 ≠ 1 := by
  intro h
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_f4rot hp h5 hζ hθ] at h1
  omega

theorem f4Dih_eq_closure :
    f4Dih p K θ = Subgroup.closure {f4s1 p K * f4s2 p K θ, f4s2 p K θ} := by
  apply le_antisymm
  · rw [f4Dih, Subgroup.closure_le]
    have hρ : f4s1 p K * f4s2 p K θ ∈ Subgroup.closure {f4s1 p K * f4s2 p K θ, f4s2 p K θ} :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hσ : f4s2 p K θ ∈ Subgroup.closure {f4s1 p K * f4s2 p K θ, f4s2 p K θ} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rintro x (rfl | rfl)
    · have h := Subgroup.mul_mem _ hρ (Subgroup.inv_mem _ hσ)
      rwa [mul_inv_cancel_right] at h
    · exact hσ
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mul_mem _ f4s1_mem_f4Dih f4s2_mem_f4Dih
    · exact f4s2_mem_f4Dih

theorem f4s2_rel :
    f4s2 p K θ * (f4s1 p K * f4s2 p K θ) * (f4s2 p K θ)⁻¹ = (f4s1 p K * f4s2 p K θ)⁻¹ := by
  have h1 : (f4s2 p K θ)⁻¹ = f4s2 p K θ := inv_eq_of_mul_eq_one_right f4s2_mul_self
  have h0 : (f4s1 p K)⁻¹ = f4s1 p K := inv_eq_of_mul_eq_one_right f4s1_mul_self
  rw [mul_inv_rev, h0, h1]
  calc f4s2 p K θ * (f4s1 p K * f4s2 p K θ) * f4s2 p K θ
      = f4s2 p K θ * f4s1 p K * (f4s2 p K θ * f4s2 p K θ) := by simp only [mul_assoc]
    _ = f4s2 p K θ * f4s1 p K := by rw [f4s2_mul_self, mul_one]

theorem f4Dih_equiv (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) : Nonempty (f4Dih p K θ ≃* DihedralGroup 8) := by
  have := finite_rootsOfUnity (K := K) hp.pos hζ
  have h := nonempty_closure_pair_mulEquiv_dihedral (ρ := f4s1 p K * f4s2 p K θ)
    (σ := f4s2 p K θ) (by rw [sq]; exact f4s2_mul_self) f4s2_rel
    (not_mem_zpowers_of_conj_eq_inv f4s2_rel (f4rot_sq_ne_one hp h5 hζ hθ))
  rw [show orderOf (f4s1 p K * f4s2 p K θ) = 8 from orderOf_f4rot hp h5 hζ hθ,
    ← f4Dih_eq_closure] at h
  exact h

theorem movedHom_f4s1 (b : G2V p K) :
    movedHom (f4s1 p K) b = f4ι0 p K (((b 0) ^ 2)⁻¹ * b 1) := by
  refine g2v_ext ?_ ?_
  · show (b 0)⁻¹ * b 1 * (b 0)⁻¹ = ((b 0) ^ 2)⁻¹ * b 1
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  · show b 1 * (b 1)⁻¹ = 1
    exact mul_inv_cancel _

theorem movedHom_f4s2 (b : G2V p K) :
    movedHom (f4s2 p K θ) b = f4ι1 p K (b 0 ^ (2 * θ + 2) * ((b 1) ^ 2)⁻¹) := by
  refine g2v_ext ?_ ?_
  · show b 0 * (b 0)⁻¹ = 1
    exact mul_inv_cancel _
  · show b 0 ^ (2 * θ + 2) * (b 1)⁻¹ * (b 1)⁻¹ = b 0 ^ (2 * θ + 2) * ((b 1) ^ 2)⁻¹
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

theorem f4_exists_sq (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (z : rootsOfUnity p K) : ∃ w : rootsOfUnity p K, w ^ 2 = z := by
  have hμ : Nat.card (rootsOfUnity p K) = p := card_rootsOfUnity_eq' hp.pos hζ
  have hcop : Nat.Coprime (Nat.card (rootsOfUnity p K)) 2 := by
    rw [hμ]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  obtain ⟨w, hw⟩ := (powCoprime hcop).surjective z
  exact ⟨w, hw⟩

theorem movedV_f4s1 : movedV (f4s1 p K) = (f4ι0 p K).range := by
  rw [movedV_eq_range]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, (movedHom_f4s1 b).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨f4ι1 p K w, ?_⟩
    rw [movedHom_f4s1, f4ι1_apply_zero, f4ι1_apply_one, one_pow, inv_one, one_mul]

theorem movedV_f4s2 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    movedV (f4s2 p K θ) = (f4ι1 p K).range := by
  rw [movedV_eq_range]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, (movedHom_f4s2 b).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := f4_exists_sq hp h5 hζ w⁻¹
    refine ⟨f4ι1 p K v, ?_⟩
    rw [movedHom_f4s2, f4ι1_apply_zero, f4ι1_apply_one, one_pow, one_mul, hv, inv_inv]

theorem card_movedV_f4s1 (hp : p.Prime) (_h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (f4s1 p K)) = p := by
  rw [movedV_f4s1, ← Nat.card_congr (MonoidHom.ofInjective f4ι0_injective).toEquiv,
    card_rootsOfUnity_eq' hp.pos hζ]

theorem card_movedV_f4s2 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (f4s2 p K θ)) = p := by
  rw [movedV_f4s2 hp h5 hζ, ← Nat.card_congr (MonoidHom.ofInjective f4ι1_injective).toEquiv,
    card_rootsOfUnity_eq' hp.pos hζ]

theorem f4_not_dvd_t (h5 : 5 ≤ p) (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) :
    ¬ (p : ℤ) ∣ 2 * (θ : ℤ) + 2 := by
  intro h
  have h2 : (p : ℤ) ∣ 2 := by
    have h3 := dvd_sub (dvd_mul_of_dvd_right hθ 2) (dvd_mul_of_dvd_right h (2 * (θ : ℤ) - 2))
    have e : 2 * (2 * (θ : ℤ) ^ 2 - 1) - (2 * (θ : ℤ) - 2) * (2 * (θ : ℤ) + 2) = 2 := by ring
    rwa [e] at h3
  have := Int.le_of_dvd (by norm_num) h2
  omega

theorem f4_not_dvd_t4 (h5 : 5 ≤ p) (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) :
    ¬ (p : ℤ) ∣ 2 * (θ : ℤ) - 2 := by
  intro h
  have h2 : (p : ℤ) ∣ 2 := by
    have h3 := dvd_sub (dvd_mul_of_dvd_right hθ 2) (dvd_mul_of_dvd_left h (2 * (θ : ℤ) + 2))
    have e : 2 * (2 * (θ : ℤ) ^ 2 - 1) - (2 * (θ : ℤ) - 2) * (2 * (θ : ℤ) + 2) = 2 := by ring
    rwa [e] at h3
  have := Int.le_of_dvd (by norm_num) h2
  omega

theorem f4_zpow_ne_one (hp : p.Prime) {z : rootsOfUnity p K} (hz : z ≠ 1) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) : z ^ n ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf z = p := orderOf_eq_prime (f4_pow_self z) hz
  intro h
  apply hn
  have h1 := orderOf_dvd_iff_zpow_eq_one.mpr h
  rwa [hord] at h1

theorem f4_pow_t_ne_one (hp : p.Prime) (h5 : 5 ≤ p) (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1)
    {z : rootsOfUnity p K} (hz : z ≠ 1) : z ^ (2 * θ + 2) ≠ 1 := by
  have h := f4_zpow_ne_one hp hz (f4_not_dvd_t h5 hθ)
  rwa [show (2 * (θ : ℤ) + 2) = ((2 * θ + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at h

theorem f4_ne_one_aux (hp : p.Prime) (h5 : 5 ≤ p) (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1)
    {u : rootsOfUnity p K} (hu : u ≠ 1) : u ^ (2 * θ + 2) * ((u ^ 2) ^ 2)⁻¹ ≠ 1 := by
  have e : u ^ (2 * θ + 2) * ((u ^ 2) ^ 2)⁻¹ = u ^ (2 * (θ : ℤ) - 2) := by
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    module
  rw [e]
  exact f4_zpow_ne_one hp hu (f4_not_dvd_t4 h5 hθ)

theorem f4Dih_irreducible (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) (B : Subgroup (G2V p K))
    (hB : ∀ γ ∈ f4Dih p K θ, ∀ x ∈ B, γ x ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hμ : Nat.card (rootsOfUnity p K) = p := card_rootsOfUnity_eq' hp.pos hζ
  have hs1 : ∀ x ∈ B, f4s1 p K x ∈ B := fun x hx => hB _ f4s1_mem_f4Dih x hx
  have hs2 : ∀ x ∈ B, f4s2 p K θ x ∈ B := fun x hx => hB _ f4s2_mem_f4Dih x hx
  have hl0 : ∀ b ∈ B, f4ι0 p K (((b 0) ^ 2)⁻¹ * b 1) ∈ B := fun b hb => by
    rw [← movedHom_f4s1]
    exact B.mul_mem (hs1 b hb) (B.inv_mem hb)
  have hl1 : ∀ b ∈ B, f4ι1 p K (b 0 ^ (2 * θ + 2) * ((b 1) ^ 2)⁻¹) ∈ B := fun b hb => by
    rw [← movedHom_f4s2]
    exact B.mul_mem (hs2 b hb) (B.inv_mem hb)
  have hcyc0 : ∀ u : rootsOfUnity p K, u ≠ 1 → f4ι0 p K u ∈ B → ∀ z, f4ι0 p K z ∈ B := by
    intro u hu1 huB z
    obtain ⟨k, rfl⟩ := mem_zpowers_of_prime_card hμ hu1 (g' := z)
    rw [map_zpow]
    exact B.zpow_mem huB k
  have hcyc1 : ∀ u : rootsOfUnity p K, u ≠ 1 → f4ι1 p K u ∈ B → ∀ z, f4ι1 p K z ∈ B := by
    intro u hu1 huB z
    obtain ⟨k, rfl⟩ := mem_zpowers_of_prime_card hμ hu1 (g' := z)
    rw [map_zpow]
    exact B.zpow_mem huB k
  have h01 : (∀ z, f4ι0 p K z ∈ B) → ∀ w, f4ι1 p K w ∈ B := by
    intro hz
    obtain ⟨w₀, hw₀⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
    have h := hl1 (f4ι0 p K w₀) (hz w₀)
    rw [f4ι0_apply_zero, f4ι0_apply_one, one_pow, inv_one, mul_one] at h
    exact hcyc1 _ (f4_pow_t_ne_one hp h5 hθ hw₀) h
  have h10 : (∀ w, f4ι1 p K w ∈ B) → ∀ z, f4ι0 p K z ∈ B := by
    intro hw z
    have h := hl0 (f4ι1 p K z) (hw z)
    rwa [f4ι1_apply_zero, f4ι1_apply_one, one_pow, inv_one, one_mul] at h
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hall : (∀ z, f4ι0 p K z ∈ B) ∧ ∀ w, f4ι1 p K w ∈ B := by
    by_cases ha : ((b 0) ^ 2)⁻¹ * b 1 = 1
    ·
      have hb1eq : b 1 = b 0 ^ 2 := (inv_mul_eq_one.mp ha).symm
      have hb0 : b 0 ≠ 1 := fun h => hb1' (g2v_ext h (by simp [hb1eq, h]))
      have hl : f4ι1 p K (b 0 ^ (2 * θ + 2) * ((b 0 ^ 2) ^ 2)⁻¹) ∈ B := by
        have h := hl1 b hbB
        rwa [hb1eq] at h
      have hw : ∀ w, f4ι1 p K w ∈ B := hcyc1 _ (f4_ne_one_aux hp h5 hθ hb0) hl
      exact ⟨h10 hw, hw⟩
    · have hz : ∀ z, f4ι0 p K z ∈ B := hcyc0 _ ha (hl0 b hbB)
      exact ⟨hz, h01 hz⟩
  rw [eq_top_iff]
  intro v _
  rw [f4ι_decomp v]
  exact B.mul_mem (hall.1 _) (hall.2 _)

theorem mulAut_dihedral_eight_eq_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (τ : MulAut (DihedralGroup 8)) (hτ : τ ^ p = 1) : τ = 1 := by
  have hp2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have hd1 : ∀ x : DihedralGroup 8, x ^ 8 = 1 → x ^ 4 ≠ 1 →
      x = DihedralGroup.r 1 ∨ x = DihedralGroup.r 3 ∨ x = DihedralGroup.r 5 ∨
        x = DihedralGroup.r 7 := by decide
  have hd2 : ∀ w : DihedralGroup 8, w * w = 1 → w ≠ 1 → w ≠ DihedralGroup.r 4 →
      ∃ j : ZMod 8, w = DihedralGroup.sr j := by decide
  have hinj1 : ∀ y : DihedralGroup 8, τ y = 1 → y = 1 := fun y h =>
    τ.injective (h.trans (map_one τ).symm)
  have hr1 : τ (DihedralGroup.r 1) = DihedralGroup.r 1 := by
    have hx8 : τ (DihedralGroup.r 1) ^ 8 = 1 := by
      rw [← map_pow, show (DihedralGroup.r 1 : DihedralGroup 8) ^ 8 = 1 by decide, map_one]
    have hx4 : τ (DihedralGroup.r 1) ^ 4 ≠ 1 := by
      rw [← map_pow]
      exact fun h => (by decide : (DihedralGroup.r 1 : DihedralGroup 8) ^ 4 ≠ 1) (hinj1 _ h)
    have hsq : (τ ^ 2) (DihedralGroup.r 1) = DihedralGroup.r 1 := by
      rw [pow_two, MulAut.mul_apply]
      rcases hd1 _ hx8 hx4 with h | h | h | h
      · rw [h, h]
      · rw [h, show (DihedralGroup.r 3 : DihedralGroup 8) = DihedralGroup.r 1 ^ 3 by decide,
          map_pow, h]
        decide
      · rw [h, show (DihedralGroup.r 5 : DihedralGroup 8) = DihedralGroup.r 1 ^ 5 by decide,
          map_pow, h]
        decide
      · rw [h, show (DihedralGroup.r 7 : DihedralGroup 8) = DihedralGroup.r 1 ^ 7 by decide,
          map_pow, h]
        decide
    have hfix := mulAut_pow_apply_of_apply_eq (τ ^ 2) hsq m
    have hτ' := hτ
    rw [hm, pow_succ', pow_mul] at hτ'
    have h1 := congrArg (fun σ : MulAut (DihedralGroup 8) => σ (DihedralGroup.r 1)) hτ'
    simpa only [MulAut.mul_apply, hfix, MulAut.one_apply] using h1
  have hr : ∀ i : ZMod 8, τ (DihedralGroup.r i) = DihedralGroup.r i := fun i => by
    rw [show (DihedralGroup.r i : DihedralGroup 8) = DihedralGroup.r 1 ^ i.val by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val], map_pow, hr1]
  obtain ⟨j, hj⟩ : ∃ j : ZMod 8, τ (DihedralGroup.sr 0) = DihedralGroup.sr j := by
    refine hd2 _ ?_ ?_ ?_
    · rw [← map_mul, show (DihedralGroup.sr 0 : DihedralGroup 8) * DihedralGroup.sr 0 = 1 by
        decide, map_one]
    · exact fun h => (by decide : (DihedralGroup.sr 0 : DihedralGroup 8) ≠ 1) (hinj1 _ h)
    · intro h
      exact (by decide : (DihedralGroup.sr 0 : DihedralGroup 8) ≠ DihedralGroup.r 4)
        (τ.injective (h.trans (hr 4).symm))
  have hsr : ∀ i : ZMod 8, τ (DihedralGroup.sr i) = DihedralGroup.sr (j + i) := fun i => by
    rw [show (DihedralGroup.sr i : DihedralGroup 8) = DihedralGroup.sr 0 * DihedralGroup.r i by
      rw [DihedralGroup.sr_mul_r, zero_add], map_mul, hj, hr, DihedralGroup.sr_mul_r]
  have hiter : ∀ (n : ℕ) (i : ZMod 8),
      (τ ^ n) (DihedralGroup.sr i) = DihedralGroup.sr ((n : ZMod 8) * j + i) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [pow_succ', MulAut.mul_apply, ih, hsr]
      congr 1
      push_cast
      ring
  have hpj : (p : ZMod 8) * j = 0 := by
    have h1 := hiter p 0
    rw [hτ, MulAut.one_apply] at h1
    simpa using (DihedralGroup.sr.inj h1).symm
  have hj0 : j = 0 := by
    have hcast : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod p 8).symm
    have key : ∀ c : ℕ, c < 8 → c % 2 = 1 → ∀ j : ZMod 8, (c : ZMod 8) * j = 0 → j = 0 := by
      decide
    rw [hcast] at hpj
    exact key (p % 8) (Nat.mod_lt _ (by norm_num)) (by omega) j hpj
  refine MulEquiv.ext fun x => ?_
  rcases x with i | i
  · rw [MulAut.one_apply]
    exact hr i
  · rw [MulAut.one_apply, hsr, hj0, zero_add]

theorem f4Dih_commutes_of_normalizes (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1)
    (φ : MulAut (G2V p K)) (hφ : φ ^ p = 1)
    (hnorm : ∀ γ ∈ f4Dih p K θ, φ * γ * φ⁻¹ ∈ f4Dih p K θ) :
    ∀ γ ∈ f4Dih p K θ, φ * γ = γ * φ := by
  obtain ⟨e⟩ := f4Dih_equiv hp h5 hζ hθ
  have hfin : Finite (f4Dih p K θ) := Finite.of_equiv _ e.symm.toEquiv
  let c : f4Dih p K θ →* f4Dih p K θ :=
    { toFun := fun γ => ⟨φ * γ * φ⁻¹, hnorm γ γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show φ * ((a : MulAut (G2V p K)) * b) * φ⁻¹ = φ * a * φ⁻¹ * (φ * b * φ⁻¹)
        group) }
  have hcinj : Function.Injective c := fun a b h => Subtype.ext (by
    have h1 := congrArg Subtype.val h
    exact mul_left_cancel (mul_right_cancel h1))
  let α : MulAut (f4Dih p K θ) := MulEquiv.ofBijective c (Finite.injective_iff_bijective.mp hcinj)
  have hα : ∀ (n : ℕ) (γ : f4Dih p K θ),
      (((α ^ n) γ : f4Dih p K θ) : MulAut (G2V p K)) = φ ^ n * γ * (φ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro γ; simp
    | succ n ih =>
      intro γ
      rw [pow_succ', MulAut.mul_apply]
      show φ * (((α ^ n) γ : f4Dih p K θ) : MulAut (G2V p K)) * φ⁻¹ = _
      rw [ih, pow_succ', mul_inv_rev]
      group
  have hαp : α ^ p = 1 := MulEquiv.ext fun γ => Subtype.ext (by rw [hα, hφ]; simp)
  have hα1 : α = 1 := by
    have h1 : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hαp, map_one]
    exact (MulAut.congr e).injective
      ((mulAut_dihedral_eight_eq_one hp h5 _ h1).trans (map_one _).symm)
  intro γ hγ
  have h3 := hα 1 ⟨γ, hγ⟩
  rw [hα1, one_pow, MulAut.one_apply, pow_one] at h3
  exact mul_inv_eq_iff_eq_mul.mp h3.symm

theorem eq_one_of_commutes_f4Dih (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1)
    (φ : MulAut (G2V p K)) (hφ : φ ^ p = 1)
    (hcomm : ∀ γ ∈ f4Dih p K θ, φ * γ = γ * φ) : φ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_rootsOfUnity (K := K) hp.pos hζ
  have hH : IsPGroup p (Subgroup.zpowers φ) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hφ
  have hdvd : p ∣ Nat.card (G2V p K) := by
    rw [card_G2V hp.pos hζ]
    exact dvd_pow_self p two_ne_zero
  have h1fix : (1 : G2V p K) ∈ MulAction.fixedPoints (Subgroup.zpowers φ) (G2V p K) :=
    fun g => show (g : MulAut (G2V p K)) 1 = 1 from map_one _
  obtain ⟨b, hbfix, hb1⟩ :=
    hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (G2V p K) hdvd h1fix
  have hφb : φ b = b := hbfix ⟨φ, Subgroup.mem_zpowers φ⟩
  have hbU : b ∈ (movedHom φ).ker := (mem_ker_movedHom φ b).mpr hφb
  have hinv : ∀ γ ∈ f4Dih p K θ, ∀ x ∈ (movedHom φ).ker, γ x ∈ (movedHom φ).ker := by
    intro γ hγ x hx
    rw [mem_ker_movedHom] at hx ⊢
    have h := congrArg (fun m : MulAut (G2V p K) => m x) (hcomm γ hγ)
    simp only [MulAut.mul_apply] at h
    rw [h, hx]
  rcases f4Dih_irreducible hp h5 hζ hθ _ hinv with h | h
  · rw [h, Subgroup.mem_bot] at hbU
    exact absurd hbU.symm hb1
  · refine MulEquiv.ext fun v => ?_
    have hv : v ∈ (movedHom φ).ker := by rw [h]; trivial
    exact (mem_ker_movedHom φ v).mp hv

theorem eq_one_of_normalizes_f4Dih (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1)
    (φ : MulAut (G2V p K)) (hφ : φ ^ p = 1)
    (hnorm : ∀ γ ∈ f4Dih p K θ, φ * γ * φ⁻¹ ∈ f4Dih p K θ) : φ = 1 :=
  eq_one_of_commutes_f4Dih hp h5 hζ hθ φ hφ (f4Dih_commutes_of_normalizes hp h5 hζ hθ φ hφ hnorm)

end CFSG.RankThree.PartOne.KFU
