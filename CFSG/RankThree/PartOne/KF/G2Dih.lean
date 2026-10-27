module

public import CFSG.RankThree.PartOne.KF.D8Module
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFU

abbrev G2V (p : ℕ) (K : Type) [Field K] : Type := Fin 2 → rootsOfUnity p K

variable {p : ℕ} {K : Type} [Field K]

theorem g2v_ext {a b : G2V p K} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b :=
  funext (Fin.forall_fin_two.mpr ⟨h0, h1⟩)

@[expose] noncomputable def g2s0 (p : ℕ) (K : Type) [Field K] : MulAut (G2V p K) where
  toFun b := ![(b 0)⁻¹, b 1 * b 0]
  invFun b := ![(b 0)⁻¹, b 1 * b 0]
  left_inv b := g2v_ext (by simp) (by simp)
  right_inv b := g2v_ext (by simp) (by simp)
  map_mul' a b :=
    g2v_ext (by simp; exact mul_comm _ _) (by simp; exact mul_mul_mul_comm _ _ _ _)

@[expose] noncomputable def g2s1 (p : ℕ) (K : Type) [Field K] : MulAut (G2V p K) where
  toFun b := ![b 0 * b 1 ^ 3, (b 1)⁻¹]
  invFun b := ![b 0 * b 1 ^ 3, (b 1)⁻¹]
  left_inv b := g2v_ext (by simp) (by simp)
  right_inv b := g2v_ext (by simp) (by simp)
  map_mul' a b :=
    g2v_ext (by simp [mul_pow]; exact mul_mul_mul_comm _ _ _ _) (by simp; exact mul_comm _ _)

theorem g2s0_apply_zero (b : G2V p K) : g2s0 p K b 0 = (b 0)⁻¹ := rfl

theorem g2s0_apply_one (b : G2V p K) : g2s0 p K b 1 = b 1 * b 0 := rfl

theorem g2s1_apply_zero (b : G2V p K) : g2s1 p K b 0 = b 0 * b 1 ^ 3 := rfl

theorem g2s1_apply_one (b : G2V p K) : g2s1 p K b 1 = (b 1)⁻¹ := rfl

theorem g2s0_mul_self : g2s0 p K * g2s0 p K = 1 :=
  MulEquiv.ext fun b =>
    g2v_ext (by simp [g2s0_apply_zero]) (by simp [g2s0_apply_zero, g2s0_apply_one])

theorem g2s1_mul_self : g2s1 p K * g2s1 p K = 1 :=
  MulEquiv.ext fun b => g2v_ext (by simp [g2s1_apply_zero, g2s1_apply_one])
    (by simp [g2s1_apply_one])

@[expose] noncomputable def g2rot (p : ℕ) (K : Type) [Field K] : MulAut (G2V p K) :=
  g2s0 p K * g2s1 p K

theorem g2rot_apply_zero (b : G2V p K) : g2rot p K b 0 = (b 0)⁻¹ * (b 1 ^ 3)⁻¹ := by
  show (b 0 * b 1 ^ 3)⁻¹ = _
  exact mul_inv _ _

theorem g2rot_apply_one (b : G2V p K) : g2rot p K b 1 = b 0 * b 1 ^ 2 := by
  show (b 1)⁻¹ * (b 0 * b 1 ^ 3) = _
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem g2rot_sq_apply_zero (b : G2V p K) : (g2rot p K ^ 2) b 0 = (b 0 ^ 2 * b 1 ^ 3)⁻¹ := by
  rw [pow_two, MulAut.mul_apply, g2rot_apply_zero, g2rot_apply_zero, g2rot_apply_one]
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem g2rot_sq_apply_one (b : G2V p K) : (g2rot p K ^ 2) b 1 = b 0 * b 1 := by
  rw [pow_two, MulAut.mul_apply, g2rot_apply_one, g2rot_apply_zero, g2rot_apply_one]
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem g2rot_cube (b : G2V p K) : (g2rot p K ^ 3) b = b⁻¹ := by
  have h : g2rot p K ^ 3 = g2rot p K * g2rot p K ^ 2 := pow_succ' _ _
  refine g2v_ext ?_ ?_
  · rw [h, MulAut.mul_apply, g2rot_apply_zero, g2rot_sq_apply_zero, g2rot_sq_apply_one,
      Pi.inv_apply]
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  · rw [h, MulAut.mul_apply, g2rot_apply_one, g2rot_sq_apply_zero, g2rot_sq_apply_one,
      Pi.inv_apply]
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem g2_braid (_hp : p.Prime) (_h5 : 5 ≤ p) : (g2s0 p K * g2s1 p K) ^ 6 = 1 := by
  show g2rot p K ^ 6 = 1
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul]
  refine MulEquiv.ext fun b => ?_
  rw [pow_two, MulAut.mul_apply, g2rot_cube, g2rot_cube, inv_inv]
  rfl

theorem finite_rootsOfUnity (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Finite (rootsOfUnity p K) :=
  Nat.finite_of_card_ne_zero (by rw [card_rootsOfUnity_eq' hp hζ]; exact hp.ne')

theorem card_G2V (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (G2V p K) = p ^ 2 := by
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    card_rootsOfUnity_eq' hp hζ]

theorem exists_ne_one_rootsOfUnity (hp : p.Prime) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    ∃ z : rootsOfUnity p K, z ≠ 1 := by
  have := finite_rootsOfUnity (K := K) hp.pos hζ
  have h : 1 < Nat.card (rootsOfUnity p K) := by
    rw [card_rootsOfUnity_eq' hp.pos hζ]
    exact hp.one_lt
  have := Finite.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

theorem g2s0_ne_one (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    g2s0 p K ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
  intro h
  have h1 := congrArg (fun m : MulAut (G2V p K) => m (Pi.mulSingle 0 z) 0) h
  simp only [g2s0_apply_zero, MulAut.one_apply, Pi.mulSingle_eq_same] at h1
  exact hz (eq_one_of_inv_eq_self (hp.odd_of_ne_two (by omega)) h1)

theorem g2s1_ne_one (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    g2s1 p K ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
  intro h
  have h1 := congrArg (fun m : MulAut (G2V p K) => m (Pi.mulSingle 1 z) 1) h
  simp only [g2s1_apply_one, MulAut.one_apply, Pi.mulSingle_eq_same] at h1
  exact hz (eq_one_of_inv_eq_self (hp.odd_of_ne_two (by omega)) h1)

theorem orderOf_g2s0 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    orderOf (g2s0 p K) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact g2s0_mul_self) (g2s0_ne_one hp h5 hζ)

theorem orderOf_g2s1 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    orderOf (g2s1 p K) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact g2s1_mul_self) (g2s1_ne_one hp h5 hζ)

theorem g2rot_sq_ne_one (hp : p.Prime) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    g2rot p K ^ 2 ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
  intro h
  have h1 := congrArg (fun m : MulAut (G2V p K) => m (Pi.mulSingle 0 z) 1) h
  simp only [g2rot_sq_apply_one, MulAut.one_apply, Pi.mulSingle_eq_same] at h1
  simp at h1
  exact hz h1

theorem g2rot_cube_ne_one (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    g2rot p K ^ 3 ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_ne_one_rootsOfUnity (K := K) hp hζ
  intro h
  have h1 := congrArg (fun m : MulAut (G2V p K) => m (Pi.mulSingle 0 z) 0) h
  simp only [g2rot_cube, MulAut.one_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at h1
  exact hz (eq_one_of_inv_eq_self (hp.odd_of_ne_two (by omega)) h1)

theorem orderOf_g2rot (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    orderOf (g2rot p K) = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (g2_braid hp h5) fun q hq hqd => ?_
  rcases (Nat.Prime.dvd_mul hq).mp (show q ∣ 2 * 3 from hqd) with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
    exact g2rot_cube_ne_one hp h5 hζ
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
    exact g2rot_sq_ne_one hp hζ

@[expose] noncomputable def g2Dih (p : ℕ) (K : Type) [Field K] : Subgroup (MulAut (G2V p K)) :=
  Subgroup.closure {g2s0 p K, g2s1 p K}

theorem g2s0_mem_g2Dih : g2s0 p K ∈ g2Dih p K := Subgroup.subset_closure (Set.mem_insert _ _)

theorem g2s1_mem_g2Dih : g2s1 p K ∈ g2Dih p K :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem g2Dih_eq_closure : g2Dih p K = Subgroup.closure {g2s0 p K * g2s1 p K, g2s1 p K} := by
  apply le_antisymm
  · rw [g2Dih, Subgroup.closure_le]
    have hρ : g2s0 p K * g2s1 p K ∈ Subgroup.closure {g2s0 p K * g2s1 p K, g2s1 p K} :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hσ : g2s1 p K ∈ Subgroup.closure {g2s0 p K * g2s1 p K, g2s1 p K} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rintro x (rfl | rfl)
    · have h := Subgroup.mul_mem _ hρ (Subgroup.inv_mem _ hσ)
      rwa [mul_inv_cancel_right] at h
    · exact hσ
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mul_mem _ g2s0_mem_g2Dih g2s1_mem_g2Dih
    · exact g2s1_mem_g2Dih

theorem g2s1_rel :
    g2s1 p K * (g2s0 p K * g2s1 p K) * (g2s1 p K)⁻¹ = (g2s0 p K * g2s1 p K)⁻¹ := by
  have h1 : (g2s1 p K)⁻¹ = g2s1 p K := inv_eq_of_mul_eq_one_right g2s1_mul_self
  have h0 : (g2s0 p K)⁻¹ = g2s0 p K := inv_eq_of_mul_eq_one_right g2s0_mul_self
  rw [mul_inv_rev, h0, h1]
  calc g2s1 p K * (g2s0 p K * g2s1 p K) * g2s1 p K
      = g2s1 p K * g2s0 p K * (g2s1 p K * g2s1 p K) := by simp only [mul_assoc]
    _ = g2s1 p K * g2s0 p K := by rw [g2s1_mul_self, mul_one]

theorem not_mem_zpowers_of_conj_eq_inv {G : Type*} [Group G] {ρ σ : G} (hrel : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hρ2 : ρ ^ 2 ≠ 1) : σ ∉ Subgroup.zpowers ρ := by
  intro hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc : ρ ^ k * ρ * (ρ ^ k)⁻¹ = ρ := by group
  rw [hc] at hrel
  apply hρ2
  rw [pow_two]
  nth_rewrite 1 [hrel]
  exact inv_mul_cancel ρ

theorem nonempty_closure_pair_mulEquiv_dihedral {G : Type*} [Group G] [Finite G] {ρ σ : G}
    (hσ : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ Subgroup.zpowers ρ) :
    Nonempty (Subgroup.closure {ρ, σ} ≃* DihedralGroup (orderOf ρ)) := by
  have hρH : ρ ∈ Subgroup.closure ({ρ, σ} : Set G) := Subgroup.subset_closure (by simp)
  have hσH : σ ∈ Subgroup.closure ({ρ, σ} : Set G) := Subgroup.subset_closure (by simp)
  have hgen : (⊤ : Subgroup (Subgroup.closure ({ρ, σ} : Set G))) =
      Subgroup.zpowers ⟨ρ, hρH⟩ ⊔ Subgroup.zpowers ⟨σ, hσH⟩ := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      ← Subgroup.closure_closure_coe_preimage (k := ({ρ, σ} : Set G))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem
    (D := Subgroup.closure ({ρ, σ} : Set G)) ⟨ρ, hρH⟩ ⟨σ, hσH⟩ hgen
    (Subtype.ext (by simpa using hσ)) (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ (by
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hmem
      exact (Subgroup.mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk] at h

theorem g2Dih_equiv (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nonempty (g2Dih p K ≃* DihedralGroup 6) := by
  have := finite_rootsOfUnity (K := K) hp.pos hζ
  have h := nonempty_closure_pair_mulEquiv_dihedral (ρ := g2s0 p K * g2s1 p K) (σ := g2s1 p K)
    (by rw [sq]; exact g2s1_mul_self) g2s1_rel
    (not_mem_zpowers_of_conj_eq_inv g2s1_rel (g2rot_sq_ne_one hp hζ))
  rw [show orderOf (g2s0 p K * g2s1 p K) = 6 from orderOf_g2rot hp h5 hζ,
    ← g2Dih_eq_closure] at h
  exact h

@[expose] def g2ι0 (p : ℕ) (K : Type) [Field K] : rootsOfUnity p K →* G2V p K where
  toFun z := ![(z ^ 2)⁻¹, z]
  map_one' := g2v_ext (by simp) (by simp)
  map_mul' a b := g2v_ext (by simp [mul_pow, mul_comm]) (by simp)

@[expose] def g2ι1 (p : ℕ) (K : Type) [Field K] : rootsOfUnity p K →* G2V p K where
  toFun w := ![w ^ 3, (w ^ 2)⁻¹]
  map_one' := g2v_ext (by simp) (by simp)
  map_mul' a b := g2v_ext (by simp [mul_pow]) (by simp [mul_pow, mul_comm])

theorem g2ι0_injective : Function.Injective (g2ι0 p K) := fun _ _ h => congrFun h 1

theorem g2ι1_injective : Function.Injective (g2ι1 p K) := by
  have key : ∀ w : rootsOfUnity p K, w = g2ι1 p K w 0 * g2ι1 p K w 1 := fun w => by
    show w = w ^ 3 * (w ^ 2)⁻¹
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  intro a b h
  calc a = g2ι1 p K a 0 * g2ι1 p K a 1 := key a
    _ = g2ι1 p K b 0 * g2ι1 p K b 1 := by rw [h]
    _ = b := (key b).symm

theorem movedHom_g2s0 (b : G2V p K) : movedHom (g2s0 p K) b = g2ι0 p K (b 0) := by
  refine g2v_ext ?_ ?_
  · show (b 0)⁻¹ * (b 0)⁻¹ = ((b 0) ^ 2)⁻¹
    rw [pow_two, mul_inv]
  · show b 1 * b 0 * (b 1)⁻¹ = b 0
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem movedHom_g2s1 (b : G2V p K) : movedHom (g2s1 p K) b = g2ι1 p K (b 1) := by
  refine g2v_ext ?_ ?_
  · show b 0 * b 1 ^ 3 * (b 0)⁻¹ = b 1 ^ 3
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  · show (b 1)⁻¹ * (b 1)⁻¹ = ((b 1) ^ 2)⁻¹
    rw [pow_two, mul_inv]

theorem movedV_g2s0 : movedV (g2s0 p K) = (g2ι0 p K).range := by
  rw [movedV_eq_range]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b 0, (movedHom_g2s0 b).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨Pi.mulSingle 0 z, ?_⟩
    rw [movedHom_g2s0, Pi.mulSingle_eq_same]

theorem movedV_g2s1 : movedV (g2s1 p K) = (g2ι1 p K).range := by
  rw [movedV_eq_range]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b 1, (movedHom_g2s1 b).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨Pi.mulSingle 1 w, ?_⟩
    rw [movedHom_g2s1, Pi.mulSingle_eq_same]

theorem card_movedV_g2s0 (hp : p.Prime) (_h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (g2s0 p K)) = p := by
  rw [movedV_g2s0, ← Nat.card_congr (MonoidHom.ofInjective g2ι0_injective).toEquiv,
    card_rootsOfUnity_eq' hp.pos hζ]

theorem card_movedV_g2s1 (hp : p.Prime) (_h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (g2s1 p K)) = p := by
  rw [movedV_g2s1, ← Nat.card_congr (MonoidHom.ofInjective g2ι1_injective).toEquiv,
    card_rootsOfUnity_eq' hp.pos hζ]

theorem g2ι_decomp (v : G2V p K) :
    v = g2ι0 p K ((v 1 ^ 3 * v 0 ^ 2)⁻¹) * g2ι1 p K ((v 1 ^ 2 * v 0)⁻¹) := by
  refine g2v_ext ?_ ?_
  · show v 0 = (((v 1 ^ 3 * v 0 ^ 2)⁻¹) ^ 2)⁻¹ * ((v 1 ^ 2 * v 0)⁻¹) ^ 3
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  · show v 1 = (v 1 ^ 3 * v 0 ^ 2)⁻¹ * (((v 1 ^ 2 * v 0)⁻¹) ^ 2)⁻¹
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem g2Dih_irreducible (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (B : Subgroup (G2V p K)) (hB : ∀ γ ∈ g2Dih p K, ∀ x ∈ B, γ x ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hμ : Nat.card (rootsOfUnity p K) = p := card_rootsOfUnity_eq' hp.pos hζ
  have hs0 : ∀ x ∈ B, g2s0 p K x ∈ B := fun x hx => hB _ g2s0_mem_g2Dih x hx
  have hs1 : ∀ x ∈ B, g2s1 p K x ∈ B := fun x hx => hB _ g2s1_mem_g2Dih x hx
  have hl0 : ∀ b ∈ B, g2ι0 p K (b 0) ∈ B := fun b hb => by
    rw [← movedHom_g2s0]
    exact B.mul_mem (hs0 b hb) (B.inv_mem hb)
  have hl1 : ∀ b ∈ B, g2ι1 p K (b 1) ∈ B := fun b hb => by
    rw [← movedHom_g2s1]
    exact B.mul_mem (hs1 b hb) (B.inv_mem hb)
  have hcyc0 : ∀ u : rootsOfUnity p K, u ≠ 1 → g2ι0 p K u ∈ B → ∀ z, g2ι0 p K z ∈ B := by
    intro u hu1 huB z
    obtain ⟨k, rfl⟩ := mem_zpowers_of_prime_card hμ hu1 (g' := z)
    rw [map_zpow]
    exact B.zpow_mem huB k
  have hcyc1 : ∀ u : rootsOfUnity p K, u ≠ 1 → g2ι1 p K u ∈ B → ∀ z, g2ι1 p K z ∈ B := by
    intro u hu1 huB z
    obtain ⟨k, rfl⟩ := mem_zpowers_of_prime_card hμ hu1 (g' := z)
    rw [map_zpow]
    exact B.zpow_mem huB k
  have hcube : ∀ z : rootsOfUnity p K, ∃ w, w ^ 3 = z := by
    have hcop : Nat.Coprime (Nat.card (rootsOfUnity p K)) 3 := by
      rw [hμ]
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    intro z
    obtain ⟨w, hw⟩ := (powCoprime hcop).surjective z
    exact ⟨w, hw⟩
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hall : (∀ z, g2ι0 p K z ∈ B) ∧ ∀ w, g2ι1 p K w ∈ B := by
    by_cases hb0 : b 0 = 1
    · have hb1'' : b 1 ≠ 1 := fun h => hb1' (g2v_ext hb0 h)
      have hw : ∀ w, g2ι1 p K w ∈ B := hcyc1 (b 1) hb1'' (hl1 b hbB)
      refine ⟨fun z => ?_, hw⟩
      obtain ⟨w, rfl⟩ := hcube z
      exact hl0 _ (hw w)
    · have hz : ∀ z, g2ι0 p K z ∈ B := hcyc0 (b 0) hb0 (hl0 b hbB)
      exact ⟨hz, fun w => hl1 _ (hz w)⟩
  rw [eq_top_iff]
  intro v _
  rw [g2ι_decomp v]
  exact B.mul_mem (hall.1 _) (hall.2 _)

theorem mulAut_pow_apply_of_apply_eq {W : Type*} [Group W] (τ : MulAut W) {x : W} (h : τ x = x)
    (k : ℕ) : (τ ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem mulAut_dihedral_six_eq_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (τ : MulAut (DihedralGroup 6)) (hτ : τ ^ p = 1) : τ = 1 := by
  have hp2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have hp3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have hd1 : ∀ x : DihedralGroup 6, x ^ 6 = 1 → x ^ 3 ≠ 1 → x ^ 2 ≠ 1 →
      x = DihedralGroup.r 1 ∨ x = DihedralGroup.r 5 := by decide
  have hd2 : ∀ w : DihedralGroup 6, w * w = 1 → w ≠ 1 → w ≠ DihedralGroup.r 3 →
      ∃ j : ZMod 6, w = DihedralGroup.sr j := by decide
  have hinj1 : ∀ y : DihedralGroup 6, τ y = 1 → y = 1 := fun y h =>
    τ.injective (h.trans (map_one τ).symm)
  have hr1 : τ (DihedralGroup.r 1) = DihedralGroup.r 1 := by
    have hx6 : τ (DihedralGroup.r 1) ^ 6 = 1 := by
      rw [← map_pow, show (DihedralGroup.r 1 : DihedralGroup 6) ^ 6 = 1 by decide, map_one]
    have hx3 : τ (DihedralGroup.r 1) ^ 3 ≠ 1 := by
      rw [← map_pow]
      exact fun h => (by decide : (DihedralGroup.r 1 : DihedralGroup 6) ^ 3 ≠ 1) (hinj1 _ h)
    have hx2 : τ (DihedralGroup.r 1) ^ 2 ≠ 1 := by
      rw [← map_pow]
      exact fun h => (by decide : (DihedralGroup.r 1 : DihedralGroup 6) ^ 2 ≠ 1) (hinj1 _ h)
    rcases hd1 _ hx6 hx3 hx2 with h | h
    · exact h
    · exfalso
      have h5' : τ (DihedralGroup.r 5) = DihedralGroup.r 1 := by
        rw [show (DihedralGroup.r 5 : DihedralGroup 6) = DihedralGroup.r 1 ^ 5 by decide,
          map_pow, h]
        decide
      have hsq : (τ ^ 2) (DihedralGroup.r 1) = DihedralGroup.r 1 := by
        rw [pow_two, MulAut.mul_apply, h, h5']
      have hfix := mulAut_pow_apply_of_apply_eq (τ ^ 2) hsq m
      have hτ' := hτ
      rw [hm, pow_succ', pow_mul] at hτ'
      have h1 := congrArg (fun σ : MulAut (DihedralGroup 6) => σ (DihedralGroup.r 1)) hτ'
      simp only [MulAut.mul_apply, hfix, MulAut.one_apply, h] at h1
      exact absurd h1 (by decide)
  have hr : ∀ i : ZMod 6, τ (DihedralGroup.r i) = DihedralGroup.r i := fun i => by
    rw [show (DihedralGroup.r i : DihedralGroup 6) = DihedralGroup.r 1 ^ i.val by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val], map_pow, hr1]
  obtain ⟨j, hj⟩ : ∃ j : ZMod 6, τ (DihedralGroup.sr 0) = DihedralGroup.sr j := by
    refine hd2 _ ?_ ?_ ?_
    · rw [← map_mul, show (DihedralGroup.sr 0 : DihedralGroup 6) * DihedralGroup.sr 0 = 1 by
        decide, map_one]
    · exact fun h => (by decide : (DihedralGroup.sr 0 : DihedralGroup 6) ≠ 1) (hinj1 _ h)
    · intro h
      exact (by decide : (DihedralGroup.sr 0 : DihedralGroup 6) ≠ DihedralGroup.r 3)
        (τ.injective (h.trans (hr 3).symm))
  have hsr : ∀ i : ZMod 6, τ (DihedralGroup.sr i) = DihedralGroup.sr (j + i) := fun i => by
    rw [show (DihedralGroup.sr i : DihedralGroup 6) = DihedralGroup.sr 0 * DihedralGroup.r i by
      rw [DihedralGroup.sr_mul_r, zero_add], map_mul, hj, hr, DihedralGroup.sr_mul_r]
  have hiter : ∀ (n : ℕ) (i : ZMod 6),
      (τ ^ n) (DihedralGroup.sr i) = DihedralGroup.sr ((n : ZMod 6) * j + i) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [pow_succ', MulAut.mul_apply, ih, hsr]
      congr 1
      push_cast
      ring
  have hpj : (p : ZMod 6) * j = 0 := by
    have h1 := hiter p 0
    rw [hτ, MulAut.one_apply] at h1
    simpa using (DihedralGroup.sr.inj h1).symm
  have hj0 : j = 0 := by
    have hcast : (p : ZMod 6) = ((p % 6 : ℕ) : ZMod 6) := (ZMod.natCast_mod p 6).symm
    rcases hp6 with h | h
    · rw [hcast, h] at hpj
      simpa using hpj
    · rw [hcast, h] at hpj
      have key : ∀ j : ZMod 6, ((5 : ℕ) : ZMod 6) * j = 0 → j = 0 := by decide
      exact key j hpj
  refine MulEquiv.ext fun x => ?_
  rcases x with i | i
  · rw [MulAut.one_apply]
    exact hr i
  · rw [MulAut.one_apply, hsr, hj0, zero_add]

theorem g2Dih_commutes_of_normalizes (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ : MulAut (G2V p K)) (hφ : φ ^ p = 1)
    (hnorm : ∀ γ ∈ g2Dih p K, φ * γ * φ⁻¹ ∈ g2Dih p K) :
    ∀ γ ∈ g2Dih p K, φ * γ = γ * φ := by
  obtain ⟨e⟩ := g2Dih_equiv hp h5 hζ
  have hfin : Finite (g2Dih p K) := Finite.of_equiv _ e.symm.toEquiv
  let c : g2Dih p K →* g2Dih p K :=
    { toFun := fun γ => ⟨φ * γ * φ⁻¹, hnorm γ γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show φ * ((a : MulAut (G2V p K)) * b) * φ⁻¹ = φ * a * φ⁻¹ * (φ * b * φ⁻¹)
        group) }
  have hcinj : Function.Injective c := fun a b h => Subtype.ext (by
    have h1 := congrArg Subtype.val h
    exact mul_left_cancel (mul_right_cancel h1))
  let α : MulAut (g2Dih p K) := MulEquiv.ofBijective c (Finite.injective_iff_bijective.mp hcinj)
  have hα : ∀ (n : ℕ) (γ : g2Dih p K),
      (((α ^ n) γ : g2Dih p K) : MulAut (G2V p K)) = φ ^ n * γ * (φ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro γ; simp
    | succ n ih =>
      intro γ
      rw [pow_succ', MulAut.mul_apply]
      show φ * (((α ^ n) γ : g2Dih p K) : MulAut (G2V p K)) * φ⁻¹ = _
      rw [ih, pow_succ', mul_inv_rev]
      group
  have hαp : α ^ p = 1 := MulEquiv.ext fun γ => Subtype.ext (by rw [hα, hφ]; simp)
  have hα1 : α = 1 := by
    have h1 : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hαp, map_one]
    exact (MulAut.congr e).injective
      ((mulAut_dihedral_six_eq_one hp h5 _ h1).trans (map_one _).symm)
  intro γ hγ
  have h3 := hα 1 ⟨γ, hγ⟩
  rw [hα1, one_pow, MulAut.one_apply, pow_one] at h3
  exact mul_inv_eq_iff_eq_mul.mp h3.symm

theorem eq_one_of_commutes_g2Dih (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ : MulAut (G2V p K)) (hφ : φ ^ p = 1)
    (hcomm : ∀ γ ∈ g2Dih p K, φ * γ = γ * φ) : φ = 1 := by
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
  have hinv : ∀ γ ∈ g2Dih p K, ∀ x ∈ (movedHom φ).ker, γ x ∈ (movedHom φ).ker := by
    intro γ hγ x hx
    rw [mem_ker_movedHom] at hx ⊢
    have h := congrArg (fun m : MulAut (G2V p K) => m x) (hcomm γ hγ)
    simp only [MulAut.mul_apply] at h
    rw [h, hx]
  rcases g2Dih_irreducible hp h5 hζ _ hinv with h | h
  · rw [h, Subgroup.mem_bot] at hbU
    exact absurd hbU.symm hb1
  · refine MulEquiv.ext fun v => ?_
    have hv : v ∈ (movedHom φ).ker := by rw [h]; trivial
    exact (mem_ker_movedHom φ v).mp hv

theorem eq_one_of_normalizes_g2Dih (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ : MulAut (G2V p K)) (hφ : φ ^ p = 1)
    (hnorm : ∀ γ ∈ g2Dih p K, φ * γ * φ⁻¹ ∈ g2Dih p K) : φ = 1 :=
  eq_one_of_commutes_g2Dih hp h5 hζ φ hφ (g2Dih_commutes_of_normalizes hp h5 hζ φ hφ hnorm)

end CFSG.RankThree.PartOne.KFU
