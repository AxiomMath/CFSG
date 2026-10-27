module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsNorm
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBasic
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNs

public section

open Polynomial Module

namespace CFSG.StandardType

namespace CoordSpNs

section Gal

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

theorem aeval_root_self : aeval (AdjoinRoot.root g) g = 0 := by
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

omit [Fact (Irreducible g)] in
theorem val_neg_one_eq (hp : 1 ≤ p) : (-1 : ZMod p).val = p - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  rw [ZMod.val_neg_one, Nat.add_sub_cancel]

theorem card_mem_galExp [Finite K] (hζ : AdjoinRoot.root g ^ p = 1) {u : (ZMod p)ˣ}
    (hu : (u : ZMod p) = (Nat.card K : ZMod p)) : u ∈ CoordSL.galExp g hζ := by
  let := Fintype.ofFinite K
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have : Algebra.IsAlgebraic K (AdjoinRoot g) := Algebra.IsAlgebraic.of_finite K (AdjoinRoot g)
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot g), ?_⟩
  change AdjoinRoot.root g ^ Fintype.card K = _
  rw [hu, ZMod.val_natCast, ← Nat.card_eq_fintype_card]
  exact pow_eq_pow_mod _ hζ

theorem neg_one_mem_galExp [Finite K] [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0) : (-1 : (ZMod p)ˣ) ∈ CoordSL.galExp g hζ := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hv : (-1 : ZMod p).val = p - 1 := val_neg_one_eq hp1
  have h0 : aeval (AdjoinRoot.root g ^ (-1 : ZMod p).val)
      (minpoly K (AdjoinRoot.root g ^ (1 : ZMod p).val)) = 0 := by
    rw [CoordSL.pow_val_one hζ, AdjoinRoot.minpoly_root (Fact.out : Irreducible g).ne_zero,
      map_mul, hv, hσ, zero_mul]
  obtain ⟨u, hu, hu1⟩ := CoordSL.exists_galExp_of_aeval hζ hprim one_ne_zero h0
  have hu' : u = -1 := Units.ext (by
    rw [Units.val_neg, Units.val_one]
    rw [mul_one] at hu1
    exact hu1.symm)
  rwa [hu'] at hu

theorem neg_one_not_mem_galExp (hp : 1 ≤ p) (hζ : AdjoinRoot.root g ^ p = 1)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g ≠ 0) : (-1 : (ZMod p)ˣ) ∉ CoordSL.galExp g hζ := by
  rintro ⟨σ, hσζ⟩
  apply hσ
  rw [Units.val_neg, Units.val_one] at hσζ
  rw [← val_neg_one_eq hp, ← hσζ, Polynomial.aeval_algEquiv, AlgHom.comp_apply,
    aeval_root_self, map_zero]

end Gal

section SelfDual

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

@[expose] noncomputable def sdC (hζ0 : AdjoinRoot.root g ≠ 0) : AdjoinRoot g ≃ₗ[K] AdjoinRoot g :=
  SpNS.mulEquivL (AdjoinRoot.root g) hζ0

theorem sdC_apply (hζ0 : AdjoinRoot.root g ≠ 0) (x : AdjoinRoot g) :
    sdC (K := K) hζ0 x = AdjoinRoot.root g * x := rfl

theorem sdC_pow_apply (hζ0 : AdjoinRoot.root g ≠ 0) (m : ℕ) (x : AdjoinRoot g) :
    (sdC (K := K) hζ0 ^ m) x = AdjoinRoot.root g ^ m * x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_apply_succ, ih, sdC_apply, pow_succ', mul_assoc]

theorem sdC_pow_eq_one (hζ0 : AdjoinRoot.root g ≠ 0) (hζ : AdjoinRoot.root g ^ p = 1) :
    sdC (K := K) hζ0 ^ p = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [sdC_pow_apply, hζ, one_mul]
  rfl

theorem sd_comm_eq_mul [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
    (hζ0 : AdjoinRoot.root g ≠ 0) {T : Module.End K (AdjoinRoot g)}
    (hT : ∀ x, T (sdC hζ0 x) = sdC hζ0 (T x)) (x : AdjoinRoot g) : T x = x * T 1 :=
  CoordSL.mul_eq_of_intertwine hζ one_ne_zero
    (fun y => by rw [CoordSL.pow_val_one hζ]; exact hT y) x

theorem formTransitive_sd [Finite K] [CharP K 2] [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
    (hζ0 : AdjoinRoot.root g ≠ 0) : FormTransitive K (AdjoinRoot g) (sdC hζ0) := by
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  refine formTransitive_of_comm (fun T T' hT hT' => ?_) (fun T hT h0 => ?_)
  · have e1 := sd_comm_eq_mul hζ hζ0 hT
    have e2 := sd_comm_eq_mul hζ hζ0 hT'
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, e1 (T' x), e2 x, e2 (T x), e1 x]
    ring
  · have e1 := sd_comm_eq_mul hζ hζ0 hT
    have h1 : T 1 * T 1 = 0 := by
      have h2 := congrArg (fun S : Module.End K (AdjoinRoot g) => S 1) h0
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at h2
      rwa [e1 (T 1)] at h2
    have h2 : T 1 = 0 := mul_self_eq_zero.mp h1
    refine LinearMap.ext fun x => ?_
    rw [e1 x, h2, mul_zero, LinearMap.zero_apply]

theorem sd_conj_of_galExp (hζ0 : AdjoinRoot.root g ≠ 0) {hζ : AdjoinRoot.root g ^ p = 1}
    {u : (ZMod p)ˣ} (hu : u ∈ CoordSL.galExp g hζ) :
    ∃ T₀ : AdjoinRoot g ≃ₗ[K] AdjoinRoot g,
      ∀ x, T₀ ((sdC hζ0 ^ (u : ZMod p).val) x) = sdC hζ0 (T₀ x) := by
  obtain ⟨σ, hσ⟩ := hu
  refine ⟨σ.symm.toLinearEquiv, fun x => ?_⟩
  rw [sdC_pow_apply, sdC_apply, AlgEquiv.toLinearEquiv_apply, AlgEquiv.toLinearEquiv_apply,
    map_mul, ← hσ, AlgEquiv.symm_apply_apply]

theorem galSigns_le_twistGroup_sd [Finite K] [CharP K 2] [Fact p.Prime]
    (hζ : AdjoinRoot.root g ^ p = 1) (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0) (hζ0 : AdjoinRoot.root g ≠ 0)
    {β : LinearMap.BilinForm K (AdjoinRoot g)} (hβa : β.IsAlt) (hβnd : β.Nondegenerate)
    (hβc : ∀ x y, β (sdC hζ0 x) (sdC hζ0 y) = β x y) :
    galSigns p (Nat.card K) ≤ twistGroup β (sdC hζ0) (sdC_pow_eq_one hζ0 hζ) := by
  have htr := formTransitive_sd hζ hζ0
  have hgal : ∀ u ∈ CoordSL.galExp g hζ, u ∈ twistGroup β (sdC hζ0) (sdC_pow_eq_one hζ0 hζ) :=
    fun u hu => by
      obtain ⟨T₀, hT₀⟩ := sd_conj_of_galExp hζ0 hu
      exact mem_twistGroup_of_conj _ htr hβa hβnd hβc T₀ hT₀
  refine (Subgroup.closure_le _).mpr fun u hu => hgal u ?_
  rcases hu with hu | hu
  · exact card_mem_galExp hζ hu
  · have hu' : u = -1 := Units.ext (by rw [hu, Units.val_neg, Units.val_one])
    rw [hu']
    exact neg_one_mem_galExp hζ hprim hσ

end SelfDual

section Paired

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

@[expose] noncomputable def prC (hζ0 : AdjoinRoot.root g ≠ 0)
    (hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0) :
    (AdjoinRoot g × AdjoinRoot g) ≃ₗ[K] (AdjoinRoot g × AdjoinRoot g) :=
  (SpNS.mulEquivL (AdjoinRoot.root g) hζ0).prodCongr
    (SpNS.mulEquivL (AdjoinRoot.root g ^ (p - 1)) hζ0')

variable (hζ0 : AdjoinRoot.root g ≠ 0) (hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0)

theorem prC_apply (x y : AdjoinRoot g) :
    prC (K := K) hζ0 hζ0' (x, y) = (AdjoinRoot.root g * x, AdjoinRoot.root g ^ (p - 1) * y) :=
  rfl

theorem prC_pow_apply (m : ℕ) (x y : AdjoinRoot g) :
    (prC (K := K) hζ0 hζ0' ^ m) (x, y) =
      (AdjoinRoot.root g ^ m * x, (AdjoinRoot.root g ^ (p - 1)) ^ m * y) := by
  induction m generalizing x y with
  | zero => simp
  | succ m ih => rw [pow_apply_succ, ih, prC_apply, pow_succ', pow_succ', mul_assoc, mul_assoc]

theorem prC_pow_eq_one (hζ : AdjoinRoot.root g ^ p = 1) : prC (K := K) hζ0 hζ0' ^ p = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, y⟩ := v
  rw [prC_pow_apply, hζ, one_mul, ← pow_mul, mul_comm (p - 1) p, pow_mul, hζ, one_pow, one_mul]
  rfl

include hζ0 hζ0' in
theorem pr_comm_eq_mul [Finite K] [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g ≠ 0)
    {T : Module.End K (AdjoinRoot g × AdjoinRoot g)}
    (hT : ∀ v, T (prC hζ0 hζ0' v) = prC hζ0 hζ0' (T v)) (x y : AdjoinRoot g) :
    T (x, y) = (x * (T (1, 0)).1, y * (T (0, 1)).2) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set m1 : ZMod p := ((-1 : (ZMod p)ˣ) : ZMod p) with hm1def
  have hv : m1.val = p - 1 := by
    rw [hm1def, Units.val_neg, Units.val_one]
    exact val_neg_one_eq hp1
  have hneg := neg_one_not_mem_galExp hp1 hζ hσ
  have hm1 : m1 ≠ 0 := fun h => by
    rw [h, ZMod.val_zero] at hv
    omega
  have hab : ∀ u ∈ CoordSL.galExp g hζ, (1 : ZMod p) ≠ u * m1 := by
    intro u hu h
    apply hneg
    have h2 : u * (-1) = 1 := Units.ext (by rw [Units.val_mul, Units.val_one]; exact h.symm)
    have h3 : u = -1 := by
      calc u = u * (-1) * (-1) := by rw [mul_assoc, neg_one_mul, neg_neg, mul_one]
        _ = -1 := by rw [h2, one_mul]
    rw [← h3]
    exact hu
  have hab' : ∀ u ∈ CoordSL.galExp g hζ, m1 ≠ u * 1 := by
    intro u hu h
    apply hneg
    have h3 : u = -1 := Units.ext (by rw [mul_one] at h; exact h.symm)
    rw [← h3]
    exact hu
  have hT0 : ∀ y, T (0, AdjoinRoot.root g ^ (p - 1) * y) =
      (AdjoinRoot.root g * (T (0, y)).1, AdjoinRoot.root g ^ (p - 1) * (T (0, y)).2) := by
    intro y
    have h1 := hT (0, y)
    rw [prC_apply, mul_zero] at h1
    rw [h1]
    rfl
  have hT1 : ∀ x, T (AdjoinRoot.root g * x, 0) =
      (AdjoinRoot.root g * (T (x, 0)).1, AdjoinRoot.root g ^ (p - 1) * (T (x, 0)).2) := by
    intro x
    have h1 := hT (x, 0)
    rw [prC_apply, mul_zero] at h1
    rw [h1]
    rfl
  set f₁₂ := LinearMap.fst K _ _ ∘ₗ T ∘ₗ LinearMap.inr K (AdjoinRoot g) (AdjoinRoot g) with hf₁₂
  set f₂₁ := LinearMap.snd K _ _ ∘ₗ T ∘ₗ LinearMap.inl K (AdjoinRoot g) (AdjoinRoot g) with hf₂₁
  set f₁₁ := LinearMap.fst K _ _ ∘ₗ T ∘ₗ LinearMap.inl K (AdjoinRoot g) (AdjoinRoot g) with hf₁₁
  set f₂₂ := LinearMap.snd K _ _ ∘ₗ T ∘ₗ LinearMap.inr K (AdjoinRoot g) (AdjoinRoot g) with hf₂₂
  have h₁₂ : f₁₂ = 0 := CoordSL.eq_zero_of_intertwine hζ hprim hm1 hab fun y => by
    rw [hv, CoordSL.pow_val_one hζ]
    exact congrArg Prod.fst (hT0 y)
  have h₂₁ : f₂₁ = 0 := CoordSL.eq_zero_of_intertwine hζ hprim one_ne_zero hab' fun x => by
    rw [hv, CoordSL.pow_val_one hζ]
    exact congrArg Prod.snd (hT1 x)
  have h₁₁ : ∀ x, f₁₁ x = x * f₁₁ 1 := CoordSL.mul_eq_of_intertwine hζ one_ne_zero fun x => by
    rw [CoordSL.pow_val_one hζ]
    exact congrArg Prod.fst (hT1 x)
  have h₂₂ : ∀ y, f₂₂ y = y * f₂₂ 1 := CoordSL.mul_eq_of_intertwine hζ hm1 fun y => by
    rw [hv]
    exact congrArg Prod.snd (hT0 y)
  have hsplit : T (x, y) = T (x, 0) + T (0, y) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have e₁₂ : (T (0, y)).1 = 0 := by
    have := LinearMap.congr_fun h₁₂ y
    exact this
  have e₂₁ : (T (x, 0)).2 = 0 := by
    have := LinearMap.congr_fun h₂₁ x
    exact this
  rw [hsplit]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, e₁₂, add_zero]
    exact h₁₁ x
  · rw [Prod.snd_add, e₂₁, zero_add]
    exact h₂₂ y

include hζ0 hζ0' in
theorem formTransitive_pr [Finite K] [CharP K 2] [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g ≠ 0) :
    FormTransitive K (AdjoinRoot g × AdjoinRoot g) (prC hζ0 hζ0') := by
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  refine formTransitive_of_comm (fun T T' hT hT' => ?_) (fun T hT h0 => ?_)
  · have e1 := pr_comm_eq_mul hζ0 hζ0' hζ hprim hσ hT
    have e2 := pr_comm_eq_mul hζ0 hζ0' hζ hprim hσ hT'
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, y⟩ := v
    rw [Module.End.mul_apply, Module.End.mul_apply, e2 x y,
      e1 (x * (T' (1, 0)).1) (y * (T' (0, 1)).2), e1 x y,
      e2 (x * (T (1, 0)).1) (y * (T (0, 1)).2)]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  · have e1 := pr_comm_eq_mul hζ0 hζ0' hζ hprim hσ hT
    have h1 := congrArg (fun S : Module.End K (AdjoinRoot g × AdjoinRoot g) => S (1, 0)) h0
    have h2 := congrArg (fun S : Module.End K (AdjoinRoot g × AdjoinRoot g) => S (0, 1)) h0
    simp only [Module.End.mul_apply, LinearMap.zero_apply] at h1 h2
    rw [e1 1 0, e1 (1 * (T (1, 0)).1)] at h1
    rw [e1 0 1, e1 (0 * (T (1, 0)).1)] at h2
    have ha : (T (1, 0)).1 = 0 := by
      have := congrArg Prod.fst h1
      simp only [one_mul, Prod.fst_zero] at this
      exact mul_self_eq_zero.mp this
    have hb : (T (0, 1)).2 = 0 := by
      have := congrArg Prod.snd h2
      simp only [one_mul, Prod.snd_zero] at this
      exact mul_self_eq_zero.mp this
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, y⟩ := v
    rw [e1, ha, hb, mul_zero, mul_zero, LinearMap.zero_apply]
    rfl

include hζ0 hζ0' in
theorem pr_conj_of_galExp {hζ : AdjoinRoot.root g ^ p = 1} {u : (ZMod p)ˣ}
    (hu : u ∈ CoordSL.galExp g hζ) :
    ∃ T₀ : (AdjoinRoot g × AdjoinRoot g) ≃ₗ[K] (AdjoinRoot g × AdjoinRoot g),
      ∀ v, T₀ ((prC hζ0 hζ0' ^ (u : ZMod p).val) v) = prC hζ0 hζ0' (T₀ v) := by
  obtain ⟨σ, hσ⟩ := hu
  refine ⟨σ.symm.toLinearEquiv.prodCongr σ.symm.toLinearEquiv, fun v => ?_⟩
  obtain ⟨x, y⟩ := v
  rw [prC_pow_apply, LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_apply, prC_apply]
  simp only [AlgEquiv.toLinearEquiv_apply, map_mul]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [← hσ, AlgEquiv.symm_apply_apply]
  · dsimp only
    rw [← pow_mul, mul_comm (p - 1) _, pow_mul, ← hσ, ← map_pow, AlgEquiv.symm_apply_apply]

include hζ0 hζ0' in
theorem pr_conj_neg_one (hp : 1 ≤ p) (hζ : AdjoinRoot.root g ^ p = 1) :
    ∃ T₀ : (AdjoinRoot g × AdjoinRoot g) ≃ₗ[K] (AdjoinRoot g × AdjoinRoot g),
      ∀ v, T₀ ((prC hζ0 hζ0' ^ ((-1 : (ZMod p)ˣ) : ZMod p).val) v) = prC hζ0 hζ0' (T₀ v) := by
  have hv : ((-1 : (ZMod p)ˣ) : ZMod p).val = p - 1 := by
    rw [Units.val_neg, Units.val_one]
    exact val_neg_one_eq hp
  have hsq : (AdjoinRoot.root g ^ (p - 1)) ^ (p - 1) = AdjoinRoot.root g := by
    have h1 := CoordSL.pow_val_pow_val hζ (-1 : ZMod p) (-1 : ZMod p)
    rw [neg_one_mul, neg_neg, CoordSL.pow_val_one hζ, val_neg_one_eq hp] at h1
    exact h1
  refine ⟨LinearEquiv.prodComm K (AdjoinRoot g) (AdjoinRoot g), fun v => ?_⟩
  obtain ⟨x, y⟩ := v
  rw [hv, prC_pow_apply, LinearEquiv.prodComm_apply, LinearEquiv.prodComm_apply, prC_apply,
    Prod.swap_prod_mk, Prod.swap_prod_mk, hsq]

include hζ0 hζ0' in
theorem galSigns_le_twistGroup_pr [Finite K] [CharP K 2] [Fact p.Prime]
    (hζ : AdjoinRoot.root g ^ p = 1) (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g ≠ 0)
    {β : LinearMap.BilinForm K (AdjoinRoot g × AdjoinRoot g)} (hβa : β.IsAlt)
    (hβnd : β.Nondegenerate) (hβc : ∀ x y, β (prC hζ0 hζ0' x) (prC hζ0 hζ0' y) = β x y) :
    galSigns p (Nat.card K) ≤ twistGroup β (prC hζ0 hζ0') (prC_pow_eq_one hζ0 hζ0' hζ) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have htr := formTransitive_pr hζ0 hζ0' hζ hprim hσ
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  rcases hu with hu | hu
  · obtain ⟨T₀, hT₀⟩ := pr_conj_of_galExp hζ0 hζ0' (card_mem_galExp hζ hu)
    exact mem_twistGroup_of_conj _ htr hβa hβnd hβc T₀ hT₀
  · have hu' : u = -1 := Units.ext (by rw [hu, Units.val_neg, Units.val_one])
    rw [hu']
    obtain ⟨T₀, hT₀⟩ := pr_conj_neg_one hζ0 hζ0' hp1 hζ
    exact mem_twistGroup_of_conj _ htr hβa hβnd hβc T₀ hT₀

end Paired

end CoordSpNs

end CFSG.StandardType
