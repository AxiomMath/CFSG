module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Timmesfeld.Bridge

namespace RootIrr

variable {G : Type*} [Group G]

structure FormHyp (M A B : Subgroup G) : Prop where
  le_B : A ≤ B
  le_M : B ≤ M
  central : ∀ α ∈ A, ∀ m ∈ M, Commute α m
  comm : ∀ m ∈ M, ∀ m' ∈ M, m * m' * m⁻¹ * m'⁻¹ ∈ A
  sq : ∀ m ∈ M, m * m ∈ A

namespace FormHyp

variable {M A B : Subgroup G} (h : FormHyp M A B)
include h

theorem comm_mul_left {m₁ m₂ m' : G} (h₁ : m₁ ∈ M) (h₂ : m₂ ∈ M) (h' : m' ∈ M) :
    m₁ * m₂ * m' * (m₁ * m₂)⁻¹ * m'⁻¹ =
      (m₂ * m' * m₂⁻¹ * m'⁻¹) * (m₁ * m' * m₁⁻¹ * m'⁻¹) := by
  have hc := h.central _ (h.comm _ h₂ _ h') _ h₁
  have e : m₁ * (m₂ * m' * m₂⁻¹ * m'⁻¹) * m₁⁻¹ = m₂ * m' * m₂⁻¹ * m'⁻¹ := by
    rw [← hc.eq, mul_inv_cancel_right]
  calc m₁ * m₂ * m' * (m₁ * m₂)⁻¹ * m'⁻¹ =
      m₁ * (m₂ * m' * m₂⁻¹ * m'⁻¹) * m₁⁻¹ * (m₁ * m' * m₁⁻¹ * m'⁻¹) := by group
    _ = _ := by rw [e]

theorem comm_mul_right {m m₁ m₂ : G} (h' : m ∈ M) (h₁ : m₁ ∈ M) (h₂ : m₂ ∈ M) :
    m * (m₁ * m₂) * m⁻¹ * (m₁ * m₂)⁻¹ =
      (m * m₁ * m⁻¹ * m₁⁻¹) * (m * m₂ * m⁻¹ * m₂⁻¹) := by
  have hc := h.central _ (h.comm _ h' _ h₂) _ h₁
  have e : m₁ * (m * m₂ * m⁻¹ * m₂⁻¹) * m₁⁻¹ = m * m₂ * m⁻¹ * m₂⁻¹ := by
    rw [← hc.eq, mul_inv_cancel_right]
  calc m * (m₁ * m₂) * m⁻¹ * (m₁ * m₂)⁻¹ =
      (m * m₁ * m⁻¹ * m₁⁻¹) * (m₁ * (m * m₂ * m⁻¹ * m₂⁻¹) * m₁⁻¹) := by group
    _ = _ := by rw [e]

theorem comm_eq_one_left {α m : G} (hα : α ∈ A) (hm : m ∈ M) : α * m * α⁻¹ * m⁻¹ = 1 := by
  rw [(h.central _ hα _ hm).eq, mul_inv_cancel_right, mul_inv_cancel]

theorem comm_eq_one_right {α m : G} (hα : α ∈ A) (hm : m ∈ M) : m * α * m⁻¹ * α⁻¹ = 1 := by
  rw [← (h.central _ hα _ hm).eq, mul_inv_cancel_right, mul_inv_cancel]

variable {lam : G → ZMod 2} (hlam : ∀ α ∈ A, ∀ β ∈ A, lam (α * β) = lam α + lam β)
include hlam

omit h in
theorem lam_one : lam 1 = 0 := by
  have := hlam 1 A.one_mem 1 A.one_mem
  rw [mul_one] at this
  exact left_eq_add.mp this

theorem lam_mul_left {m₁ m₂ m' : G} (h₁ : m₁ ∈ M) (h₂ : m₂ ∈ M) (h' : m' ∈ M) :
    lam (m₁ * m₂ * m' * (m₁ * m₂)⁻¹ * m'⁻¹) =
      lam (m₁ * m' * m₁⁻¹ * m'⁻¹) + lam (m₂ * m' * m₂⁻¹ * m'⁻¹) := by
  rw [h.comm_mul_left h₁ h₂ h', hlam _ (h.comm _ h₂ _ h') _ (h.comm _ h₁ _ h'), add_comm]

theorem lam_mul_right {m m₁ m₂ : G} (h' : m ∈ M) (h₁ : m₁ ∈ M) (h₂ : m₂ ∈ M) :
    lam (m * (m₁ * m₂) * m⁻¹ * (m₁ * m₂)⁻¹) =
      lam (m * m₁ * m⁻¹ * m₁⁻¹) + lam (m * m₂ * m⁻¹ * m₂⁻¹) := by
  rw [h.comm_mul_right h' h₁ h₂, hlam _ (h.comm _ h' _ h₁) _ (h.comm _ h' _ h₂)]

theorem exists_eq_of_radical [Finite G]
    (hrad : ∀ b ∈ B, (∀ b' ∈ B, lam (b * b' * b⁻¹ * b'⁻¹) = 0) → b ∈ A) {m : G} (hm : m ∈ M) :
    ∃ b ∈ B, ∀ b' ∈ B, lam (m * b' * m⁻¹ * b'⁻¹) = lam (b * b' * b⁻¹ * b'⁻¹) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBM : ∀ b ∈ B, b ∈ M := fun b hb => h.le_M hb
  have hn : (A.subgroupOf B).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← (h.central _ hx _ (hBM _ g.2)).eq, mul_inv_cancel_right]
    exact hx⟩
  let instQ : CommGroup (↥B ⧸ A.subgroupOf B) :=
    { (inferInstance : Group (↥B ⧸ A.subgroupOf B)) with
      mul_comm := fun u v => by
        induction u using QuotientGroup.induction_on with
        | H b =>
          induction v using QuotientGroup.induction_on with
          | H b' =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have := h.comm _ (hBM _ (B.inv_mem b'.2)) _ (hBM _ (B.inv_mem b.2))
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            convert this using 1
            group }
  let instW : AddCommGroup (Additive (↥B ⧸ A.subgroupOf B)) := Additive.addCommGroup
  let instMod : Module (ZMod 2) (Additive (↥B ⧸ A.subgroupOf B)) :=
    AddCommGroup.zmodModule (n := 2) fun w => by
      obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
      have hw : w = Additive.ofMul (b : ↥B ⧸ A.subgroupOf B) := by rw [hb]; rfl
      rw [hw, two_nsmul, ← ofMul_mul, ← QuotientGroup.mk_mul, ofMul_eq_zero,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      exact h.sq _ (hBM _ b.2)
  have : Finite (Additive (↥B ⧸ A.subgroupOf B)) :=
    Finite.of_surjective (fun b : ↥B => Additive.ofMul (b : ↥B ⧸ A.subgroupOf B))
      (fun w => QuotientGroup.mk_surjective (Additive.toMul w))
  have : FiniteDimensional (ZMod 2) (Additive (↥B ⧸ A.subgroupOf B)) :=
    Module.Finite.of_finite
  let φ : ∀ g : G, g ∈ M → ↥B →* Multiplicative (ZMod 2) := fun g hg =>
    { toFun := fun b => Multiplicative.ofAdd (lam (g * b * g⁻¹ * (b : G)⁻¹))
      map_one' := by
        simp only [OneMemClass.coe_one, mul_one, inv_one, mul_inv_cancel]
        rw [lam_one hlam, ofAdd_zero]
      map_mul' := fun b b' => by
        simp only [Subgroup.coe_mul]
        rw [h.lam_mul_right hlam hg (hBM _ b.2) (hBM _ b'.2), ofAdd_add] }
  have hφ : ∀ g (hg : g ∈ M), A.subgroupOf B ≤ (φ g hg).ker := by
    intro g hg x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (lam (g * x * g⁻¹ * (x : G)⁻¹)) = 1
    rw [h.comm_eq_one_right hx hg, lam_one hlam, ofAdd_zero]
  let L : ∀ g : G, g ∈ M → Additive (↥B ⧸ A.subgroupOf B) →ₗ[ZMod 2] ZMod 2 := fun g hg =>
    (MonoidHom.toAdditiveLeft (QuotientGroup.lift _ (φ g hg) (hφ g hg))).toZModLinearMap 2
  have hL : ∀ g (hg : g ∈ M) (b : ↥B),
      L g hg (Additive.ofMul (b : ↥B ⧸ A.subgroupOf B)) = lam (g * b * g⁻¹ * (b : G)⁻¹) :=
    fun _ _ _ => rfl
  let Φ : ↥B →* Multiplicative (Module.Dual (ZMod 2) (Additive (↥B ⧸ A.subgroupOf B))) :=
    { toFun := fun b => Multiplicative.ofAdd (L b (hBM _ b.2))
      map_one' := by
        rw [← ofAdd_zero]
        congr 1
        refine LinearMap.ext fun w => ?_
        induction w using QuotientGroup.induction_on with
        | H b' =>
          change lam (((1 : ↥B) : G) * b' * ((1 : ↥B) : G)⁻¹ * (b' : G)⁻¹) = 0
          simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, mul_inv_cancel]
          exact lam_one hlam
      map_mul' := fun b₁ b₂ => by
        rw [← ofAdd_add]
        congr 1
        refine LinearMap.ext fun w => ?_
        induction w using QuotientGroup.induction_on with
        | H b' =>
          change lam (((b₁ * b₂ : ↥B) : G) * b' * ((b₁ * b₂ : ↥B) : G)⁻¹ * (b' : G)⁻¹) =
            lam ((b₁ : G) * b' * (b₁ : G)⁻¹ * (b' : G)⁻¹) +
              lam ((b₂ : G) * b' * (b₂ : G)⁻¹ * (b' : G)⁻¹)
          simp only [Subgroup.coe_mul]
          exact h.lam_mul_left hlam (hBM _ b₁.2) (hBM _ b₂.2) (hBM _ b'.2) }
  have hΦ : A.subgroupOf B ≤ Φ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (L x (hBM _ x.2)) =
      Multiplicative.ofAdd (0 : Module.Dual (ZMod 2) (Additive (↥B ⧸ A.subgroupOf B)))
    congr 1
    refine LinearMap.ext fun w => ?_
    induction w using QuotientGroup.induction_on with
    | H b' =>
      change lam ((x : G) * b' * (x : G)⁻¹ * (b' : G)⁻¹) = 0
      rw [h.comm_eq_one_left hx (hBM _ b'.2), lam_one hlam]
  let Ψ : Additive (↥B ⧸ A.subgroupOf B) →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Additive (↥B ⧸ A.subgroupOf B)) :=
    (MonoidHom.toAdditiveLeft (QuotientGroup.lift _ Φ hΦ)).toZModLinearMap 2
  have hΨ : ∀ b : ↥B, Ψ (Additive.ofMul (b : ↥B ⧸ A.subgroupOf B)) = L b (hBM _ b.2) :=
    fun _ => rfl
  have hinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun w hw => ?_
    induction w using QuotientGroup.induction_on with
    | H b =>
      change Ψ (Additive.ofMul (b : ↥B ⧸ A.subgroupOf B)) = 0 at hw
      rw [hΨ] at hw
      have hbA : (b : G) ∈ A := hrad _ b.2 fun b' hb' => by
        have := LinearMap.congr_fun hw (Additive.ofMul ((⟨b', hb'⟩ : ↥B) : ↥B ⧸ A.subgroupOf B))
        rwa [hL (b : G) (hBM _ b.2), LinearMap.zero_apply] at this
      change ((b : ↥B ⧸ A.subgroupOf B)) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hbA
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w, hw⟩ := hsurj (L m hm)
  induction w using QuotientGroup.induction_on with
  | H b =>
    change Ψ (Additive.ofMul (b : ↥B ⧸ A.subgroupOf B)) = L m hm at hw
    rw [hΨ] at hw
    refine ⟨b, b.2, fun b' hb' => ?_⟩
    have := LinearMap.congr_fun hw (Additive.ofMul ((⟨b', hb'⟩ : ↥B) : ↥B ⧸ A.subgroupOf B))
    rw [hL (b : G) (hBM _ b.2), hL m hm] at this
    exact this.symm

end FormHyp

theorem exists_lam (A : Subgroup G) (hcomm : ∀ x ∈ A, ∀ y ∈ A, Commute x y)
    (hsq : ∀ x ∈ A, x * x = 1) {α : G} (hα : α ∈ A) (hα1 : α ≠ 1) :
    ∃ lam : G → ZMod 2, (∀ x ∈ A, ∀ y ∈ A, lam (x * y) = lam x + lam y) ∧ lam α ≠ 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let instC : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun x y => Subtype.ext (hcomm _ x.2 _ y.2).eq }
  let instW : AddCommGroup (Additive ↥A) := Additive.addCommGroup
  let instMod : Module (ZMod 2) (Additive ↥A) :=
    AddCommGroup.zmodModule (n := 2) fun w => by
      rw [two_nsmul]
      change Additive.ofMul (Additive.toMul w * Additive.toMul w) = 0
      rw [ofMul_eq_zero]
      exact Subtype.ext (hsq _ (Additive.toMul w).2)
  have hw : Additive.ofMul (⟨α, hα⟩ : ↥A) ≠ 0 := fun h =>
    hα1 (congrArg Subtype.val (ofMul_eq_zero.1 h))
  obtain ⟨φ, hφ⟩ := not_forall.1 fun h =>
    hw ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) (Additive.ofMul (⟨α, hα⟩ : ↥A))).1 h)
  refine ⟨fun g => if hg : g ∈ A then φ (Additive.ofMul ⟨g, hg⟩) else 0, fun x hx y hy => ?_, ?_⟩
  · simp only [hx, hy, A.mul_mem hx hy, ↓reduceDIte]
    rw [← map_add]
    rfl
  · simpa only [hα, ↓reduceDIte] using hφ

end RootIrr

end CFSG.Timmesfeld.Bridge
