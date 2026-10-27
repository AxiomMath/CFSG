module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

section Isotropic

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem two_mul_finrank_le_of_isotropic_form (B : LinearMap.BilinForm F W) (hB : B.Nondegenerate)
    (U : Submodule F W) (hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 0) :
    2 * Module.finrank F U ≤ Module.finrank F W := by
  have hle : U ≤ B.orthogonal U := fun y hy =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 (fun x hx => hU x hx y hy)
  have h1 : Module.finrank F U ≤ Module.finrank F (B.orthogonal U) :=
    Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hB U
  omega

end Isotropic

section Commutators

variable {N : Type*} [Group N]

theorem commutator_mul_left_of_central (hcen : ∀ a b n : N, ⁅a, b⁆ * n = n * ⁅a, b⁆) (a b c : N) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, ← hcen b c a]
  simp only [mul_assoc, mul_inv_cancel_left]
  exact hcen b c ⁅a, c⁆

theorem commutator_mul_right_of_central (hcen : ∀ a b n : N, ⁅a, b⁆ * n = n * ⁅a, b⁆) (a b c : N) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h := hcen a c b
  calc ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ := by group
    _ = ⁅a, b⁆ * (⁅a, c⁆ * b) * b⁻¹ := by rw [h]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by group

end Commutators

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

section Pairing

theorem exists_pairing {N : Type*} [Group N] (V : Subgroup N)
    (hVcen : ∀ v ∈ V, ∀ n : N, v * n = n * v) (hcomm : ∀ x y : N, ⁅x, y⁆ ∈ V)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (v₀ : N) (hv₀V : v₀ ∈ V) (hv₀ : v₀ ≠ 1) :
    ∃ pr : N → N → ZMod 2,
      (∀ x y z, pr (x * y) z = pr x z + pr y z) ∧
      (∀ x y z, pr x (y * z) = pr x y + pr x z) ∧
      (∀ v ∈ V, ∀ y, pr v y = 0) ∧
      (∀ x, ∀ v ∈ V, pr x v = 0) ∧
      (∀ x y, pr x y = pr y x) ∧
      (∀ x y, ⁅x, y⁆ = 1 → pr x y = 0) ∧
      (∀ x y, ⁅x, y⁆ = v₀ → pr x y = 1) := by
  have hcen : ∀ a b n : N, ⁅a, b⁆ * n = n * ⁅a, b⁆ := fun a b n => hVcen _ (hcomm a b) n
  have hL := commutator_mul_left_of_central hcen
  have hR := commutator_mul_right_of_central hcen
  have hinv : ∀ v ∈ V, v⁻¹ = v := fun v hv =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV2 v hv)
  letI : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hVcen a.1 a.2 b.1) }
  have hVexp : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    show Additive.ofMul ((Additive.toMul x) ^ 2) = Additive.ofMul 1
    exact congrArg Additive.ofMul (Subtype.ext (hV2 _ (Additive.toMul x).2))
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule hVexp
  have hne : (Additive.ofMul (⟨v₀, hv₀V⟩ : V)) ≠ 0 := by
    intro h
    have h2 : Additive.ofMul (⟨v₀, hv₀V⟩ : V) = Additive.ofMul (1 : V) := h
    exact hv₀ (congrArg Subtype.val (Additive.ofMul.injective h2))
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hne
  have hφ0 : ∀ x y : N, ⁅x, y⁆ = 1 → lam (Additive.ofMul ⟨⁅x, y⁆, hcomm x y⟩) = 0 := by
    intro x y h
    have e : (Additive.ofMul ⟨⁅x, y⁆, hcomm x y⟩ : Additive V) = 0 :=
      congrArg Additive.ofMul (Subtype.ext h)
    rw [e, map_zero]
  refine ⟨fun x y => lam (Additive.ofMul ⟨⁅x, y⁆, hcomm x y⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    dsimp only
    rw [← map_add]
    congr 1
    exact congrArg Additive.ofMul (Subtype.ext (hL x y z))
  · intro x y z
    dsimp only
    rw [← map_add]
    congr 1
    exact congrArg Additive.ofMul (Subtype.ext (hR x y z))
  · intro v hv y
    exact hφ0 v y (commutatorElement_eq_one_iff_mul_comm.mpr (hVcen v hv y))
  · intro x v hv
    exact hφ0 x v (commutatorElement_eq_one_iff_mul_comm.mpr (hVcen v hv x).symm)
  · intro x y
    dsimp only
    have e : ⁅y, x⁆ = ⁅x, y⁆ := by
      have h := hinv _ (hcomm x y)
      rw [commutatorElement_inv] at h
      exact h
    have e2 : (Additive.ofMul ⟨⁅y, x⁆, hcomm y x⟩ : Additive V) =
        Additive.ofMul ⟨⁅x, y⁆, hcomm x y⟩ := congrArg Additive.ofMul (Subtype.ext e)
    rw [e2]
  · intro x y h
    exact hφ0 x y h
  · intro x y h
    dsimp only
    have e : (Additive.ofMul ⟨⁅x, y⁆, hcomm x y⟩ : Additive V) = Additive.ofMul ⟨v₀, hv₀V⟩ :=
      congrArg Additive.ofMul (Subtype.ext h)
    rw [e, hlam]

end Pairing

section Descent

theorem bilin_of_pairing {N G : Type*} [Group N] [CommGroup G] [Module (ZMod 2) (Additive G)]
    (p : N →* G) (hp : Function.Surjective p) (V : Subgroup N)
    (hker : ∀ n : N, p n = 1 ↔ n ∈ V) (pr : N → N → ZMod 2)
    (h1 : ∀ x y z, pr (x * y) z = pr x z + pr y z)
    (h2 : ∀ x y z, pr x (y * z) = pr x y + pr x z)
    (h3 : ∀ v ∈ V, ∀ y, pr v y = 0) (h4 : ∀ x, ∀ v ∈ V, pr x v = 0) :
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive G), ∀ x y : N,
      B (Additive.ofMul (p x)) (Additive.ofMul (p y)) = pr x y := by
  have hres1 : ∀ x x' z : N, p x' = p x → pr x' z = pr x z := by
    intro x x' z h
    have hv : x⁻¹ * x' ∈ V := (hker _).1 (by rw [map_mul, map_inv, h, inv_mul_cancel])
    have e : x' = x * (x⁻¹ * x') := (mul_inv_cancel_left x x').symm
    rw [e, h1, h3 _ hv, add_zero]
  have hres2 : ∀ x y y' : N, p y' = p y → pr x y' = pr x y := by
    intro x y y' h
    have hv : y⁻¹ * y' ∈ V := (hker _).1 (by rw [map_mul, map_inv, h, inv_mul_cancel])
    have e : y' = y * (y⁻¹ * y') := (mul_inv_cancel_left y y').symm
    rw [e, h2, h4 x _ hv, add_zero]
  have hΦ : ∃ Φ : G → G → ZMod 2, ∀ x y : N, Φ (p x) (p y) = pr x y := by
    refine ⟨fun q₁ q₂ => pr (Function.surjInv hp q₁) (Function.surjInv hp q₂), fun x y => ?_⟩
    exact (hres1 x (Function.surjInv hp (p x)) (Function.surjInv hp (p y))
      (Function.surjInv_eq hp (p x))).trans
      (hres2 x y (Function.surjInv hp (p y)) (Function.surjInv_eq hp (p y)))
  obtain ⟨Φ, hΦ⟩ := hΦ
  have hmul1 : ∀ q₁ q₂ q : G, Φ (q₁ * q₂) q = Φ q₁ q + Φ q₂ q := by
    intro q₁ q₂ q
    obtain ⟨x₁, rfl⟩ := hp q₁
    obtain ⟨x₂, rfl⟩ := hp q₂
    obtain ⟨y, rfl⟩ := hp q
    rw [← map_mul, hΦ, hΦ, hΦ, h1]
  have hmul2 : ∀ q q₁ q₂ : G, Φ q (q₁ * q₂) = Φ q q₁ + Φ q q₂ := by
    intro q q₁ q₂
    obtain ⟨x, rfl⟩ := hp q
    obtain ⟨x₁, rfl⟩ := hp q₁
    obtain ⟨x₂, rfl⟩ := hp q₂
    rw [← map_mul, hΦ, hΦ, hΦ, h2]
  have hone1 : ∀ q : G, Φ 1 q = 0 := by
    intro q
    obtain ⟨x, hx⟩ := hp 1
    obtain ⟨y, rfl⟩ := hp q
    rw [← hx, hΦ]
    exact h3 x ((hker x).1 hx) y
  have hone2 : ∀ q : G, Φ q 1 = 0 := by
    intro q
    obtain ⟨x, hx⟩ := hp 1
    obtain ⟨y, rfl⟩ := hp q
    rw [← hx, hΦ]
    exact h4 y x ((hker x).1 hx)
  refine ⟨LinearMap.mk₂ (ZMod 2) (fun w₁ w₂ => Φ (Additive.toMul w₁) (Additive.toMul w₂))
    (fun m₁ m₂ n => hmul1 (Additive.toMul m₁) (Additive.toMul m₂) (Additive.toMul n))
    (fun c m n => ?_)
    (fun m n₁ n₂ => hmul2 (Additive.toMul m) (Additive.toMul n₁) (Additive.toMul n₂))
    (fun c m n => ?_), fun x y => ?_⟩
  · rcases zmod_two_cases c with rfl | rfl
    · simp only [zero_smul]
      exact hone1 _
    · simp only [one_smul]
  · rcases zmod_two_cases c with rfl | rfl
    · simp only [zero_smul]
      exact hone2 _
    · simp only [one_smul]
  · simp only [LinearMap.mk₂_apply]
    exact hΦ x y

end Descent

section Main

theorem card_sq_le_of_abelian_in_semiextraspecial {N : Type*} [Group N] [Finite N] (V : Subgroup N)
    (hVcen : ∀ v ∈ V, ∀ n : N, v * n = n * v) (hcomm : ∀ x y : N, ⁅x, y⁆ ∈ V)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hZ : ∀ x : N, (∀ n : N, x * n = n * x) → x ∈ V)
    (hsemi : ∀ x : N, x ∉ V → ∀ v ∈ V, ∃ n : N, ⁅x, n⁆ = v)
    (A : Subgroup N) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ^ 2 ≤ Nat.card N * Nat.card V := by
  have hcen : ∀ a b n : N, ⁅a, b⁆ * n = n * ⁅a, b⁆ := fun a b n => hVcen _ (hcomm a b) n
  have hL := commutator_mul_left_of_central hcen
  have hsq : ∀ x : N, x ^ 2 ∈ V := by
    intro x
    apply hZ
    intro n
    have h1 : ⁅x ^ 2, n⁆ = 1 := by
      rw [pow_two, hL]
      have h := hV2 _ (hcomm x n)
      rw [pow_two] at h
      exact h
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  by_cases hV1 : ∃ v ∈ V, v ≠ 1
  swap
  · have hV1' : ∀ v ∈ V, v = 1 := fun v hv => by
      by_contra hne
      exact hV1 ⟨v, hv, hne⟩
    have hN1 : ∀ n : N, n = 1 := by
      intro n
      have hc : ∀ m : N, n * m = m * n := fun m =>
        commutatorElement_eq_one_iff_mul_comm.mp (hV1' _ (hcomm n m))
      exact hV1' n (hZ n hc)
    haveI : Subsingleton N := ⟨fun a b => by rw [hN1 a, hN1 b]⟩
    have hA1 : Nat.card A = 1 := Nat.card_of_subsingleton (1 : A)
    have hN1' : Nat.card N = 1 := Nat.card_of_subsingleton (1 : N)
    have hV1' : Nat.card V = 1 := Nat.card_of_subsingleton (1 : V)
    rw [hA1, hN1', hV1']
    norm_num
  obtain ⟨v₀, hv₀V, hv₀⟩ := hV1
  obtain ⟨pr, h1, h2, h3, h4, h5, h6, h7⟩ := exists_pairing V hVcen hcomm hV2 v₀ hv₀V hv₀
  haveI hVn : V.Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      rw [← hVcen n hn g]
      group
    rw [e]
    exact hn⟩
  have hGcomm : ∀ a b : N ⧸ V, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have h := hcomm y⁻¹ x⁻¹
        rw [commutatorElement_def] at h
        have e : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * (y⁻¹)⁻¹ * (x⁻¹)⁻¹ := by group
        rw [e]
        exact h
  letI hCG : CommGroup (N ⧸ V) := { (inferInstance : Group (N ⧸ V)) with mul_comm := hGcomm }
  haveI hFin : Finite (Additive (N ⧸ V)) := Finite.of_equiv (N ⧸ V) Additive.ofMul
  have hrep : ∀ (q : N ⧸ V) (w : Additive (N ⧸ V)), Additive.toMul w = q →
      w = Additive.ofMul q := by
    intro q w h
    subst h
    rfl
  have hW2 : ∀ w : Additive (N ⧸ V), (2 : ℕ) • w = 0 := by
    intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective V (Additive.toMul w)
    rw [hrep _ _ hx.symm]
    show Additive.ofMul (((x : N) : N ⧸ V) ^ 2) = Additive.ofMul 1
    congr 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsq x
  letI : Module (ZMod 2) (Additive (N ⧸ V)) := AddCommGroup.zmodModule hW2
  haveI hWfin : Module.Finite (ZMod 2) (Additive (N ⧸ V)) := Module.finite_iff_finite.mpr hFin
  have hsurjW : ∀ w : Additive (N ⧸ V), ∃ x : N, w = Additive.ofMul (QuotientGroup.mk' V x) := by
    intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective V (Additive.toMul w)
    exact ⟨x, hrep _ _ hx.symm⟩
  obtain ⟨B, hB⟩ := bilin_of_pairing (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V) V
    (fun n => by rw [QuotientGroup.mk'_apply]; exact QuotientGroup.eq_one_iff n) pr h1 h2 h3 h4
  have hrefl : LinearMap.IsRefl B := by
    intro w₁ w₂ h
    obtain ⟨x, rfl⟩ := hsurjW w₁
    obtain ⟨y, rfl⟩ := hsurjW w₂
    rw [hB x y] at h
    rw [hB y x, ← h5 x y]
    exact h
  have hsepL : LinearMap.SeparatingLeft B := by
    intro w hw
    obtain ⟨x, rfl⟩ := hsurjW w
    by_contra hne
    have hxV : x ∉ V := by
      intro hx
      have h1x : QuotientGroup.mk' V x = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff x).mpr hx
      exact hne (congrArg Additive.ofMul h1x)
    obtain ⟨n, hn⟩ := hsemi x hxV v₀ hv₀V
    have hBn := hw (Additive.ofMul (QuotientGroup.mk' V n))
    rw [hB x n, h7 x n hn] at hBn
    exact one_ne_zero hBn
  have hnd : B.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr hsepL
  let f : A →* N ⧸ V := (QuotientGroup.mk' V).comp A.subtype
  let U : Submodule (ZMod 2) (Additive (N ⧸ V)) :=
    { carrier := {w | Additive.toMul w ∈ f.range}
      add_mem' := fun {a b} ha hb => f.range.mul_mem ha hb
      zero_mem' := f.range.one_mem
      smul_mem' := by
        intro c w hw
        rcases zmod_two_cases c with rfl | rfl
        · rw [zero_smul]
          exact f.range.one_mem
        · rw [one_smul]
          exact hw }
  have hUmem : ∀ w : Additive (N ⧸ V), w ∈ U ↔ Additive.toMul w ∈ f.range :=
    fun w => Iff.rfl
  have hUa : ∀ w ∈ U, ∃ a : A, w = Additive.ofMul (QuotientGroup.mk' V (a : N)) := by
    intro w hw
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 ((hUmem w).1 hw)
    exact ⟨a, hrep _ _ ha.symm⟩
  have hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hUa x hx
    obtain ⟨b, rfl⟩ := hUa y hy
    rw [hB (a : N) (b : N)]
    exact h6 _ _ (commutatorElement_eq_one_iff_mul_comm.mpr (hA _ a.2 _ b.2))
  have h2u : 2 * Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (Additive (N ⧸ V)) :=
    two_mul_finrank_le_of_isotropic_form B hnd U hU
  have hKV : ∀ k : f.ker, ((k : A) : N) ∈ V := by
    intro k
    have hk : f (k : A) = 1 := MonoidHom.mem_ker.1 k.2
    have hk' : (((k : A) : N) : N ⧸ V) = 1 := hk
    exact (QuotientGroup.eq_one_iff _).1 hk'
  have hK : Nat.card f.ker ≤ Nat.card V := by
    refine Nat.card_le_card_of_injective (fun k : f.ker => (⟨((k : A) : N), hKV k⟩ : V)) ?_
    intro k₁ k₂ h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : V => (v : N)) h
  have hrange : Nat.card f.range = Nat.card U :=
    Nat.card_congr
      { toFun := fun q => ⟨Additive.ofMul q.1, q.2⟩
        invFun := fun w => ⟨Additive.toMul w.1, w.2⟩
        left_inv := fun q => rfl
        right_inv := fun w => rfl }
  have hUc : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [h, Nat.card_zmod]
  have hWc : Nat.card (Additive (N ⧸ V)) = 2 ^ Module.finrank (ZMod 2) (Additive (N ⧸ V)) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (N ⧸ V))
    rw [h, Nat.card_zmod]
  have hGc : Nat.card (N ⧸ V) = Nat.card (Additive (N ⧸ V)) := Nat.card_congr Additive.ofMul
  have hNV : Nat.card N = Nat.card (N ⧸ V) * Nat.card V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  have hAc : Nat.card A = Nat.card f.ker * Nat.card f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  have hN2 : Nat.card N = 2 ^ Module.finrank (ZMod 2) (Additive (N ⧸ V)) * Nat.card V := by
    rw [hNV, hGc, hWc]
  have hfin : Nat.card A = Nat.card f.ker * 2 ^ Module.finrank (ZMod 2) U := by
    rw [hAc, hrange, hUc]
  have hu : 2 ^ (2 * Module.finrank (ZMod 2) U) ≤
      2 ^ Module.finrank (ZMod 2) (Additive (N ⧸ V)) :=
    Nat.pow_le_pow_right (by norm_num) h2u
  rw [hN2]
  calc Nat.card A ^ 2 = Nat.card f.ker ^ 2 * 2 ^ (2 * Module.finrank (ZMod 2) U) := by
        rw [hfin]
        ring
    _ ≤ Nat.card V ^ 2 * 2 ^ Module.finrank (ZMod 2) (Additive (N ⧸ V)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hK 2) hu
    _ = 2 ^ Module.finrank (ZMod 2) (Additive (N ⧸ V)) * Nat.card V * Nat.card V := by ring

end Main

end CFSG.RankThree.GF2n.Stroth80
