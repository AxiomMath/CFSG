module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec17.Ronan1724BFT

open Module
open scoped commutatorElement

theorem commutatorElement_pow_three_eq_one {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) : ⁅x, y⁆ ^ 3 = 1 := by
  set z := ⁅x, y⁆ with hz
  have hcy : MulAut.conj x y = z * y := by
    rw [MulAut.conj_apply, hz, commutatorElement_def]
    group
  have hcz : MulAut.conj x z = z := by
    rw [MulAut.conj_apply, ← hzx.eq, mul_inv_cancel_right]
  have hpow : ∀ n : ℕ, (MulAut.conj x ^ n) y = z ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hcz, hcy, pow_succ, mul_assoc]
  have h3 := hpow 3
  rw [← map_pow, hx, map_one, MulAut.one_apply] at h3
  exact mul_eq_right.mp h3.symm

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem false_of_heisenberg_vec [FiniteDimensional K M] (h3 : (3 : K) ≠ 0)
    (hdim : finrank K M ≤ 5) (X Y Z G : M →ₗ[K] M)
    (hX3 : ∀ v, X (X (X v)) = v) (hZ3 : ∀ v, Z (Z (Z v)) = v)
    (hXZ : ∀ v, X (Z v) = Z (X v)) (hYZ : ∀ v, Y (Z v) = Z (Y v))
    (hXY : ∀ v, X (Y v) = Y (X (Z v))) (hGZ : ∀ v, G (Z v) = Z (Z (G v)))
    (hY : Function.Injective Y) (hG : Function.Injective G) (hZ1 : ∃ v, Z v ≠ v) : False := by
  set S : M →ₗ[K] M := LinearMap.id + Z + Z ∘ₗ Z with hS
  have hSapp : ∀ v, S v = v + Z v + Z (Z v) := fun v => by simp [hS]
  set W : Submodule K M := LinearMap.ker S with hWdef
  have hmemW : ∀ v, v ∈ W ↔ v + Z v + Z (Z v) = 0 := fun v => by
    rw [hWdef, LinearMap.mem_ker, hSapp]
  obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w ∈ W, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective S := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      exact hcon
    have hsurj : Function.Surjective S := LinearMap.injective_iff_surjective.mp hinj
    obtain ⟨v, hv⟩ := hZ1
    apply hv
    obtain ⟨u, rfl⟩ := hsurj v
    rw [hSapp, map_add, map_add, hZ3]
    abel
  have hXW : ∀ v ∈ W, X v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    have h : X v + Z (X v) + Z (Z (X v)) = X (v + Z v + Z (Z v)) := by
      rw [map_add, map_add, hXZ (Z v), hXZ v]
    rw [h, hv, map_zero]
  have hYW : ∀ v ∈ W, Y v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    have h : Y v + Z (Y v) + Z (Z (Y v)) = Y (v + Z v + Z (Z v)) := by
      rw [map_add, map_add, hYZ (Z v), hYZ v]
    rw [h, hv, map_zero]
  have hZW : ∀ v ∈ W, Z v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    have h : Z v + Z (Z v) + Z (Z (Z v)) = v + Z v + Z (Z v) := by
      rw [hZ3]
      abel
    rw [h, hv]
  have hGW : ∀ v ∈ W, G v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    have h1 : G (Z v) = Z (Z (G v)) := hGZ v
    have h2 : G (Z (Z v)) = Z (G v) := by rw [hGZ (Z v), h1, hZ3 (Z (G v))]
    have h : G v + Z (G v) + Z (Z (G v)) = G (v + Z v + Z (Z v)) := by
      rw [map_add, map_add, h1, h2]
      abel
    rw [h, hv, map_zero]
  set V₀ : Submodule K M := W ⊓ LinearMap.ker (X - LinearMap.id) with hV₀
  set V₁ : Submodule K M := W ⊓ LinearMap.ker (X - Z) with hV₁
  set V₂ : Submodule K M := W ⊓ LinearMap.ker (X - Z ∘ₗ Z) with hV₂
  have hmem₀ : ∀ v, v ∈ V₀ ↔ v ∈ W ∧ X v = v := fun v => by
    simp only [hV₀, Submodule.mem_inf, LinearMap.mem_ker (f := X - LinearMap.id),
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hmem₁ : ∀ v, v ∈ V₁ ↔ v ∈ W ∧ X v = Z v := fun v => by
    simp only [hV₁, Submodule.mem_inf, LinearMap.mem_ker (f := X - Z), LinearMap.sub_apply,
      sub_eq_zero]
  have hmem₂ : ∀ v, v ∈ V₂ ↔ v ∈ W ∧ X v = Z (Z v) := fun v => by
    simp only [hV₂, Submodule.mem_inf, LinearMap.mem_ker (f := X - Z ∘ₗ Z), LinearMap.sub_apply,
      LinearMap.comp_apply, sub_eq_zero]
  have hY01 : ∀ v ∈ V₀, Y v ∈ V₁ := by
    intro v hv
    rw [hmem₀] at hv
    rw [hmem₁]
    refine ⟨hYW v hv.1, ?_⟩
    rw [hXY, hXZ, hv.2, hYZ]
  have hY12 : ∀ v ∈ V₁, Y v ∈ V₂ := by
    intro v hv
    rw [hmem₁] at hv
    rw [hmem₂]
    refine ⟨hYW v hv.1, ?_⟩
    rw [hXY, hXZ, hv.2, hYZ, hYZ]
  have hY20 : ∀ v ∈ V₂, Y v ∈ V₀ := by
    intro v hv
    rw [hmem₂] at hv
    rw [hmem₀]
    refine ⟨hYW v hv.1, ?_⟩
    rw [hXY, hXZ, hv.2, hZ3]
  have hZ00 : ∀ v ∈ V₀, Z v ∈ V₀ := by
    intro v hv
    rw [hmem₀] at hv ⊢
    exact ⟨hZW v hv.1, by rw [hXZ, hv.2]⟩
  have hinjR : ∀ {p q : Submodule K M} (h : ∀ v ∈ p, Y v ∈ q),
      Function.Injective (Y.restrict h) := by
    intro p q h a b hab
    apply Subtype.ext
    apply hY
    have := congrArg Subtype.val hab
    simpa using this
  have hd01 := LinearMap.finrank_le_finrank_of_injective (hinjR hY01)
  have hd12 := LinearMap.finrank_le_finrank_of_injective (hinjR hY12)
  have hd20 := LinearMap.finrank_le_finrank_of_injective (hinjR hY20)
  have hindep : finrank K V₀ + finrank K V₁ + finrank K V₂ ≤ 5 := by
    let Φ : (V₀ × V₁ × V₂) →ₗ[K] M := V₀.subtype.coprod (V₁.subtype.coprod V₂.subtype)
    have hΦ : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨a, b, c⟩ habc
      rw [LinearMap.mem_ker] at habc
      have e₀ : (a : M) + ((b : M) + (c : M)) = 0 := by
        simpa [Φ, LinearMap.coprod_apply] using habc
      have hXa : X a = a := ((hmem₀ a).1 a.2).2
      have hXb : X b = Z b := ((hmem₁ b).1 b.2).2
      have hXc : X c = Z (Z c) := ((hmem₂ c).1 c.2).2
      have hbW : (b : M) + Z b + Z (Z b) = 0 := (hmemW b).1 ((hmem₁ b).1 b.2).1
      have hcW : (c : M) + Z c + Z (Z c) = 0 := (hmemW c).1 ((hmem₂ c).1 c.2).1
      have e₁ : (a : M) + (Z b + Z (Z c)) = 0 := by
        have h := congrArg X e₀
        rwa [map_add, map_add, hXa, hXb, hXc, map_zero] at h
      have e₂ : (a : M) + (Z (Z b) + Z c) = 0 := by
        have h := congrArg X e₁
        simp only [map_add, map_zero, hXa, hXZ, hXb, hXc, hZ3] at h
        exact h
      have ha3 : (3 : K) • (a : M) = 0 := by
        have h : (3 : K) • (a : M) = ((a : M) + ((b : M) + (c : M))) + ((a : M) + (Z b + Z (Z c)))
            + ((a : M) + (Z (Z b) + Z c)) - ((b : M) + Z b + Z (Z b))
            - ((c : M) + Z c + Z (Z c)) := by module
        rw [h, e₀, e₁, e₂, hbW, hcW]
        simp
      have ha : (a : M) = 0 := by
        rcases smul_eq_zero.mp ha3 with h | h
        · exact absurd h h3
        · exact h
      have hc' : (c : M) = -(b : M) := by
        rw [ha, zero_add] at e₀
        exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact e₀)
      have hZb : Z b = Z (Z b) := by
        rw [ha, zero_add, hc', map_neg, map_neg, ← sub_eq_add_neg, sub_eq_zero] at e₁
        exact e₁
      have hb1 : (b : M) = Z b := by
        have h := congrArg (fun v => Z (Z v)) hZb
        simp only [hZ3] at h
        exact h
      have hb : (b : M) = 0 := by
        have h3b : (3 : K) • (b : M) = 0 := by
          have h : (3 : K) • (b : M) = (b : M) + Z b + Z (Z b) := by
            rw [← hb1, ← hb1]
            module
          rw [h]
          exact hbW
        rcases smul_eq_zero.mp h3b with h | h
        · exact absurd h h3
        · exact h
      have hc : (c : M) = 0 := by rw [hc', hb, neg_zero]
      refine Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hc))
    have h := LinearMap.finrank_le_finrank_of_injective hΦ
    rw [Module.finrank_prod, Module.finrank_prod] at h
    omega
  have hspan : ∀ w ∈ W, ∃ p₀ ∈ V₀, ∃ p₁ ∈ V₁, ∃ p₂ ∈ V₂, (3 : K) • w = p₀ + p₁ + p₂ := by
    intro w hw
    have hXw := hXW w hw
    have hXXw := hXW _ hXw
    refine ⟨w + X w + X (X w), ?_, w + Z (Z (X w)) + Z (X (X w)), ?_,
      w + Z (X w) + Z (Z (X (X w))), ?_, ?_⟩
    · rw [hmem₀]
      refine ⟨W.add_mem (W.add_mem hw hXw) hXXw, ?_⟩
      rw [map_add, map_add, hX3]
      abel
    · rw [hmem₁]
      refine ⟨W.add_mem (W.add_mem hw (hZW _ (hZW _ hXw))) (hZW _ hXXw), ?_⟩
      simp only [map_add, hXZ, hX3, hZ3]
      abel
    · rw [hmem₂]
      refine ⟨W.add_mem (W.add_mem hw (hZW _ hXw)) (hZW _ (hZW _ hXXw)), ?_⟩
      simp only [map_add, hXZ, hX3, hZ3]
      abel
    · have hs1 := (hmemW _).1 hXw
      have hs2 := (hmemW _).1 hXXw
      have h : (3 : K) • w = (w + X w + X (X w)) + (w + Z (Z (X w)) + Z (X (X w))) +
          (w + Z (X w) + Z (Z (X (X w)))) - (X w + Z (X w) + Z (Z (X w))) -
          (X (X w) + Z (X (X w)) + Z (Z (X (X w)))) := by module
      rw [h, hs1, hs2, sub_zero, sub_zero]
  have hpos : 0 < finrank K V₀ := by
    by_contra hd
    have hd0 : finrank K V₀ = 0 := by omega
    have hd1 : finrank K V₁ = 0 := by omega
    have hd2 : finrank K V₂ = 0 := by omega
    obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, hsum⟩ := hspan w₀ hw₀W
    have h0 : p₀ = 0 := by
      rw [Submodule.finrank_eq_zero.mp hd0] at hp₀
      exact (Submodule.mem_bot K).mp hp₀
    have h1 : p₁ = 0 := by
      rw [Submodule.finrank_eq_zero.mp hd1] at hp₁
      exact (Submodule.mem_bot K).mp hp₁
    have h2 : p₂ = 0 := by
      rw [Submodule.finrank_eq_zero.mp hd2] at hp₂
      exact (Submodule.mem_bot K).mp hp₂
    rw [h0, h1, h2, add_zero, add_zero] at hsum
    rcases smul_eq_zero.mp hsum with h | h
    · exact h3 h
    · exact hw₀ h
  have hd : finrank K V₀ = 1 := by omega
  obtain ⟨u₀, -, hspan₀⟩ := finrank_eq_one_iff'.mp hd
  obtain ⟨μ, hμ⟩ := hspan₀ ⟨Z u₀, hZ00 _ u₀.2⟩
  have hμ' : Z u₀ = μ • (u₀ : M) := by
    have h := congrArg Subtype.val hμ
    simpa using h.symm
  have hmu0 : ∀ v ∈ V₀, Z v = μ • v := by
    intro v hv
    obtain ⟨c, hc⟩ := hspan₀ ⟨v, hv⟩
    have hv' : v = c • (u₀ : M) := by
      have h := congrArg Subtype.val hc
      simpa using h.symm
    rw [hv', map_smul, hμ', smul_comm]
  have hmu2 : ∀ v ∈ V₂, Z v = μ • v := by
    intro v hv
    apply hY
    rw [hYZ, hmu0 _ (hY20 v hv), map_smul]
  have hmu1 : ∀ v ∈ V₁, Z v = μ • v := by
    intro v hv
    apply hY
    rw [hYZ, hmu2 _ (hY12 v hv), map_smul]
  have hmuW : ∀ w ∈ W, Z w = μ • w := by
    intro w hw
    obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, hsum⟩ := hspan w hw
    have h : (3 : K) • Z w = (3 : K) • (μ • w) := by
      rw [← map_smul, hsum, map_add, map_add, hmu0 _ hp₀, hmu1 _ hp₁, hmu2 _ hp₂,
        smul_comm (3 : K) μ w, hsum, smul_add, smul_add]
    exact smul_right_injective M h3 h
  have hZw₀ := hmuW w₀ hw₀W
  have hpoly : 1 + μ + μ ^ 2 = 0 := by
    have h := (hmemW w₀).1 hw₀W
    rw [hZw₀, map_smul, hZw₀, smul_smul] at h
    have h' : (1 + μ + μ ^ 2) • w₀ = 0 := by
      rw [← h]
      module
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' hw₀
  have hGw₀W := hGW w₀ hw₀W
  have hGw₀ : G w₀ ≠ 0 := fun h => hw₀ (hG (by rw [h, map_zero]))
  have hμμ : μ = μ ^ 2 := by
    have h := hGZ w₀
    rw [hZw₀, map_smul, hmuW _ hGw₀W, map_smul, hmuW _ hGw₀W, smul_smul] at h
    have h' : (μ - μ ^ 2) • G w₀ = 0 := by rw [sub_smul, h, sq, sub_self]
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd h'' hGw₀
  have hμ01 : μ = 0 ∨ μ = 1 := by
    have h : μ * (1 - μ) = 0 := by
      rw [mul_sub, mul_one, ← sq]
      exact sub_eq_zero.mpr hμμ
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (sub_eq_zero.mp h').symm
  rcases hμ01 with h | h
  · rw [h] at hpoly
    norm_num at hpoly
  · rw [h] at hpoly
    apply h3
    linear_combination hpoly

theorem gl_mul_apply (a b : LinearMap.GeneralLinearGroup K M) (v : M) :
    ((a * b : LinearMap.GeneralLinearGroup K M) : M →ₗ[K] M) v =
      (a : M →ₗ[K] M) ((b : M →ₗ[K] M) v) := rfl

theorem gl_injective (a : LinearMap.GeneralLinearGroup K M) :
    Function.Injective (a : M →ₗ[K] M) := by
  intro u v h
  have key : ∀ w : M,
      ((a⁻¹ : LinearMap.GeneralLinearGroup K M) : M →ₗ[K] M) ((a : M →ₗ[K] M) w) = w := fun w => by
    rw [← gl_mul_apply, inv_mul_cancel]
    rfl
  have h' := congrArg ((a⁻¹ : LinearMap.GeneralLinearGroup K M) : M →ₗ[K] M) h
  rwa [key, key] at h'

theorem false_of_gl_heisenberg [FiniteDimensional K M] (h3 : (3 : K) ≠ 0)
    (hdim : finrank K M ≤ 5) {x y g : LinearMap.GeneralLinearGroup K M} (hx : x ^ 3 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (hz1 : ⁅x, y⁆ ≠ 1)
    (hg : g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆⁻¹) : False := by
  set z := ⁅x, y⁆ with hz
  have hz3 : z ^ 3 = 1 := commutatorElement_pow_three_eq_one hx hzx hzy
  have hxy : x * y = y * (x * z) := by
    have h1 : x * y = z * y * x := by
      rw [hz, commutatorElement_def]
      group
    rw [h1, hzy.eq, mul_assoc, hzx.eq]
  have hzinv : z⁻¹ = z ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hz3)
  have hgz : g * z = z * (z * g) := by
    rw [← mul_assoc, ← sq, ← hzinv, ← hg]
    group
  have hx3 : x * (x * x) = 1 := by rw [← pow_three]; exact hx
  have hz3' : z * (z * z) = 1 := by rw [← pow_three]; exact hz3
  have happ : ∀ {a b : LinearMap.GeneralLinearGroup K M}, a = b → ∀ v : M,
      (a : M →ₗ[K] M) v = (b : M →ₗ[K] M) v := fun h v => by rw [h]
  refine false_of_heisenberg_vec h3 hdim (x : M →ₗ[K] M) (y : M →ₗ[K] M) (z : M →ₗ[K] M)
    (g : M →ₗ[K] M) (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_)
    (fun v => ?_) (gl_injective y) (gl_injective g) ?_
  · simpa only [gl_mul_apply, Units.val_one, Module.End.one_apply] using happ hx3 v
  · simpa only [gl_mul_apply, Units.val_one, Module.End.one_apply] using happ hz3' v
  · simpa only [gl_mul_apply] using (happ hzx.eq v).symm
  · simpa only [gl_mul_apply] using (happ hzy.eq v).symm
  · simpa only [gl_mul_apply] using happ hxy v
  · simpa only [gl_mul_apply] using happ hgz v
  · by_contra hcon
    push Not at hcon
    apply hz1
    ext v
    exact hcon v
