module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.RankThree.Literature.FSmithOrthogonal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.Literature.FSmith

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Center

variable {H : Type*} [Group H] {Q : Subgroup H}

theorem ofMul_of_inv (x : Q) :
    Additive.ofMul (Abelianization.of x⁻¹) = -Additive.ofMul (Abelianization.of x) := by
  rw [map_inv, ofMul_inv]

theorem ofMul_of_eq_iff (hQ : IsExtraspecialPGroup 2 Q) (x y : Q) :
    Additive.ofMul (Abelianization.of x) = Additive.ofMul (Abelianization.of y) ↔
      x * y⁻¹ ∈ center Q := by
  rw [← ofMul_of_eq_zero_iff hQ, ofMul_of_mul, ofMul_of_inv, ← sub_eq_add_neg, sub_eq_zero]

theorem mem_center_iff_coe (hQ : IsExtraspecialPGroup 2 Q) {z₀ : H}
    (hz₀ : ∀ g : H, g * z₀ = z₀ * g) (hz₀1 : z₀ ≠ 1) (hz₀Q : z₀ ∈ Q) {x : Q} :
    x ∈ center Q ↔ (x : H) = 1 ∨ (x : H) = z₀ := by
  have hzc : (⟨z₀, hz₀Q⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g => Subtype.ext (hz₀ g)
  constructor
  · intro hx
    by_cases h1 : x = 1
    · left
      rw [h1]
      rfl
    · right
      have hz1' : (⟨z₀, hz₀Q⟩ : Q) ≠ 1 := fun h => hz₀1 (congrArg Subtype.val h)
      exact congrArg Subtype.val (eq_of_mem_center hQ hx hzc h1 hz1')
  · rintro (h | h)
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = ⟨z₀, hz₀Q⟩ from Subtype.ext h]
      exact hzc

theorem sq_eq_one_of_central (hQ : IsExtraspecialPGroup 2 Q) {z₀ : H}
    (hz₀ : ∀ g : H, g * z₀ = z₀ * g) (hz₀Q : z₀ ∈ Q) : z₀ * z₀ = 1 := by
  have hzc : (⟨z₀, hz₀Q⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g => Subtype.ext (hz₀ g)
  have h := congrArg Subtype.val (sq_eq_one_of_mem_center hQ hzc)
  rwa [pow_two] at h

end Center

theorem zmod2_vec_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (u : V) :
    u + u = 0 := by
  rw [← two_smul (ZMod 2) u, show (2 : ZMod 2) = 0 from rfl, zero_smul]

section Construction

variable {H : Type*} [Group H] {Q : Subgroup H} [Finite Q] (hQ : IsExtraspecialPGroup 2 Q)
  (hQn : Q.Normal) [Module (ZMod 2) (Additive (Abelianization Q))]

omit [Finite Q] in
include hQ in
theorem conjLinEquiv_of_mem {b : H} (hb : b ∈ Q) : conjLinEquiv hQn b = 1 := by
  ext u
  obtain ⟨x, rfl⟩ := exists_ofMul_of u
  rw [conjLinEquiv_apply, LinearEquiv.coe_one, id]
  have h : conjAut hQn b x = ⁅(⟨b, hb⟩ : Q), x⁆ * x := Subtype.ext (by
    rw [conjAut_apply]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group)
  rw [h, ofMul_of_mul, (ofMul_of_eq_zero_iff hQ _).mpr (commutatorElement_mem_center hQ _ _),
    zero_add]

theorem conjAut_mul_inv_mem_center {g : H} {d : Q}
    (hg : ∀ u, conjLinEquiv hQn g u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d))
    {y : Q} (hy : y * d = d * y) : conjAut hQn g y * y⁻¹ ∈ center Q := by
  rw [← ofMul_of_eq_iff hQ, ← conjLinEquiv_apply, hg,
    (polar_extraspecialQuadForm_eq_zero_iff hQ y d).mpr hy, zero_smul, add_zero]

theorem conjAut_mul_inv_mem_center' {g : H} {d : Q}
    (hg : ∀ u, conjLinEquiv hQn g u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d))
    {y : Q} (hy : y * d ≠ d * y) : conjAut hQn g y * (y * d)⁻¹ ∈ center Q := by
  have h1 : polar (extraspecialQuadForm hQ) (Additive.ofMul (Abelianization.of y))
      (Additive.ofMul (Abelianization.of d)) = 1 :=
    zmod2_eq_one_of_ne_zero fun h => hy ((polar_extraspecialQuadForm_eq_zero_iff hQ y d).mp h)
  rw [← ofMul_of_eq_iff hQ, ← conjLinEquiv_apply, hg, h1, one_smul, ofMul_of_mul]


section Central

variable {z₀ : H} (hz₀ : ∀ g : H, g * z₀ = z₀ * g) (hz₀1 : z₀ ≠ 1) (hz₀Q : z₀ ∈ Q)
include hQ hz₀ hz₀1 hz₀Q

omit [Finite Q] [Module (ZMod 2) (Additive (Abelianization Q))] in
theorem conjAut_of_mem_center {c : Q} (hc : c ∈ center Q) (g : H) : conjAut hQn g c = c := by
  apply Subtype.ext
  rw [conjAut_apply]
  rcases (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp hc with h | h <;> rw [h]
  · group
  · rw [hz₀ g, mul_inv_cancel_right]

theorem coe_mul_self_eq {d : Q}
    (hd : extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of d)) = 1) :
    (d : H) * d = z₀ := by
  have h2 : d ^ 2 ≠ 1 := by
    intro h
    rw [extraspecialQuadForm_apply] at hd
    simp [h] at hd
  rcases (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp (sq_mem_center hQ d) with h | h
  · exact absurd (Subtype.ext h) h2
  · rw [← h, SubmonoidClass.coe_pow, pow_two]

end Central

include hQ in
theorem mem_center_or_of_forall_commute {d s : Q}
    (hs : ∀ y : Q, y * d = d * y → s * y = y * s) : s ∈ center Q ∨ s * d⁻¹ ∈ center Q := by
  rw [← ofMul_of_eq_iff hQ, ← ofMul_of_eq_zero_iff hQ]
  by_contra! h
  obtain ⟨x, hx1, hx0⟩ := exists_polar_eq_one_polar_eq_zero (extraspecialQuadForm_nondegenerate hQ)
    h.1 h.2
  obtain ⟨y, rfl⟩ := exists_ofMul_of x
  have hyd := (polar_extraspecialQuadForm_eq_zero_iff hQ y d).mp hx0
  have hys := (polar_extraspecialQuadForm_eq_zero_iff hQ y s).mpr (hs y hyd).symm
  rw [hys] at hx1
  exact zero_ne_one hx1

theorem exists_not_commute {d : Q}
    (hd : extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of d)) = 1) :
    ∃ b : Q, b * d ≠ d * b := by
  have hd0 : Additive.ofMul (Abelianization.of d) ≠ 0 := fun h => by
    rw [h, map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨x, hx⟩ := exists_polar_ne_zero (extraspecialQuadForm_nondegenerate hQ) hd0
  obtain ⟨b, rfl⟩ := exists_ofMul_of x
  exact ⟨b, fun h => hx ((polar_extraspecialQuadForm_eq_zero_iff hQ d b).mpr h.symm)⟩

theorem exists_commute_not_commute
    (h3 : 3 ≤ Module.finrank (ZMod 2) (Additive (Abelianization Q))) {d : Q}
    (hd : extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of d)) = 1) :
    ∃ y₁ y₂ : Q, y₁ * d = d * y₁ ∧ y₂ * d = d * y₂ ∧ y₁ * y₂ ≠ y₂ * y₁ := by
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  obtain ⟨b, hb⟩ := exists_not_commute hQ hd
  obtain ⟨x, hx0, hxd, hxb⟩ := exists_ne_zero_polar_eq_zero (Q := extraspecialQuadForm hQ) h3
    (Additive.ofMul (Abelianization.of d)) (Additive.ofMul (Abelianization.of b))
  have hxd' : x ≠ Additive.ofMul (Abelianization.of d) := by
    rintro rfl
    exact hb ((polar_extraspecialQuadForm_eq_zero_iff hQ d b).mp hxb).symm
  obtain ⟨x', hx'1, hx'd⟩ :=
    exists_polar_eq_one_polar_eq_zero (extraspecialQuadForm_nondegenerate hQ) hx0 hxd'
  obtain ⟨y₁, rfl⟩ := exists_ofMul_of x
  obtain ⟨y₂, rfl⟩ := exists_ofMul_of x'
  refine ⟨y₁, y₂, (polar_extraspecialQuadForm_eq_zero_iff hQ y₁ d).mp hxd,
    (polar_extraspecialQuadForm_eq_zero_iff hQ y₂ d).mp hx'd, fun h => ?_⟩
  rw [(polar_extraspecialQuadForm_eq_zero_iff hQ y₂ y₁).mpr h.symm] at hx'1
  exact zero_ne_one hx'1


section Transvection

variable {z₀ : H} (hz₀ : ∀ g : H, g * z₀ = z₀ * g) (hz₀1 : z₀ ≠ 1) (hz₀Q : z₀ ∈ Q)
include hz₀ hz₀1

theorem exists_fixed_commutator
    (h3 : 3 ≤ Module.finrank (ZMod 2) (Additive (Abelianization Q))) {d : Q}
    (hd : extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of d)) = 1) {g : H}
    (hg : ∀ u, conjLinEquiv hQn g u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d))
    (hgd : conjAut hQn g d = d * ⟨z₀, hz₀Q⟩) :
    ∃ c₁ c₂ : Q, c₁ * d = d * c₁ ∧ c₂ * d = d * c₂ ∧ conjAut hQn g c₁ = c₁ ∧
      conjAut hQn g c₂ = c₂ ∧ ((⁅c₁, c₂⁆ : Q) : H) = z₀ := by
  set zq : Q := ⟨z₀, hz₀Q⟩ with hzq
  have hzc : ∀ x : Q, x * zq = zq * x := fun x => Subtype.ext (hz₀ x)
  have hzz : zq * zq = 1 := Subtype.ext (sq_eq_one_of_central hQ hz₀ hz₀Q)
  have hfix : ∀ y : Q, y * d = d * y → ∃ c : Q, (c = y ∨ c = y * d) ∧ conjAut hQn g c = c := by
    intro y hy
    have hc := conjAut_mul_inv_mem_center hQ hQn hg hy
    rcases (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp hc with h | h
    · refine ⟨y, Or.inl rfl, ?_⟩
      have h' : conjAut hQn g y * y⁻¹ = 1 := Subtype.ext h
      exact mul_inv_eq_one.mp h'
    · refine ⟨y * d, Or.inr rfl, ?_⟩
      have h' : conjAut hQn g y * y⁻¹ = zq := Subtype.ext h
      have h'' : conjAut hQn g y = zq * y := by rw [← h', inv_mul_cancel_right]
      rw [map_mul, h'', hgd]
      calc zq * y * (d * zq) = zq * (y * d * zq) := by group
        _ = y * d * zq * zq := (hzc _).symm
        _ = y * d * (zq * zq) := by group
        _ = y * d := by rw [hzz, mul_one]
  have hcd : ∀ y : Q, y * d = d * y → ∀ c : Q, (c = y ∨ c = y * d) → c * d = d * c := by
    rintro y hy c (rfl | rfl)
    · exact hy
    · calc y * d * d = d * y * d := by rw [hy]
        _ = d * (y * d) := by rw [mul_assoc]
  have hleft : ∀ y x : Q, x * d = d * x → ⁅y * d, x⁆ = ⁅y, x⁆ := by
    intro y x hx
    simp only [commutatorElement_def]
    calc y * d * x * (y * d)⁻¹ * x⁻¹ = y * (d * x) * d⁻¹ * y⁻¹ * x⁻¹ := by group
      _ = y * (x * d) * d⁻¹ * y⁻¹ * x⁻¹ := by rw [hx]
      _ = y * x * y⁻¹ * x⁻¹ := by group
  have hright : ∀ y x : Q, x * d = d * x → ⁅x, y * d⁆ = ⁅x, y⁆ := by
    intro y x hx
    simp only [commutatorElement_def]
    have hx' : d * x⁻¹ = x⁻¹ * d := by
      calc d * x⁻¹ = x⁻¹ * (x * d) * x⁻¹ := by group
        _ = x⁻¹ * (d * x) * x⁻¹ := by rw [hx]
        _ = x⁻¹ * d := by group
    calc x * (y * d) * x⁻¹ * (y * d)⁻¹ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [hx']
      _ = x * y * x⁻¹ * y⁻¹ := by group
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₁₂⟩ := exists_commute_not_commute hQ h3 hd
  obtain ⟨c₁, hc₁, hc₁g⟩ := hfix y₁ hy₁
  obtain ⟨c₂, hc₂, hc₂g⟩ := hfix y₂ hy₂
  have hc₁d := hcd y₁ hy₁ c₁ hc₁
  have hc₂d := hcd y₂ hy₂ c₂ hc₂
  have hcomm : ⁅c₁, c₂⁆ = ⁅y₁, y₂⁆ := by
    have e1 : ⁅c₁, c₂⁆ = ⁅y₁, c₂⁆ := by
      rcases hc₁ with rfl | rfl
      · rfl
      · exact hleft _ _ hc₂d
    rw [e1]
    rcases hc₂ with rfl | rfl
    · rfl
    · exact hright _ _ hy₁
  refine ⟨c₁, c₂, hc₁d, hc₂d, hc₁g, hc₂g, ?_⟩
  rw [hcomm]
  have hne : ⁅y₁, y₂⁆ ≠ 1 := fun h => hy₁₂ (commutatorElement_eq_one_iff_mul_comm.mp h)
  rcases (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp (commutatorElement_mem_center hQ y₁ y₂)
    with h | h
  · exact absurd (Subtype.ext h) hne
  · exact h

theorem conjAut_eq_of_sq {d : Q}
    (hd : extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of d)) = 1) {x : H}
    (hx : ∀ u, conjLinEquiv hQn x u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d))
    (hxx : x * x = 1 ∨ x * x = z₀) : conjAut hQn x d = d * ⟨z₀, hz₀Q⟩ := by
  obtain ⟨b, hb⟩ := exists_not_commute hQ hd
  have hμ := conjAut_mul_inv_mem_center' hQ hQn hx hb
  obtain ⟨μ, hμc, h2⟩ : ∃ μ ∈ center Q, conjAut hQn x b = μ * (b * d) :=
    ⟨_, hμ, by rw [inv_mul_cancel_right]⟩
  have h1 : conjAut hQn x (conjAut hQn x b) = b := by
    apply Subtype.ext
    rw [conjAut_apply, conjAut_apply]
    have hc : (x * x) * (b : H) = b * (x * x) := by
      rcases hxx with h | h <;> rw [h]
      · group
      · exact (hz₀ b).symm
    calc x * (x * (b : H) * x⁻¹) * x⁻¹ = (x * x) * b * (x * x)⁻¹ := by group
      _ = b := by rw [hc, mul_inv_cancel_right]
  have h3 : conjAut hQn x μ = μ := conjAut_of_mem_center hQ hQn hz₀ hz₀1 hz₀Q hμc x
  have h4 : μ * μ = 1 := by rw [← pow_two]; exact sq_eq_one_of_mem_center hQ hμc
  have key : b * 1 = b * (d * conjAut hQn x d) := by
    calc b * 1 = conjAut hQn x (conjAut hQn x b) := by rw [mul_one, h1]
      _ = conjAut hQn x (μ * (b * d)) := by rw [h2]
      _ = conjAut hQn x μ * (conjAut hQn x b * conjAut hQn x d) := by rw [map_mul, map_mul]
      _ = μ * (μ * (b * d) * conjAut hQn x d) := by rw [h3, h2]
      _ = (μ * μ) * (b * (d * conjAut hQn x d)) := by group
      _ = b * (d * conjAut hQn x d) := by rw [h4, one_mul]
  have h5 : d * conjAut hQn x d = 1 := (mul_left_cancel key).symm
  have hdd : d * d = ⟨z₀, hz₀Q⟩ := Subtype.ext (coe_mul_self_eq hQ hz₀ hz₀1 hz₀Q hd)
  have hzz : (⟨z₀, hz₀Q⟩ : Q) * ⟨z₀, hz₀Q⟩ = 1 := Subtype.ext (sq_eq_one_of_central hQ hz₀ hz₀Q)
  rw [eq_inv_of_mul_eq_one_right h5]
  exact (eq_inv_of_mul_eq_one_right (by rw [← mul_assoc, hdd, hzz])).symm

include hz₀Q in
theorem exists_sq_mem_center (hCQ : centralizer (Q : Set H) ≤ Q) {d : Q}
    (hd : extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of d)) = 1) {m : H}
    (hm : ∀ u, conjLinEquiv hQn m u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d)) :
    ∃ x : H, conjLinEquiv hQn x = conjLinEquiv hQn m ∧ (x * x = 1 ∨ x * x = z₀) := by
  have hrefl : conjLinEquiv hQn m =
      reflect (extraspecialQuadForm hQ) (Additive.ofMul (Abelianization.of d)) :=
    eq_reflect_of_apply hd hm
  have hmm : extraspecialConjOrth hQ hQn (m * m) = 1 := by
    apply Subtype.ext
    change conjLinEquiv hQn (m * m) = 1
    rw [map_mul, hrefl, reflect_mul_self]
  have hsQ : m * m ∈ Q := mem_of_extraspecialConjOrth_eq_one hQ hQn hCQ hmm
  have hs : ∀ y : Q, y * d = d * y → (⟨m * m, hsQ⟩ : Q) * y = y * ⟨m * m, hsQ⟩ := by
    intro y hy
    obtain ⟨c, hc, hcy⟩ : ∃ c ∈ center Q, conjAut hQn m y = c * y :=
      ⟨_, conjAut_mul_inv_mem_center hQ hQn hm hy, by rw [inv_mul_cancel_right]⟩
    have hfix : conjAut hQn m (conjAut hQn m y) = y := by
      rw [hcy, map_mul, conjAut_of_mem_center hQ hQn hz₀ hz₀1 hz₀Q hc m, hcy, ← mul_assoc,
        ← pow_two, sq_eq_one_of_mem_center hQ hc, one_mul]
    have hH : (m * m) * (y : H) * (m * m)⁻¹ = y := by
      have := congrArg Subtype.val hfix
      rw [conjAut_apply, conjAut_apply] at this
      calc (m * m) * (y : H) * (m * m)⁻¹ = m * (m * y * m⁻¹) * m⁻¹ := by group
        _ = y := this
    apply Subtype.ext
    change m * m * (y : H) = y * (m * m)
    calc m * m * (y : H) = (m * m) * (y : H) * (m * m)⁻¹ * (m * m) := by group
      _ = y * (m * m) := by rw [hH]
  rcases mem_center_or_of_forall_commute hQ hs with h | h
  · exact ⟨m, rfl, (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp h⟩
  · obtain ⟨b, hb⟩ := exists_not_commute hQ hd
    refine ⟨b * m, by rw [map_mul, conjLinEquiv_of_mem hQ hQn b.2, one_mul], ?_⟩
    set t : Q := b * conjAut hQn m b * ⟨m * m, hsQ⟩ with htdef
    have ht : (t : H) = b * m * (b * m) := by
      rw [htdef]
      simp only [Subgroup.coe_mul, conjAut_apply]
      group
    have hcls1 : Additive.ofMul (Abelianization.of (conjAut hQn m b)) =
        Additive.ofMul (Abelianization.of b) + Additive.ofMul (Abelianization.of d) := by
      rw [← ofMul_of_mul]
      exact (ofMul_of_eq_iff hQ _ _).mpr (conjAut_mul_inv_mem_center' hQ hQn hm hb)
    have hcls2 : Additive.ofMul (Abelianization.of (⟨m * m, hsQ⟩ : Q)) =
        Additive.ofMul (Abelianization.of d) := (ofMul_of_eq_iff hQ _ _).mpr h
    have htc : t ∈ center Q := by
      rw [← ofMul_of_eq_zero_iff hQ, htdef, ofMul_of_mul, ofMul_of_mul, hcls1, hcls2]
      rw [show Additive.ofMul (Abelianization.of b) + (Additive.ofMul (Abelianization.of b) +
          Additive.ofMul (Abelianization.of d)) + Additive.ofMul (Abelianization.of d) =
          (Additive.ofMul (Abelianization.of b) + Additive.ofMul (Abelianization.of b)) +
          (Additive.ofMul (Abelianization.of d) + Additive.ofMul (Abelianization.of d)) by abel,
        zmod2_vec_add_self, zmod2_vec_add_self, add_zero]
    rw [← ht]
    exact (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp htc

theorem exists_involution (hCQ : centralizer (Q : Set H) ≤ Q)
    (h3 : 3 ≤ Module.finrank (ZMod 2) (Additive (Abelianization Q))) {d : Q}
    (hd : extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of d)) = 1) {m : H}
    (hm : ∀ u, conjLinEquiv hQn m u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d)) :
    ∃ a : H, conjLinEquiv hQn a = conjLinEquiv hQn m ∧ a * a = 1 ∧
      conjAut hQn a d = d * ⟨z₀, hz₀Q⟩ := by
  obtain ⟨x, hxm, hxx⟩ := exists_sq_mem_center hQ hQn hz₀ hz₀1 hz₀Q hCQ hd hm
  have hx : ∀ u, conjLinEquiv hQn x u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d) := fun u => by
    rw [hxm]
    exact hm u
  have hxd := conjAut_eq_of_sq hQ hQn hz₀ hz₀1 hz₀Q hd hx hxx
  rcases hxx with hxx | hxx
  · exact ⟨x, hxm, hxx, hxd⟩
  obtain ⟨c₁, c₂, hc₁d, hc₂d, hc₁x, hc₂x, hc⟩ :=
    exists_fixed_commutator hQ hQn hz₀ hz₀1 hz₀Q h3 hd hx hxd
  obtain ⟨c, hcd, hcx, hcc⟩ :
      ∃ c : Q, c * d = d * c ∧ conjAut hQn x c = c ∧ (c : H) * c = z₀ := by
    have hsq : ∀ y : Q, (y : H) * y = 1 ∨ (y : H) * y = z₀ := fun y => by
      have := (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp (sq_mem_center hQ y)
      rwa [SubmonoidClass.coe_pow, pow_two] at this
    rcases hsq c₁ with h1 | h1
    · rcases hsq c₂ with h2 | h2
      · refine ⟨c₁ * c₂, ?_, by rw [map_mul, hc₁x, hc₂x], ?_⟩
        · rw [mul_assoc, hc₂d, ← mul_assoc, hc₁d, mul_assoc]
        · have e1 : (c₁ * c₂) * (c₁ * c₂) = ⁅c₂, c₁⁆ * (c₁ * c₁) * (c₂ * c₂) := by
            have := mul_sq_eq hQ c₁ c₂
            rwa [pow_two, pow_two, pow_two] at this
          have e2 : c₁ * c₁ = 1 := Subtype.ext h1
          have e3 : c₂ * c₂ = 1 := Subtype.ext h2
          have e5 : (⁅c₁, c₂⁆ : Q)⁻¹ = ⁅c₁, c₂⁆ := inv_eq_of_mul_eq_one_right (by
            rw [← pow_two]
            exact sq_eq_one_of_mem_center hQ (commutatorElement_mem_center hQ c₁ c₂))
          have e6 : (c₁ * c₂) * (c₁ * c₂) = ⁅c₁, c₂⁆ := by
            rw [e1, e2, e3, mul_one, mul_one, ← commutatorElement_inv, e5]
          calc ((c₁ * c₂ : Q) : H) * ((c₁ * c₂ : Q) : H) = (((c₁ * c₂) * (c₁ * c₂) : Q) : H) :=
                rfl
            _ = ((⁅c₁, c₂⁆ : Q) : H) := by rw [e6]
            _ = z₀ := hc
      · exact ⟨c₂, hc₂d, hc₂x, h2⟩
    · exact ⟨c₁, hc₁d, hc₁x, h1⟩
  have hxc : x * (c : H) = c * x := by
    have := congrArg Subtype.val hcx
    rw [conjAut_apply] at this
    calc x * (c : H) = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [this]
  refine ⟨x * c, ?_, ?_, ?_⟩
  · rw [map_mul, conjLinEquiv_of_mem hQ hQn c.2, mul_one, hxm]
  · calc x * c * (x * c) = x * ((c : H) * x) * c := by group
      _ = x * (x * c) * c := by rw [← hxc]
      _ = (x * x) * ((c : H) * c) := by group
      _ = 1 := by rw [hxx, hcc, sq_eq_one_of_central hQ hz₀ hz₀Q]
  · apply Subtype.ext
    rw [conjAut_apply]
    have hcd' : (c : H) * d * (c : H)⁻¹ = d := by
      have := congrArg Subtype.val hcd
      simp only [Subgroup.coe_mul] at this
      rw [this, mul_inv_cancel_right]
    have := congrArg Subtype.val hxd
    rw [conjAut_apply] at this
    calc x * c * (d : H) * (x * c)⁻¹ = x * ((c : H) * d * (c : H)⁻¹) * x⁻¹ := by group
      _ = x * d * x⁻¹ := by rw [hcd']
      _ = _ := this

include hz₀Q in
theorem exists_smith_subgroup (hCQ : centralizer (Q : Set H) ≤ Q)
    (h3 : 3 ≤ Module.finrank (ZMod 2) (Additive (Abelianization Q)))
    {v : Additive (Abelianization Q)} (hv : extraspecialQuadForm hQ v = 1) {m : H}
    (hm : ∀ u, conjLinEquiv hQn m u = u + polar (extraspecialQuadForm hQ) u v • v) :
    ∃ a : H, ∃ F : Subgroup H,
      (∀ u, conjLinEquiv hQn a u = u + polar (extraspecialQuadForm hQ) u v • v) ∧
      a * a = 1 ∧ a ∈ F ∧ z₀ ∈ F ∧ IsPGroup 2 F ∧
      (∀ j : H, (∀ f ∈ F, j * f = f * j) → j = 1 ∨ j = z₀) ∧
      (∀ f ∈ F, f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z₀) ∧ (∃ e ∈ F, e * a * e⁻¹ = a * z₀) ∧
      (∃ c₁ ∈ F, ∃ c₂ ∈ F, c₁ * a = a * c₁ ∧ c₂ * a = a * c₂ ∧ ⁅c₁, c₂⁆ = z₀) := by
  obtain ⟨d, rfl⟩ := exists_ofMul_of v
  obtain ⟨a, ham, haa, had⟩ := exists_involution hQ hQn hz₀ hz₀1 hz₀Q hCQ h3 hv hm
  have ha : ∀ u, conjLinEquiv hQn a u = u + polar (extraspecialQuadForm hQ) u
      (Additive.ofMul (Abelianization.of d)) • Additive.ofMul (Abelianization.of d) := fun u => by
    rw [ham]
    exact hm u
  have hd0 : Additive.ofMul (Abelianization.of d) ≠ 0 := fun h => by
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hzz : z₀ * z₀ = 1 := sq_eq_one_of_central hQ hz₀ hz₀Q
  have hzinv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hzz
  have hadH : a * (d : H) * a⁻¹ = d * z₀ := by
    have := congrArg Subtype.val had
    rwa [conjAut_apply] at this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hadH' : a⁻¹ * (d : H) * a = d * z₀ := by
    calc a⁻¹ * (d : H) * a = a * d * a⁻¹ := by rw [hainv]
      _ = d * z₀ := hadH
  set D : Subgroup H := Q ⊓ centralizer {(d : H)} with hDdef
  have hmemD : ∀ y : Q, y * d = d * y → (y : H) ∈ D := fun y hy =>
    mem_inf.mpr ⟨y.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy)⟩
  set F : Subgroup H := D ⊔ zpowers a with hFdef
  have hDF : D ≤ F := le_sup_left
  have haF : a ∈ F := mem_sup_right (mem_zpowers a)
  have hz₀F : z₀ ∈ F :=
    hDF (mem_inf.mpr ⟨hz₀Q, mem_centralizer_singleton_iff.mpr (hz₀ d).symm⟩)
  refine ⟨a, F, ha, haa, haF, hz₀F, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hza : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa))
    have : Q.Normal := hQn
    exact (hQ.1.to_sup_of_normal_left hza).to_le (sup_le_sup_right inf_le_left _)
  ·
    intro j hj
    have hja : j * a = a * j := hj a haF
    have hjD : ∀ y : Q, y * d = d * y → j * y = y * j := fun y hy => hj y (hDF (hmemD y hy))
    have hρj : conjLinEquiv hQn j = 1 ∨
        conjLinEquiv hQn j = reflect (extraspecialQuadForm hQ) (Additive.ofMul
          (Abelianization.of d)) := by
      refine eq_one_or_eq_reflect_of_fix (extraspecialQuadForm_nondegenerate hQ) hv
        (conjLinEquiv_mem hQ hQn j) fun u hu => ?_
      obtain ⟨y, rfl⟩ := exists_ofMul_of u
      have hy : y * d = d * y := (polar_extraspecialQuadForm_eq_zero_iff hQ y d).mp hu
      rw [conjLinEquiv_apply, show conjAut hQn j y = y from
        Subtype.ext (by rw [conjAut_apply, hjD y hy, mul_inv_cancel_right])]
    rcases hρj with h1 | h1
    · have hjQ : j ∈ Q := mem_of_extraspecialConjOrth_eq_one hQ hQn hCQ (Subtype.ext h1)
      have hs : ∀ y : Q, y * d = d * y → (⟨j, hjQ⟩ : Q) * y = y * ⟨j, hjQ⟩ :=
        fun y hy => Subtype.ext (hjD y hy)
      rcases mem_center_or_of_forall_commute hQ hs with h | h
      · exact (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp h
      · exfalso
        have hμ : j * (d : H)⁻¹ = 1 ∨ j * (d : H)⁻¹ = z₀ :=
          (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp h
        have hμc : ∀ g : H, g * (j * (d : H)⁻¹) = (j * (d : H)⁻¹) * g := by
          intro g
          rcases hμ with h | h <;> rw [h]
          · group
          · exact hz₀ g
        have key : a * j * a⁻¹ = j * z₀ := by
          calc a * j * a⁻¹ = a * ((j * (d : H)⁻¹) * d) * a⁻¹ := by group
            _ = (a * (j * (d : H)⁻¹)) * d * a⁻¹ := by group
            _ = ((j * (d : H)⁻¹) * a) * d * a⁻¹ := by rw [hμc a]
            _ = (j * (d : H)⁻¹) * (a * d * a⁻¹) := by group
            _ = (j * (d : H)⁻¹) * (d * z₀) := by rw [hadH]
            _ = j * z₀ := by group
        have : a * j * a⁻¹ = j := by rw [← hja, mul_inv_cancel_right]
        rw [this] at key
        exact hz₀1 (by simpa using key.symm)
    · exfalso
      have hja' : conjLinEquiv hQn (j * a⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, ← eq_reflect_of_apply hv ha, mul_inv_cancel]
      have hqQ : j * a⁻¹ ∈ Q := mem_of_extraspecialConjOrth_eq_one hQ hQn hCQ (Subtype.ext hja')
      have hqa : a * (j * a⁻¹) * a⁻¹ = j * a⁻¹ := by
        calc a * (j * a⁻¹) * a⁻¹ = (a * j) * a⁻¹ * a⁻¹ := by group
          _ = (j * a) * a⁻¹ * a⁻¹ := by rw [hja]
          _ = j * a⁻¹ := by group
      have hfixq : conjLinEquiv hQn a (Additive.ofMul (Abelianization.of (⟨_, hqQ⟩ : Q))) =
          Additive.ofMul (Abelianization.of (⟨_, hqQ⟩ : Q)) := by
        rw [conjLinEquiv_apply, show conjAut hQn a ⟨_, hqQ⟩ = ⟨_, hqQ⟩ from
          Subtype.ext (by rw [conjAut_apply]; exact hqa)]
      rw [ha] at hfixq
      have hpol : polar (extraspecialQuadForm hQ) (Additive.ofMul (Abelianization.of
          (⟨_, hqQ⟩ : Q))) (Additive.ofMul (Abelianization.of d)) = 0 := by
        rcases zmod2_eq_zero_or_eq_one (polar (extraspecialQuadForm hQ) (Additive.ofMul
          (Abelianization.of (⟨_, hqQ⟩ : Q))) (Additive.ofMul (Abelianization.of d))) with h | h
        · exact h
        · exfalso
          rw [h, one_smul, add_eq_left] at hfixq
          exact hd0 hfixq
      have hqd := congrArg Subtype.val ((polar_extraspecialQuadForm_eq_zero_iff hQ _ d).mp hpol)
      change j * a⁻¹ * (d : H) = d * (j * a⁻¹) at hqd
      have hjd : j * (d : H) = d * j := hjD d rfl
      have key : (j * a⁻¹) * (d : H) * (j * a⁻¹)⁻¹ = d * z₀ := by
        calc (j * a⁻¹) * (d : H) * (j * a⁻¹)⁻¹ = j * (a⁻¹ * d * a) * j⁻¹ := by group
          _ = j * (d * z₀) * j⁻¹ := by rw [hadH']
          _ = (j * d) * z₀ * j⁻¹ := by group
          _ = (d * j) * z₀ * j⁻¹ := by rw [hjd]
          _ = d * (j * z₀) * j⁻¹ := by group
          _ = d * (z₀ * j) * j⁻¹ := by rw [hz₀ j]
          _ = d * z₀ := by group
      rw [hqd, mul_inv_cancel_right] at key
      exact hz₀1 (by simpa using key.symm)
  ·
    have hconjz : ∀ f : H, f * (a * z₀) * f⁻¹ = f * a * f⁻¹ * z₀ := fun f => by
      calc f * (a * z₀) * f⁻¹ = f * a * (z₀ * f⁻¹) := by group
        _ = f * a * (f⁻¹ * z₀) := by rw [← hz₀ f⁻¹]
        _ = f * a * f⁻¹ * z₀ := by group
    let S : Subgroup H :=
      { carrier := {f | f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z₀}
        mul_mem' := by
          intro f g hf hg
          simp only [Set.mem_ofPred_eq] at hf hg ⊢
          have e : f * g * a * (f * g)⁻¹ = f * (g * a * g⁻¹) * f⁻¹ := by group
          rw [e]
          rcases hg with hg | hg <;> rw [hg]
          · exact hf
          · rw [hconjz]
            rcases hf with hf | hf <;> rw [hf]
            · exact Or.inr rfl
            · left
              rw [mul_assoc, hzz, mul_one]
        one_mem' := Or.inl (by group)
        inv_mem' := by
          intro f hf
          simp only [Set.mem_ofPred_eq, inv_inv] at hf ⊢
          rcases hf with hf | hf
          · left
            calc f⁻¹ * a * f = f⁻¹ * (f * a * f⁻¹) * f := by rw [hf]
              _ = a := by group
          · right
            have h1 : f⁻¹ * a * f * z₀ = a := by
              calc f⁻¹ * a * f * z₀ = f⁻¹ * a * (f * z₀) := by group
                _ = f⁻¹ * a * (z₀ * f) := by rw [hz₀ f]
                _ = f⁻¹ * (a * z₀) * f := by group
                _ = f⁻¹ * (f * a * f⁻¹) * f := by rw [hf]
                _ = a := by group
            calc f⁻¹ * a * f = f⁻¹ * a * f * (z₀ * z₀) := by rw [hzz, mul_one]
              _ = (f⁻¹ * a * f * z₀) * z₀ := by group
              _ = a * z₀ := by rw [h1] }
    have hDS : D ≤ S := by
      intro f hf
      obtain ⟨hfQ, hfd⟩ := mem_inf.mp hf
      have hy : (⟨f, hfQ⟩ : Q) * d = d * ⟨f, hfQ⟩ :=
        Subtype.ext (mem_centralizer_singleton_iff.mp hfd)
      have hc := conjAut_mul_inv_mem_center hQ hQn ha hy
      have hc' : a * f * a⁻¹ * f⁻¹ = 1 ∨ a * f * a⁻¹ * f⁻¹ = z₀ := by
        have := (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp hc
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply] using this
      have e : f * a * f⁻¹ = (a * f * a⁻¹ * f⁻¹)⁻¹ * a := by group
      change f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z₀
      rw [e]
      rcases hc' with h | h <;> rw [h]
      · left
        group
      · right
        rw [hzinv, hz₀ a]
    have hFS : F ≤ S := sup_le hDS ((zpowers_le (G := H)).mpr (Or.inl (by group)))
    exact fun f hf => hFS hf
  ·
    refine ⟨d, hDF (hmemD d rfl), ?_⟩
    calc (d : H) * a * (d : H)⁻¹ = (a * d * a⁻¹ * (d : H)⁻¹)⁻¹ * a := by group
      _ = ((d : H) * z₀ * (d : H)⁻¹)⁻¹ * a := by rw [hadH]
      _ = z₀⁻¹ * a := by rw [hz₀ d, mul_inv_cancel_right]
      _ = a * z₀ := by rw [hzinv, hz₀ a]
  ·
    obtain ⟨c₁, c₂, hc₁d, hc₂d, hc₁a, hc₂a, hc⟩ :=
      exists_fixed_commutator hQ hQn hz₀ hz₀1 hz₀Q h3 hv ha had
    have hcomm : ∀ c : Q, conjAut hQn a c = c → (c : H) * a = a * c := fun c hc => by
      have := congrArg Subtype.val hc
      rw [conjAut_apply] at this
      calc (c : H) * a = a * c * a⁻¹ * a := by rw [this]
        _ = a * c := by group
    exact ⟨c₁, hDF (hmemD c₁ hc₁d), c₂, hDF (hmemD c₂ hc₂d), hcomm c₁ hc₁a, hcomm c₂ hc₂a, hc⟩

end Transvection

end Construction

end CFSG.RankThree.Literature.FSmith
