module

public import CFSG.RankThree.PartTwo.Sec16.ResGapProofFiveAlg
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.ResGapFive

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

section Quot

variable {U Φ : Subgroup G}

@[expose] def conjU (g : G) (hg : g ∈ normalizer (U : Set G)) : ↥U →* ↥U where
  toFun u := ⟨g * u * g⁻¹, (mem_normalizer_iff.mp hg u).mp u.2⟩
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp only [Subgroup.coe_mul]; group

theorem conjU_coe (g : G) (hg : g ∈ normalizer (U : Set G)) (u : ↥U) :
    ((conjU g hg u : ↥U) : G) = g * u * g⁻¹ := rfl

theorem normal_subgroupOf (hΦU : Φ ≤ U) (hUΦ : U ≤ normalizer (Φ : Set G)) :
    (Φ.subgroupOf U).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hΦU).mpr hUΦ

@[expose] noncomputable def conjQ (hΦU : Φ ≤ U) (hUΦ : U ≤ normalizer (Φ : Set G)) (g : G)
    (hgU : g ∈ normalizer (U : Set G)) (hgΦ : g ∈ normalizer (Φ : Set G)) :
    haveI := normal_subgroupOf hΦU hUΦ
    ↥U ⧸ Φ.subgroupOf U →* ↥U ⧸ Φ.subgroupOf U :=
  haveI := normal_subgroupOf hΦU hUΦ
  QuotientGroup.map (Φ.subgroupOf U) (Φ.subgroupOf U) (conjU g hgU) (by
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, conjU_coe]
    exact (mem_normalizer_iff.mp hgΦ _).mp (Subgroup.mem_subgroupOf.mp hu))

theorem conjQ_mk (hΦU : Φ ≤ U) (hUΦ : U ≤ normalizer (Φ : Set G)) (g : G)
    (hgU : g ∈ normalizer (U : Set G)) (hgΦ : g ∈ normalizer (Φ : Set G)) (u : ↥U) :
    haveI := normal_subgroupOf hΦU hUΦ
    conjQ hΦU hUΦ g hgU hgΦ (u : ↥U ⧸ Φ.subgroupOf U) =
      ((conjU g hgU u : ↥U) : ↥U ⧸ Φ.subgroupOf U) := by
  have := normal_subgroupOf hΦU hUΦ
  exact QuotientGroup.map_mk _ _ _ _ _

theorem mk_eq_mk_iff (hΦU : Φ ≤ U) (hUΦ : U ≤ normalizer (Φ : Set G)) (a b : ↥U) :
    haveI := normal_subgroupOf hΦU hUΦ
    ((a : ↥U ⧸ Φ.subgroupOf U) = (b : ↥U ⧸ Φ.subgroupOf U)) ↔ (a : G)⁻¹ * b ∈ Φ := by
  have := normal_subgroupOf hΦU hUΦ
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

end Quot

variable [Finite G]

theorem mem_normalizer_of_conj_mem {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h k hk, fun hk => ?_⟩
  let f : K → K := fun a => ⟨g * a * g⁻¹, h a a.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g * k * g⁻¹, hk⟩
  have h1 : g * (a : G) * g⁻¹ = g * k * g⁻¹ := congrArg Subtype.val ha
  rw [← mul_left_cancel (mul_right_cancel h1)]
  exact a.2

theorem conj_mem_or {U Φ : Subgroup G} {x c : G} (hΦU : Φ ≤ U)
    (hUΦ : U ≤ normalizer (Φ : Set G)) (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Φ)
    (hsq : ∀ u ∈ U, u ^ 2 ∈ Φ) (hxU : x ∈ normalizer (U : Set G))
    (hcU : c ∈ normalizer (U : Set G)) (hxΦ : x ∈ normalizer (Φ : Set G))
    (hcΦ : c ∈ normalizer (Φ : Set G)) (hx5 : x ^ 5 = 1) (hc3 : c ^ 3 = 1)
    (hxc : x * c = c * x) (hxf : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ Φ → u ∈ Φ)
    (hcf : ∀ u ∈ U, c * u * c⁻¹ * u⁻¹ ∈ Φ → u ∈ Φ)
    (hirr : ∀ V : Subgroup G, Φ ≤ V → V ≤ U → x ∈ normalizer (V : Set G) →
      c ∈ normalizer (V : Set G) → V = Φ ∨ V = U) :
    (∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((x * u * x⁻¹) * (x⁻¹ * u * x)) ∈ Φ) ∨
      (∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((x ^ 2 * u * (x ^ 2)⁻¹) * ((x ^ 2)⁻¹ * u * x ^ 2)) ∈ Φ) := by
  classical
  have hN := normal_subgroupOf hΦU hUΦ
  set N := Φ.subgroupOf U with hNdef
  have hQcomm : ∀ a b : ↥U ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff hΦU hUΦ]
    have h := hcomm _ (inv_mem b.2) _ (inv_mem a.2)
    have e : ((a * b : ↥U) : G)⁻¹ * ((b * a : ↥U) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact h
  let _ : CommGroup (↥U ⧸ N) := { (inferInstance : Group (↥U ⧸ N)) with mul_comm := hQcomm }
  set φx := conjQ hΦU hUΦ x hxU hxΦ with hφx
  set φc := conjQ hΦU hUΦ c hcU hcΦ with hφc
  set X : Additive (↥U ⧸ N) →+ Additive (↥U ⧸ N) := MonoidHom.toAdditive φx with hX
  set C : Additive (↥U ⧸ N) →+ Additive (↥U ⧸ N) := MonoidHom.toAdditive φc with hC
  have hXapp : ∀ u : ↥U, X (Additive.ofMul (u : ↥U ⧸ N)) =
      Additive.ofMul ((conjU x hxU u : ↥U) : ↥U ⧸ N) := fun u => by
    rw [hX, MonoidHom.toAdditive_apply_apply, toMul_ofMul, hφx, conjQ_mk]
  have hCapp : ∀ u : ↥U, C (Additive.ofMul (u : ↥U ⧸ N)) =
      Additive.ofMul ((conjU c hcU u : ↥U) : ↥U ⧸ N) := fun u => by
    rw [hC, MonoidHom.toAdditive_apply_apply, toMul_ofMul, hφc, conjQ_mk]
  have hind : ∀ (P : Additive (↥U ⧸ N) → Prop),
      (∀ u : ↥U, P (Additive.ofMul (u : ↥U ⧸ N))) → ∀ w, P w := by
    intro P hP w
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have : w = Additive.ofMul (u : ↥U ⧸ N) := by rw [hu]; rfl
    rw [this]
    exact hP u
  have hsurj : ∀ w : Additive (↥U ⧸ N), ∃ u : ↥U, w = Additive.ofMul (u : ↥U ⧸ N) := by
    intro w
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    exact ⟨u, by rw [hu]; rfl⟩
  have hofMul_eq : ∀ a b : ↥U, Additive.ofMul (a : ↥U ⧸ N) = Additive.ofMul (b : ↥U ⧸ N) ↔
      (a : G)⁻¹ * b ∈ Φ := fun a b => by
    rw [Additive.ofMul.apply_eq_iff_eq, mk_eq_mk_iff hΦU hUΦ]
  have hadd : ∀ a b : ↥U, Additive.ofMul (a : ↥U ⧸ N) + Additive.ofMul (b : ↥U ⧸ N) =
      Additive.ofMul ((a * b : ↥U) : ↥U ⧸ N) := fun a b => by
    rw [← ofMul_mul, QuotientGroup.mk_mul]
  have hzero : (0 : Additive (↥U ⧸ N)) = Additive.ofMul ((1 : ↥U) : ↥U ⧸ N) := by
    rw [QuotientGroup.mk_one, ofMul_one]
  have h2 : ∀ w : Additive (↥U ⧸ N), w + w = 0 := by
    refine hind _ fun u => ?_
    rw [hadd, hzero, hofMul_eq]
    have h := inv_mem (hsq u u.2)
    simpa [pow_two] using h
  have hx5' : x * (x * (x * (x * x))) = 1 := by rw [← hx5]; simp [pow_succ, mul_assoc]
  have hX5 : ∀ w, X (X (X (X (X w)))) = w := by
    refine hind _ fun u => ?_
    simp only [hXapp]
    rw [hofMul_eq]
    simp only [conjU_coe]
    have e : x * (x * (x * (x * (x * (u : G) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ =
        (x * (x * (x * (x * x)))) * u * (x * (x * (x * (x * x))))⁻¹ := by group
    rw [e, hx5']
    simp
  have hc3' : c * (c * c) = 1 := by rw [← hc3]; simp [pow_succ, mul_assoc]
  have hC3 : ∀ w, C (C (C w)) = w := by
    refine hind _ fun u => ?_
    simp only [hCapp]
    rw [hofMul_eq]
    simp only [conjU_coe]
    have e : c * (c * (c * (u : G) * c⁻¹) * c⁻¹) * c⁻¹ = (c * (c * c)) * u * (c * (c * c))⁻¹ := by
      group
    rw [e, hc3']
    simp
  have hXC : ∀ w, X (C w) = C (X w) := by
    refine hind _ fun u => ?_
    simp only [hXapp, hCapp]
    rw [hofMul_eq]
    simp only [conjU_coe]
    have e : x * (c * (u : G) * c⁻¹) * x⁻¹ = c * (x * u * x⁻¹) * c⁻¹ := by
      calc x * (c * (u : G) * c⁻¹) * x⁻¹ = (x * c) * u * (x * c)⁻¹ := by group
        _ = (c * x) * u * (c * x)⁻¹ := by rw [hxc]
        _ = c * (x * u * x⁻¹) * c⁻¹ := by group
    rw [e, inv_mul_cancel]
    exact one_mem _
  have hfix : ∀ {g : G} (hgU : g ∈ normalizer (U : Set G)),
      (∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ Φ → u ∈ Φ) →
      ∀ u : ↥U, Additive.ofMul ((conjU g hgU u : ↥U) : ↥U ⧸ N) = Additive.ofMul (u : ↥U ⧸ N) →
        Additive.ofMul (u : ↥U ⧸ N) = 0 := by
    intro g hgU hf u h
    rw [hofMul_eq, conjU_coe] at h
    have h1 := (mem_normalizer_iff.mp (hUΦ u.2) _).mp (inv_mem h)
    have e : (u : G) * ((g * u * g⁻¹)⁻¹ * u)⁻¹ * (u : G)⁻¹ = g * u * g⁻¹ * (u : G)⁻¹ := by group
    rw [e] at h1
    have hu := hf u u.2 h1
    rw [hzero, hofMul_eq]
    simpa using inv_mem hu
  have hXf : ∀ w, X w = w → w = 0 := by
    refine hind _ fun u hu => ?_
    rw [hXapp] at hu
    exact hfix hxU hxf u hu
  have hCf : ∀ w, C w = w → w = 0 := by
    refine hind _ fun u hu => ?_
    rw [hCapp] at hu
    exact hfix hcU hcf u hu
  have hirr' : ∀ V : AddSubgroup (Additive (↥U ⧸ N)), (∀ v ∈ V, X v ∈ V) →
      (∀ v ∈ V, C v ∈ V) → V = ⊥ ∨ V = ⊤ := by
    intro V hVX hVC
    set VG : Subgroup G :=
      ((AddSubgroup.toSubgroup' V).comap (QuotientGroup.mk' N)).map U.subtype with hVG
    have hmemVG : ∀ u : ↥U, (u : G) ∈ VG ↔ Additive.ofMul (u : ↥U ⧸ N) ∈ V := by
      intro u
      constructor
      · rintro ⟨v, hv, hvu⟩
        have hvu' : v = u := Subtype.ext hvu
        rw [← hvu']
        exact (AddSubgroup.mem_toSubgroup' V _).mp hv
      · intro h
        exact ⟨u, (AddSubgroup.mem_toSubgroup' V _).mpr h, rfl⟩
    have hΦVG : Φ ≤ VG := by
      intro g hg
      refine (hmemVG ⟨g, hΦU hg⟩).mpr ?_
      have : Additive.ofMul ((⟨g, hΦU hg⟩ : ↥U) : ↥U ⧸ N) = 0 := by
        rw [hzero, hofMul_eq]
        simpa using hg
      rw [this]
      exact V.zero_mem
    have hVGU : VG ≤ U := Subgroup.map_subtype_le _
    have hconj : ∀ {g : G} (hgU : g ∈ normalizer (U : Set G)),
        (∀ u : ↥U, Additive.ofMul (u : ↥U ⧸ N) ∈ V →
          Additive.ofMul ((conjU g hgU u : ↥U) : ↥U ⧸ N) ∈ V) →
        g ∈ normalizer (VG : Set G) := by
      intro g hgU hg
      refine mem_normalizer_of_conj_mem fun k hk => ?_
      have hkU : k ∈ U := hVGU hk
      have hkV := (hmemVG ⟨k, hkU⟩).mp hk
      exact (hmemVG (conjU g hgU ⟨k, hkU⟩)).mpr (hg ⟨k, hkU⟩ hkV)
    have hxVG : x ∈ normalizer (VG : Set G) := hconj hxU fun u hu => by
      rw [← hXapp]
      exact hVX _ hu
    have hcVG : c ∈ normalizer (VG : Set G) := hconj hcU fun u hu => by
      rw [← hCapp]
      exact hVC _ hu
    rcases hirr VG hΦVG hVGU hxVG hcVG with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      rw [AddSubgroup.mem_bot]
      obtain ⟨u, rfl⟩ := hsurj w
      have hu' : (u : G) ∈ Φ := h ▸ (hmemVG u).mpr hw
      rw [hzero, hofMul_eq]
      simpa using inv_mem hu'
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨u, hu⟩ := hsurj w
      rw [hu]
      have huVG : (u : G) ∈ VG := by rw [h]; exact u.2
      exact (hmemVG u).mp huVG
  have hx4 : x * (x * (x * x)) = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hx5]
    simp [pow_succ, mul_assoc]
  have hx3 : x * (x * x) = (x ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hx5]
    simp [pow_succ, mul_assoc]
  have hx4c : ∀ g : G, x * (x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ = x⁻¹ * g * x := by
    intro g
    have e : x * (x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ =
        (x * (x * (x * x))) * g * (x * (x * (x * x)))⁻¹ := by group
    rw [e, hx4, inv_inv]
  have hx3c : ∀ g : G, x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = (x ^ 2)⁻¹ * g * x ^ 2 := by
    intro g
    have e : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * g * (x * (x * x))⁻¹ := by
      group
    rw [e, hx3, inv_inv]
  have hx2c : ∀ g : G, x * (x * g * x⁻¹) * x⁻¹ = x ^ 2 * g * (x ^ 2)⁻¹ := by
    intro g
    rw [sq, mul_inv_rev]
    group
  rcases Alg.eq_omega_or h2 X C hX5 hC3 hXC hXf hCf hirr' with h | h
  · left
    intro u hu
    have h1 := h (Additive.ofMul ((⟨u, hu⟩ : ↥U) : ↥U ⧸ N))
    simp only [hXapp, hCapp, hadd] at h1
    rw [hofMul_eq] at h1
    simp only [conjU_coe, Subgroup.coe_mul] at h1
    rw [hx4c] at h1
    exact h1
  · right
    intro u hu
    have h1 := h (Additive.ofMul ((⟨u, hu⟩ : ↥U) : ↥U ⧸ N))
    simp only [hXapp, hCapp, hadd] at h1
    rw [hofMul_eq] at h1
    simp only [conjU_coe, Subgroup.coe_mul] at h1
    rw [hx3c, hx2c] at h1
    exact h1

end CFSG.RankThree.PartTwo.Sec16.ResGapFive
