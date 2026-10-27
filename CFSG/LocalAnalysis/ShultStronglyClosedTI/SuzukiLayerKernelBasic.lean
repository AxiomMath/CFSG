module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiRootAutomorphismUnipotent
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureBasic

public section

namespace CFSG.ShultStronglyClosedTI.SuzukiLayerKernel

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open SuzukiModel SuzukiRootAutomorphism
open scoped commutatorElement

theorem map_omega₁_subtype {G : Type*} [Group G] (H : Subgroup G) (p : ℕ) :
    (CFSG.omega₁ (G := H) (p := p)).map H.subtype =
      Subgroup.closure {g | g ∈ H ∧ g ^ p = 1} := by
  rw [CFSG.omega₁, CFSG.omega, MonoidHom.map_closure, pow_one]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by rw [Subgroup.coe_subtype, ← SubmonoidClass.coe_pow, hx, OneMemClass.coe_one]⟩
  · rintro ⟨hg, hgp⟩
    exact ⟨⟨g, hg⟩, Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgp), rfl⟩

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem mem_suzukiZ0_iff_sq_eq_one
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : suzukiGroup a K} :
    g ∈ suzukiZ0 a K ↔ g ∈ suzukiU a K ∧ g ^ 2 = 1 := by
  constructor
  · intro hg
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hg
    exact ⟨suzukiSElt_mem_suzukiU a K 0 v, by rw [sq]; exact suzukiSElt_zero_mul_self hK v⟩
  · rintro ⟨hg, hsq⟩
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    have h := congrArg (fun x : suzukiU a K => (x : suzukiGroup a K)) (unipotentElt_sq hK u v)
    simp only [SubmonoidClass.coe_pow, coe_unipotentElt] at h
    rw [hsq, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at h
    obtain rfl : u = 0 := (pow_eq_zero_iff (Nat.succ_ne_zero _)).1 h.2.symm
    exact (mem_suzukiZ0_iff hK).2 ⟨v, rfl⟩

theorem map_omega₁_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (CFSG.omega₁ (G := suzukiU a K) (p := 2)).map (suzukiU a K).subtype = suzukiZ0 a K := by
  rw [map_omega₁_subtype, ← Subgroup.closure_eq (suzukiZ0 a K)]
  congr 1
  ext g
  exact (mem_suzukiZ0_iff_sq_eq_one hK).symm

theorem mem_subgroupOf_suzukiZ0_iff
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : suzukiU a K} :
    x ∈ (suzukiZ0 a K).subgroupOf (suzukiU a K) ↔ x ^ 2 = 1 := by
  rw [Subgroup.mem_subgroupOf, mem_suzukiZ0_iff_sq_eq_one hK, and_iff_right x.2]
  constructor
  · intro h
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact h)
  · intro h
    rw [← SubmonoidClass.coe_pow, h, OneMemClass.coe_one]

theorem suzukiZ0_characteristic (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((suzukiZ0 a K).subgroupOf (suzukiU a K)).Characteristic := by
  refine Subgroup.characteristic_iff_comap_eq.2 fun ϕ => Subgroup.ext fun x => ?_
  rw [Subgroup.mem_comap, mem_subgroupOf_suzukiZ0_iff hK, mem_subgroupOf_suzukiZ0_iff hK,
    MulEquiv.coe_toMonoidHom, ← map_pow, map_eq_one_iff ϕ ϕ.injective]

theorem eq_zero_of_suzukiSElt_mem_suzukiZ0
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {u v : K}
    (h : suzukiSElt a K u v ∈ suzukiZ0 a K) : u = 0 := by
  obtain ⟨w, hw⟩ := (mem_suzukiZ0_iff hK).1 h
  exact (suzukiSElt_inj.1 hw).1.symm

theorem suzukiSElt_inv_mul_mem_suzukiZ0
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v w : K) :
    (suzukiSElt a K u v)⁻¹ * suzukiSElt a K u w ∈ suzukiZ0 a K := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  rw [suzukiSElt_inv hK, suzukiSElt_mul hK, show u + u = 0 by linear_combination u * h2]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem suzukiU_quotient_comm (hK : Nat.card K = 2 ^ (2 * a + 1))
    [((suzukiZ0 a K).subgroupOf (suzukiU a K)).Normal]
    (x y : suzukiU a K ⧸ (suzukiZ0 a K).subgroupOf (suzukiU a K)) : x * y = y * x := by
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have h : (((x * y)⁻¹ * (y * x) : suzukiU a K) : suzukiGroup a K) =
      ⁅((y : suzukiGroup a K))⁻¹, ((x : suzukiGroup a K))⁻¹⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_inv_rev, inv_inv]
    group
  rw [h]
  exact commutatorElement_mem_suzukiZ0 hK (inv_mem y.2) (inv_mem x.2)

theorem suzukiT_faithful_quotient
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {t : suzukiGroup a K}
    (ht : t ∈ suzukiT a K)
    (h : ∀ x ∈ suzukiU a K, x⁻¹ * (t * x * t⁻¹) ∈ suzukiZ0 a K) : t = 1 := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 ht
  have h1 := h _ (suzukiSElt_mem_suzukiU a K 1 0)
  rw [suzukiDElt_conj' hK, suzukiSElt_inv hK, suzukiSElt_mul hK] at h1
  have hl := eq_zero_of_suzukiSElt_mem_suzukiZ0 hK h1
  have hl' : ((l⁻¹ : Kˣ) : K) = 1 := by linear_combination hl - h2
  rw [show l = 1 from inv_eq_one.1 (Units.ext (by rw [hl', Units.val_one])), suzukiDElt_one]

theorem suzuki_equivariant_hom_trivial
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    [((suzukiZ0 a K).subgroupOf (suzukiU a K)).Normal]
    (ℓ : suzukiU a K ⧸ (suzukiZ0 a K).subgroupOf (suzukiU a K) →* suzukiZ0 a K)
    (hℓ : ∀ t ∈ suzukiT a K, ∀ x y : suzukiU a K, (y : suzukiGroup a K) = t * x * t⁻¹ →
      (ℓ y : suzukiGroup a K) = t * ℓ x * t⁻¹) : ℓ = 1 := by
  obtain ⟨h2, hadd, -⟩ := suzuki_frob_data a hK
  have hex : ∀ x : K, ∃ b : K,
      suzukiSElt a K 0 b = (ℓ (unipotentElt a K x 0) : suzukiGroup a K) :=
    fun x => (mem_suzukiZ0_iff hK).1 (ℓ _).2
  choose f hf using hex
  have hmk : ∀ x y : K,
      ((unipotentElt a K x 0 : suzukiU a K) : suzukiU a K ⧸
        (suzukiZ0 a K).subgroupOf (suzukiU a K)) * (unipotentElt a K y 0 : suzukiU a K) =
        (unipotentElt a K (x + y) 0 : suzukiU a K) := by
    intro x y
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf, unipotentElt_mul hK]
    exact suzukiSElt_inv_mul_mem_suzukiZ0 hK _ _ _
  have hfadd : ∀ x y : K, f (x + y) = f x + f y := by
    intro x y
    have h := congrArg (fun q => (ℓ q : suzukiGroup a K)) (hmk x y)
    simp only [map_mul, Subgroup.coe_mul, ← hf] at h
    rw [suzukiSElt_mul hK, suzukiSElt_inj] at h
    linear_combination -h.2
  have hfsmul : ∀ (μ : Kˣ) (x : K), f (μ * x) = (μ : K) ^ (2 ^ (a + 1) + 1) * f x := by
    intro μ x
    have h := hℓ (suzukiDElt a K μ⁻¹) (suzukiDElt_mem_suzukiT a K _) (unipotentElt a K x 0)
      (unipotentElt a K (μ * x) 0) (by
        rw [coe_unipotentElt, coe_unipotentElt, suzukiDElt_conj' hK, inv_inv, mul_zero])
    rw [← hf, ← hf, suzukiDElt_conj' hK, inv_inv, suzukiSElt_inj] at h
    exact h.2
  have hf0 : f 0 = 0 := by
    have h := hfadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hfpow : ∀ y : K, f y = y ^ (2 ^ (a + 1) + 1) * f 1 := by
    intro y
    by_cases hy : y = 0
    · rw [hy, hf0, zero_pow (Nat.succ_ne_zero _), zero_mul]
    · have h := hfsmul (Units.mk0 y hy) 1
      rwa [Units.val_mk0, mul_one] at h
  obtain ⟨h, hh⟩ := exists_add_pow_ne_zero hK ha
  have hc : f 1 = 0 := by
    have e := hfadd h 1
    rw [hfpow (h + 1), hfpow h, pow_succ (h + 1), hadd, one_pow, pow_succ h] at e
    have e' : (h + h ^ 2 ^ (a + 1)) * f 1 = 0 := by linear_combination e
    exact (mul_eq_zero.1 e').resolve_left hh
  refine MonoidHom.ext fun q => ?_
  induction q using QuotientGroup.induction_on with | H x => ?_
  obtain ⟨u, v, rfl⟩ := exists_unipotentElt_eq hK x
  have hq : ((unipotentElt a K u v : suzukiU a K) : suzukiU a K ⧸
      (suzukiZ0 a K).subgroupOf (suzukiU a K)) = (unipotentElt a K u 0 : suzukiU a K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact suzukiSElt_inv_mul_mem_suzukiZ0 hK _ _ _
  rw [hq, MonoidHom.one_apply]
  refine Subtype.ext ?_
  rw [← hf, hfpow, hc, mul_zero, suzukiSElt_zero_zero hK]
  rfl

end CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
