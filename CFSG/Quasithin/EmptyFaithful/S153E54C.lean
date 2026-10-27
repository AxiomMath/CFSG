module

public import CFSG.Quasithin.EmptyFaithful.S153EO4
public import CFSG.Quasithin.EmptyFaithful.S153E54A

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.T1531O4
open CFSG.Quasithin.S153E CFSG.Quasithin.Om4Model

section Model

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem exists_vec_iso (hcard : Nat.card W = 16) {q : W → ZMod 2} (hq1 : IsQuadraticFormOn q)
    (hq2 : IsNondegQuadratic q) (hq3 : IsPlusType q) :
    ∃ c : W ≃* Vec, ∀ v, q v = detQ (c v) := by
  have hexp : ∀ w : W, w * w = 1 := S152O.sq_eq_one_of_nondeg hq1 hq2
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hqe⟩ :=
    S153.exists_decomposition_of_plusType hexp hcard hq1 hq2 hq3
  refine ⟨(S1417.coordEquiv hinf hsup φ₁ φ₂).trans kappa, fun v => ?_⟩
  rw [hqe v, quadOf_eq_qFloc hinf hsup φ₁ φ₂ v]
  exact qFloc_eq_detQ _

variable {q : W → ZMod 2}

private theorem hR_sub (hcard : Nat.card W = 16) (hexp' : ∀ w : W, w ^ 2 = 1) (c : W ≃* Vec)
    (hqc : ∀ v, q v = detQ (c v)) (γ : Gam) :
    rhoV c γ ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers (rhoV c γ)))) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [hqc, hqc, rhoV_apply, detQ_act]
  · apply even_rk_comm_of_card hexp' hcard
    have := card_fixV_conjBack c (rho γ)
    change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = _ at this
    change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 1 ∨
      Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 4 ∨
      Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 16
    rw [this]
    exact nat_card_fix γ

private theorem g₀_odd (hcard : Nat.card W = 16) (hexp' : ∀ w : W, w ^ 2 = 1) (c : W ≃* Vec)
    (hqc : ∀ v, q v = detQ (c v)) :
    conjBack c transV ∈ orthogonalGroupOf q ∧
      ¬ Even (rk (commV (Subgroup.zpowers (conjBack c transV)))) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [hqc, hqc, conjBack_apply, detQ_trans]
  · refine not_even_rk_comm_of_card hexp' hcard _ ?_
    rw [card_fixV_conjBack c transV]
    simp only [Nat.card_eq_fintype_card]
    exact transCount

theorem range_iff (hcard : Nat.card W = 16) (hq1 : IsQuadraticFormOn q) (hq2 : IsNondegQuadratic q)
    (hq3 : IsPlusType q) (c : W ≃* Vec) (hqc : ∀ v, q v = detQ (c v)) (g : MulAut W) :
    g ∈ (rhoV c).range ↔ g ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers g))) := by
  have hexp : ∀ w : W, w * w = 1 := S152O.sq_eq_one_of_nondeg hq1 hq2
  have hexp' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  constructor
  · rintro ⟨γ, rfl⟩
    exact hR_sub hcard hexp' c hqc γ
  · rintro ⟨hgO, hgE⟩
    by_contra hgR
    obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
    have hO72 : Nat.card (orthogonalGroupOf q) = 72 := hS.card_X
    have hR36 : Nat.card (rhoV c).range = 36 := by
      rw [← card_Gam]
      exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective c)).toEquiv).symm
    have hRO : (rhoV c).range ≤ orthogonalGroupOf q := by
      rintro _ ⟨γ, rfl⟩
      exact (hR_sub hcard hexp' c hqc γ).1
    have hindex : ((rhoV c).range.subgroupOf (orthogonalGroupOf q)).index = 2 := by
      have h1 := Subgroup.card_mul_index ((rhoV c).range.subgroupOf (orthogonalGroupOf q))
      have h2 : Nat.card ((rhoV c).range.subgroupOf (orthogonalGroupOf q)) =
          Nat.card (rhoV c).range :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRO).toEquiv
      rw [h2, hR36, hO72] at h1
      omega
    obtain ⟨hg₀O, hg₀odd⟩ := g₀_odd hcard hexp' c hqc
    have hg₀R : conjBack c transV ∉ (rhoV c).range := by
      rintro ⟨γ, hγ⟩
      exact hg₀odd (hγ ▸ (hR_sub hcard hexp' c hqc γ).2)
    have key := Subgroup.mul_mem_iff_of_index_two hindex
      (a := (⟨conjBack c transV, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹) (b := ⟨g, hgO⟩)
    have hprod : (⟨conjBack c transV, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹ * ⟨g, hgO⟩ ∈
        (rhoV c).range.subgroupOf (orthogonalGroupOf q) := by
      rw [key]
      constructor
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h)) hg₀R
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp h) hgR
    obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.mp hprod
    have hg : g = conjBack c (transV * rho γ) := by
      have h1 : rhoV c γ = (conjBack c transV)⁻¹ * g := by simpa using hγ
      have h2 : g = conjBack c transV * rhoV c γ := by rw [h1]; group
      rw [h2, conjBack_mul]
      rfl
    have hcard' := card_fixV_conjBack c (transV * rho γ)
    rw [← hg] at hcard'
    have hct : Fintype.card {v : Vec // transV (act γ v) = v} = 2 ∨
        Fintype.card {v : Vec // transV (act γ v) = v} = 8 := transCount_mul γ
    rcases hct with h2 | h8
    · refine not_even_rk_comm_of_card_two hexp' hcard g ?_ hgE
      rw [hcard']
      simp only [Nat.card_eq_fintype_card]
      exact h2
    · refine not_even_rk_comm_of_card hexp' hcard g ?_ hgE
      rw [hcard']
      simp only [Nat.card_eq_fintype_card]
      exact h8

theorem odd_eq_mul (hcard : Nat.card W = 16) (hq1 : IsQuadraticFormOn q) (hq2 : IsNondegQuadratic q)
    (hq3 : IsPlusType q) (c : W ≃* Vec) (hqc : ∀ v, q v = detQ (c v)) {x : MulAut W}
    (hxO : x ∈ orthogonalGroupOf q) (hxodd : ¬ Even (rk (commV (Subgroup.zpowers x)))) :
    ∃ ω ∈ (rhoV c).range, x = conjBack c transV * ω := by
  have hexp : ∀ w : W, w * w = 1 := S152O.sq_eq_one_of_nondeg hq1 hq2
  have hexp' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
  have hO72 : Nat.card (orthogonalGroupOf q) = 72 := hS.card_X
  have hR36 : Nat.card (rhoV c).range = 36 := by
    rw [← card_Gam]
    exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective c)).toEquiv).symm
  have hRO : (rhoV c).range ≤ orthogonalGroupOf q := by
    rintro _ ⟨γ, rfl⟩
    exact (hR_sub hcard hexp' c hqc γ).1
  have hindex : ((rhoV c).range.subgroupOf (orthogonalGroupOf q)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((rhoV c).range.subgroupOf (orthogonalGroupOf q))
    have h2 : Nat.card ((rhoV c).range.subgroupOf (orthogonalGroupOf q)) =
        Nat.card (rhoV c).range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRO).toEquiv
    rw [h2, hR36, hO72] at h1
    omega
  obtain ⟨hg₀O, hg₀odd⟩ := g₀_odd hcard hexp' c hqc
  have hg₀R : conjBack c transV ∉ (rhoV c).range := by
    rintro ⟨γ, hγ⟩
    exact hg₀odd (hγ ▸ (hR_sub hcard hexp' c hqc γ).2)
  have hxR : x ∉ (rhoV c).range := fun h =>
    hxodd ((range_iff hcard hq1 hq2 hq3 c hqc x).1 h).2
  have key := Subgroup.mul_mem_iff_of_index_two hindex
    (a := (⟨conjBack c transV, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹) (b := ⟨x, hxO⟩)
  have hprod : (⟨conjBack c transV, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹ * ⟨x, hxO⟩ ∈
      (rhoV c).range.subgroupOf (orthogonalGroupOf q) := by
    rw [key]
    constructor
    · intro h
      exact absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h)) hg₀R
    · intro h
      exact absurd (Subgroup.mem_subgroupOf.mp h) hxR
  have hω := Subgroup.mem_subgroupOf.mp hprod
  refine ⟨(conjBack c transV)⁻¹ * x, by simpa using hω, ?_⟩
  group

private theorem transV_invol : ∀ v : Vec, transV (transV v) = v := by decide +kernel

omit [Finite W] in
theorem conj_swap₁ (c : W ≃* Vec) (a : DihedralGroup 3) :
    ∃ b : DihedralGroup 3,
      conjBack c transV * rhoV c (a, 1) * (conjBack c transV)⁻¹ = rhoV c (1, b) := by
  obtain ⟨b, hb⟩ := swap_fact₁ a
  refine ⟨b, MulEquiv.ext fun u => c.injective ?_⟩
  have h1 : c ((conjBack c transV)⁻¹ u) = transV (c u) := by
    have h2 := conjBack_apply c transV ((conjBack c transV)⁻¹ u)
    rw [show conjBack c transV ((conjBack c transV)⁻¹ u) = u from by
      rw [← MulAut.mul_apply, mul_inv_cancel]; rfl] at h2
    rw [h2, transV_invol]
  rw [MulAut.mul_apply, MulAut.mul_apply, conjBack_apply, rhoV_apply, h1, rhoV_apply]
  exact hb (c u)

omit [Finite W] in
theorem conj_swap₂ (c : W ≃* Vec) (b : DihedralGroup 3) :
    ∃ a : DihedralGroup 3,
      conjBack c transV * rhoV c (1, b) * (conjBack c transV)⁻¹ = rhoV c (a, 1) := by
  obtain ⟨a, ha⟩ := swap_fact₂ b
  refine ⟨a, MulEquiv.ext fun u => c.injective ?_⟩
  have h1 : c ((conjBack c transV)⁻¹ u) = transV (c u) := by
    have h2 := conjBack_apply c transV ((conjBack c transV)⁻¹ u)
    rw [show conjBack c transV ((conjBack c transV)⁻¹ u) = u from by
      rw [← MulAut.mul_apply, mul_inv_cancel]; rfl] at h2
    rw [h2, transV_invol]
  rw [MulAut.mul_apply, MulAut.mul_apply, conjBack_apply, rhoV_apply, h1, rhoV_apply]
  exact ha (c u)

theorem exists_split_swap (hcard : Nat.card W = 16) (hq1 : IsQuadraticFormOn q)
    (hq2 : IsNondegQuadratic q) (hq3 : IsPlusType q) :
    ∃ R₁ R₂ : Subgroup (MulAut W),
      (∀ g : MulAut W, g ∈ R₁ ⊔ R₂ ↔
        g ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers g)))) ∧
      R₁ ⊓ R₂ = ⊥ ∧ (∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a) ∧
      Nonempty (↥R₁ ≃* DihedralGroup 3) ∧ Nonempty (↥R₂ ≃* DihedralGroup 3) ∧
      ∀ x ∈ orthogonalGroupOf q, ¬ Even (rk (commV (Subgroup.zpowers x))) →
        (∀ g ∈ R₁, x * g * x⁻¹ ∈ R₂) ∧ (∀ g ∈ R₂, x * g * x⁻¹ ∈ R₁) := by
  obtain ⟨c, hqc⟩ := exists_vec_iso hcard hq1 hq2 hq3
  let ι₁ : DihedralGroup 3 →* MulAut W := (rhoV c).comp (MonoidHom.inl _ _)
  let ι₂ : DihedralGroup 3 →* MulAut W := (rhoV c).comp (MonoidHom.inr _ _)
  have hι₁ : Function.Injective ι₁ := fun a b h => (Prod.mk.inj (rhoV_injective c h)).1
  have hι₂ : Function.Injective ι₂ := fun a b h => (Prod.mk.inj (rhoV_injective c h)).2
  have hprod : ∀ a b : DihedralGroup 3, rhoV c (a, b) = ι₁ a * ι₂ b := by
    intro a b
    show rhoV c (a, b) = rhoV c (a, 1) * rhoV c (1, b)
    rw [← map_mul]
    simp
  have hsup : ι₁.range ⊔ ι₂.range = (rhoV c).range := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨(a, 1), rfl⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨(1, b), rfl⟩
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [hprod]
      exact Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨ι₁.range, ι₂.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [hsup]
    exact range_iff hcard hq1 hq2 hq3 c hqc g
  · rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h1 : rhoV c (a, 1) = rhoV c (1, b) := by
      have e1 : rhoV c (a, 1) = ι₁ a := rfl
      have e2 : rhoV c (1, b) = ι₂ b := rfl
      rw [e1, e2, hb]
    have h2 := rhoV_injective c h1
    have ha : a = 1 := congrArg Prod.fst h2
    rw [ha, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have h2 : ι₂ b * ι₁ a = rhoV c (a, b) := by
      show rhoV c (1, b) * rhoV c (a, 1) = rhoV c (a, b)
      rw [← map_mul]
      simp
    rw [h2, hprod]
  · exact ⟨(MonoidHom.ofInjective hι₁).symm⟩
  · exact ⟨(MonoidHom.ofInjective hι₂).symm⟩
  · intro x hxO hxodd
    obtain ⟨ω, ⟨γ, rfl⟩, rfl⟩ := odd_eq_mul hcard hq1 hq2 hq3 c hqc hxO hxodd
    obtain ⟨γ₁, γ₂⟩ := γ
    constructor
    · rintro _ ⟨a, rfl⟩
      have e : conjBack c transV * rhoV c (γ₁, γ₂) * ι₁ a *
          (conjBack c transV * rhoV c (γ₁, γ₂))⁻¹ =
          conjBack c transV * rhoV c (γ₁ * a * γ₁⁻¹, 1) * (conjBack c transV)⁻¹ := by
        have : rhoV c (γ₁ * a * γ₁⁻¹, 1) = rhoV c (γ₁, γ₂) * ι₁ a * (rhoV c (γ₁, γ₂))⁻¹ := by
          show _ = rhoV c (γ₁, γ₂) * rhoV c (a, 1) * (rhoV c (γ₁, γ₂))⁻¹
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          ext <;> simp
        rw [this]
        group
      obtain ⟨b, hb⟩ := conj_swap₁ c (γ₁ * a * γ₁⁻¹)
      rw [e, hb]
      exact ⟨b, rfl⟩
    · rintro _ ⟨b, rfl⟩
      have e : conjBack c transV * rhoV c (γ₁, γ₂) * ι₂ b *
          (conjBack c transV * rhoV c (γ₁, γ₂))⁻¹ =
          conjBack c transV * rhoV c (1, γ₂ * b * γ₂⁻¹) * (conjBack c transV)⁻¹ := by
        have : rhoV c (1, γ₂ * b * γ₂⁻¹) = rhoV c (γ₁, γ₂) * ι₂ b * (rhoV c (γ₁, γ₂))⁻¹ := by
          show _ = rhoV c (γ₁, γ₂) * rhoV c (1, b) * (rhoV c (γ₁, γ₂))⁻¹
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          ext <;> simp
        rw [this]
        group
      obtain ⟨a, ha⟩ := conj_swap₂ c (γ₂ * b * γ₂⁻¹)
      rw [e, ha]
      exact ⟨a, rfl⟩

omit [Finite W] in
theorem quadPolar_eq_polarDet (c : W ≃* Vec) (hqc : ∀ v, q v = detQ (c v)) (x y : W) :
    quadPolar q x y = polarDet (toMt (c x)) (toMt (c y)) := by
  unfold quadPolar polarDet
  simp only [hqc, map_mul, toMt_det, toMt_mul]

end Model

end S153E54

end CFSG.Quasithin
