module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


section Cyclic

variable {Q : Type*} [Group Q]

theorem mem_zpowers_of_cube_of_cyclic [IsCyclic Q] {x y : Q} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy3 : y ^ 3 = 1) : y ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hfx : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx3⟩
  have hfy : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hy3⟩
  have : Finite (Subgroup.zpowers x) := hfx.finite_zpowers
  have : Finite (Subgroup.zpowers y) := hfy.finite_zpowers
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy])
  rw [← heq]
  exact Subgroup.mem_zpowers y

theorem exists_lt_three_pow_mul_eq_one_of_mem {x y : Q} (hx3 : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : ∃ k < 3, x ^ k * y = 1 := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨w, hw⟩ : ∃ w : ℤ, (((-z) % 3).toNat : ℤ) + z = 3 * w := ⟨-((-z) / 3), by omega⟩
  refine ⟨((-z) % 3).toNat, by omega, ?_⟩
  rw [← zpow_natCast, ← zpow_add, hw, zpow_mul, zpow_ofNat, hx3, one_zpow]

theorem cube_eq_one_of_conj_cube {d φ : Q} (h : (d * φ * d⁻¹) ^ 3 = 1) : φ ^ 3 = 1 := by
  rw [conj_pow] at h
  calc φ ^ 3 = d⁻¹ * (d * φ ^ 3 * d⁻¹) * d := by group
    _ = 1 := by rw [h]; group

end Cyclic

section OuterCyclic

variable {M : Type*} [Group M]

theorem isCyclic_outer_of_normal_form {Γ : Type*} [Group Γ] [IsCyclic Γ] (ψ : Γ →* MulAut M)
    (h : ∀ α : MulAut M, ∃ (m : M) (γ : Γ), α = MulAut.conj m * ψ γ) :
    IsCyclic (Outer M) := by
  refine isCyclic_of_surjective ((QuotientGroup.mk' (inner M)).comp ψ) fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H α =>
    obtain ⟨m, γ, rfl⟩ := h α
    refine ⟨γ, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := inner M) _).mpr ⟨m, rfl⟩, one_mul]

theorem isCyclic_range_of_cyclic {Γ G : Type*} [Group Γ] [Group G] [IsCyclic Γ] (ψ : Γ →* G) :
    IsCyclic ψ.range :=
  isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective

end OuterCyclic

@[expose] def OutThreeBound (M : Type*) [Group M] : Prop :=
  ∀ B' : Subgroup (MulAut M), (∀ x ∈ B', x ^ 3 = 1) →
    ∃ α ∈ B', ∀ β ∈ B', ∃ k < 3, IsInnerAut (α ^ k * β)

section Transport

variable {M N : Type*} [Group M] [Group N]

theorem OutThreeBound.of_mulEquiv (h : OutThreeBound N) (e : M ≃* N) : OutThreeBound M := by
  intro B hB
  obtain ⟨α', hα'B, hα'⟩ := h (B.map (MulAut.congr e).toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    change (MulAut.congr e x) ^ 3 = 1
    rw [← map_pow, hB x hx, map_one])
  obtain ⟨α, hαB, rfl⟩ := hα'B
  refine ⟨α, hαB, fun β hβ => ?_⟩
  obtain ⟨k, hk, hin⟩ := hα' (MulAut.congr e β) ⟨β, hβ, rfl⟩
  refine ⟨k, hk, ?_⟩
  rw [← isInnerAut_congr e]
  change IsInnerAut ((MulAut.congr e α) ^ k * MulAut.congr e β) at hin
  rwa [← map_pow, ← map_mul] at hin

end Transport

section OutCases

variable {M : Type*} [Group M]

theorem outThreeBound_of_cube_inner (h : ∀ τ : MulAut M, τ ^ 3 = 1 → IsInnerAut τ) :
    OutThreeBound M := fun B hB =>
  ⟨1, B.one_mem, fun β hβ => ⟨0, by norm_num, by rw [pow_zero, one_mul]; exact h β (hB β hβ)⟩⟩

theorem cube_inner_of_card_outer_dvd_two (h : Nat.card (Outer M) ∣ 2) :
    ∀ τ : MulAut M, τ ^ 3 = 1 → IsInnerAut τ := by
  intro τ hτ
  have hne : Nat.card (Outer M) ≠ 0 := fun h0 => by
    rw [h0] at h
    omega
  have : Finite (Outer M) := Nat.finite_of_card_ne_zero hne
  obtain ⟨c, hc⟩ := h
  have h2 : (QuotientGroup.mk τ : Outer M) ^ 2 = 1 := by
    rw [hc, pow_mul, pow_card_eq_one', one_pow]
  have h3 : (QuotientGroup.mk τ : Outer M) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
  have h1 : (QuotientGroup.mk τ : Outer M) = 1 := by
    calc (QuotientGroup.mk τ : Outer M) = (QuotientGroup.mk τ) ^ 3 * ((QuotientGroup.mk τ) ^ 2)⁻¹ :=
          by group
      _ = 1 := by rw [h3, h2]; simp
  exact (QuotientGroup.eq_one_iff (N := inner M) τ).mp h1

theorem outThreeBound_of_card_outer_dvd_two (h : Nat.card (Outer M) ∣ 2) : OutThreeBound M :=
  outThreeBound_of_cube_inner (cube_inner_of_card_outer_dvd_two h)

theorem outThreeBound_of_isCyclic (h : IsCyclic (Outer M)) : OutThreeBound M := by
  intro B hB
  by_cases hall : ∀ α ∈ B, IsInnerAut α
  · exact ⟨1, B.one_mem, fun β hβ => ⟨0, by norm_num, by rw [pow_zero, one_mul]; exact hall β hβ⟩⟩
  push Not at hall
  obtain ⟨α, hαB, hαin⟩ := hall
  refine ⟨α, hαB, fun β hβ => ?_⟩
  have hα1 : (QuotientGroup.mk α : Outer M) ≠ 1 := fun h1 =>
    hαin ((QuotientGroup.eq_one_iff (N := inner M) α).mp h1)
  have hα3 : (QuotientGroup.mk α : Outer M) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hB α hαB, QuotientGroup.mk_one]
  have hβ3 : (QuotientGroup.mk β : Outer M) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hB β hβ, QuotientGroup.mk_one]
  obtain ⟨k, hk, h1⟩ := exists_lt_three_pow_mul_eq_one_of_mem hα3
    (mem_zpowers_of_cube_of_cyclic hα3 hα1 hβ3)
  refine ⟨k, hk, ?_⟩
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul] at h1
  exact (QuotientGroup.eq_one_iff (N := inner M) _).mp h1

end OutCases

section Pinned

variable {M : Type*} [Group M]

theorem outThreeBound_of_pinned_cube (P : PinnedAut M) (hnorm : P.inndiag.Normal)
    (hkind : ∀ τ : MulAut M, τ ^ 3 = 1 → τ ∉ P.inndiag → P.IsField τ)
    (hcyc : IsCyclic P.field) (hcube : ∀ δ ∈ P.inndiag, δ ^ 3 = 1 → IsInnerAut δ) :
    OutThreeBound M := by
  intro B hB
  by_cases hall : ∀ α ∈ B, α ∈ P.inndiag
  · exact ⟨1, B.one_mem, fun β hβ => ⟨0, by norm_num, by
      rw [pow_zero, one_mul]; exact hcube β (hall β hβ) (hB β hβ)⟩⟩
  push Not at hall
  obtain ⟨α, hαB, hαD⟩ := hall
  refine ⟨α, hαB, fun β hβB => ?_⟩
  have hα3 : α ^ 3 = 1 := hB α hαB
  have hβ3 : β ^ 3 = 1 := hB β hβB
  by_cases hβD : β ∈ P.inndiag
  · exact ⟨0, by norm_num, by rw [pow_zero, one_mul]; exact hcube β hβD hβ3⟩
  obtain ⟨φ, hφ, hφ1, d, hd, hαeq⟩ := hkind α hα3 hαD
  obtain ⟨φ', hφ', -, d', hd', hβeq⟩ := hkind β hβ3 hβD
  have hφ3 : φ ^ 3 = 1 := cube_eq_one_of_conj_cube (hαeq ▸ hα3)
  have hφ'3 : φ' ^ 3 = 1 := cube_eq_one_of_conj_cube (hβeq ▸ hβ3)
  have hmem : (⟨φ', hφ'⟩ : P.field) ∈ Subgroup.zpowers (⟨φ, hφ⟩ : P.field) :=
    mem_zpowers_of_cube_of_cyclic (Subtype.ext (by simpa using hφ3))
      (fun h => hφ1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hφ'3))
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hφz : φ ^ z = φ' := by
    have := congrArg Subtype.val hz
    simpa using this
  have := hnorm
  set π := QuotientGroup.mk' P.inndiag with hπ
  have hconj : ∀ e ψ : MulAut M, e ∈ P.inndiag → π (e * ψ * e⁻¹) = π ψ := by
    intro e ψ he
    have he1 : π e = 1 := (QuotientGroup.eq_one_iff (N := P.inndiag) e).mpr he
    rw [map_mul, map_mul, map_inv, he1, one_mul, inv_one, mul_one]
  have hπα : π α = π φ := by rw [hαeq, hconj d φ hd]
  have hπβ : π β = π α ^ z := by rw [hβeq, hconj d' φ' hd', hπα, ← map_zpow, hφz]
  have hπα3 : π α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  obtain ⟨k, hk, h1⟩ := exists_lt_three_pow_mul_eq_one_of_mem hπα3 (Subgroup.mem_zpowers_iff.mpr
    ⟨z, hπβ.symm⟩)
  rw [← map_pow, ← map_mul] at h1
  have hD : α ^ k * β ∈ P.inndiag := (QuotientGroup.eq_one_iff (N := P.inndiag) _).mp h1
  exact ⟨k, hk, hcube _ hD (hB _ (B.mul_mem (B.pow_mem hαB k) hβB))⟩

end Pinned

end CFSG.Quasithin.SBd19F
