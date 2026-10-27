module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass

public section

namespace CFSG.StandardType

namespace D4Bstar

open CFSG.StandardType.Triality CFSG.StandardType.D4Rank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms

section TriPart

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def IsTriPart (k : ℕ) (α : MulAut (Om8 K)) : Prop :=
  ∃ (γ : Om8 K) (σ : K ≃+* K), α = MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ)

theorem isTriPart_one : IsTriPart 0 (1 : MulAut (Om8 K)) :=
  ⟨1, 1, by rw [map_one, pow_zero, map_one, one_mul, one_mul]⟩

theorem theta_pow_fieldAutP_mul (k l : ℕ) (σ τ : K ≃+* K) :
    (theta ^ k * AutOm.fieldAutP 4 σ) * (theta ^ l * AutOm.fieldAutP 4 τ) =
      (theta : MulAut (Om8 K)) ^ (k + l) * AutOm.fieldAutP 4 (σ * τ) := by
  have hc : AutOm.fieldAutP 4 σ * (theta : MulAut (Om8 K)) ^ l =
      theta ^ l * AutOm.fieldAutP 4 σ :=
    ((Commute.pow_left (theta_fieldAutP σ : Commute theta (AutOm.fieldAutP 4 σ)) l)).eq.symm
  calc (theta ^ k * AutOm.fieldAutP 4 σ) * (theta ^ l * AutOm.fieldAutP 4 τ)
      = theta ^ k * (AutOm.fieldAutP 4 σ * theta ^ l) * AutOm.fieldAutP 4 τ := by
        simp only [mul_assoc]
    _ = theta ^ k * (theta ^ l * AutOm.fieldAutP 4 σ) * AutOm.fieldAutP 4 τ := by rw [hc]
    _ = (theta : MulAut (Om8 K)) ^ (k + l) * AutOm.fieldAutP 4 (σ * τ) := by
        rw [map_mul (AutOm.fieldAutP 4) σ τ, pow_add]
        simp only [mul_assoc]

theorem IsTriPart.mul {k l : ℕ} {α α' : MulAut (Om8 K)} (h : IsTriPart k α)
    (h' : IsTriPart l α') : IsTriPart (k + l) (α * α') := by
  obtain ⟨γ, σ, rfl⟩ := h
  obtain ⟨γ', τ, rfl⟩ := h'
  set t : MulAut (Om8 K) := theta ^ k * AutOm.fieldAutP 4 σ with ht
  refine ⟨γ * t γ', σ * τ, ?_⟩
  calc MulAut.conj γ * t * (MulAut.conj γ' * (theta ^ l * AutOm.fieldAutP 4 τ))
      = MulAut.conj γ * (t * MulAut.conj γ') * (theta ^ l * AutOm.fieldAutP 4 τ) := by
        simp only [mul_assoc]
    _ = MulAut.conj γ * (MulAut.conj (t γ') * t) * (theta ^ l * AutOm.fieldAutP 4 τ) := by
        rw [mulAut_mul_conj]
    _ = MulAut.conj (γ * t γ') * (t * (theta ^ l * AutOm.fieldAutP 4 τ)) := by
        rw [map_mul MulAut.conj]
        simp only [mul_assoc]
    _ = MulAut.conj (γ * t γ') * (theta ^ (k + l) * AutOm.fieldAutP 4 (σ * τ)) := by
        rw [ht, theta_pow_fieldAutP_mul]

theorem IsTriPart.pow {k : ℕ} {α : MulAut (Om8 K)} (h : IsTriPart k α) (j : ℕ) :
    IsTriPart (j * k) (α ^ j) := by
  induction j with
  | zero => rw [zero_mul, pow_zero]; exact isTriPart_one
  | succ j ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul h

theorem IsTriPart.mod_three {k : ℕ} {α : MulAut (Om8 K)} (h : IsTriPart k α) :
    IsTriPart (k % 3) α := by
  obtain ⟨γ, σ, rfl⟩ := h
  exact ⟨γ, σ, by rw [pow_eq_pow_mod k theta_cube]⟩

theorem exists_pair_of_isTriPart_zero {α : MulAut (Om8 K)} (h : IsTriPart 0 α) :
    ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = α := by
  obtain ⟨γ, σ, rfl⟩ := h
  obtain ⟨g₁, hg₁⟩ := exists_pair_of_mem_inner (K := K) ⟨γ, rfl⟩
  refine ⟨g₁ * AutOm.gField (n := 4) σ, ?_⟩
  rw [map_mul, hg₁, pow_zero, one_mul, AutOm.fieldAutP_eq]

end TriPart

section Transfer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type*} [Group G] {ψ : Sp8 F →* G}

omit [Finite F] in
theorem injective_of_ker_le_center (hker : ψ.ker ≤ Subgroup.center (Sp8 F)) :
    Function.Injective ψ := by
  have hcen := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := F) (n := 4)
    (by norm_num)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  exact hker.trans hcen.le

omit [Finite F] [CharP F 2] in
theorem conj_rel_pow {c : G} {β : MulAut (Sp8 F)} (hβ : ∀ y, ψ (β y) = c⁻¹ * ψ y * c) (j : ℕ) :
    ∀ y, ψ ((β ^ j) y) = (c ^ j)⁻¹ * ψ y * c ^ j := by
  induction j with
  | zero => intro y; simp
  | succ j ih =>
    intro y
    rw [pow_succ β j, MulAut.mul_apply, ih, hβ, pow_succ' c j]
    group

omit [Finite F] [CharP F 2] in
theorem conj_rel_mul {a b : G} {βa βb : MulAut (Sp8 F)} (ha : ∀ y, ψ (βa y) = a⁻¹ * ψ y * a)
    (hb : ∀ y, ψ (βb y) = b⁻¹ * ψ y * b) :
    ∀ y, ψ ((βb * βa) y) = (a * b)⁻¹ * ψ y * (a * b) := by
  intro y
  rw [MulAut.mul_apply, hb, ha]
  group

theorem ggSpinSemilinear_of_isTriPart (hinj : Function.Injective ψ) {c : G}
    {β : MulAut (Sp8 F)} (hβ : ∀ y, ψ (β y) = c⁻¹ * ψ y * c) {k : ℕ} (hk : k % 3 = 0)
    (h : IsTriPart k (MulAut.congr modelEquiv8 β)) : GGSpinSemilinear (quadPlus 4 F) ψ c := by
  have h0 := h.mod_three
  rw [hk] at h0
  obtain ⟨g, hg⟩ := exists_pair_of_isTriPart_zero h0
  exact ggSpinSemilinear_of_conjAct hinj hβ hg

theorem isTriPart_of_not_semilinear (hinj : Function.Injective ψ) {c : G}
    {β : MulAut (Sp8 F)} (hβ : ∀ y, ψ (β y) = c⁻¹ * ψ y * c)
    (hc3 : c ^ 3 ∈ Subgroup.centralizer (ψ.range : Set G))
    (hns : ¬ GGSpinSemilinear (quadPlus 4 F) ψ c) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ IsTriPart k (MulAut.congr modelEquiv8 β) := by
  have hcomm3 : ∀ y, ψ y * c ^ 3 = c ^ 3 * ψ y := fun y =>
    Subgroup.mem_centralizer_iff.mp hc3 (ψ y) ⟨y, rfl⟩
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun y => hinj ?_
    rw [MulAut.one_apply, conj_rel_pow hβ 3, mul_assoc, hcomm3, inv_mul_cancel_left]
  have hα3 : (MulAut.congr modelEquiv8 β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hns' : ∀ g : similarityPairs (coordinateQuadPlus 4 F),
      conjAct _ g ≠ MulAut.congr modelEquiv8 β :=
    fun g hg => hns (ggSpinSemilinear_of_conjAct hinj hβ hg)
  obtain ⟨γ, k, σ, hk, hα⟩ := exists_conj_theta_pow_fieldAutP _ hα3 hns'
  exact ⟨k, hk, γ, σ, hα⟩

theorem exists_semilinear_mul_pow (hinj : Function.Injective ψ) {a b : G}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G))
    (hb : b ∈ Subgroup.normalizer (ψ.range : Set G))
    (ha3 : a ^ 3 ∈ Subgroup.centralizer (ψ.range : Set G))
    (hb3 : b ^ 3 ∈ Subgroup.centralizer (ψ.range : Set G))
    (hbs : ¬ GGSpinSemilinear (quadPlus 4 F) ψ b) :
    ∃ j : ℕ, j < 3 ∧ GGSpinSemilinear (quadPlus 4 F) ψ (a * b ^ j) := by
  by_cases has : GGSpinSemilinear (quadPlus 4 F) ψ a
  · exact ⟨0, by norm_num, by rwa [pow_zero, mul_one]⟩
  obtain ⟨βa, hβa⟩ := exists_mulAut_conj ψ hinj ha
  obtain ⟨βb, hβb⟩ := exists_mulAut_conj ψ hinj hb
  obtain ⟨ka, hka, hTa⟩ := isTriPart_of_not_semilinear hinj hβa ha3 has
  obtain ⟨kb, hkb, hTb⟩ := isTriPart_of_not_semilinear hinj hβb hb3 hbs
  obtain ⟨j, hj3, hj⟩ : ∃ j : ℕ, j < 3 ∧ (j * kb + ka) % 3 = 0 := by
    rcases hka with rfl | rfl <;> rcases hkb with rfl | rfl
    exacts [⟨2, by norm_num, by norm_num⟩, ⟨1, by norm_num, by norm_num⟩,
      ⟨1, by norm_num, by norm_num⟩, ⟨2, by norm_num, by norm_num⟩]
  refine ⟨j, hj3, ggSpinSemilinear_of_isTriPart hinj (conj_rel_mul hβa (conj_rel_pow hβb j)) hj
    ?_⟩
  rw [map_mul, map_pow]
  exact (hTb.pow j).mul hTa

end Transfer

end D4Bstar

end CFSG.StandardType
