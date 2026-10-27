module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.EmptyFaithful.S143EF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Util

theorem commutator_mem_of_index_eq_two {A : Type*} [Group A] {H : Subgroup A} (h : H.index = 2)
    (a b : A) : a * b * a⁻¹ * b⁻¹ ∈ H := by
  have hN : H.Normal := Subgroup.normal_of_index_eq_two h
  have hcard : Nat.card (A ⧸ H) = 2 := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsCyclic (A ⧸ H) := isCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hcomm : ∀ x y : A ⧸ H, x * y = y * x := by
    intro x y
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    exact (Commute.zpow_zpow_self g i j).eq
  have h1 := hcomm (QuotientGroup.mk a) (QuotientGroup.mk b)
  have h2 : ((a * b * a⁻¹ * b⁻¹ : A) : A ⧸ H) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    rw [h1]; group
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem commutator_mem_of_relIndex_two {G : Type*} [Group G] {N H : Subgroup G}
    (h : N.relIndex H = 2) {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  have h1 := commutator_mem_of_index_eq_two (H := N.subgroupOf H) h ⟨a, ha⟩ ⟨b, hb⟩
  exact h1

end Util

section Model

variable {W : Type*} [Group W]

theorem centralizes_of_cube {X : Subgroup (MulAut W)} (hF : OddFacts X) {E : Subgroup (MulAut W)}
    (hEX : E ≤ X) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEsq : ∀ a ∈ E, a * a = 1)
    {x : MulAut W} (hx : x ∈ X) (hx3 : x ^ 3 = 1) (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E) :
    ∀ e ∈ E, x * e * x⁻¹ = e := by
  intro e he
  have heX : e ∈ X := hEX he
  have he2 : e * e = 1 := hEsq e he
  have hy : e * x⁻¹ * e ∈ X := X.mul_mem (X.mul_mem heX (X.inv_mem hx)) heX
  have hy3 : (e * x⁻¹ * e) ^ 3 = 1 := by
    have hx3' : x⁻¹ * x⁻¹ * x⁻¹ = 1 := by
      have : x * x * x = 1 := by simpa [pow_succ] using hx3
      calc x⁻¹ * x⁻¹ * x⁻¹ = (x * x * x)⁻¹ := by group
        _ = 1 := by rw [this]; group
    calc (e * x⁻¹ * e) ^ 3 = e * x⁻¹ * e * (e * x⁻¹ * e) * (e * x⁻¹ * e) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = e * (x⁻¹ * x⁻¹ * x⁻¹) * e := by
          calc e * x⁻¹ * e * (e * x⁻¹ * e) * (e * x⁻¹ * e)
              = e * x⁻¹ * (e * e) * x⁻¹ * (e * e) * x⁻¹ * e := by group
            _ = e * (x⁻¹ * x⁻¹ * x⁻¹) * e := by rw [he2]; group
      _ = 1 := by rw [hx3']; simpa using he2
  have hcube := hF.cube_mul x hx (e * x⁻¹ * e) hy hx3 hy3
  set e' := x * e * x⁻¹ with he'def
  have he'E : e' ∈ E := hxE e he
  have hprod : x * (e * x⁻¹ * e) = e' * e := by rw [he'def]; group
  rw [hprod] at hcube
  have hsq : (e' * e) * (e' * e) = 1 := by
    calc (e' * e) * (e' * e) = e' * (e * e') * e := by group
      _ = e' * (e' * e) * e := by rw [hEab e he e' he'E]
      _ = (e' * e') * (e * e) := by group
      _ = 1 := by rw [hEsq e' he'E, he2]; group
  have h3 : (e' * e) ^ 3 = e' * e := by
    calc (e' * e) ^ 3 = (e' * e) * ((e' * e) * (e' * e)) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = e' * e := by rw [hsq]; group
  have h4 : e' * e = 1 := by rw [← h3]; exact hcube
  have h5 : e' = e⁻¹ := eq_inv_of_mul_eq_one_left h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_right he2

end Model

section Eight

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem exists_two_involutions_of_card_eight (h : OfourStruct X L₁ L₂ t)
    {P : Subgroup (MulAut W)} (hPX : P ≤ X) (hP8 : Nat.card P = 8) :
    ∃ e₁ ∈ P, ∃ e₂ ∈ P, e₁ ≠ e₂ ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 := by
  obtain ⟨T', hT'⟩ := exists_isSylowTwoOf X
  have hT'8 := h.card_T hT'
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP8]; norm_num)
  have hPsyl : IsSylowTwoOf P X := isSylowTwoOf_of_card_eq hPX hP2 (by
    rw [hP8, ← hT'.card_eq, hT'8])
  obtain ⟨g, hgX, hg⟩ := hPsyl.exists_conj hT'
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT'
  have hs₁T : s₁ ∈ T' := hF.sylow.s₁_mem_S.1
  have hs₂T : s₂ ∈ T' := hF.sylow.s₂_mem_S.1
  have hconj : ∀ s ∈ T', g⁻¹ * s * g ∈ P := by
    intro s hs
    rw [hg] at hs
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hs
    simpa [MulAut.conj_apply, mul_assoc] using hp
  refine ⟨g⁻¹ * s₁ * g, hconj s₁ hs₁T, g⁻¹ * s₂ * g, hconj s₂ hs₂T, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    exact hF.ne (mul_left_cancel (mul_right_cancel he))
  · intro he
    apply hF.sylow.s₁_ne
    have : s₁ = g * 1 * g⁻¹ := by
      calc s₁ = g * (g⁻¹ * s₁ * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [he]
    rw [this]; group
  · intro he
    apply hF.sylow.s₂_ne
    have : s₂ = g * 1 * g⁻¹ := by
      calc s₂ = g * (g⁻¹ * s₂ * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [he]
    rw [this]; group
  · calc g⁻¹ * s₁ * g * (g⁻¹ * s₁ * g) = g⁻¹ * (s₁ * s₁) * g := by group
      _ = 1 := by rw [hF.s₁_sq]; group
  · calc g⁻¹ * s₂ * g * (g⁻¹ * s₂ * g) = g⁻¹ * (s₂ * s₂) * g := by group
      _ = 1 := by rw [hF.s₂_sq]; group

end Eight

end S143

end CFSG.Quasithin
