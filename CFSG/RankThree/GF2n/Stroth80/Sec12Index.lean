module

public import CFSG.RankThree.GF2n.Stroth80.QuadIso

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {γ : G → K}

theorem card_le_two_mul_of_fixer (M₀ : Tim79.QuadModel QF V K γ)
    (Λ Λ₀ : Subgroup (M₀.E ≃ₗ[K] M₀.E)) (Wp : Submodule K M₀.E) (w' : M₀.E)
    (hdim : Module.finrank K Wp = 2) (hnd : Wp ⊓ M₀.B.orthogonal Wp = ⊥) (hw' : w' ∈ Wp)
    (hQw' : M₀.Qf w' ≠ 0) (hiso : ∀ T ∈ Λ, ∀ e, M₀.Qf (T e) = M₀.Qf e)
    (hfix : ∀ T ∈ Λ, T w' = w') (hst : ∀ T ∈ Λ, ∀ y ∈ Wp, T y ∈ Wp) (hle : Λ₀ ≤ Λ)
    (hΛ₀ : ∀ T ∈ Λ, T ∈ Λ₀ ↔ ∀ y ∈ Wp, T y = y) :
    Nat.card Λ ≤ 2 * Nat.card Λ₀ := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsymm : ∀ x y : M₀.E, M₀.B x y = M₀.B y x := fun x y => by
    rw [Tim79.QuadModel.B_comm, CharTwo.neg_eq]
  have hw'0 : w' ≠ 0 := fun h0 => hQw' (by rw [h0]; exact Tim79.QuadModel.Qf_zero)
  obtain ⟨y₀, hy₀P, hy₀⟩ : ∃ y₀ ∈ Wp, M₀.B w' y₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hmem : w' ∈ Wp ⊓ M₀.B.orthogonal Wp :=
      ⟨hw', LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => by
        show M₀.B n w' = 0
        rw [hsymm, hcon n hn]⟩
    rw [hnd, Submodule.mem_bot] at hmem
    exact hw'0 hmem
  have hy₀' : M₀.B y₀ w' ≠ 0 := by rw [hsymm]; exact hy₀
  have hspan : Wp = Submodule.span K {w', y₀} := by
    have hle' : Submodule.span K {w', y₀} ≤ Wp := by
      rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hw'
      · rw [Set.mem_singleton_iff.mp hx]; exact hy₀P
    have hli : LinearIndependent K ![w', y₀] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst'
      have h1 : M₀.B w' (s • w' + t • y₀) = 0 := by rw [hst']; simp
      simp only [map_add, map_smul, M₀.alt, smul_eq_mul] at h1
      have ht : t = 0 := by
        have : t * M₀.B w' y₀ = 0 := by simpa using h1
        exact (mul_eq_zero.mp this).resolve_right hy₀
      subst ht
      rw [zero_smul, add_zero] at hst'
      exact ⟨(smul_eq_zero.mp hst').resolve_right hw'0, rfl⟩
    have hr : Set.range ![w', y₀] = {w', y₀} := by
      ext x
      simp [Matrix.range_cons, Set.pair_comm]
    have hfin := finrank_span_eq_card hli
    rw [hr] at hfin
    simp only [Fintype.card_fin] at hfin
    exact (Submodule.eq_of_le_of_finrank_eq hle' (by rw [hdim]; exact hfin.symm ▸ rfl)).symm
  have hex : ∀ T ∈ Λ, ∃ a : K, T y₀ = y₀ + a • w' := by
    intro T hT
    have hmem : T y₀ - y₀ ∈ Wp := Wp.sub_mem (hst T hT y₀ hy₀P) hy₀P
    rw [hspan] at hmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hb : M₀.B (T y₀ - y₀) w' = 0 := by
      have h1 := Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hiso T hT) y₀ w'
      rw [show (T : M₀.E →ₗ[K] M₀.E) w' = w' from hfix T hT] at h1
      rw [map_sub, LinearMap.sub_apply]
      have h1' : M₀.B (T y₀) w' = M₀.B y₀ w' := h1
      rw [h1', sub_self]
    rw [← hαβ] at hb
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, M₀.alt,
      smul_eq_mul] at hb
    have hβ : β = 0 := by
      have : β * M₀.B y₀ w' = 0 := by simpa using hb
      exact (mul_eq_zero.mp this).resolve_right hy₀'
    refine ⟨α, ?_⟩
    rw [hβ, zero_smul, add_zero] at hαβ
    rw [hαβ]
    abel
  choose! a ha using hex
  have hmul : ∀ T₁ ∈ Λ, ∀ T₂ ∈ Λ, a (T₁ * T₂) = a T₁ + a T₂ := by
    intro T₁ h₁ T₂ h₂'
    have e1 := ha (T₁ * T₂) (Λ.mul_mem h₁ h₂')
    have e2 : (T₁ * T₂) y₀ = y₀ + (a T₁ + a T₂) • w' := by
      show T₁ (T₂ y₀) = _
      rw [ha T₂ h₂', map_add, map_smul, hfix T₁ h₁, ha T₁ h₁, add_smul]
      abel
    rw [e1] at e2
    have e3 : (a (T₁ * T₂) - (a T₁ + a T₂)) • w' = 0 := by
      rw [sub_smul]
      have := add_left_cancel e2
      rw [this, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp e3).resolve_right hw'0)
  have hone : a 1 = 0 := by
    have := hmul 1 Λ.one_mem 1 Λ.one_mem
    rw [one_mul] at this
    exact left_eq_add.mp this
  let ψ : ↥Λ →* Multiplicative K :=
    { toFun := fun T => Multiplicative.ofAdd (a T.1)
      map_one' := by simp [hone]
      map_mul' := fun T₁ T₂ => by
        simp only [Subgroup.coe_mul]
        rw [hmul T₁.1 T₁.2 T₂.1 T₂.2]
        rfl }
  have hker : ψ.ker = Λ₀.subgroupOf Λ := by
    ext T
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (a T.1) = 1 ↔ _
    rw [ofAdd_eq_one, hΛ₀ T.1 T.2]
    constructor
    · intro h0 y hy
      rw [hspan] at hy
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [map_add, map_smul, map_smul, hfix T.1 T.2, ha T.1 T.2, h0, zero_smul, add_zero]
    · intro hy
      have h1 := ha T.1 T.2
      rw [hy y₀ hy₀P] at h1
      have h3 : a T.1 • w' = 0 := by
        have : y₀ + a T.1 • w' = y₀ + 0 := by rw [← h1, add_zero]
        exact add_left_cancel this
      exact (smul_eq_zero.mp h3).resolve_right hw'0
  have hvals : ∀ T : ↥Λ, a T.1 = 0 ∨ a T.1 = -(M₀.B y₀ w') / M₀.Qf w' := by
    intro T
    have hq := hiso T.1 T.2 y₀
    rw [ha T.1 T.2, M₀.Qf_add, M₀.Qf_smul, map_smul] at hq
    have h3 : a T.1 * (a T.1 * M₀.Qf w' + M₀.B y₀ w') = 0 := by
      have : M₀.Qf y₀ + a T.1 ^ 2 * M₀.Qf w' + a T.1 • M₀.B y₀ w' = M₀.Qf y₀ := hq
      simp only [smul_eq_mul] at this
      linear_combination this
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · right
      field_simp
      linear_combination h
  have hrange : Nat.card ψ.range ≤ 2 := by
    let c : K := -(M₀.B y₀ w') / M₀.Qf w'
    have hinj : Function.Injective (fun y : ψ.range => decide (y.1 = 1)) := by
      intro y₁ y₂ hy
      obtain ⟨T₁, hT₁⟩ := MonoidHom.mem_range.mp y₁.2
      obtain ⟨T₂, hT₂⟩ := MonoidHom.mem_range.mp y₂.2
      have hv1 : y₁.1 = Multiplicative.ofAdd (a T₁.1) := hT₁.symm
      have hv2 : y₂.1 = Multiplicative.ofAdd (a T₂.1) := hT₂.symm
      refine Subtype.ext ?_
      simp only [decide_eq_decide] at hy
      by_cases h1 : y₁.1 = 1
      · rw [h1, ← hy.mp h1]
      · have h2' : y₂.1 ≠ 1 := fun h => h1 (hy.mpr h)
        have e1 : a T₁.1 = c := by
          rcases hvals T₁ with h | h
          · exact absurd (by rw [hv1, h]; rfl) h1
          · exact h
        have e2 : a T₂.1 = c := by
          rcases hvals T₂ with h | h
          · exact absurd (by rw [hv2, h]; rfl) h2'
          · exact h
        rw [hv1, hv2, e1, e2]
    calc Nat.card ψ.range ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have hcard : Nat.card Λ = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hkcard : Nat.card ψ.ker = Nat.card Λ₀ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hcard, hkcard]
  calc Nat.card Λ₀ * Nat.card ψ.range ≤ Nat.card Λ₀ * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card Λ₀ := mul_comm _ _

end CFSG.RankThree.GF2n.Stroth80
