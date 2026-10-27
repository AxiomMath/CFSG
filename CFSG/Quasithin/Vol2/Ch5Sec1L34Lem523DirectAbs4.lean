module

public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs1

public section

namespace CFSG.Quasithin.H13.Abs523

variable {V : Type} [CommGroup V] [Finite V]

theorem mem_join_form {𝒦V : Subgroup (MulAut V)} {vV : MulAut V}
    (hvN : vV ∈ Subgroup.normalizer (𝒦V : Set (MulAut V))) (hvv : vV * vV = 1)
    {x : MulAut V} (hx : x ∈ 𝒦V ⊔ Subgroup.zpowers vV) :
    ∃ k ∈ 𝒦V, x = k ∨ x = k * vV := by
  have hinv : vV⁻¹ = vV := by
    rw [inv_eq_iff_mul_eq_one, hvv]
  have hconj : ∀ k ∈ 𝒦V, vV * k * vV⁻¹ ∈ 𝒦V := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp hvN k).mp hk
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hk | hz
    · exact ⟨x, hk, Or.inl rfl⟩
    · rcases mem_zpowers_of_invol hvv x hz with rfl | rfl
      · exact ⟨1, one_mem _, Or.inl rfl⟩
      · exact ⟨1, one_mem _, Or.inr (one_mul _)⟩
  | one => exact ⟨1, one_mem _, Or.inl rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨k₁, hk₁, h₁⟩ := ihx
    obtain ⟨k₂, hk₂, h₂⟩ := ihy
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact ⟨k₁ * k₂, mul_mem hk₁ hk₂, Or.inl (by rw [h₁, h₂])⟩
    · exact ⟨k₁ * k₂, mul_mem hk₁ hk₂, Or.inr (by rw [h₁, h₂]; group)⟩
    · refine ⟨k₁ * (vV * k₂ * vV⁻¹), mul_mem hk₁ (hconj k₂ hk₂), Or.inr ?_⟩
      rw [h₁, h₂, hinv]
      calc k₁ * vV * k₂ = k₁ * vV * k₂ * (vV * vV) := by rw [hvv, mul_one]
        _ = k₁ * (vV * k₂ * vV) * vV := by group
    · refine ⟨k₁ * (vV * k₂ * vV⁻¹), mul_mem hk₁ (hconj k₂ hk₂), Or.inl ?_⟩
      rw [h₁, h₂, hinv]
      group
  | inv x _ ih =>
    obtain ⟨k, hk, h⟩ := ih
    rcases h with h | h
    · exact ⟨k⁻¹, inv_mem hk, Or.inl (by rw [h])⟩
    · refine ⟨vV * k⁻¹ * vV⁻¹, hconj k⁻¹ (inv_mem hk), Or.inr ?_⟩
      rw [h]
      calc (k * vV)⁻¹ = vV⁻¹ * k⁻¹ := mul_inv_rev _ _
        _ = vV * k⁻¹ := by rw [hinv]
        _ = vV * k⁻¹ * (vV * vV) := by rw [hvv, mul_one]
        _ = vV * k⁻¹ * vV⁻¹ * vV := by rw [hinv]; group

theorem center_bot_of_simple_nonab (G : Type) [Group G] [IsSimpleGroup G]
    (hab : ¬ IsMulCommutative G) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hab

theorem perfect_of_simple_nonab (G : Type) [Group G] [IsSimpleGroup G]
    (hab : ¬ IsMulCommutative G) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) with h | h
  · exfalso
    apply hab
    refine ⟨⟨fun a b => ?_⟩⟩
    have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  · exact h

theorem isQuasisimple_of_simple_nonab (G : Type) [Group G] [IsSimpleGroup G]
    (hab : ¬ IsMulCommutative G) : CFSG.IsQuasisimple G := by
  refine ⟨perfect_of_simple_nonab G hab, ?_, ?_⟩
  · exact ((QuotientGroup.quotientMulEquivOfEq (center_bot_of_simple_nonab G hab)).trans
      QuotientGroup.quotientBot).isSimpleGroup
  · have hnc : ∃ a b : G, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hab ⟨⟨fun a b => h a b⟩⟩
    obtain ⟨a, b, hne⟩ := hnc
    let e : G ⧸ Subgroup.center G ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq (center_bot_of_simple_nonab G hab)).trans
        QuotientGroup.quotientBot
    refine ⟨e.symm a, e.symm b, fun heq => hne ?_⟩
    have := congrArg e heq
    simpa using this

theorem eq_one_of_commutes {𝒦V : Subgroup (MulAut V)} {vV : MulAut V}
    (hvN : vV ∈ Subgroup.normalizer (𝒦V : Set (MulAut V))) (hvv : vV * vV = 1)
    (hV2 : ∀ x : V, x ^ 2 = 1) [IsSimpleGroup ↥𝒦V] (hab : ¬ IsMulCommutative ↥𝒦V)
    (hirrK : ∀ U : Subgroup V, (∀ k ∈ 𝒦V, ∀ u ∈ U, k u ∈ U) → U ≠ ⊥ → U = ⊤)
    {c : MulAut V} (hcM : c ∈ 𝒦V ⊔ Subgroup.zpowers vV)
    (hc : ∀ k ∈ 𝒦V, k * c = c * k) : c = 1 := by
  have hcen := center_bot_of_simple_nonab ↥𝒦V hab
  have hcen1 : ∀ g : MulAut V, g ∈ 𝒦V → (∀ k ∈ 𝒦V, k * g = g * k) → g = 1 := by
    intro g hg hgc
    have hmem : (⟨g, hg⟩ : ↥𝒦V) ∈ Subgroup.center ↥𝒦V := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hgc h.1 h.2
    rw [hcen, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hinv : vV⁻¹ = vV := by rw [inv_eq_iff_mul_eq_one, hvv]
  have hconj : ∀ k ∈ 𝒦V, vV * k * vV⁻¹ ∈ 𝒦V := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp hvN k).mp hk
  have hx2 : ∀ a : V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV2 a)
  obtain ⟨k₀, hk₀, h⟩ := mem_join_form hvN hvv hcM
  rcases h with h | h
  ·
    rw [h] at hc ⊢
    exact hcen1 k₀ hk₀ (fun k hk => hc k hk)
  · rw [h] at hc ⊢
    set s : MulAut V := k₀ * vV with hs
    have hsq : s * s = k₀ * (vV * k₀ * vV⁻¹) := by
      rw [hs, hinv]
      group
    have hsq2 : s * s ∈ 𝒦V := by
      rw [hsq]
      exact mul_mem hk₀ (hconj k₀ hk₀)
    have hcomm2 : ∀ k ∈ 𝒦V, k * (s * s) = (s * s) * k := by
      intro k hk
      have hks : k * s = s * k := hc k hk
      calc k * (s * s) = (k * s) * s := (mul_assoc _ _ _).symm
        _ = (s * k) * s := by rw [hks]
        _ = s * (k * s) := by rw [mul_assoc]
        _ = s * (s * k) := by rw [hks]
        _ = (s * s) * k := (mul_assoc _ _ _).symm
    have hsq1 : s * s = 1 := hcen1 (s * s) hsq2 hcomm2
    let S : Subgroup V :=
      { carrier := {x | s x = x}
        mul_mem' := fun {a b} ha hb => by
          show s (a * b) = a * b
          rw [map_mul]
          have ha' : s a = a := ha
          have hb' : s b = b := hb
          rw [ha', hb']
        one_mem' := by
          show s 1 = 1
          exact map_one s
        inv_mem' := fun {a} ha => by
          show s a⁻¹ = a⁻¹
          have ha' : s a = a := ha
          rw [map_inv, ha'] }
    have hSinv : ∀ k ∈ 𝒦V, ∀ x ∈ S, k x ∈ S := by
      intro k hk x hx
      have hx' : s x = x := hx
      show s (k x) = k x
      have hks : k * s = s * k := hc k hk
      calc s (k x) = (s * k) x := rfl
        _ = (k * s) x := by rw [hks]
        _ = k x := by rw [MulAut.mul_apply, hx']
    have hsS : ∀ x : V, s x = x := by
      by_cases hS : S = ⊥
      · intro x
        have hss' : s (s x) = x := by
          have := congrArg (fun F : MulAut V => F x) hsq1
          simpa [MulAut.mul_apply] using this
        have hy : s x * x⁻¹ ∈ S := by
          show s (s x * x⁻¹) = s x * x⁻¹
          rw [map_mul, map_inv, hss', hx2 (s x), hx2 x]
          exact mul_comm _ _
        rw [hS, Subgroup.mem_bot, mul_inv_eq_one] at hy
        exact hy
      · intro x
        have hST : S = ⊤ := hirrK S hSinv hS
        have hx : x ∈ S := by
          rw [hST]
          exact Subgroup.mem_top x
        exact hx
    exact MulEquiv.ext fun x => by
      rw [MulAut.one_apply]
      exact hsS x

end CFSG.Quasithin.H13.Abs523
