module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Model

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t₀ : MulAut W}

theorem not_stabilizes_coset (h : OfourStruct X L₁ L₂ t₀) {q : W → ZMod 2}
    (hq : ∀ w, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1)
    (hexp : ∀ w : W, w * w = 1) {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X)
    {R'' : Subgroup (MulAut W)} (hR''T : R'' ≤ T') (hR''card : Nat.card R'' = 4) {v x : W}
    (hv1 : v ≠ 1) (hvfix : ∀ y ∈ T', y v = v) (hx1 : x ≠ 1) (hxv : x ≠ v) (hxq : q x = 0)
    (hvxq : q (v * x) = 0) (hR : ∀ y ∈ R'', y x = x ∨ y x = x * v) :
    ∀ τ ∈ T', τ ∉ R'' → τ x ≠ x ∧ τ x ≠ x * v := by
  intro τ hτT hτR
  obtain ⟨s₁, s₂, τ₀, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hs₁T : s₁ ∈ T' := hF.sylow.s₁_mem_S.1
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hva : v = a₁ * a₂ := by
    rcases hF.fix v hvfix with he | he
    · exact absurd he hv1
    · exact he
  have ha₁ := hF.sylow.a₁_mem
  have ha₂ := hF.sylow.a₂_mem
  have ha₁1 := hF.sylow.a₁_ne
  have ha₂1 := hF.sylow.a₂_ne
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hexp w)
  obtain ⟨x₁, hx₁, x₂, hx₂, hxe⟩ := h.exists_decomp_W x
  have hx₁1 : x₁ ≠ 1 := by
    intro he
    rw [he, one_mul] at hxe
    have : q x = 1 := (hq x).mpr ⟨Or.inr (hxe ▸ hx₂), hx1⟩
    rw [hxq] at this
    exact zero_ne_one this
  have hx₂1 : x₂ ≠ 1 := by
    intro he
    rw [he, mul_one] at hxe
    have : q x = 1 := (hq x).mpr ⟨Or.inl (hxe ▸ hx₁), hx1⟩
    rw [hxq] at this
    exact zero_ne_one this
  have hx₁a : x₁ ≠ a₁ := by
    intro he
    have hvx : v * x = a₂ * x₂ := by
      rw [hva, hxe, he]
      calc a₁ * a₂ * (a₁ * x₂) = (a₁ * a₁) * (a₂ * x₂) := by
            calc a₁ * a₂ * (a₁ * x₂) = a₁ * (a₂ * a₁) * x₂ := by group
              _ = a₁ * (a₁ * a₂) * x₂ := by rw [mul_comm a₂ a₁]
              _ = (a₁ * a₁) * (a₂ * x₂) := by group
        _ = a₂ * x₂ := by rw [hexp a₁, one_mul]
    by_cases hx₂a : a₂ * x₂ = 1
    · apply hxv
      have : x₂ = a₂ := by
        have := mul_eq_one_iff_eq_inv.mp hx₂a
        rw [hinv] at this
        exact this.symm
      rw [hxe, he, this, hva]
    · have : q (v * x) = 1 := (hq _).mpr ⟨Or.inr (by rw [hvx]; exact (commV L₂).mul_mem ha₂ hx₂), by
        rw [hvx]; exact hx₂a⟩
      rw [hvxq] at this
      exact zero_ne_one this
  have hx₂a : x₂ ≠ a₂ := by
    intro he
    have hvx : v * x = a₁ * x₁ := by
      rw [hva, hxe, he]
      calc a₁ * a₂ * (x₁ * a₂) = a₁ * x₁ * (a₂ * a₂) := by
            calc a₁ * a₂ * (x₁ * a₂) = a₁ * (a₂ * x₁) * a₂ := by group
              _ = a₁ * (x₁ * a₂) * a₂ := by rw [mul_comm a₂ x₁]
              _ = a₁ * x₁ * (a₂ * a₂) := by group
        _ = a₁ * x₁ := by rw [hexp a₂, mul_one]
    by_cases hx₁a' : a₁ * x₁ = 1
    · apply hxv
      have : x₁ = a₁ := by
        have := mul_eq_one_iff_eq_inv.mp hx₁a'
        rw [hinv] at this
        exact this.symm
      rw [hxe, he, this, hva]
    · have : q (v * x) = 1 := (hq _).mpr ⟨Or.inl (by rw [hvx]; exact (commV L₁).mul_mem ha₁ hx₁), by
        rw [hvx]; exact hx₁a'⟩
      rw [hvxq] at this
      exact zero_ne_one this
  have hs₁x₂ : s₁ x₂ = x₂ := h.L₁_fix₂ hs₁L hx₂
  have hs₁x : s₁ x = s₁ x₁ * x₂ := by rw [hxe, map_mul, hs₁x₂]
  have hs₁x₁ : s₁ x₁ ∈ commV L₁ := commV_stable L₁ hs₁L hx₁
  have hmove₁ : s₁ x ≠ x := by
    intro he
    rw [hs₁x, hxe] at he
    have := S1417.eq_of_mul_eq_of_inf_eq_bot h.inf hs₁x₁ hx₁ hx₂ hx₂ he
    rcases (hF.sylow.fix₁ x₁ hx₁).mp this.1 with h1 | h1
    · exact hx₁1 h1
    · exact hx₁a h1
  have hmove₂ : s₁ x ≠ x * v := by
    intro he
    rw [hs₁x, hxe, hva] at he
    have e : x₁ * x₂ * (a₁ * a₂) = (x₁ * a₁) * (x₂ * a₂) := by
      calc x₁ * x₂ * (a₁ * a₂) = x₁ * (x₂ * a₁) * a₂ := by group
        _ = x₁ * (a₁ * x₂) * a₂ := by rw [mul_comm x₂ a₁]
        _ = (x₁ * a₁) * (x₂ * a₂) := by group
    rw [e] at he
    have := S1417.eq_of_mul_eq_of_inf_eq_bot h.inf hs₁x₁ ((commV L₁).mul_mem hx₁ ha₁) hx₂
      ((commV L₂).mul_mem hx₂ ha₂) he
    have h3 : x₂ * a₂ = x₂ * 1 := by rw [mul_one]; exact this.2.symm
    exact ha₂1 (mul_left_cancel h3)
  by_contra hcon
  have hτ : τ x = x ∨ τ x = x * v := by
    by_contra h'
    push Not at h'
    exact hcon ⟨h'.1, h'.2⟩
  have hidx : (R''.subgroupOf T').index = 2 := by
    have h1 := Subgroup.relIndex_mul_card R'' T'
    rw [inf_eq_left.mpr hR''T, hR''card, h.card_T hT] at h1
    exact (by omega : R''.relIndex T' = 2)
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have hall : ∀ y ∈ T', y x = x ∨ y x = x * v := by
    intro y hyT
    by_cases hyR : y ∈ R''
    · exact hR y hyR
    ·
      have h1 : y * τ⁻¹ ∈ R'' := by
        have hya : (⟨y, hyT⟩ * a : ↥T') ∈ R''.subgroupOf T' := by
          have := ha ⟨y, hyT⟩
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h1
          · exact absurd (Subgroup.mem_subgroupOf.mp h1) hyR
        have hτa : (⟨τ, hτT⟩ * a : ↥T') ∈ R''.subgroupOf T' := by
          have := ha ⟨τ, hτT⟩
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h1
          · exact absurd (Subgroup.mem_subgroupOf.mp h1) hτR
        have := (R''.subgroupOf T').mul_mem hya ((R''.subgroupOf T').inv_mem hτa)
        have e : (⟨y, hyT⟩ * a * (⟨τ, hτT⟩ * a)⁻¹ : ↥T') = ⟨y * τ⁻¹, T'.mul_mem hyT (T'.inv_mem hτT)⟩ := by
          apply Subtype.ext
          simp [mul_assoc]
        rw [e] at this
        exact this
      have hρT : y * τ⁻¹ ∈ T' := hR''T h1
      have h2 : y x = (y * τ⁻¹) (τ x) := by
        have e : y = (y * τ⁻¹) * τ := by group
        conv_lhs => rw [e]
        rfl
      have hvv : v * v = 1 := hexp v
      have hρv : (y * τ⁻¹) v = v := hvfix _ hρT
      rw [h2]
      rcases hτ with hτ | hτ
      · rw [hτ]
        exact hR _ h1
      · rw [hτ, map_mul, hρv]
        rcases hR _ h1 with h3 | h3
        · right; rw [h3]
        · left
          rw [h3, mul_assoc, hvv, mul_one]
  rcases hall s₁ hs₁T with he | he
  · exact hmove₁ he
  · exact hmove₂ he

end Model

end S143

end CFSG.Quasithin
