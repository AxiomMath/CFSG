module

public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ6
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ5

public section

namespace CFSG.Quasithin.Ch3E213M.G41.CTwo

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem two_lt_card_of_mem [Finite k] {F : Subfield k} {x y : k} (hx : x ∈ F) (hy : y ∈ F)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) : 2 < Nat.card F := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
  exact ⟨0, ⟨x, hx⟩, ⟨y, hy⟩, fun h => hx0 (congrArg Subtype.val h).symm,
    fun h => hy0 (congrArg Subtype.val h).symm, fun h => hxy (congrArg Subtype.val h)⟩

theorem charP_subfield (F : Subfield k) : CharP F 2 :=
  (F.subtype : F →+* k).charP Subtype.val_injective 2

namespace CentreSystem

variable (S : CentreSystem k)

theorem exists_suzuki_shape [Finite k] {Q : k → k → Prop} (hQP : ∀ {b c}, Q b c → S.P b c)
    (hQ₀ : Q S.b₀ S.c₀) {h₁ h₂ : k} (hh₁ : h₁ ≠ 0) {r : ℕ}
    (hσ : ∀ {b c}, Q b c → Q (h₁ * c ^ 2 ^ r) (h₂ * (b ^ 2 ^ r) ^ 2)) {b₁ c₁ b₂ c₂ : k}
    (hQ₁ : Q b₁ c₁) (hQ₂ : Q b₂ c₂) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₁₂ : b₁ ≠ b₂) :
    ∃ (F₁ : Subfield k) (a : ℕ), 1 ≤ a ∧ Nat.card F₁ = 2 ^ (2 * a + 1) ∧
      ∀ {b c : k}, Q b c → ∃ d ∈ F₁, b = S.b₀ * d ∧ c = S.c₀ * d ^ 2 ^ (a + 1) := by
  have memF1 : ∀ {b c : k}, Q b c → b / S.b₀ ∈ S.F1 := fun h =>
    S.mem_F1.mpr ⟨S.div_mem_F0 (hQP h), (S.chi_chi_of_Q hQP hQ₀ hh₁ hσ h).1,
      (S.chi_chi_of_Q hQP hQ₀ hh₁ hσ h).2⟩
  have h3 : 2 < Nat.card S.F1 :=
    two_lt_card_of_mem (memF1 hQ₁) (memF1 hQ₂) (div_ne_zero hb₁ S.b₀_ne)
      (div_ne_zero hb₂ S.b₀_ne) fun h => hb₁₂ ((div_left_inj' S.b₀_ne).mp h)
  have := charP_subfield S.F1
  obtain ⟨a, ha, hcard, hψ⟩ := exists_eq_pow_of_comp_eq_sq S.psi S.psi_psi h3
  refine ⟨S.F1, a, ha, hcard, fun {b c} h => ⟨b / S.b₀, memF1 h,
    by rw [mul_div_cancel₀ _ S.b₀_ne], ?_⟩⟩
  have e := congrArg Subtype.val (hψ ⟨b / S.b₀, memF1 h⟩)
  rw [coe_psi, SubmonoidClass.coe_pow] at e
  rw [S.eq_chi (hQP h), e]

end CentreSystem

end CFSG.Quasithin.Ch3E213M.G41.CTwo
