module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.S1567W2
public import CFSG.Quasithin.EmptyFaithful.S153E59C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

@[expose] def Case3Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G) (L : Subgroup G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368NoTwo T Mc M E s →
    Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) →
    L ∈ cComp (G0_153 T Mc M E s) → G0_153 T Mc M E s ≤ Subgroup.normalizer (L : Set G) →
    ((G0_153 T Mc M E s : Subgroup G) : Set G) = (L : Set G) * (TE153 T E : Set G) →
    IsC134Case3 (G0_153 T Mc M E s) (TE153 T E) L → False

namespace S1567

section Card

variable {G : Type} [Group G]

theorem natCard_multiplicative_pi (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Fintype F] :
    Nat.card (Multiplicative (Fin k → ι → F)) = Fintype.card F ^ (Fintype.card ι * k) := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp [← pow_mul, mul_comm]

theorem card_eq_card_mul_of_surjective67 {V Z : Subgroup G} (hZV : Z ≤ V) {H : Type*} [Group H]
    (β : ↥V →* H) (hβ : Function.Surjective β) (hker : β.ker = Z.subgroupOf V) :
    Nat.card ↥V = Nat.card ↥Z * Nat.card H := by
  have h := Subgroup.card_ker_mul_card_of_surjective hβ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at h
  exact h.symm

theorem card_of_isSumOfNaturalModulesVia {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {α : ↥A →* ↥Γ} {dual : Bool} {k : ℕ} (h : IsSumOfNaturalModulesVia A V Z α dual k) :
    Nat.card ↥V = Nat.card ↥Z * Fintype.card F ^ (Fintype.card ι * k) := by
  obtain ⟨-, hZV, β, hβ, hker, -⟩ := h
  rw [card_eq_card_mul_of_surjective67 hZV β hβ hker, natCard_multiplicative_pi]

end Card

section Field

variable {G : Type} [Group G] [Finite G]

theorem card_statedSL_eq_of_same_ker {L : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (α₁ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F₁))
    (α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F₂))
    (h₁ : Function.Surjective α₁) (h₂ : Function.Surjective α₂) (hk : α₁.ker = α₂.ker) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F₁) =
      Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F₂) := by
  have e1 := Subgroup.card_ker_mul_card_of_surjective h₁
  have e2 := Subgroup.card_ker_mul_card_of_surjective h₂
  rw [hk] at e1
  have hpos : 0 < Nat.card α₂.ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)

theorem card_field_eq_two {L : Subgroup G}
    (α₀ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (h₀s : Function.Surjective α₀)
    (h₀k : α₀.ker = CFSG.pCore 2 ↥L) {F : Type} [Field F] [Fintype F]
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hs : Function.Surjective α)
    (hk : α.ker = CFSG.pCore 2 ↥L) : Fintype.card F = 2 := by
  have h := card_statedSL_eq_of_same_ker α α₀ hs h₀s (hk.trans h₀k.symm)
  rw [S153E59.card_statedSL_three_two,
    CFSG.SectionRank.OddCover.card_statedSL_three_eq_mul (p := Nat.card F) rfl] at h
  rw [← Nat.card_eq_fintype_card]
  have hp1 : 1 ≤ Nat.card F := Nat.card_pos
  generalize Nat.card F = p at h hp1 ⊢
  rcases Nat.lt_or_ge p 2 with hp | hp
  · have : p = 1 := by omega
    subst this
    simp at h
  · have h5 : p ≤ 5 := by
      by_contra hc
      push Not at hc
      have h1 : 1 ≤ (p - 1) * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by
        apply Nat.mul_ne_zero <;> omega)
      have h2 : 1 ≤ (p - 1) * (p ^ 2 + p + 1) := Nat.one_le_iff_ne_zero.mpr (by
        apply Nat.mul_ne_zero <;> omega)
      have h3 : p ^ 3 ≤ p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1)) := by
        calc p ^ 3 = p ^ 3 * 1 * 1 := by ring
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h2
      have h4 : 6 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hc 3
      omega
    interval_cases p <;> simp_all

end Field

section Cases

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem c134Q_le_pCoreOf {G₀ L : Subgroup G} (hLG : L ≤ G₀) : c134Q G₀ L ≤ pCoreOf 2 G₀ := by
  unfold c134Q
  rw [Subgroup.commutator_le]
  intro x hx l hl
  rw [commutatorElement_def]
  have h1 : l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 G₀ :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₀ (hLG hl)) _).mp
      ((pCoreOf 2 G₀).inv_mem hx)
  have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 G₀).mul_mem hx h1

theorem card_c134Q_of_case1 {G₀ R L : Subgroup G}
    (α₀ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (h₀s : Function.Surjective α₀)
    (h₀k : α₀.ker = CFSG.pCore 2 ↥L) (h : IsC134Case1 G₀ R L) : Nat.card ↥(c134Q G₀ L) = 8 := by
  obtain ⟨-, n, F, _, _, hF, hsec⟩ := h
  obtain ⟨α, hαs, hαk, hvia⟩ :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have h2 := card_field_eq_two α₀ h₀s h₀k α hαs hαk
  have h3 := card_of_isSumOfNaturalModulesVia hvia
  rw [Subgroup.card_bot, h2, Fintype.card_fin] at h3
  rw [h3]
  norm_num

theorem card_c134Q_of_case2 {G₀ R L : Subgroup G}
    (α₀ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (h₀s : Function.Surjective α₀)
    (h₀k : α₀.ker = CFSG.pCore 2 ↥L) (h : IsC134Case2 G₀ R L) : Nat.card ↥(c134Q G₀ L) = 64 := by
  obtain ⟨⟨n, F, _, _, α, hF, ⟨hαs, hαk⟩, hvia⟩, -⟩ := h
  have h2 := card_field_eq_two α₀ h₀s h₀k α hαs hαk
  have h3 := card_of_isSumOfNaturalModulesVia hvia
  rw [Subgroup.card_bot, h2, Fintype.card_fin] at h3
  rw [h3]
  norm_num

omit [Finite G] in
theorem card_c134Q_of_case5 {G₀ R L : Subgroup G} (h : IsC134Case5 G₀ R L) :
    Nat.card ↥(c134Q G₀ L) = 16 := by
  obtain ⟨⟨α, -, hCQ, hvia⟩, -⟩ := h
  have h3 := card_of_isSumOfNaturalModulesVia hvia
  rw [hCQ, ZMod.card, Fintype.card_fin] at h3
  rw [h3]
  norm_num

end Cases

end S1567

end CFSG.Quasithin
