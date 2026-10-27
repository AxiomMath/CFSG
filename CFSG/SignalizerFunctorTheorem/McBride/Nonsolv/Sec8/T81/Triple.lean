module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Refine
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux2
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Lines

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

section Generic

variable {G : Type*} [Group G]

@[expose] def refineFam (Ω Ω' : Set (Subgroup G)) : Set (Subgroup G) :=
  {Z | ∃ X ∈ Ω, ∃ Y ∈ Ω', Z = X ⊓ Y}

@[expose] def tripleFam (Ω₁ Ω₂ Ω₃ : Set (Subgroup G)) : Set (Subgroup G) :=
  refineFam (refineFam Ω₁ Ω₂) Ω₃

theorem tripleFam_le {Ω₁ Ω₂ Ω₃ : Set (Subgroup G)} {Z : Subgroup G}
    (hZ : Z ∈ tripleFam Ω₁ Ω₂ Ω₃) :
    (∃ X ∈ Ω₁, Z ≤ X) ∧ (∃ X ∈ Ω₂, Z ≤ X) ∧ (∃ X ∈ Ω₃, Z ≤ X) := by
  obtain ⟨W, ⟨X₁, hX₁, X₂, hX₂, rfl⟩, X₃, hX₃, rfl⟩ := hZ
  exact ⟨⟨X₁, hX₁, inf_le_left.trans inf_le_left⟩, ⟨X₂, hX₂, inf_le_left.trans inf_le_right⟩,
    ⟨X₃, hX₃, inf_le_right⟩⟩

variable [Finite G]

theorem isDirectProduct_tripleFam {M : Subgroup G} {Ω₁ Ω₂ Ω₃ : Set (Subgroup G)}
    (hM : ⁅M, M⁆ = M) (h₁ : IsDirectProduct Ω₁ M) (h₂ : IsDirectProduct Ω₂ M)
    (h₃ : IsDirectProduct Ω₃ M) : IsDirectProduct (tripleFam Ω₁ Ω₂ Ω₃) M :=
  IsDirectProduct.refine_of_perfect (IsDirectProduct.refine_of_perfect h₁ h₂ hM) h₃ hM

omit [Finite G] in
theorem inv_mul_mem_of_map_conj_eq {A H N : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsRegFam A H Ω N) {X : Subgroup G} (hX : X ∈ Ω) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (h : X.map (MulAut.conj a).toMonoidHom = X.map (MulAut.conj b).toMonoidHom) : b⁻¹ * a ∈ N := by
  rw [← hΩ.stabilizer X hX]
  refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hb) ha, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := Near.Thm210.map_conj_map_conj X a b⁻¹
  rw [h, Near.Thm210.map_conj_map_conj, inv_mul_cancel, Near.Thm210.map_conj_one] at h1
  exact h1.symm

theorem exists_common_conj {A M B₁ B₂ B₃ : Subgroup G} {Ω₁ Ω₂ Ω₃ : Set (Subgroup G)}
    (h₁ : IsRegFam A M Ω₁ B₁) (h₂ : IsRegFam A M Ω₂ B₂) (h₃ : IsRegFam A M Ω₃ B₃)
    (hB : B₁ ⊓ B₂ ⊓ B₃ = ⊥) (hcard : Nat.card B₁ * Nat.card B₂ * Nat.card B₃ = Nat.card A ^ 2)
    {X₁ X₂ X₃ : Subgroup G} (hX₁ : X₁ ∈ Ω₁) (hX₂ : X₂ ∈ Ω₂) (hX₃ : X₃ ∈ Ω₃)
    {Y₁ Y₂ Y₃ : Subgroup G} (hY₁ : Y₁ ∈ Ω₁) (hY₂ : Y₂ ∈ Ω₂) (hY₃ : Y₃ ∈ Ω₃) :
    ∃ a ∈ A, Y₁ = X₁.map (MulAut.conj a).toMonoidHom ∧ Y₂ = X₂.map (MulAut.conj a).toMonoidHom ∧
      Y₃ = X₃.map (MulAut.conj a).toMonoidHom := by
  let Φ : ↥A → ↥Ω₁ × ↥Ω₂ × ↥Ω₃ := fun a =>
    (⟨X₁.map (MulAut.conj (a : G)).toMonoidHom, h₁.map_conj_mem a a.2 X₁ hX₁⟩,
     ⟨X₂.map (MulAut.conj (a : G)).toMonoidHom, h₂.map_conj_mem a a.2 X₂ hX₂⟩,
     ⟨X₃.map (MulAut.conj (a : G)).toMonoidHom, h₃.map_conj_mem a a.2 X₃ hX₃⟩)
  have hinj : Function.Injective Φ := by
    intro a b hab
    simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨e₁, e₂, e₃⟩ := hab
    have hmem : (b : G)⁻¹ * a ∈ B₁ ⊓ B₂ ⊓ B₃ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨inv_mul_mem_of_map_conj_eq h₁ hX₁ a.2 b.2 e₁,
          inv_mul_mem_of_map_conj_eq h₂ hX₂ a.2 b.2 e₂⟩,
        inv_mul_mem_of_map_conj_eq h₃ hX₃ a.2 b.2 e₃⟩
    rw [hB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem.symm
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hn : Nat.card Ω₁ * Nat.card Ω₂ * Nat.card Ω₃ = Nat.card A := by
    have h : (Nat.card Ω₁ * Nat.card Ω₂ * Nat.card Ω₃) * Nat.card A ^ 2 =
        Nat.card A * Nat.card A ^ 2 := by
      calc (Nat.card Ω₁ * Nat.card Ω₂ * Nat.card Ω₃) * Nat.card A ^ 2
          = (Nat.card Ω₁ * Nat.card Ω₂ * Nat.card Ω₃) *
              (Nat.card B₁ * Nat.card B₂ * Nat.card B₃) := by rw [hcard]
        _ = (Nat.card Ω₁ * Nat.card B₁) * (Nat.card Ω₂ * Nat.card B₂) *
              (Nat.card Ω₃ * Nat.card B₃) := by ring
        _ = Nat.card A * Nat.card A * Nat.card A := by
          rw [h₁.card_mul_card, h₂.card_mul_card, h₃.card_mul_card]
        _ = Nat.card A * Nat.card A ^ 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hApos 2) h
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_prod, ← mul_assoc, hn])
  obtain ⟨c, hc⟩ := hbij.2 (⟨Y₁, hY₁⟩, ⟨Y₂, hY₂⟩, ⟨Y₃, hY₃⟩)
  simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at hc
  obtain ⟨e₁, e₂, e₃⟩ := hc
  exact ⟨c, c.2, e₁.symm, e₂.symm, e₃.symm⟩

theorem isRegFam_tripleFam {A M B₁ B₂ B₃ : Subgroup G} {Ω₁ Ω₂ Ω₃ : Set (Subgroup G)}
    (hM : ⁅M, M⁆ = M) (hM1 : M ≠ ⊥) (h₁ : IsRegFam A M Ω₁ B₁) (h₂ : IsRegFam A M Ω₂ B₂)
    (h₃ : IsRegFam A M Ω₃ B₃) (hB : B₁ ⊓ B₂ ⊓ B₃ = ⊥)
    (hcard : Nat.card B₁ * Nat.card B₂ * Nat.card B₃ = Nat.card A ^ 2) :
    IsRegFam A M (tripleFam Ω₁ Ω₂ Ω₃) ⊥ := by
  have hdp : IsDirectProduct (tripleFam Ω₁ Ω₂ Ω₃) M :=
    isDirectProduct_tripleFam hM h₁.isDirectProduct h₂.isDirectProduct h₃.isDirectProduct
  have hconj : ∀ (a : G) (X₁ X₂ X₃ : Subgroup G),
      (X₁ ⊓ X₂ ⊓ X₃).map (MulAut.conj a).toMonoidHom = X₁.map (MulAut.conj a).toMonoidHom ⊓
        X₂.map (MulAut.conj a).toMonoidHom ⊓ X₃.map (MulAut.conj a).toMonoidHom := by
    intro a X₁ X₂ X₃
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective]
  have htrans : ∀ L ∈ tripleFam Ω₁ Ω₂ Ω₃, ∀ L' ∈ tripleFam Ω₁ Ω₂ Ω₃,
      ∃ a ∈ A, L' = L.map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨_, ⟨X₁, hX₁, X₂, hX₂, rfl⟩, X₃, hX₃, rfl⟩ _
      ⟨_, ⟨Y₁, hY₁, Y₂, hY₂, rfl⟩, Y₃, hY₃, rfl⟩
    obtain ⟨a, ha, e₁, e₂, e₃⟩ := exists_common_conj h₁ h₂ h₃ hB hcard hX₁ hX₂ hX₃ hY₁ hY₂ hY₃
    exact ⟨a, ha, by rw [hconj, ← e₁, ← e₂, ← e₃]⟩
  have hmem : ∀ a ∈ A, ∀ L ∈ tripleFam Ω₁ Ω₂ Ω₃,
      L.map (MulAut.conj a).toMonoidHom ∈ tripleFam Ω₁ Ω₂ Ω₃ := by
    rintro a ha _ ⟨_, ⟨X₁, hX₁, X₂, hX₂, rfl⟩, X₃, hX₃, rfl⟩
    exact ⟨_, ⟨_, h₁.map_conj_mem a ha X₁ hX₁, _, h₂.map_conj_mem a ha X₂ hX₂, rfl⟩, _,
      h₃.map_conj_mem a ha X₃ hX₃, hconj a X₁ X₂ X₃⟩
  have hne : ∀ L ∈ tripleFam Ω₁ Ω₂ Ω₃, L ≠ ⊥ := by
    intro L hL hbot
    apply hM1
    rw [← hdp.sSup_eq]
    refine le_bot_iff.mp (sSup_le fun L' hL' => ?_)
    obtain ⟨a, -, rfl⟩ := htrans L hL L' hL'
    rw [hbot, Subgroup.map_bot]
  have hstab : ∀ L ∈ tripleFam Ω₁ Ω₂ Ω₃, A ⊓ Subgroup.normalizer (L : Set G) = ⊥ := by
    intro L hL
    refine eq_bot_iff.mpr fun a ha => ?_
    obtain ⟨haA, haL⟩ := Subgroup.mem_inf.mp ha
    have hLa : L.map (MulAut.conj a).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haL
    have key : ∀ {Ω : Set (Subgroup G)} {B : Subgroup G} (hΩ : IsRegFam A M Ω B)
        {X : Subgroup G}, X ∈ Ω → L ≤ X → a ∈ B := by
      intro Ω B hΩ X hX hLX
      by_contra haB
      have hXa := hΩ.map_conj_mem a haA X hX
      have hdisj : Disjoint X (X.map (MulAut.conj a).toMonoidHom) :=
        hΩ.isDirectProduct.indep.pairwiseDisjoint hX hXa (hΩ.map_conj_ne haA haB hX).symm
      have hLX' : L ≤ X.map (MulAut.conj a).toMonoidHom := hLa ▸ Subgroup.map_mono hLX
      exact hne L hL (disjoint_self.mp (hdisj.mono hLX hLX'))
    obtain ⟨⟨X₁, hX₁, hLX₁⟩, ⟨X₂, hX₂, hLX₂⟩, ⟨X₃, hX₃, hLX₃⟩⟩ := tripleFam_le hL
    have hmem' : a ∈ B₁ ⊓ B₂ ⊓ B₃ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨key h₁ hX₁ hLX₁, key h₂ hX₂ hLX₂⟩,
        key h₃ hX₃ hLX₃⟩
    rwa [hB] at hmem'
  obtain ⟨X₁, hX₁⟩ := h₁.nonempty
  obtain ⟨X₂, hX₂⟩ := h₂.nonempty
  obtain ⟨X₃, hX₃⟩ := h₃.nonempty
  exact ⟨hdp, ⟨_, _, ⟨X₁, hX₁, X₂, hX₂, rfl⟩, X₃, hX₃, rfl⟩, hne, hmem, htrans, hstab⟩

end Generic

section Setting

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

structure ThreePlanes (p : ℕ) (A B₁ B₂ B₃ : Subgroup G) (c₁₂ c₁₃ : G) : Prop where
  mem₁ : B₁ ∈ signalizerFunctorEk p 2 A
  mem₂ : B₂ ∈ signalizerFunctorEk p 2 A
  mem₃ : B₃ ∈ signalizerFunctorEk p 2 A
  inf_eq_bot : B₁ ⊓ B₂ ⊓ B₃ = ⊥
  c₁₂_ne : c₁₂ ≠ 1
  zpowers_c₁₂ : Subgroup.zpowers c₁₂ = B₁ ⊓ B₂
  c₁₃_ne : c₁₃ ≠ 1
  zpowers_c₁₃ : Subgroup.zpowers c₁₃ = B₁ ⊓ B₃

theorem exists_threePlanes (h : Counterexample p A θ) :
    ∃ (B₁ B₂ B₃ : Subgroup G) (c₁₂ c₁₃ : G), ThreePlanes p A B₁ B₂ B₃ c₁₂ c₁₃ := by
  have hex : ∀ B : Subgroup G, Nat.card B ≤ p ^ 2 → ∃ a ∈ A, a ∉ B := by
    intro B hB
    by_contra! hcon
    have hAB : A ≤ B := hcon
    have h1 := Subgroup.card_le_of_le hAB
    rw [h.card] at h1
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  obtain ⟨a₁, ha₁, ha₁1⟩ := h.exists_ne_one
  have hE₁ := h.zpowers_mem_E1 ha₁ ha₁1
  obtain ⟨a₂, ha₂, ha₂E⟩ := hex (Subgroup.zpowers a₁) (by
    rw [h.card_zpowers ha₁ ha₁1]
    exact Nat.le_self_pow (by norm_num) p)
  have ha₂1 : a₂ ≠ 1 := fun h1 => ha₂E (h1 ▸ one_mem _)
  have hE₂ := h.zpowers_mem_E1 ha₂ ha₂1
  have hE₁₂ : Subgroup.zpowers a₁ ≠ Subgroup.zpowers a₂ := fun heq =>
    ha₂E (heq ▸ Subgroup.mem_zpowers a₂)
  have hB₃ := h.sup_mem_E2_of_ne hE₁ hE₂ hE₁₂
  obtain ⟨a₃, ha₃, ha₃B⟩ := hex _ hB₃.2.le
  have ha₃1 : a₃ ≠ 1 := fun h1 => ha₃B (h1 ▸ one_mem _)
  have hE₃ := h.zpowers_mem_E1 ha₃ ha₃1
  have hE₁₃ : Subgroup.zpowers a₁ ≠ Subgroup.zpowers a₃ := fun heq =>
    ha₃B (Subgroup.mem_sup_left (heq ▸ Subgroup.mem_zpowers a₃))
  have hE₂₃ : Subgroup.zpowers a₂ ≠ Subgroup.zpowers a₃ := fun heq =>
    ha₃B (Subgroup.mem_sup_right (heq ▸ Subgroup.mem_zpowers a₃))
  have hB₂ := h.sup_mem_E2_of_ne hE₁ hE₃ hE₁₃
  have hB₁ := h.sup_mem_E2_of_ne hE₂ hE₃ hE₂₃
  set E₁ := Subgroup.zpowers a₁
  set E₂ := Subgroup.zpowers a₂
  set E₃ := Subgroup.zpowers a₃
  have ha₁B₃ : a₁ ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_left (Subgroup.mem_zpowers a₁)
  have ha₂B₃ : a₂ ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_right (Subgroup.mem_zpowers a₂)
  have ha₁B₂ : a₁ ∈ E₁ ⊔ E₃ := Subgroup.mem_sup_left (Subgroup.mem_zpowers a₁)
  have ha₃B₂ : a₃ ∈ E₁ ⊔ E₃ := Subgroup.mem_sup_right (Subgroup.mem_zpowers a₃)
  have ha₂B₁ : a₂ ∈ E₂ ⊔ E₃ := Subgroup.mem_sup_left (Subgroup.mem_zpowers a₂)
  have ha₃B₁ : a₃ ∈ E₂ ⊔ E₃ := Subgroup.mem_sup_right (Subgroup.mem_zpowers a₃)
  have ha₁B₁ : a₁ ∉ E₂ ⊔ E₃ := by
    intro ha₁B
    have hle : E₁ ⊔ E₂ ≤ E₂ ⊔ E₃ :=
      sup_le (Subgroup.zpowers_le.mpr ha₁B) le_sup_left
    have heq : E₁ ⊔ E₂ = E₂ ⊔ E₃ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hB₃.2, hB₁.2])
    exact ha₃B (heq ▸ ha₃B₁)
  have hB₁₂ : E₂ ⊔ E₃ ≠ E₁ ⊔ E₃ := fun heq => ha₁B₁ (heq ▸ ha₁B₂)
  have hB₁₃ : E₂ ⊔ E₃ ≠ E₁ ⊔ E₂ := fun heq => ha₁B₁ (heq ▸ ha₁B₃)
  have hl₁₂ := h.inf_mem_E1_of_ne_E2 hB₁ hB₂ hB₁₂
  have hl₁₃ := h.inf_mem_E1_of_ne_E2 hB₁ hB₃ hB₁₃
  have hz₁₂ : (E₂ ⊔ E₃) ⊓ (E₁ ⊔ E₃) = E₃ :=
    h.line_eq_zpowers hl₁₂ (Subgroup.mem_inf.mpr ⟨ha₃B₁, ha₃B₂⟩) ha₃1
  have hz₁₃ : (E₂ ⊔ E₃) ⊓ (E₁ ⊔ E₂) = E₂ :=
    h.line_eq_zpowers hl₁₃ (Subgroup.mem_inf.mpr ⟨ha₂B₁, ha₂B₃⟩) ha₂1
  refine ⟨E₂ ⊔ E₃, E₁ ⊔ E₃, E₁ ⊔ E₂, a₃, a₂, hB₁, hB₂, hB₃, ?_, ha₃1, hz₁₂.symm, ha₂1,
    hz₁₃.symm⟩
  rw [hz₁₂, eq_bot_iff]
  intro x hx
  obtain ⟨hxE, hxB⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxeq : E₃ = Subgroup.zpowers x := h.line_eq_zpowers hE₃ hxE hx1
  have hle : Subgroup.zpowers x ≤ E₁ ⊔ E₂ := Subgroup.zpowers_le.mpr hxB
  exact ha₃B (hle (hxeq ▸ Subgroup.mem_zpowers a₃))

end Setting

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
