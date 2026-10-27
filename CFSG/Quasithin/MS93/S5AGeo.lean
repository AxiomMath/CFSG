module

public import CFSG.Quasithin.MS93.MSPOff

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

theorem finrank_le_four (W : Submodule F (V4 F)) : Module.finrank F W ≤ 4 := by
  have := Submodule.finrank_le W
  simpa using this

theorem finrank_pos_of_ne_bot {W : Submodule F (V4 F)} (hW : W ≠ ⊥) :
    0 < Module.finrank F W :=
  Nat.pos_of_ne_zero fun h => hW (Submodule.finrank_eq_zero.1 h)

theorem IsLine.eq_of_le {l l' : Submodule F (V4 F)} (hl : IsLine l) (hl' : IsLine l')
    (h : l ≤ l') : l = l' :=
  Submodule.eq_of_le_of_finrank_eq h (by rw [hl.1, hl'.1])

theorem isPoint_inf {l₁ l₂ : Submodule F (V4 F)} (h₁ : IsLine l₁) (h₂ : IsLine l₂)
    (hne : l₁ ≠ l₂) (h0 : l₁ ⊓ l₂ ≠ ⊥) : IsPoint (l₁ ⊓ l₂) := by
  have hpos := finrank_pos_of_ne_bot h0
  have hle : Module.finrank F ↥(l₁ ⊓ l₂) ≤ 2 := by
    have := Submodule.finrank_mono (inf_le_left : l₁ ⊓ l₂ ≤ l₁)
    rw [h₁.1] at this
    exact this
  have hne2 : Module.finrank F ↥(l₁ ⊓ l₂) ≠ 2 := by
    intro h2
    have e1 : l₁ ⊓ l₂ = l₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, h₁.1])
    have e2 : l₁ ⊓ l₂ = l₂ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h2, h₂.1])
    exact hne (e1.symm.trans e2)
  show Module.finrank F ↥(l₁ ⊓ l₂) = 1
  omega

variable [Finite F] [CharP F 2]

theorem fixSp_ne_bot {R : Subgroup (Sp4 F)} (hR : IsPGroup 2 R) : fixSp R ≠ ⊥ := by
  obtain ⟨w, -, hw0, hw⟩ := exists_fixed_ne_zero hR (W := ⊤) top_ne_bot
    fun _ _ _ _ => Submodule.mem_top
  intro h
  have : w ∈ fixSp R := mem_fixSp.2 hw
  rw [h, Submodule.mem_bot] at this
  exact hw0 this

theorem inf_fixSp_ne_bot {R A B : Subgroup (Sp4 F)} (hR : IsPGroup 2 R) (hA : A ≤ R)
    (hB : B ≤ R) : fixSp A ⊓ fixSp B ≠ ⊥ := by
  intro h
  apply fixSp_ne_bot hR
  rw [eq_bot_iff, ← h]
  exact le_inf (fixSp_antitone hA) (fixSp_antitone hB)

omit [CharP F 2] in
theorem fixSp_eq_of_le_qLine {l : Submodule F (V4 F)} (hl : IsLine l) {E : Subgroup (Sp4 F)}
    (hE : E ≤ qLine l) (hcard : Nat.card F < Nat.card E) : fixSp E = l := by
  have hlE : l ≤ fixSp E := (fixSp_qLine hl).symm.le.trans (fixSp_antitone hE)
  have h2 : 2 ≤ Module.finrank F (fixSp E) := by
    have := Submodule.finrank_mono hlE
    rw [hl.1] at this
    exact this
  have h4 := finrank_le_four (fixSp E)
  have hne4 : Module.finrank F (fixSp E) ≠ 4 := by
    intro h'
    have htop : fixSp E = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h']; simp)
    have hE1 := fixSp_eq_top_iff.1 htop
    rw [hE1, Subgroup.card_bot] at hcard
    have : 0 < Nat.card F := Nat.card_pos
    omega
  have hne3 : Module.finrank F (fixSp E) ≠ 3 := by
    intro h3
    obtain ⟨p, hp, -, hEp⟩ := exists_point_of_finrank_fixSp_three h3
    have := Subgroup.card_le_of_le hEp
    rw [card_xPoint hp] at this
    omega
  have h2' : Module.finrank F (fixSp E) = 2 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq hlE (by rw [h2', hl.1])).symm

omit [Finite F] [CharP F 2] in
theorem qLine_comm {l : Submodule F (V4 F)} (hl : IsLine l) {x y : Sp4 F} (hx : x ∈ qLine l)
    (hy : y ∈ qLine l) : x * y = y * x := by
  obtain ⟨g, rfl⟩ := exists_map_ln₀_eq hl
  rw [qLine_map_eq, mem_map_conj] at hx hy
  have h := Q₁_comm hx hy
  have h' : g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by
    rw [h]
  simpa [mul_assoc] using h'

omit [Finite F] [CharP F 2] in
theorem sub_mem_of_mem_xPoint {p : Submodule F (V4 F)} (hp : IsPoint p) {g : Sp4 F}
    (hg : g ∈ xPoint p) (v : V4 F) : mat g *ᵥ v - v ∈ p := by
  have := sub_mem_commSp hg v
  rwa [commSp_xPoint hp] at this

omit [Finite F] [CharP F 2] in
theorem xPoint_le_stab_of_le {p W : Submodule F (V4 F)} (hp : IsPoint p) (hpW : p ≤ W) :
    xPoint p ≤ stab W := by
  intro g hg
  refine mem_stab_of_le fun v hv => ?_
  have h := sub_mem_of_mem_xPoint hp hg v
  have : mat g *ᵥ v = (mat g *ᵥ v - v) + v := by abel
  rw [this]
  exact W.add_mem (hpW h) hv

theorem le_perp_of_xPoint_le {p₁ p₂ : Submodule F (V4 F)} (hp₁ : IsPoint p₁) (hp₂ : IsPoint p₂)
    (hne : p₁ ≠ p₂) {R : Subgroup (Sp4 F)} (hR : IsPGroup 2 R) (h₁ : xPoint p₁ ≤ R)
    (h₂ : xPoint p₂ ≤ R) : p₂ ≤ perp p₁ := by
  by_contra hperp
  set R' := xPoint p₁ ⊔ xPoint p₂ with hR'
  have hR'2 : IsPGroup 2 R' := hR.to_le (sup_le h₁ h₂)
  set P := p₁ ⊔ p₂ with hP
  have hinv : R' ≤ stab P :=
    sup_le (xPoint_le_stab_of_le hp₁ le_sup_left) (xPoint_le_stab_of_le hp₂ le_sup_right)
  have hP0 : P ≠ ⊥ := fun h0 => by
    have := finrank_pos_of_ne_bot (show p₁ ≠ ⊥ from fun h => by
      have := hp₁; unfold IsPoint at this; rw [h, finrank_bot] at this; omega)
    have hle : p₁ ≤ ⊥ := h0 ▸ (le_sup_left : p₁ ≤ P)
    rw [le_bot_iff] at hle
    have := hp₁; unfold IsPoint at this; rw [hle, finrank_bot] at this; omega
  obtain ⟨w, hwP, hw0, hwfix⟩ := exists_fixed_ne_zero hR'2 hP0
    fun r hr v hv => mulVec_mem_of_mem_stab (hinv hr) hv
  have hw₁ : w ∈ perp p₁ := by
    have : w ∈ fixSp (xPoint p₁) := mem_fixSp.2 fun r hr =>
      hwfix r ((le_sup_left : xPoint p₁ ≤ R') hr)
    rwa [fixSp_xPoint hp₁] at this
  have hw₂ : w ∈ perp p₂ := by
    have : w ∈ fixSp (xPoint p₂) := mem_fixSp.2 fun r hr =>
      hwfix r ((le_sup_right : xPoint p₂ ≤ R') hr)
    rwa [fixSp_xPoint hp₂] at this
  obtain ⟨x₁, hx₁0, rfl⟩ := exists_eq_span_of_isPoint hp₁
  obtain ⟨x₂, hx₂0, rfl⟩ := exists_eq_span_of_isPoint hp₂
  have h12 : form F x₁ x₂ ≠ 0 := by
    intro h
    apply hperp
    rw [Submodule.span_singleton_le_iff_mem, mem_perp_span]
    exact h
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hwP
  obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.1 hy₁
  obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
  rw [mem_perp_span] at hw₁ hw₂
  simp only [map_add, map_smul, form_self, smul_eq_mul, mul_zero, zero_add, add_zero] at hw₁ hw₂
  have hc₂ : c₂ = 0 := by
    rcases mul_eq_zero.1 hw₁ with h | h
    · exact h
    · exact absurd h h12
  have h21 : form F x₂ x₁ ≠ 0 := by rw [form_swap]; exact neg_ne_zero.2 h12
  have hc₁ : c₁ = 0 := by
    rcases mul_eq_zero.1 hw₂ with h | h
    · exact h
    · exact absurd h h21
  apply hw0
  rw [hc₁, hc₂, zero_smul, zero_smul, add_zero]

omit [Finite F] [CharP F 2] in
theorem isLine_sup {p₁ p₂ : Submodule F (V4 F)} (hp₁ : IsPoint p₁) (hp₂ : IsPoint p₂)
    (hne : p₁ ≠ p₂) (hperp : p₂ ≤ perp p₁) : IsLine (p₁ ⊔ p₂) := by
  obtain ⟨x₁, hx₁0, rfl⟩ := exists_eq_span_of_isPoint hp₁
  obtain ⟨x₂, hx₂0, rfl⟩ := exists_eq_span_of_isPoint hp₂
  have hx₂ : x₂ ∉ F ∙ x₁ := by
    intro hx
    apply hne
    have hle : F ∙ x₂ ≤ F ∙ x₁ := (Submodule.span_singleton_le_iff_mem _ _).2 hx
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hx₂0,
      finrank_span_singleton hx₁0])).symm
  have hspan : (F ∙ x₁) ⊔ (F ∙ x₂) = Submodule.span F {x₁, x₂} := by
    rw [Submodule.span_insert]
  rw [hspan]
  refine ⟨finrank_span_pair hx₁0 hx₂, form_span_pair ?_⟩
  have := hperp (Submodule.mem_span_singleton_self x₂)
  exact mem_perp_span.1 this

omit [Finite F] [CharP F 2] in
theorem xPoint_inf_xPoint {p₁ p₂ : Submodule F (V4 F)} (hp₁ : IsPoint p₁) (hp₂ : IsPoint p₂)
    (hne : p₁ ≠ p₂) : xPoint p₁ ⊓ xPoint p₂ = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h : perp p₁ ⊔ perp p₂ = ⊤ := by
    have hne' : perp p₁ ≠ perp p₂ := fun h => hne (by rw [← perp_perp p₁, h, perp_perp])
    have h3₁ : Module.finrank F (perp p₁) = 3 := by
      have := finrank_perp p₁; unfold IsPoint at hp₁; omega
    have h3₂ : Module.finrank F (perp p₂) = 3 := by
      have := finrank_perp p₂; unfold IsPoint at hp₂; omega
    by_contra hlt
    have hle4 : Module.finrank F ↥(perp p₁ ⊔ perp p₂) < 4 := by
      have := Submodule.finrank_lt hlt
      simpa using this
    have e1 : perp p₁ = perp p₁ ⊔ perp p₂ :=
      Submodule.eq_of_le_of_finrank_eq le_sup_left (by
        have := Submodule.finrank_mono (le_sup_left : perp p₁ ≤ perp p₁ ⊔ perp p₂)
        omega)
    have e2 : perp p₂ = perp p₁ ⊔ perp p₂ :=
      Submodule.eq_of_le_of_finrank_eq le_sup_right (by
        have := Submodule.finrank_mono (le_sup_right : perp p₂ ≤ perp p₁ ⊔ perp p₂)
        omega)
    exact hne' (e1.trans e2.symm)
  have hfix : fixSp (Subgroup.zpowers g) = ⊤ := by
    rw [eq_top_iff, ← h]
    refine sup_le ?_ ?_
    · intro v hv
      rw [mem_fixSp]
      intro r hr
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
      exact (mem_fixer.1 ((xPoint p₁).zpow_mem hg.1 n) v hv)
    · intro v hv
      rw [mem_fixSp]
      intro r hr
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
      exact (mem_fixer.1 ((xPoint p₂).zpow_mem hg.2 n) v hv)
  have := fixSp_eq_top_iff.1 hfix
  rw [Subgroup.zpowers_eq_bot] at this
  exact this

omit [CharP F 2] in
theorem card_xPoint_sup {p₁ p₂ : Submodule F (V4 F)} (hp₁ : IsPoint p₁) (hp₂ : IsPoint p₂)
    (hne : p₁ ≠ p₂) (hperp : p₂ ≤ perp p₁) :
    Nat.card F ^ 2 ≤ Nat.card ↥(xPoint p₁ ⊔ xPoint p₂) := by
  have hl := isLine_sup hp₁ hp₂ hne hperp
  have hA : xPoint p₁ ≤ qLine (p₁ ⊔ p₂) := xPoint_le_qLine hl le_sup_left
  have hB : xPoint p₂ ≤ qLine (p₁ ⊔ p₂) := xPoint_le_qLine hl le_sup_right
  let f : ↥(xPoint p₁) × ↥(xPoint p₂) → ↥(xPoint p₁ ⊔ xPoint p₂) := fun x =>
    ⟨(x.1 : Sp4 F) * x.2, Subgroup.mul_mem _ (le_sup_left (α := Subgroup (Sp4 F)) x.1.2)
      (le_sup_right (α := Subgroup (Sp4 F)) x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
    have h' : (x₁ : Sp4 F) * y₁ = x₂ * y₂ := congrArg Subtype.val h
    have hx : (x₂ : Sp4 F)⁻¹ * x₁ = y₂ * (y₁ : Sp4 F)⁻¹ := by
      calc (x₂ : Sp4 F)⁻¹ * x₁ = (x₂ : Sp4 F)⁻¹ * (x₁ * y₁) * (y₁ : Sp4 F)⁻¹ := by group
        _ = (x₂ : Sp4 F)⁻¹ * (x₂ * y₂) * (y₁ : Sp4 F)⁻¹ := by rw [h']
        _ = y₂ * (y₁ : Sp4 F)⁻¹ := by group
    have hmem : (x₂ : Sp4 F)⁻¹ * x₁ ∈ xPoint p₁ ⊓ xPoint p₂ :=
      ⟨(xPoint p₁).mul_mem ((xPoint p₁).inv_mem x₂.2) x₁.2,
        hx ▸ (xPoint p₂).mul_mem y₂.2 ((xPoint p₂).inv_mem y₁.2)⟩
    rw [xPoint_inf_xPoint hp₁ hp₂ hne, Subgroup.mem_bot] at hmem
    have hxe : (x₁ : Sp4 F) = x₂ := by
      calc (x₁ : Sp4 F) = x₂ * ((x₂ : Sp4 F)⁻¹ * x₁) := by group
        _ = x₂ := by rw [hmem, mul_one]
    have hye : (y₁ : Sp4 F) = y₂ := by
      have := h'
      rw [hxe] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hxe) (Subtype.ext hye)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, card_xPoint hp₁, card_xPoint hp₂, ← sq] at this

end CFSG.Quasithin.MS93.S5
