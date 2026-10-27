module

public import CFSG.Quasithin.MS93.S33XSp

public section

namespace CFSG.Quasithin.MS93.S511S

open CFSG.Quasithin MSP Matrix

variable {F : Type} [Field F]

theorem card_le_of_le_fixer_three [Finite F] {B : Subgroup (Sp4 F)} {W : Submodule F (V4 F)}
    (hW : Module.finrank F W = 3) (hB : B ≤ fixer W) : Nat.card B ≤ Nat.card F := by
  have hp : IsPoint (perp W) := by
    have := finrank_perp W
    unfold IsPoint
    omega
  have hx : fixer W = xPoint (perp W) := by
    show fixer W = fixer (perp (perp W))
    rw [perp_perp]
  calc Nat.card B ≤ Nat.card (xPoint (perp W)) := Subgroup.card_le_of_le (hx ▸ hB)
    _ = Nat.card F := card_xPoint hp

theorem fixSp_eq_of_le_qLine [Finite F] {l : Submodule F (V4 F)} (hl : IsLine l)
    {B : Subgroup (Sp4 F)} (hB : B ≤ qLine l) (hcard : Nat.card F < Nat.card B) :
    fixSp B = l := by
  have h1 : l ≤ fixSp B := by
    have := fixSp_antitone hB
    rwa [fixSp_qLine hl] at this
  have hne : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    have : 1 ≤ Nat.card F := Nat.card_pos
    omega
  have h3 := S33.finrank_fixSp_le_three' hne
  by_contra hneq
  have hlt : l < fixSp B := lt_of_le_of_ne h1 (Ne.symm hneq)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hl.1] at h2
  have hW : Module.finrank F (fixSp B) = 3 := by omega
  have := card_le_of_le_fixer_three hW (le_fixer_iff.2 le_rfl)
  omega

theorem commSp_eq_of_le_qLine [Finite F] {l : Submodule F (V4 F)} (hl : IsLine l)
    {B : Subgroup (Sp4 F)} (hB : B ≤ qLine l) (hcard : Nat.card F < Nat.card B) :
    commSp B = l := by
  rw [S33.commSp_eq_perp_fixSp, fixSp_eq_of_le_qLine hl hB hcard, hl.perp_eq]

theorem finrank_inf_fixSp_le_one {l : Submodule F (V4 F)} (hl : IsLine l)
    {B : Subgroup (Sp4 F)} (hB : B ≤ qLine l) (hne : B ≠ ⊥) {W : Submodule F (V4 F)}
    (hW : Module.finrank F W ≤ 2) (hWl : W ⊓ l = ⊥) :
    Module.finrank F ↥(W ⊓ fixSp B) ≤ 1 := by
  have h3 := S33.finrank_fixSp_le_three' hne
  have hlB : l ≤ fixSp B := by
    have := fixSp_antitone hB
    rwa [fixSp_qLine hl] at this
  by_contra hgt
  push Not at hgt
  have hle : Module.finrank F ↥(W ⊓ fixSp B) ≤ Module.finrank F W :=
    Submodule.finrank_mono inf_le_left
  have hW2 : Module.finrank F W = 2 := by omega
  have hWB : W ≤ fixSp B := by
    have heq : W ⊓ fixSp B = W :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    rw [← heq]
    exact inf_le_right
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq W l
  rw [hWl, finrank_bot, hW2, hl.1] at hsup
  have hle' : Module.finrank F ↥(W ⊔ l) ≤ Module.finrank F (fixSp B) :=
    Submodule.finrank_mono (sup_le hWB hlB)
  omega

theorem fixSp_sup_eq_bot [CharP F 2] {A₁ A₂ : Subgroup (Sp4 F)} (hgen : A₁ ⊔ A₂ = ⊤) :
    fixSp A₁ ⊓ fixSp A₂ = ⊥ := by
  have hle : fixSp A₁ ⊓ fixSp A₂ ≤ fixSp (⊤ : Subgroup (Sp4 F)) := by
    intro v hv
    rw [← hgen]
    have : A₁ ⊔ A₂ ≤ fixer (F ∙ v) := by
      refine sup_le (le_fixer_iff.2 ?_) (le_fixer_iff.2 ?_)
      · exact (Submodule.span_le).2 (Set.singleton_subset_iff.2 hv.1)
      · exact (Submodule.span_le).2 (Set.singleton_subset_iff.2 hv.2)
    exact (le_fixer_iff.1 this) (Submodule.mem_span_singleton_self v)
  have htop : fixSp (⊤ : Subgroup (Sp4 F)) = ⊥ := by
    have h1 : fixSp (⊤ : Subgroup (Sp4 F)) ≤ fixSp (Q₁ F) ⊓ fixSp (qLine (ln₀' F)) :=
      le_inf (fixSp_antitone le_top) (fixSp_antitone le_top)
    rw [fixSp_Q₁, fixSp_qLine isLine_ln₀', ln₀_inf_ln₀'] at h1
    exact le_bot_iff.1 h1
  exact le_bot_iff.1 (hle.trans htop.le)

theorem card_le_of_finrank_le_one [Finite F] {W : Submodule F (V4 F)}
    (hW : Module.finrank F W ≤ 1) : Nat.card W ≤ Nat.card F := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  calc Nat.card F ^ Module.finrank F W ≤ Nat.card F ^ 1 :=
        Nat.pow_le_pow_right Nat.card_pos hW
    _ = Nat.card F := pow_one _

end CFSG.Quasithin.MS93.S511S
