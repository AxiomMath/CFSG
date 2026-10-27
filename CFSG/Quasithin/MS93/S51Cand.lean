module

public import CFSG.Quasithin.MS93.S5A54Sp
public import CFSG.Quasithin.MS93.MSPLevi

public section

namespace CFSG.Quasithin.MS93.S51

open Matrix MSP CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem le_perp_sup {p p₁ p₂ : Submodule F (V4 F)} (h₁ : p ≤ perp p₁) (h₂ : p ≤ perp p₂) :
    p ≤ perp (p₁ ⊔ p₂) := by
  intro v hv
  rw [mem_perp]
  intro w hw
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add, LinearMap.add_apply, mem_perp.1 (h₁ hv) w₁ hw₁, mem_perp.1 (h₂ hv) w₂ hw₂,
    add_zero]

theorem isCandSp_of_le_qLine {R A : Subgroup (Sp4 F)} {l : Submodule F (V4 F)} (hl : IsLine l)
    (hAl : A ≤ qLine l) (hAR : A ≤ R) (hq2 : Nat.card F ^ 2 ≤ Nat.card A) : S5.IsCandSp R A := by
  have hfix : Nat.card F ^ 2 ≤ Nat.card (fixSp A) := by
    have hle : l ≤ fixSp A := le_fixer_iff.1 hAl
    have := Nat.card_le_card_of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
    rw [Module.natCard_eq_pow_finrank (K := F) (V := l), hl.1] at this
    exact this
  refine ⟨hAR, ?_, ?_⟩
  · rw [card_V4, show 4 = 2 + 2 from rfl, pow_add]
    exact Nat.mul_le_mul hfix hq2
  · rw [card_V4, show 4 = 2 + 2 from rfl, pow_add]
    exact Nat.mul_le_mul_right _ hfix

theorem card_xPoint_sup_le {p₁ p₂ : Submodule F (V4 F)} (hp₁ : IsPoint p₁) (hp₂ : IsPoint p₂)
    (hc : ∀ x ∈ xPoint p₁, ∀ y ∈ xPoint p₂, x * y = y * x) :
    Nat.card ↥(xPoint p₁ ⊔ xPoint p₂) ≤ Nat.card F ^ 2 := by
  have hN : xPoint p₁ ≤ Subgroup.normalizer (xPoint p₂ : Set (Sp4 F)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hc x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have hy' : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [hy', hc x⁻¹ ((xPoint p₁).inv_mem hx) _ hy, mul_assoc, inv_mul_cancel, mul_one]
      exact hy
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN
  let f : ↥(xPoint p₁) × ↥(xPoint p₂) → ↥(xPoint p₁ ⊔ xPoint p₂) := fun x =>
    ⟨(x.1 : Sp4 F) * x.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
      (Subgroup.mem_sup_right x.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ ((xPoint p₁ ⊔ xPoint p₂ : Subgroup (Sp4 F)) : Set (Sp4 F)) := hz
    rw [hset] at hz'
    obtain ⟨x, hx, y, hy, rfl⟩ := hz'
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, card_xPoint hp₁, card_xPoint hp₂, ← sq] at this

variable [CharP F 2]

theorem conf_analysis {R : Subgroup (Sp4 F)} (hR : IsPGroup 2 R)
    {p₁ p₂ : Submodule F (V4 F)} (hp₁ : IsPoint p₁) (hp₂ : IsPoint p₂)
    (hJR : xPoint p₁ ⊔ xPoint p₂ ≤ R)
    (hmax : ∀ A ∈ S5.candMax R, A ≤ xPoint p₁ ⊔ xPoint p₂) :
    S5.candMax R = {xPoint p₁ ⊔ xPoint p₂} ∧
      R ⊓ fixer (fixSp (xPoint p₁ ⊔ xPoint p₂)) ≤ xPoint p₁ ⊔ xPoint p₂ ∧
      ∀ A : Subgroup (Sp4 F), A ≤ R → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
        Nat.card (V4 F) ≤ Nat.card (fixSp A) * Nat.card A → A ≤ xPoint p₁ ⊔ xPoint p₂ := by
  classical
  set Jb := xPoint p₁ ⊔ xPoint p₂ with hJb
  have hq := S5.one_lt_card_F (F := F)
  have hq2 : Nat.card F < Nat.card F ^ 2 := by
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq (by norm_num)
  have hcase : p₁ = p₂ ∨ (p₁ ≠ p₂ ∧ p₂ ≤ perp p₁) := by
    by_cases he : p₁ = p₂
    · exact Or.inl he
    · exact Or.inr ⟨he, S5.le_perp_of_xPoint_le hp₁ hp₂ he hR (le_sup_left.trans hJR)
        (le_sup_right.trans hJR)⟩
  have hJcard : (p₁ = p₂ ∧ Nat.card Jb = Nat.card F) ∨
      (p₁ ≠ p₂ ∧ p₂ ≤ perp p₁ ∧ Nat.card Jb = Nat.card F ^ 2) := by
    rcases hcase with he | ⟨hne, hperp⟩
    · left
      refine ⟨he, ?_⟩
      rw [hJb, he, sup_idem, card_xPoint hp₂]
    · right
      refine ⟨hne, hperp, le_antisymm ?_ (S5.card_xPoint_sup hp₁ hp₂ hne hperp)⟩
      have hl := S5.isLine_sup hp₁ hp₂ hne hperp
      exact card_xPoint_sup_le hp₁ hp₂ fun x hx y hy =>
        S5.qLine_comm hl (xPoint_le_qLine hl le_sup_left hx) (xPoint_le_qLine hl le_sup_right hy)
  have hJcand : S5.IsCandSp R Jb := by
    rcases hJcard with ⟨he, -⟩ | ⟨hne, hperp, hc⟩
    · rw [hJb, he, sup_idem]
      exact S5.isCandSp_xPoint hp₂ (le_sup_right.trans hJR)
    · have hl := S5.isLine_sup hp₁ hp₂ hne hperp
      exact isCandSp_of_le_qLine hl (sup_le (xPoint_le_qLine hl le_sup_left)
        (xPoint_le_qLine hl le_sup_right)) hJR hc.ge
  have hmem : ∀ A ∈ S5.candMax R, A = Jb := fun A hA =>
    Subgroup.eq_of_le_of_card_ge (hmax A hA) (hA.2 Jb hJcand)
  obtain ⟨A₀, hA₀⟩ := S5.candMax_nonempty R
  have hJmax : Jb ∈ S5.candMax R := hmem A₀ hA₀ ▸ hA₀
  have hcm : S5.candMax R = {Jb} := Set.eq_singleton_iff_unique_mem.2 ⟨hJmax, hmem⟩
  have hbig : ∀ B, S5.IsCandSp R B → Nat.card Jb ≤ Nat.card B → B = Jb := fun B hB hc =>
    hmem B ⟨hB, fun C hC => (hJmax.2 C hC).trans hc⟩
  have hRQ : p₁ ≠ p₂ → p₂ ≤ perp p₁ → R ⊓ qLine (p₁ ⊔ p₂) = Jb := by
    intro hne hperp
    have hl := S5.isLine_sup hp₁ hp₂ hne hperp
    have hJl : Jb ≤ qLine (p₁ ⊔ p₂) :=
      sup_le (xPoint_le_qLine hl le_sup_left) (xPoint_le_qLine hl le_sup_right)
    have hc : Nat.card Jb = Nat.card F ^ 2 := by
      rcases hJcard with ⟨he, -⟩ | ⟨-, -, hc⟩
      · exact absurd he hne
      · exact hc
    have hle : Jb ≤ R ⊓ qLine (p₁ ⊔ p₂) := le_inf hJR hJl
    refine hbig _ (isCandSp_of_le_qLine hl inf_le_right inf_le_left ?_)
      (Subgroup.card_le_of_le hle)
    rw [← hc]
    exact Subgroup.card_le_of_le hle
  refine ⟨hcm, ?_, ?_⟩
  ·
    rcases hcase with he | ⟨hne, hperp⟩
    · have hJ : Jb = xPoint p₂ := by rw [hJb, he, sup_idem]
      rw [hJ, fixSp_xPoint hp₂]
      exact inf_le_right
    · have hl := S5.isLine_sup hp₁ hp₂ hne hperp
      have hJl : Jb ≤ qLine (p₁ ⊔ p₂) :=
        sup_le (xPoint_le_qLine hl le_sup_left) (xPoint_le_qLine hl le_sup_right)
      have h1 : fixer (fixSp Jb) ≤ qLine (p₁ ⊔ p₂) := fixer_antitone (le_fixer_iff.1 hJl)
      exact (inf_le_inf_left R h1).trans (hRQ hne hperp).le
  ·
    intro A hAR hAc hA
    by_cases hA1 : A = ⊥
    · rw [hA1]
      exact bot_le
    have hA2 : IsPGroup 2 A := hR.to_le hAR
    by_cases h2 : 2 ≤ Module.finrank F (fixSp A)
    ·
      have hAcand : S5.IsCandSp R A := by
        refine ⟨hAR, hA, ?_⟩
        rw [card_V4, card_fixSp, ← pow_add]
        exact Nat.pow_le_pow_right Nat.card_pos (by have := S5.finrank_le_four (fixSp A); omega)
      have hAJ : Nat.card A ≤ Nat.card Jb := hJmax.2 A hAcand
      rcases S5.isCandSp_cases hR hAcand hA1 with ⟨p', hp', rfl⟩ | ⟨l, hl, hAl, -, hcard⟩
      · rcases hJcard with ⟨he, hc⟩ | ⟨hne, hperp, -⟩
        · rw [hbig _ hAcand (by rw [hc, card_xPoint hp'])]
        ·
          have hl₀ := S5.isLine_sup hp₁ hp₂ hne hperp
          have hp'l : p' ≤ p₁ ⊔ p₂ := by
            have hperp_i : ∀ {p}, IsPoint p → xPoint p ≤ R → p' = p ∨ p' ≤ perp p := by
              intro p hp hpR
              by_cases he : p' = p
              · exact Or.inl he
              · exact Or.inr (S5.le_perp_of_xPoint_le hp hp' (Ne.symm he) hR hpR hAR)
            rcases hperp_i hp₁ (le_sup_left.trans hJR) with h1 | h1
            · rw [h1]; exact le_sup_left
            rcases hperp_i hp₂ (le_sup_right.trans hJR) with h2 | h2
            · rw [h2]; exact le_sup_right
            rw [← hl₀.perp_eq]
            exact le_perp_sup h1 h2
          rw [← hRQ hne hperp]
          exact le_inf hAR (xPoint_le_qLine hl₀ hp'l)
      · rcases hJcard with ⟨-, hc⟩ | ⟨hne, hperp, hc⟩
        · exfalso
          have := hAJ.trans hc.le
          omega
        · have hB := isCandSp_of_le_qLine hl inf_le_right (inf_le_left : R ⊓ qLine l ≤ R)
            (hcard.trans (Subgroup.card_le_of_le (le_inf hAR hAl)))
          have hBJ := hbig _ hB (by
            rw [hc]
            exact hcard.trans (Subgroup.card_le_of_le (le_inf hAR hAl)))
          rw [← hBJ]
          exact le_inf hAR hAl
    ·
      exfalso
      have hpos := S5.finrank_pos_of_ne_bot (S5.fixSp_ne_bot hA2)
      have hfd : Module.finrank F (fixSp A) = 1 := by omega
      set p := fixSp A with hpdef
      have hp : IsPoint p := hfd
      have hAp : A ≤ fixer p := le_fixer_iff.2 le_rfl
      obtain ⟨l₀, hl₀, hpl, hAl⟩ := S5.exists_line_mod hp hA2 hAp
      have hbound := S5.card_le_card_inf_mul hp hl₀ hpl hAp hAl
      have hA3 : Nat.card F ^ 3 ≤ Nat.card A := by
        rw [card_V4, card_fixSp, hfd, pow_one] at hA
        have : Nat.card F * Nat.card F ^ 3 ≤ Nat.card F * Nat.card A := by
          rw [← pow_succ']; exact hA
        exact Nat.le_of_mul_le_mul_left this Nat.card_pos
      have hq3 : Nat.card F ^ 2 ≤ Nat.card ↥(qLine l₀ ⊓ A) := by
        have : Nat.card F ^ 2 * Nat.card F ≤ Nat.card ↥(qLine l₀ ⊓ A) * Nat.card F := by
          rw [← pow_succ]; exact hA3.trans hbound
        exact Nat.le_of_mul_le_mul_right this Nat.card_pos
      have hB := isCandSp_of_le_qLine hl₀ inf_le_right (inf_le_left : R ⊓ qLine l₀ ≤ R)
        (hq3.trans (Subgroup.card_le_of_le ((inf_le_inf_left _ hAR).trans_eq (inf_comm _ _))))
      rcases hJcard with ⟨-, hc⟩ | ⟨hne, hperp, hc⟩
      · have h1 := hJmax.2 _ hB
        have h2 : Nat.card F ^ 2 ≤ Nat.card ↥(R ⊓ qLine l₀) :=
          hq3.trans (Subgroup.card_le_of_le (le_inf (inf_le_right.trans hAR) inf_le_left))
        omega
      ·
        have hBle : Nat.card Jb ≤ Nat.card ↥(R ⊓ qLine l₀) := by
          rw [hc]
          exact hq3.trans (Subgroup.card_le_of_le (le_inf (inf_le_right.trans hAR) inf_le_left))
        have hBJ := hbig _ hB hBle
        have hsub : qLine l₀ ⊓ A ≤ Jb := by
          rw [← hBJ]
          exact le_inf (inf_le_right.trans hAR) inf_le_left
        have heq : qLine l₀ ⊓ A = Jb :=
          Subgroup.eq_of_le_of_card_ge hsub (by rw [hc]; exact hq3)
        have hJA : Jb ≤ A := heq ▸ inf_le_right
        have hfixi : ∀ {p'}, IsPoint p' → xPoint p' ≤ Jb → p' ≤ fixSp A := by
          intro p' hp' hpJ
          obtain ⟨v, hv0, rfl⟩ := exists_eq_span_of_isPoint hp'
          rw [Submodule.span_singleton_le_iff_mem, mem_fixSp]
          intro x hx
          exact mulVec_eq_of_commute_transv hv0
            (hAc x hx _ (hJA (hpJ (transv_mem_xPoint v 1))))
        have hl : p₁ ⊔ p₂ ≤ fixSp A := sup_le (hfixi hp₁ le_sup_left) (hfixi hp₂ le_sup_right)
        have := Submodule.finrank_mono hl
        rw [(S5.isLine_sup hp₁ hp₂ hne hperp).1, hfd] at this
        omega

end CFSG.Quasithin.MS93.S51
