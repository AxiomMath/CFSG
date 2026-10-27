module

public import CFSG.Quasithin.MS93.MSPOff

public section

namespace CFSG.Quasithin.MS93.S512T

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP

variable {F : Type} [Field F]

theorem card_fixer_le [Finite F] {W : Submodule F (V4 F)} (hW : 3 ≤ Module.finrank F W) :
    Nat.card (fixer W) ≤ Nat.card F := by
  have hle : W ≤ fixSp (fixer W) := le_fixer_iff.1 le_rfl
  have h3 : 3 ≤ Module.finrank F (fixSp (fixer W)) := hW.trans (Submodule.finrank_mono hle)
  have h4 : Module.finrank F (fixSp (fixer W)) ≤ 4 := by
    have := Submodule.finrank_le (fixSp (fixer W))
    simpa using this
  rcases (show Module.finrank F (fixSp (fixer W)) = 3 ∨
      Module.finrank F (fixSp (fixer W)) = 4 by omega) with h | h
  · obtain ⟨p, hp, -, hE⟩ := exists_point_of_finrank_fixSp_three h
    calc Nat.card (fixer W) ≤ Nat.card (xPoint p) := Subgroup.card_le_of_le hE
      _ = Nat.card F := card_xPoint hp
  · have htop : fixSp (fixer W) = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h]; simp)
    rw [fixSp_eq_top_iff.1 htop, Subgroup.card_bot]
    exact Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'

theorem sub_mem_of_mem_qLine {l : Submodule F (V4 F)} (hl : IsLine l) {g : Sp4 F}
    (hg : g ∈ qLine l) (v : V4 F) : mat g *ᵥ v - v ∈ l := by
  have := sub_mem_perp_of_mem_fixer hg v
  rwa [hl.perp_eq] at this

theorem sub_mul_of_mem_qLine {l : Submodule F (V4 F)} (hl : IsLine l) {g h : Sp4 F}
    (hg : g ∈ qLine l) (hh : h ∈ qLine l) (w : V4 F) :
    mat (g * h) *ᵥ w - w = (mat g *ᵥ w - w) + (mat h *ᵥ w - w) := by
  have h1 : mat g *ᵥ (mat h *ᵥ w - w) = mat h *ᵥ w - w := hg _ (sub_mem_of_mem_qLine hl hh w)
  rw [mulVec_sub] at h1
  rw [mat_mul_mulVec]
  have h2 : mat g *ᵥ (mat h *ᵥ w) = (mat h *ᵥ w - w) + mat g *ᵥ w := by
    rw [sub_eq_iff_eq_add] at h1
    exact h1
  rw [h2]
  abel

theorem card_le_sq_of_sub_mem [Finite F] {l : Submodule F (V4 F)} (hl : IsLine l) {w : V4 F}
    (hw : w ∉ l) {A : Subgroup (Sp4 F)} (hA : A ≤ qLine l) {P : Submodule F (V4 F)}
    (hP : Module.finrank F P ≤ 1) (hAP : ∀ g ∈ A, mat g *ᵥ w - w ∈ P) :
    Nat.card A ≤ Nat.card F ^ 2 := by
  let φ : ↥A →* Multiplicative ↥P :=
    { toFun := fun g => Multiplicative.ofAdd ⟨mat (g : Sp4 F) *ᵥ w - w, hAP g g.2⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp [mat_one]
      map_mul' := by
        intro g h
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp only [Subgroup.coe_mul, toAdd_ofAdd, toAdd_mul, Submodule.coe_add]
        exact sub_mul_of_mem_qLine hl (hA g.2) (hA h.2) w }
  have hker : φ.ker.map A.subtype ≤ fixer (l ⊔ F ∙ w) := by
    rintro _ ⟨g, hg, rfl⟩ v hv
    have hgw : mat (g : Sp4 F) *ᵥ w = w := by
      have h1 : φ g = 1 := hg
      have h2 := congrArg (fun y => ((Multiplicative.toAdd y : ↥P) : V4 F)) h1
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one,
        Submodule.coe_zero] at h2
      exact sub_eq_zero.1 h2
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    change mat (g : Sp4 F) *ᵥ (y + c • w) = y + c • w
    rw [mulVec_add, mulVec_smul, hA g.2 y hy, hgw]
  have hdim : 3 ≤ Module.finrank F ↥(l ⊔ F ∙ w) := by
    have hdisj : l ⊓ F ∙ w = ⊥ := by
      rw [eq_bot_iff]
      intro v ⟨hvl, hvw⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvw
      by_cases hc : c = 0
      · rw [hc, zero_smul]
        exact Submodule.zero_mem _
      · exfalso
        apply hw
        have := l.smul_mem c⁻¹ hvl
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hw0 : w ≠ 0 := fun h0 => hw (h0 ▸ l.zero_mem)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq l (F ∙ w)
    rw [hdisj, finrank_bot, finrank_span_singleton hw0, hl.1] at h1
    omega
  have hcard_ker : Nat.card φ.ker ≤ Nat.card F := by
    calc Nat.card φ.ker = Nat.card (φ.ker.map A.subtype) :=
          (Subgroup.card_map_of_injective A.subtype_injective).symm
      _ ≤ Nat.card (fixer (l ⊔ F ∙ w)) := Subgroup.card_le_of_le hker
      _ ≤ Nat.card F := card_fixer_le hdim
  have hcard_range : Nat.card φ.range ≤ Nat.card F := by
    calc Nat.card φ.range ≤ Nat.card (Multiplicative ↥P) := Subgroup.card_le_card_group _
      _ = Nat.card ↥P := rfl
      _ = Nat.card F ^ Module.finrank F P := Module.natCard_eq_pow_finrank (K := F)
      _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right Nat.card_pos hP
      _ = Nat.card F := pow_one _
  have hmul : Nat.card φ.ker * Nat.card φ.range = Nat.card A := by
    rw [← Subgroup.index_ker φ, mul_comm]
    exact Subgroup.index_mul_card φ.ker
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := hmul.symm
    _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul hcard_ker hcard_range
    _ = Nat.card F ^ 2 := (sq _).symm

theorem finrank_inf_le_one {l₁ l₂ : Submodule F (V4 F)} (h₁ : IsLine l₁) (h₂ : IsLine l₂)
    (hne : l₁ ≠ l₂) : Module.finrank F ↥(l₁ ⊓ l₂) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have h1 : Module.finrank F ↥(l₁ ⊓ l₂) = 2 := by
    have := Submodule.finrank_mono (inf_le_left : l₁ ⊓ l₂ ≤ l₁)
    rw [h₁.1] at this
    omega
  have e1 : l₁ ⊓ l₂ = l₁ :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, h₁.1])
  have e2 : l₁ ⊓ l₂ = l₂ :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, h₂.1])
  exact hne (e1.symm.trans e2)

theorem exists_mem_not_mem {l₁ l₂ : Submodule F (V4 F)} (h₁ : IsLine l₁) (h₂ : IsLine l₂)
    (hne : l₁ ≠ l₂) : ∃ w ∈ l₂, w ∉ l₁ := by
  by_contra hcon
  push Not at hcon
  have hle : l₂ ≤ l₁ := fun w hw => hcon w hw
  exact hne (Submodule.eq_of_le_of_finrank_eq hle (by rw [h₁.1, h₂.1])).symm

theorem card_qLine_inf_stab_le [Finite F] {l₁ l₂ : Submodule F (V4 F)} (h₁ : IsLine l₁)
    (h₂ : IsLine l₂) (hne : l₁ ≠ l₂) :
    Nat.card ↥(qLine l₁ ⊓ stab l₂) ≤ Nat.card F ^ 2 := by
  obtain ⟨w, hw₂, hw₁⟩ := exists_mem_not_mem h₁ h₂ hne
  refine card_le_sq_of_sub_mem h₁ hw₁ inf_le_left (finrank_inf_le_one h₁ h₂ hne) ?_
  rintro g ⟨hg₁, hg₂⟩
  exact ⟨sub_mem_of_mem_qLine h₁ hg₁ w,
    l₂.sub_mem (mulVec_mem_of_mem_stab hg₂ hw₂) hw₂⟩

theorem card_qLine_inf_qLine_le [Finite F] {l₁ l₂ : Submodule F (V4 F)} (h₁ : IsLine l₁)
    (h₂ : IsLine l₂) (hne : l₁ ≠ l₂) :
    Nat.card ↥(qLine l₁ ⊓ qLine l₂) ≤ Nat.card F := by
  have hle : qLine l₁ ⊓ qLine l₂ ≤ fixer (l₁ ⊔ l₂) := by
    rintro g ⟨hg₁, hg₂⟩ v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [mulVec_add, hg₁ y hy, hg₂ z hz]
  have hdim : 3 ≤ Module.finrank F ↥(l₁ ⊔ l₂) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq l₁ l₂
    have := finrank_inf_le_one h₁ h₂ hne
    rw [h₁.1, h₂.1] at h
    omega
  exact (Subgroup.card_le_of_le hle).trans (card_fixer_le hdim)

theorem card_qPoint_inf_qLine_le [Finite F] {p l : Submodule F (V4 F)} (hp : IsPoint p)
    (hl : IsLine l) : Nat.card ↥(qPoint p ⊓ qLine l) ≤ Nat.card F ^ 2 := by
  by_cases hpl : p ≤ l
  ·
    have hdim : Module.finrank F ↥(perp p) = 3 := by
      have := finrank_perp p
      have hp1 : Module.finrank F p = 1 := hp
      omega
    obtain ⟨w, hwp, hwl⟩ : ∃ w ∈ perp p, w ∉ l := by
      by_contra hcon
      push Not at hcon
      have := Submodule.finrank_mono (show perp p ≤ l from fun w hw => hcon w hw)
      rw [hdim, hl.1] at this
      omega
    refine card_le_sq_of_sub_mem hl hwl inf_le_right (le_of_eq hp) ?_
    rintro g ⟨hg₁, -⟩
    exact hg₁.2 w hwp
  ·
    have hle : qPoint p ⊓ qLine l ≤ fixer (p ⊔ l) := by
      rintro g ⟨hg₁, hg₂⟩ v hv
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
      rw [mulVec_add, hg₁.1 y hy, hg₂ z hz]
    have hdim : 3 ≤ Module.finrank F ↥(p ⊔ l) := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq p l
      have hinf : p ⊓ l = ⊥ := by
        have hle1 : Module.finrank F ↥(p ⊓ l) ≤ 1 := by
          have := Submodule.finrank_mono (inf_le_left : p ⊓ l ≤ p)
          rwa [show Module.finrank F p = 1 from hp] at this
        rcases (show Module.finrank F ↥(p ⊓ l) = 0 ∨ Module.finrank F ↥(p ⊓ l) = 1 by omega)
          with h0 | h1
        · exact Submodule.finrank_eq_zero.1 h0
        · exfalso
          apply hpl
          have e : p ⊓ l = p :=
            Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1]; exact hp.symm)
          rw [← e]
          exact inf_le_right
      rw [hinf, finrank_bot, show Module.finrank F p = 1 from hp, hl.1] at h
      omega
    calc Nat.card ↥(qPoint p ⊓ qLine l) ≤ Nat.card (fixer (p ⊔ l)) := Subgroup.card_le_of_le hle
      _ ≤ Nat.card F := card_fixer_le hdim
      _ ≤ Nat.card F ^ 2 := by
        rcases Nat.eq_zero_or_pos (Nat.card F) with h0 | hpos
        · rw [h0]
          simp
        · exact Nat.le_self_pow (by norm_num) _

theorem eq_top_of_invariant {W : AddSubgroup (V4 F)}
    (hW : ∀ g : Sp4 F, ∀ v ∈ W, mat g *ᵥ v ∈ W) {v : V4 F} (hv : v ∈ W) (hv0 : v ≠ 0) :
    W = ⊤ := by
  have key : ∀ x : V4 F, form F x v ≠ 0 → x ∈ W := by
    intro x hx
    have h1 := hW (transv x (form F x v)⁻¹) v hv
    rw [transv_mulVec, inv_mul_cancel₀ hx, one_smul] at h1
    have := W.sub_mem h1 hv
    rwa [add_sub_cancel_left] at this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : V4 F, form F x₀ v = 1 := by
    obtain ⟨y, hy⟩ := exists_form_eq_one hv0
    refine ⟨-y, ?_⟩
    rw [map_neg, LinearMap.neg_apply, form_swap, hy, neg_neg]
  rw [eq_top_iff]
  intro y _
  by_cases hy : form F y v = 0
  · have h1 : y + x₀ ∈ W := key _ (by rw [map_add, LinearMap.add_apply, hy, hx₀]; simp)
    have h2 : x₀ ∈ W := key _ (by rw [hx₀]; exact one_ne_zero)
    have := W.sub_mem h1 h2
    rwa [add_sub_cancel_right] at this
  · exact key y hy

end CFSG.Quasithin.MS93.S512T
