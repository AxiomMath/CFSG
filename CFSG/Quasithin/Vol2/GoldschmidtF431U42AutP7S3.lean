module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7E4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cnt

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem mem_Th2_of {l : PL} (h1 : l ∈ Al2) (h2 : l ≠ idL) (h3 : l ∉ ZCl) : l ∈ Th2 := by
  unfold Th2
  rw [List.mem_filter]
  refine ⟨h1, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  exact ⟨h2, by simpa using h3⟩

theorem Th2_props {l : PL} (h : l ∈ Th2) : l ∈ Al2 ∧ l ≠ idL ∧ l ∉ ZCl := by
  unfold Th2 at h
  rw [List.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h2
  exact ⟨h1, h2.1, by simpa using h2.2⟩

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Theta

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c)

include hZ

theorem toG_eltB_Th2 {l : PL} (hl : l ∈ Th2) :
    c.iso.toG (eltB l) ∈ c.iso.imgG A2h ∧ c.iso.toG (eltB l) ≠ 1 ∧
      ¬ IsConj (c.iso.toG (eltB l)) z := by
  obtain ⟨hlA, hl1, hlZ⟩ := Th2_props hl
  have hlT : l ∈ Thl := A2_check.2.2.2.1 l hlA
  have hrep : RepL l (eltB l : P45) := by
    rw [coe_eltB hlT]
    exact repL_eltOfL hlT
  refine ⟨c.iso.mem_imgG.2 ⟨eltB l, ⟨l, hlA, hrep⟩, rfl⟩, ?_, ?_⟩
  · intro h
    have h0 : eltB l = 1 := c.iso.toG_injective (h.trans c.iso.toG_one.symm)
    have h1 : ((eltB l : Ah) : P45) = 1 := by rw [h0]; rfl
    rw [h1] at hrep
    exact hl1 (repL_unique hrep (repL_one 45))
  · intro h
    have hT : ((eltB l : Bh) : Ah) ∈ That := by
      rw [coe_eltB hlT]
      exact eltOfL_mem hlT
    obtain ⟨l', hl', hrep'⟩ := (hZ hT).1 h
    have := repL_unique hrep' hrep
    exact hlZ (this ▸ hl')

omit hZ in
theorem conj_Theta {n u : G} (hn : n ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G))
    (hu : u ∈ c.iso.imgG A2h ∧ u ≠ 1 ∧ ¬ IsConj u z) :
    n * u * n⁻¹ ∈ c.iso.imgG A2h ∧ n * u * n⁻¹ ≠ 1 ∧ ¬ IsConj (n * u * n⁻¹) z := by
  obtain ⟨huA, hu1, huz⟩ := hu
  refine ⟨(Subgroup.mem_normalizer_iff.1 hn u).1 huA, ?_, ?_⟩
  · intro h
    apply hu1
    have : u = n⁻¹ * (n * u * n⁻¹) * n := by group
    rw [this, h]
    group
  · intro h
    apply huz
    obtain ⟨c0, hc0⟩ := isConj_iff.1 h
    exact isConj_iff.2 ⟨c0 * n, by rw [← hc0]; group⟩

omit hZ in
theorem mem_imgG_four {l₁ l₂ : PL} (h1T : l₁ ∈ Thl) (h2T : l₂ ∈ Thl) {S : Subgroup Ah}
    (hS : ∀ a ∈ S, ∃ l ∈ [idL, l₁, l₂, comp l₁ l₂], RepL l (a : P45)) {u : G}
    (hu : u ∈ c.iso.imgG S) :
    u = 1 ∨ u = c.iso.toG (eltB l₁) ∨ u = c.iso.toG (eltB l₂) ∨
      u = c.iso.toG (eltB l₁) * c.iso.toG (eltB l₂) := by
  obtain ⟨b, hbS, rfl⟩ := c.iso.mem_imgG.1 hu
  obtain ⟨l, hl, hrep⟩ := hS _ hbS
  have hr1 : RepL l₁ (eltB l₁ : P45) := by
    rw [coe_eltB h1T]
    exact repL_eltOfL h1T
  have hr2 : RepL l₂ (eltB l₂ : P45) := by
    rw [coe_eltB h2T]
    exact repL_eltOfL h2T
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h
  · left
    rw [h] at hrep
    have : b = 1 := Subtype.ext (Subtype.ext (eq_of_repL hrep (repL_one 45)))
    rw [this, c.iso.toG_one]
  · right; left
    rw [h] at hrep
    have : b = eltB l₁ := Subtype.ext (Subtype.ext (eq_of_repL hrep hr1))
    rw [this]
  · right; right; left
    rw [h] at hrep
    have : b = eltB l₂ := Subtype.ext (Subtype.ext (eq_of_repL hrep hr2))
    rw [this]
  · right; right; right
    rw [h] at hrep
    have : b = eltB l₁ * eltB l₂ := Subtype.ext (Subtype.ext (eq_of_repL hrep (repL_mul hr1 hr2)))
    rw [this, AutIso.toG_mul]

end Theta

@[expose] def Theta (c : AutCtx G M₁ M₂ z) : Set G :=
  {u | u ∈ c.iso.imgG A2h ∧ u ≠ 1 ∧ ¬ IsConj u z}

theorem Bl_pairs :
    (Th2.getD 0 [] ∈ Th2 ∧ Th2.getD 3 [] ∈ Th2 ∧ Th2.getD 0 [] ≠ Th2.getD 3 [] ∧
      comp (Th2.getD 0 []) (Th2.getD 3 []) ∈ Th2) ∧
    (Th2.getD 1 [] ∈ Th2 ∧ Th2.getD 2 [] ∈ Th2 ∧ Th2.getD 1 [] ≠ Th2.getD 2 [] ∧
      comp (Th2.getD 1 []) (Th2.getD 2 []) ∈ Th2) := by
  decide +kernel

section Main

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c)

include hZ

theorem E4_G {w w' : G} (hw : w ∈ Theta c) (hw' : w' ∈ Theta c) (hne : w ≠ w')
    (hww : w * w' ∈ Theta c) :
    (w ∈ c.iso.imgG B1h ∧ w' ∈ c.iso.imgG B1h) ∨ (w ∈ c.iso.imgG B2h ∧ w' ∈ c.iso.imgG B2h) := by
  obtain ⟨hwA, hw1, hwz⟩ := hw
  obtain ⟨hwA', hw1', hwz'⟩ := hw'
  obtain ⟨hwwA, hww1, hwwz⟩ := hww
  obtain ⟨a, ha, rfl⟩ := c.iso.mem_imgG.1 hwA
  obtain ⟨a', ha', rfl⟩ := c.iso.mem_imgG.1 hwA'
  obtain ⟨la, hla, hrepa⟩ := ha
  obtain ⟨la', hla', hrepa'⟩ := ha'
  have hnz : ∀ {b : Bh} {l : PL}, (b : Ah) ∈ That → RepL l (b : P45) → ¬ IsConj (c.iso.toG b) z →
      l ∉ ZCl := fun {_} {l} hb hrep hc hl => hc ((hZ hb).2 ⟨l, hl, hrep⟩)
  have hn1 : ∀ {b : Bh} {l : PL}, RepL l (b : P45) → c.iso.toG b ≠ 1 → l ≠ idL := by
    intro b l hrep hb hl
    apply hb
    have h0 : b = 1 := Subtype.ext (Subtype.ext (eq_of_repL hrep (hl ▸ repL_one 45)))
    rw [h0, c.iso.toG_one]
  have hmem := fun {l : PL} (hl : l ∈ Al2) (h1 : l ≠ idL) (h2 : l ∉ ZCl) => mem_Th2_of hl h1 h2
  have hTa : (a : Ah) ∈ That := A2h_le_That ⟨la, hla, hrepa⟩
  have hTa' : (a' : Ah) ∈ That := A2h_le_That ⟨la', hla', hrepa'⟩
  have hla2 : la ∈ Th2 := hmem hla (hn1 hrepa hw1) (hnz hTa hrepa hwz)
  have hla2' : la' ∈ Th2 := hmem hla' (hn1 hrepa' hw1') (hnz hTa' hrepa' hwz')
  have hne' : la ≠ la' := by
    intro h
    apply hne
    have : a = a' := Subtype.ext (Subtype.ext (eq_of_repL hrepa (h ▸ hrepa')))
    rw [this]
  have hprod : RepL (comp la la') ((a * a' : Bh) : P45) := repL_mul hrepa hrepa'
  have hTaa : ((a * a' : Bh) : Ah) ∈ That := That.mul_mem hTa hTa'
  have hww1' : c.iso.toG (a * a') ≠ 1 := by
    rw [AutIso.toG_mul]; exact hww1
  have hwwz' : ¬ IsConj (c.iso.toG (a * a')) z := by
    rw [AutIso.toG_mul]; exact hwwz
  have hcomp : comp la la' ∈ Th2 :=
    hmem (A2_check.2.1 la hla la' hla') (hn1 hprod hww1') (hnz hTaa hprod hwwz')
  rcases E4_pair la hla2 la' hla2' hne' hcomp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨c.iso.mem_imgG.2 ⟨a, ⟨la, h1, hrepa⟩, rfl⟩,
      c.iso.mem_imgG.2 ⟨a', ⟨la', h2, hrepa'⟩, rfl⟩⟩
  · exact Or.inr ⟨c.iso.mem_imgG.2 ⟨a, ⟨la, h1, hrepa⟩, rfl⟩,
      c.iso.mem_imgG.2 ⟨a', ⟨la', h2, hrepa'⟩, rfl⟩⟩

theorem conjSub_B_cases {l₁ l₂ : PL} (hl₁ : l₁ ∈ Th2) (hl₂ : l₂ ∈ Th2) (hne : l₁ ≠ l₂)
    (hcl : comp l₁ l₂ ∈ Th2) {S : Subgroup Ah}
    (hS : ∀ a ∈ S, ∃ l ∈ [idL, l₁, l₂, comp l₁ l₂], RepL l (a : P45)) (hSB : S ≤ Bh)
    (hcard : Nat.card ↥S = 4) {n : G}
    (hn : n ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G)) :
    B6.conjSub n (c.iso.imgG S) = c.iso.imgG B1h ∨
      B6.conjSub n (c.iso.imgG S) = c.iso.imgG B2h := by
  have hl₁T : l₁ ∈ Thl := A2_check.2.2.2.1 l₁ (Th2_props hl₁).1
  have hl₂T : l₂ ∈ Thl := A2_check.2.2.2.1 l₂ (Th2_props hl₂).1
  have hclT : comp l₁ l₂ ∈ Thl := A2_check.2.2.2.1 _ (Th2_props hcl).1
  have hr1 : RepL l₁ (eltB l₁ : P45) := by
    rw [coe_eltB hl₁T]; exact repL_eltOfL hl₁T
  have hr2 : RepL l₂ (eltB l₂ : P45) := by
    rw [coe_eltB hl₂T]; exact repL_eltOfL hl₂T
  have hrc : RepL (comp l₁ l₂) (eltB (comp l₁ l₂) : P45) := by
    rw [coe_eltB hclT]; exact repL_eltOfL hclT
  set b₁ := c.iso.toG (eltB l₁) with hb₁
  set b₂ := c.iso.toG (eltB l₂) with hb₂
  have hb₁Θ : b₁ ∈ Theta c := toG_eltB_Th2 c hZ hl₁
  have hb₂Θ : b₂ ∈ Theta c := toG_eltB_Th2 c hZ hl₂
  have hb₁₂ : b₁ * b₂ ∈ Theta c := by
    have e : eltB (comp l₁ l₂) = eltB l₁ * eltB l₂ :=
      Subtype.ext (Subtype.ext (eq_of_repL hrc (repL_mul hr1 hr2)))
    have := toG_eltB_Th2 c hZ hcl
    rwa [e, AutIso.toG_mul] at this
  have hwΘ : n * b₁ * n⁻¹ ∈ Theta c := conj_Theta c hn hb₁Θ
  have hw'Θ : n * b₂ * n⁻¹ ∈ Theta c := conj_Theta c hn hb₂Θ
  have hwwΘ : (n * b₁ * n⁻¹) * (n * b₂ * n⁻¹) ∈ Theta c := by
    have := conj_Theta c hn hb₁₂
    have e : n * (b₁ * b₂) * n⁻¹ = (n * b₁ * n⁻¹) * (n * b₂ * n⁻¹) := by group
    rwa [e] at this
  have hne' : n * b₁ * n⁻¹ ≠ n * b₂ * n⁻¹ := by
    intro h
    apply hne
    have h1 : b₁ = b₂ := by
      have := congrArg (fun x => n⁻¹ * x * n) h
      simpa [mul_assoc] using this
    have h2 : eltB l₁ = eltB l₂ := c.iso.toG_injective h1
    have h3 : ((eltB l₁ : Ah) : P45) = ((eltB l₂ : Ah) : P45) := by rw [h2]
    exact repL_unique hr1 (h3 ▸ hr2)
  have hcardS : Nat.card ↥(B6.conjSub n (c.iso.imgG S)) = 4 := by
    rw [conjSub_card, c.iso.card_imgG hSB, hcard]
  have hf : ∀ y ∈ c.iso.imgG S, n * y * n⁻¹ = 1 ∨ n * y * n⁻¹ = n * b₁ * n⁻¹ ∨
      n * y * n⁻¹ = n * b₂ * n⁻¹ ∨ n * y * n⁻¹ = (n * b₁ * n⁻¹) * (n * b₂ * n⁻¹) := by
    intro y hy
    rcases mem_imgG_four c hl₁T hl₂T hS hy with h | h | h | h
    · left; rw [h]; group
    · right; left; rw [h]
    · right; right; left; rw [h]
    · right; right; right; rw [h, ← hb₁, ← hb₂]; group
  rcases E4_G c hZ hwΘ hw'Θ hne' hwwΘ with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
  · left
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · rw [B6.mem_conjSub] at hx
      have := hf _ hx
      have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
      rw [e] at this
      rcases this with h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact hw1
      · rw [h]; exact hw2
      · rw [h]; exact Subgroup.mul_mem _ hw1 hw2
    · rw [hcardS, c.iso.card_imgG (B1h_le_A2h.trans A2h_le_That |>.trans That_le_Bh), card_B1h]
  · right
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · rw [B6.mem_conjSub] at hx
      have := hf _ hx
      have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
      rw [e] at this
      rcases this with h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact hw1
      · rw [h]; exact hw2
      · rw [h]; exact Subgroup.mul_mem _ hw1 hw2
    · rw [hcardS, c.iso.card_imgG (B2h_le_A2h.trans A2h_le_That |>.trans That_le_Bh), card_B2h]

end Main

end CFSG.Quasithin.H13.F431.U42Aut
