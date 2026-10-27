module

public import CFSG.Monster.B.GSide.BT2Reduce

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : V → V → V → Prop}

variable (G T) in
@[expose] def TriRel (x a b b' : V) : Prop :=
  ∀ (h₁ : G.Adj x a) (h₂ : G.Adj a b) (h₃ : G.Adj b x) (h₂' : G.Adj a b') (h₃' : G.Adj b' x),
    HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁ h₂' h₃')

theorem TriRel.refl (x a b : V) : TriRel G T x a b b := fun _ _ _ _ _ => HomotopicT.refl _

theorem TriRel.symm {x a b b' : V} (h : TriRel G T x a b b') : TriRel G T x a b' b :=
  fun h₁ h₂ h₃ h₂' h₃' => (h h₁ h₂' h₃' h₂ h₃).symm

theorem TriRel.trans {x a b b' b'' : V} (hab' : G.Adj a b') (hb'x : G.Adj b' x)
    (h : TriRel G T x a b b') (h' : TriRel G T x a b' b'') : TriRel G T x a b b'' :=
  fun h₁ h₂ h₃ h₂'' h₃'' => (h h₁ h₂ h₃ hab' hb'x).trans (h' h₁ hab' hb'x h₂'' h₃'')

theorem TriRel.map {V' : Type*} {G' : SimpleGraph V'} {T' : V' → V' → V' → Prop} (f : G →g G')
    (hf : ∀ u w z, T u w z → T' (f u) (f w) (f z)) {x a b b' : V}
    (hxa : G.Adj x a) (hab : G.Adj a b) (hbx : G.Adj b x) (hab' : G.Adj a b')
    (hb'x : G.Adj b' x) (h : TriRel G T x a b b') : TriRel G' T' (f x) (f a) (f b) (f b') :=
  fun _ _ _ _ _ => HomotopicT.map f hf (h hxa hab hbx hab' hb'x)

theorem edgeConst_of_triRel {x a : V}
    (h : ∀ b b', G.Adj a b → G.Adj b x → ¬ T x a b → G.Adj a b' → G.Adj b' x → ¬ T x a b' →
      TriRel G T x a b b') : EdgeConst G T x a :=
  fun b b' h₁ h₂ h₃ h₂' h₃' hb hb' => h b b' h₂ h₃ hb h₂' h₃' hb' h₁ h₂ h₃ h₂' h₃'

theorem homotopicT_triLoop_nil {x a c : V} (h₁ : G.Adj x a) (h₂ : G.Adj a c) (h₃ : G.Adj c x)
    (hT : T x a c) : HomotopicT T (triLoop h₁ h₂ h₃) .nil := by
  have h := (ElemMoveT.triangle (T := T) (.nil : G.Walk x x) .nil h₁ h₂ h₃ hT).homotopicT
  simpa [triLoop] using h.symm

section Action

variable {X : Type*} [Group X] [MulAction X V]
  (hadj : ∀ (g : X) {u w : V}, G.Adj u w → G.Adj (g • u) (g • w))
  (hT : ∀ (g : X) {u w z : V}, T u w z → T (g • u) (g • w) (g • z))
include hadj hT

theorem TriRel.smul {x a : V} {g : X} (hg : g • x = x ∧ g • a = a) {b b' : V}
    (hab : G.Adj a b) (hbx : G.Adj b x) (hab' : G.Adj a b') (hb'x : G.Adj b' x)
    (h : TriRel G T x a b b') : TriRel G T x a (g • b) (g • b') := by
  intro h₁ h₂ h₃ h₂' h₃'
  have h₁' : G.Adj (g • x) (g • a) := hadj g h₁
  have e := TriRel.map (G := G) (T := T) (T' := T) ⟨fun v => g • v, hadj g⟩
    (fun _ _ _ ht => hT g ht) h₁
    hab hbx hab' hb'x h
  change TriRel G T (g • x) (g • a) (g • b) (g • b') at e
  rw [hg.1, hg.2] at e
  exact e h₁ h₂ h₃ h₂' h₃'

theorem edgeConst_of_bridge {x a : V} (A M : Subgroup X) (hA : ∀ g ∈ A, g • x = x ∧ g • a = a)
    (hMA : M ≤ A) {b₀ : V} (hb₀ : G.Adj a b₀ ∧ G.Adj b₀ x ∧ ¬ T x a b₀)
    (htrans : ∀ b, G.Adj a b → G.Adj b x → ¬ T x a b → ∃ g ∈ A, g • b₀ = b)
    (S₀ : Set V) (hS₀ : ∀ s ∈ S₀, s ≠ b₀ → G.Adj b₀ s)
    (hK1 : ∀ g ∈ M, TriRel G T x a b₀ (g • b₀))
    (hmax : ∀ g ∈ A, g • b₀ ∉ S₀ → A ≤ M ⊔ Subgroup.zpowers g)
    {c₀ c₁ : V} (hc₀ : G.Adj a c₀ ∧ G.Adj c₀ x ∧ ¬ T x a c₀)
    (hc₁ : G.Adj a c₁ ∧ G.Adj c₁ x ∧ ¬ T x a c₁) (hne : c₀ ≠ c₁) (hnadj : ¬ G.Adj c₀ c₁)
    (hbridge : TriRel G T x a c₀ c₁) : EdgeConst G T x a := by
  have hadjA : ∀ g ∈ A, G.Adj a (g • b₀) ∧ G.Adj (g • b₀) x := by
    intro g hg
    have h1 := hadj g hb₀.1
    have h2 := hadj g hb₀.2.1
    rw [(hA g hg).2] at h1
    rw [(hA g hg).1] at h2
    exact ⟨h1, h2⟩
  let H : Subgroup X :=
    { carrier := {g | g ∈ A ∧ TriRel G T x a b₀ (g • b₀)}
      one_mem' := ⟨A.one_mem, by rw [one_smul]; exact TriRel.refl _ _ _⟩
      mul_mem' := by
        rintro g h ⟨hgA, hg⟩ ⟨hhA, hh⟩
        refine ⟨A.mul_mem hgA hhA, ?_⟩
        have hg' := TriRel.smul hadj hT (hA g hgA) hb₀.1 hb₀.2.1 (hadjA h hhA).1
          (hadjA h hhA).2 hh
        rw [mul_smul]
        exact hg.trans (hadjA g hgA).1 (hadjA g hgA).2 hg'
      inv_mem' := by
        rintro g ⟨hgA, hg⟩
        refine ⟨A.inv_mem hgA, ?_⟩
        have hgi : g⁻¹ • x = x ∧ g⁻¹ • a = a := by
          rw [inv_smul_eq_iff, inv_smul_eq_iff]
          exact ⟨(hA g hgA).1.symm, (hA g hgA).2.symm⟩
        have e := TriRel.smul hadj hT hgi hb₀.1 hb₀.2.1 (hadjA g hgA).1 (hadjA g hgA).2 hg
        rw [inv_smul_smul] at e
        exact e.symm }
  have hMH : M ≤ H := fun g hg => ⟨hMA hg, hK1 g hg⟩
  obtain ⟨h, hhA, rfl⟩ := htrans c₀ hc₀.1 hc₀.2.1 hc₀.2.2
  obtain ⟨k, hkA, rfl⟩ := htrans c₁ hc₁.1 hc₁.2.1 hc₁.2.2
  have hhi : h⁻¹ • x = x ∧ h⁻¹ • a = a := by
    rw [inv_smul_eq_iff, inv_smul_eq_iff]
    exact ⟨(hA h hhA).1.symm, (hA h hhA).2.symm⟩
  have hgA : h⁻¹ * k ∈ A := A.mul_mem (A.inv_mem hhA) hkA
  have hgH : h⁻¹ * k ∈ H := by
    refine ⟨hgA, ?_⟩
    have e := TriRel.smul hadj hT hhi hc₀.1 hc₀.2.1 hc₁.1 hc₁.2.1 hbridge
    rwa [inv_smul_smul, ← mul_smul] at e
  have hgS : (h⁻¹ * k) • b₀ ∉ S₀ := by
    intro hS
    have hne' : (h⁻¹ * k) • b₀ ≠ b₀ := by
      intro e
      apply hne
      rw [mul_smul, inv_smul_eq_iff] at e
      exact e.symm
    have hb := hadj h (hS₀ _ hS hne')
    rw [mul_smul, smul_inv_smul] at hb
    exact hnadj hb
  have hAH : A ≤ H :=
    (hmax _ hgA hgS).trans (sup_le hMH ((Subgroup.zpowers_le).2 hgH))
  refine edgeConst_of_triRel fun b b' hab hbx hb hab' hb'x hb' => ?_
  obtain ⟨g₁, hg₁A, rfl⟩ := htrans b hab hbx hb
  obtain ⟨g₂, hg₂A, rfl⟩ := htrans b' hab' hb'x hb'
  exact (hAH hg₁A).2.symm.trans hb₀.1 hb₀.2.1 (hAH hg₂A).2

theorem edgeConst_of_bridge_good {x a : V} (A : Subgroup X)
    (hA : ∀ g ∈ A, g • x = x ∧ g • a = a) {b₀ c : V} (hb₀ : G.Adj a b₀ ∧ G.Adj b₀ x)
    (htrans : ∀ b, G.Adj a b → G.Adj b x → ¬ T x a b → ∃ g ∈ A, g • b₀ = b)
    (hc : G.Adj a c ∧ G.Adj c x ∧ T x a c) (hbridge : TriRel G T x a b₀ c) :
    EdgeConst G T x a := by
  have hnull : ∀ b, G.Adj a b → G.Adj b x → ¬ T x a b → ∀ (h₁ : G.Adj x a)
      (h₂ : G.Adj a b) (h₃ : G.Adj b x), HomotopicT T (triLoop h₁ h₂ h₃) .nil := by
    intro b hab hbx hb h₁ h₂ h₃
    obtain ⟨g, hgA, rfl⟩ := htrans b hab hbx hb
    have hgc : G.Adj a (g • c) ∧ G.Adj (g • c) x := by
      have e1 := hadj g hc.1
      have e2 := hadj g hc.2.1
      rw [(hA g hgA).2] at e1
      rw [(hA g hgA).1] at e2
      exact ⟨e1, e2⟩
    have hT' : T x a (g • c) := by
      have e := hT g hc.2.2
      rwa [(hA g hgA).1, (hA g hgA).2] at e
    have e := TriRel.smul hadj hT (hA g hgA) hb₀.1 hb₀.2 hc.1 hc.2.1 hbridge
    exact (e h₁ h₂ h₃ hgc.1 hgc.2).trans (homotopicT_triLoop_nil h₁ hgc.1 hgc.2 hT')
  intro b b' h₁ h₂ h₃ h₂' h₃' hb hb'
  exact (hnull b h₂ h₃ hb h₁ h₂ h₃).trans (hnull b' h₂' h₃' hb' h₁ h₂' h₃').symm

end Action

end CFSG.Monster.B.GSide
