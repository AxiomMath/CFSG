module

public import CFSG.Timmesfeld.Transvection.Basic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem commuting_conjSub_mul_iff_of_mul_self (E : Subgroup G) {x : G} (y : G)
    (hxx : x * x = 1) :
    Commuting E (conjSub E (x * y)) ↔ Commuting (conjSub E x) (conjSub E y) := by
  have h := Aux.commuting_conjSub_iff (X := E) (Y := conjSub E (x * y)) x
  rw [← h, ← conjSub_mul, show x * (x * y) = y by rw [← mul_assoc, hxx, one_mul]]

theorem not_commuting_conjSub [Finite G] (hΔ : IsTransvectionClass Δ) {P Q : Subgroup G}
    (hQ : Q ∈ Δ) (hPQ : Opposite P Q) {x : G} (hx : x ∈ P) (hx1 : x ≠ 1) :
    ¬ Commuting Q (conjSub Q x) := by
  intro hc
  have hne : conjSub Q x ≠ Q := fun h => hx1 (hPQ.eq_one_of_conjSub_eq hx h)
  obtain ⟨u, hu, hu1⟩ := hΔ.root.exists_ne_one hQ
  obtain ⟨w, hw, hw1⟩ := hΔ.root.exists_ne_one (hΔ.root.conjSub_mem hQ x)
  have hu' : u ∈ conjSub Q 1 := by rwa [conjSub_one]
  have := hPQ.symm.conjSub_eq_of_commute (hΔ.root.mul_self Q hQ) (one_mem _)
    (Subgroup.mem_sup_right hx) hu' hu1 hw hw1 (hc u hu w hw)
  rw [conjSub_one] at this
  exact hne this

theorem partner_partner {E A : Subgroup G} (hEA : Opposite E A) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) : partner A E (partner E A e) = e :=
  (eq_partner hEA.symm (partner_mem hEA he he1) (partner_ne_one hEA he he1) he
    (conjSub_partner hEA he he1).symm).symm

section FourOne

variable [Finite G] (hΔ : IsTransvectionClass Δ) {A C E : Subgroup G}
include hΔ

omit [Finite G] in
theorem commuting_conjSub_partner_mul (hA : A ∈ Δ) (hcAC : Commuting A C) (hEA : Opposite E A)
    (hEC : Opposite E C) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    Commuting E (conjSub E (partner E A e * partner E C e)) := by
  rw [commuting_conjSub_mul_iff_of_mul_self E _
    (hΔ.root.mul_self A hA _ (partner_mem hEA he he1)), conjSub_partner hEA he he1,
    conjSub_partner hEC he he1]
  exact hcAC.conjSub e

theorem commuting_conjSub_mul_iff (hA : A ∈ Δ) (hE : E ∈ Δ) (hcAC : Commuting A C)
    (hEA : Opposite E A) (hEC : Opposite E C) {a c : G} (ha : a ∈ A) (hc : c ∈ C) :
    Commuting E (conjSub E (a * c)) ↔
      (a = 1 ∧ c = 1) ∨ ∃ e ∈ E, e ≠ 1 ∧ a = partner E A e ∧ c = partner E C e := by
  constructor
  · intro h
    by_cases ha1 : a = 1
    · subst ha1
      rw [one_mul] at h
      by_cases hc1 : c = 1
      · exact Or.inl ⟨rfl, hc1⟩
      · exact absurd h (not_commuting_conjSub hΔ hE hEC.symm hc hc1)
    by_cases hc1 : c = 1
    · subst hc1
      rw [mul_one] at h
      exact absurd h (not_commuting_conjSub hΔ hE hEA.symm ha ha1)
    set e := partner A E a with he_def
    have he := partner_mem hEA.symm ha ha1
    have he1 := partner_ne_one hEA.symm ha ha1
    have hae : a = partner E A e := (partner_partner hEA.symm ha ha1).symm
    refine Or.inr ⟨e, he, he1, hae, ?_⟩
    by_contra hcne
    set c₀ := partner E C e with hc₀_def
    have hc₀ := partner_mem hEC he he1
    have haa := hΔ.root.mul_self A hA a ha
    have h₀ := commuting_conjSub_partner_mul hΔ hA hcAC hEA hEC he he1
    rw [← hae] at h₀
    rw [commuting_conjSub_mul_iff_of_mul_self E _ haa] at h h₀
    have hne : conjSub E c ≠ conjSub E c₀ := by
      intro heq
      have hn : conjSub E (c₀⁻¹ * c) = E := by
        rw [conjSub_mul, heq, ← conjSub_mul, inv_mul_cancel, conjSub_one]
      have := hEC.symm.eq_one_of_conjSub_eq (C.mul_mem (C.inv_mem hc₀) hc) hn
      rw [inv_mul_eq_one] at this
      exact hcne this.symm
    have hsup := hEC.sup_conjSub_eq (hΔ.root.mul_self E hE) (Subgroup.mem_sup_right hc)
      (Subgroup.mem_sup_right hc₀) hne
    have hcE : Commuting (conjSub E a) E := by
      have := Commuting.sup_right h h₀
      rw [hsup] at this
      exact this.mono le_rfl le_sup_left
    exact not_commuting_conjSub hΔ hE hEA.symm ha ha1 hcE.symm
  · rintro (⟨rfl, rfl⟩ | ⟨e, he, he1, rfl, rfl⟩)
    · rw [mul_one, conjSub_one]
      exact hΔ.root.commuting_self hE
    · exact commuting_conjSub_partner_mul hΔ hA hcAC hEA hEC he he1

end FourOne

@[expose] def graphSet (A : Subgroup G) (g : G) : Set G :=
  (fun a => a * (g * a * g⁻¹)) '' (A : Set G)

@[expose] def graph (A : Subgroup G) (g : G) : Subgroup G :=
  Subgroup.closure (graphSet A g)

section Graph

variable {A : Subgroup G} {g : G} (hAg : Commuting A (conjSub A g))
include hAg

theorem graphSet_mul {x y : G} (hx : x ∈ graphSet A g) (hy : y ∈ graphSet A g) :
    x * y ∈ graphSet A g := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨a * b, A.mul_mem ha hb, ?_⟩
  have hcomm : Commute (g * a * g⁻¹) b := (hAg b hb _ (conj_mem_conjSub g ha)).symm
  calc a * b * (g * (a * b) * g⁻¹) = a * (b * (g * a * g⁻¹)) * (g * b * g⁻¹) := by group
    _ = a * (g * a * g⁻¹ * b) * (g * b * g⁻¹) := by rw [hcomm.eq]
    _ = a * (g * a * g⁻¹) * (b * (g * b * g⁻¹)) := by group

theorem graphSet_inv {x : G} (hx : x ∈ graphSet A g) : x⁻¹ ∈ graphSet A g := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a⁻¹, A.inv_mem ha, ?_⟩
  have hcomm : Commute a⁻¹ (g * a⁻¹ * g⁻¹) :=
    hAg a⁻¹ (A.inv_mem ha) _ (conj_mem_conjSub g (A.inv_mem ha))
  show a⁻¹ * (g * a⁻¹ * g⁻¹) = (a * (g * a * g⁻¹))⁻¹
  rw [hcomm.eq]
  group

theorem mem_graph_iff {x : G} : x ∈ graph A g ↔ ∃ a ∈ A, x = a * (g * a * g⁻¹) := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun y _ => ∃ a ∈ A, y = a * (g * a * g⁻¹))
      (fun y hy => ?_) ⟨1, A.one_mem, by group⟩ (fun y z _ _ hy hz => ?_)
      (fun y _ hy => ?_) hx
    · obtain ⟨a, ha, rfl⟩ := hy
      exact ⟨a, ha, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      obtain ⟨c, hc, hc'⟩ := graphSet_mul hAg ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨c, hc, hc'.symm⟩
    · obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨c, hc, hc'⟩ := graphSet_inv hAg ⟨a, ha, rfl⟩
      exact ⟨c, hc, hc'.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.subset_closure ⟨a, ha, rfl⟩

end Graph

section FourTwo

variable [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) {A E : Subgroup G}
  {g : G}
include hΔ hiso

omit [Finite G] hΔ hiso in
theorem partner_conjSub_of_commute (hEA : Opposite E A) (hgE : ∀ x ∈ E, Commute g x) {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) :
    partner E (conjSub A g) e = g * partner E A e * g⁻¹ := by
  have h := partner_conj hEA he he1 g
  rwa [Aux.conjSub_eq_of_commute hgE, (hgE e he).eq, mul_inv_cancel_right] at h

theorem commuting_conjSub_iff_mem_graph (hA : A ∈ Δ) (hE : E ∈ Δ)
    (hAg : Commuting A (conjSub A g)) (hne : A ≠ conjSub A g) (hEA : Opposite E A)
    (hgE : ∀ x ∈ E, Commute g x) {a a' : G} (ha : a ∈ A) (ha' : a' ∈ conjSub A g) :
    Commuting E (conjSub E (a * a')) ↔ a * a' ∈ graph A g := by
  have hEAg : Opposite E (conjSub A g) := by
    have := hEA.conj g
    rwa [Aux.conjSub_eq_of_commute hgE] at this
  rw [commuting_conjSub_mul_iff hΔ hA hE hAg hEA hEAg ha ha', mem_graph_iff hAg]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨e, he, he1, rfl, rfl⟩)
    · exact ⟨1, A.one_mem, by group⟩
    · exact ⟨partner E A e, partner_mem hEA he he1, by
        rw [partner_conjSub_of_commute hEA hgE he he1]⟩
  · rintro ⟨b, hb, hab⟩
    have hbot := hΔ.inf_eq_bot hiso hA (hΔ.root.conjSub_mem hA g) hne
    have hgb : g * b * g⁻¹ ∈ conjSub A g := conj_mem_conjSub g hb
    have hx : b⁻¹ * a ∈ A ⊓ conjSub A g := by
      refine ⟨A.mul_mem (A.inv_mem hb) ha, ?_⟩
      have : b⁻¹ * a = g * b * g⁻¹ * a'⁻¹ := by
        calc b⁻¹ * a = b⁻¹ * (a * a') * a'⁻¹ := by group
          _ = b⁻¹ * (b * (g * b * g⁻¹)) * a'⁻¹ := by rw [hab]
          _ = g * b * g⁻¹ * a'⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hgb (Subgroup.inv_mem _ ha')
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hx
    subst hx
    have ha'b : a' = g * b * g⁻¹ := by
      have := hab
      rwa [mul_right_inj] at this
    by_cases hb1 : b = 1
    · subst hb1
      left
      exact ⟨rfl, by rw [ha'b]; group⟩
    · right
      refine ⟨partner A E b, partner_mem hEA.symm hb hb1, partner_ne_one hEA.symm hb hb1,
        (partner_partner hEA.symm hb hb1).symm, ?_⟩
      rw [ha'b, partner_conjSub_of_commute hEA hgE (partner_mem hEA.symm hb hb1)
        (partner_ne_one hEA.symm hb hb1), partner_partner hEA.symm hb hb1]

theorem commuting_conjSub_graph (hA : A ∈ Δ) (hE : E ∈ Δ)
    (hAg : Commuting A (conjSub A g)) (hne : A ≠ conjSub A g) (hEA : Opposite E A)
    (hgE : ∀ x ∈ E, Commute g x) {τ τ' : G} (hτ : τ ∈ graph A g) (hτ' : τ' ∈ graph A g) :
    Commuting (conjSub E τ) (conjSub E τ') := by
  obtain ⟨b, hb, rfl⟩ := (mem_graph_iff hAg).1 hτ
  have hgb : g * b * g⁻¹ ∈ conjSub A g := conj_mem_conjSub g hb
  have hττ : b * (g * b * g⁻¹) * (b * (g * b * g⁻¹)) = 1 := by
    have h1 := hΔ.root.mul_self A hA b hb
    have h2 := hΔ.root.mul_self _ (hΔ.root.conjSub_mem hA g) _ hgb
    have hc : Commute b (g * b * g⁻¹) := hAg b hb _ hgb
    calc b * (g * b * g⁻¹) * (b * (g * b * g⁻¹)) =
          b * (g * b * g⁻¹ * b) * (g * b * g⁻¹) := by group
      _ = b * (b * (g * b * g⁻¹)) * (g * b * g⁻¹) := by rw [hc.symm.eq]
      _ = (b * b) * ((g * b * g⁻¹) * (g * b * g⁻¹)) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  rw [← commuting_conjSub_mul_iff_of_mul_self E τ' hττ]
  obtain ⟨c, hc, rfl⟩ := (mem_graph_iff hAg).1 hτ'
  have hmem : b * (g * b * g⁻¹) * (c * (g * c * g⁻¹)) ∈ graph A g :=
    Subgroup.mul_mem _ hτ hτ'
  have hrw : b * (g * b * g⁻¹) * (c * (g * c * g⁻¹)) = (b * c) * (g * (b * c) * g⁻¹) := by
    have hcb : Commute (g * b * g⁻¹) c := (hAg c hc _ hgb).symm
    calc b * (g * b * g⁻¹) * (c * (g * c * g⁻¹)) =
          b * ((g * b * g⁻¹) * c) * (g * c * g⁻¹) := by group
      _ = b * (c * (g * b * g⁻¹)) * (g * c * g⁻¹) := by rw [hcb.eq]
      _ = (b * c) * (g * (b * c) * g⁻¹) := by group
  rw [hrw] at hmem ⊢
  exact (commuting_conjSub_iff_mem_graph hΔ hiso hA hE hAg hne hEA hgE (A.mul_mem hb hc)
    (conj_mem_conjSub g (A.mul_mem hb hc))).2 hmem

end FourTwo

end CFSG.Timmesfeld.Transvection
