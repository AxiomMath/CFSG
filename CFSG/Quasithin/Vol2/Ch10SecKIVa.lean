module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Basic

variable {G : Type} [Group G]

theorem card_eq_sixty {B : Subgroup G} (h : IsAlt 5 ↥B) : Nat.card B = 60 := by
  obtain ⟨a⟩ := h
  rw [Nat.card_congr a.toEquiv, Dickson.card_alt_five]

theorem isSimpleGroup_of_isAlt {B : Subgroup G} (h : IsAlt 5 ↥B) : IsSimpleGroup ↥B := by
  obtain ⟨a⟩ := h
  have : Finite ↥B := Finite.of_equiv _ a.symm.toEquiv
  have : Nontrivial ↥B := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [card_eq_sixty ⟨a⟩]
    norm_num)
  exact IsSimpleGroup.isSimpleGroup_of_surjective a.symm.toMonoidHom a.symm.surjective

theorem eq_of_card_sup_eq [Finite G] {B₁ B₂ : Subgroup G}
    (h₁ : Nat.card ↥(B₁ ⊔ B₂) = Nat.card B₁) (h₂ : Nat.card ↥(B₁ ⊔ B₂) = Nat.card B₂) :
    B₁ = B₂ :=
  (Subgroup.eq_of_le_of_card_ge le_sup_left h₁.le).trans
    (Subgroup.eq_of_le_of_card_ge le_sup_right h₂.le).symm

theorem eq_top_of_map_eq_top {Z : Type} [Group Z] (e : G ≃* Z) {H : Subgroup G}
    (h : H.map e.toMonoidHom = ⊤) : H = ⊤ := by
  have := congrArg (Subgroup.comap e.toMonoidHom) h
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this

end Basic


theorem sup_eq_top_psl2_prime {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hY : IsPSL 2 p 1 Y) {B₁ B₂ : Subgroup Y} (h₁ : IsAlt 5 ↥B₁)
    (h₂ : IsAlt 5 ↥B₂) (hne : B₁ ≠ B₂) : B₁ ⊔ B₂ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := Vol2Native.A312L.equiv_psl2_zmod_of_model hY
  obtain ⟨a₁⟩ := h₁
  have hM : Nonempty (↥(B₁.map e.toMonoidHom) ≃* alternatingGroup (Fin 5)) :=
    ⟨(B₁.equivMapOfInjective e.toMonoidHom e.injective).symm.trans a₁⟩
  rcases Dickson.overgroup_alternating_five_psl2_prime hp2
      (Subgroup.map_mono (le_sup_left : B₁ ≤ B₁ ⊔ B₂)) hM with h | h
  · exact eq_top_of_map_eq_top e h
  · exfalso
    have hc : Nat.card ↥(B₁ ⊔ B₂) = 60 :=
      (Nat.card_congr ((B₁ ⊔ B₂).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans h
    exact hne (eq_of_card_sup_eq (hc.trans (card_eq_sixty ⟨a₁⟩).symm)
      (hc.trans (card_eq_sixty h₂).symm))

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV
