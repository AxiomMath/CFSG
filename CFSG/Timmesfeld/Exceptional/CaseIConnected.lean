module

public import CFSG.Timmesfeld.Exceptional.CaseIReduction

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def ExcCollConnected (D : Set G) : Prop :=
  ∀ S ⊆ D, S.Nonempty → (∀ x ∈ S, ∀ y ∈ D, Commute x y → x * y ∈ D → y ∈ S) → D ⊆ S

theorem exists_levi_collinear_of_collConnected [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D)
    (hC : ExcCollConnected D) {x y u : G} (hx : x ∈ D) (hy : y ∈ D) (hu : u ∈ D)
    (hxy : ¬ Commute x y) (hodd : Odd (orderOf (x * y))) (hux : Commute u x)
    (huy : Commute u y) :
    ∃ a ∈ D, ∃ b ∈ D, ∃ v ∈ D, ∃ z ∈ D, ¬ Commute a b ∧ Odd (orderOf (a * b)) ∧
      Commute v a ∧ Commute v b ∧ Commute a z ∧ a * z ∈ D ∧ Commute v z ∧ v * z ∈ D := by
  by_contra hne
  have key : ∀ a ∈ D, ∀ b ∈ D, ¬ Commute a b → Odd (orderOf (a * b)) → ∀ v ∈ D,
      Commute v a → Commute v b → ∀ f ∈ D, Commute v f → v * f ∈ D → Commute a f := by
    intro a ha b hb hab hoddab v hv hva hvb f hf hvf hvfD
    by_contra haf
    obtain ⟨hzD, haz, hazD, hvz, hvzD⟩ :=
      collinear_sq_of_pq hclass hD hPQ ha hb hv hf hab hoddab hva hvb hvf hvfD haf
    exact hne ⟨a, ha, b, hb, v, hv, _, hzD, hab, hoddab, hva, hvb, haz, hazD, hvz, hvzD⟩
  have hyx : ¬ Commute y x := fun h => hxy h.symm
  have hoddyx : Odd (orderOf (y * x)) := by rwa [orderOf_mul_comm_eq]
  have hall := hC {v | v ∈ D ∧ Commute v x ∧ Commute v y} (fun v hv => hv.1) ⟨u, hu, hux, huy⟩
    (by
      rintro v ⟨hv, hvx, hvy⟩ f hf hvf hvfD
      exact ⟨hf, (key x hx y hy hxy hodd v hv hvx hvy f hf hvf hvfD).symm,
        (key y hy x hx hyx hoddyx v hv hvy hvx f hf hvf hvfD).symm⟩)
  exact hxy (hall hy).2.1.symm

theorem false_of_exceptional_levi_of_collConnected [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D)
    (hC : ExcCollConnected D) (hP1 : ExcP1 D) {d c u : G} (hd : d ∈ D) (hc : c ∈ D)
    (hu : u ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c)))
    (h3 : orderOf (d * c) ≠ 3) (hud : Commute u d) (huc : Commute u c) : False := by
  have hcd : ¬ Commute c d := fun h => hdc h.symm
  have hoddc : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
  have h3c : orderOf (c * d) ≠ 3 := by rwa [orderOf_mul_comm_eq]
  have key : ∀ a ∈ D, ∀ b ∈ D, ¬ Commute a b → Odd (orderOf (a * b)) →
      orderOf (a * b) ≠ 3 → ∀ v ∈ D, Commute v a → Commute v b → ∀ f ∈ D, Commute v f →
      v * f ∈ D → Commute a f := by
    intro a ha b hb hab hoddab h3ab v hv hva hvb f hf hvf hvfD
    by_contra haf
    obtain ⟨hzD, haz, hazD, hvz, hvzD⟩ :=
      collinear_sq_of_pq hclass hD hPQ ha hb hv hf hab hoddab hva hvb hvf hvfD haf
    exact h3ab (hP1 a ha b hb hab hoddab _ hzD haz hazD
      (orderOf_mul_eq_four_of_collinear_of_commute hD hb hzD hv hab hoddab haz hazD hvz hvzD hvb))
  have hall := hC {v | v ∈ D ∧ Commute v d ∧ Commute v c} (fun v hv => hv.1) ⟨u, hu, hud, huc⟩
    (by
      rintro v ⟨hv, hvd, hvc⟩ f hf hvf hvfD
      exact ⟨hf, (key d hd c hc hdc hodd h3 v hv hvd hvc f hf hvf hvfD).symm,
        (key c hc d hd hcd hoddc h3c v hv hvc hvd f hf hvf hvfD).symm⟩)
  exact hdc (hall hc).2.1.symm

theorem leviOrderThree_of_collConnected [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D) (hC : ExcCollConnected D) (hP1 : ExcP1 D) :
    LeviOrderThree D := fun _ hx _ hy hxy hodd _ hb hbx hby => by
  by_contra h3
  exact false_of_exceptional_levi_of_collConnected hclass hD hPQ hC hP1 hx hy hb hxy hodd h3 hbx
    hby

end CFSG.Timmesfeld.Moufang
