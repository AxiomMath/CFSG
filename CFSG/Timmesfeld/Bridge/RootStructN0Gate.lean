module

public import CFSG.Timmesfeld.Bridge.RootStructR2Orbit
public import CFSG.Timmesfeld.Bridge.RootStructWTIFaithful

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def AllGates (D : Set G) (b x : G) : Prop :=
  ∀ a ∈ D, Commute b a → b * a ∈ D → a ∉ rootSet D b →
    ∃ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a ∧ orderOf (x * p) = 4

@[expose] def ThinAllBad (D : Set G) : Prop :=
  ∀ b ∈ D, ∀ x ∈ D, ¬ Commute b x → Odd (orderOf (b * x)) → OneOpposite D b x →
    ¬ AllGates D b x

@[expose] def ThinAllBadFalse : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStructE G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D →
    Moufang.ExcCollConnected D → ¬ ThreeLines D → AllLinesTI D → ThinAllBad D → False

theorem OneOpposite.conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {b x : G}
    (H : OneOpposite D b x) (g : G) : OneOpposite D (g * b * g⁻¹) (g * x * g⁻¹) := by
  obtain ⟨e, he, hbe, hbeD, h4⟩ := H
  refine ⟨g * e * g⁻¹, conj_mem_of_isClass hclass g he, (Commute.conj_iff g).2 hbe, ?_, ?_⟩
  · rw [show g * b * g⁻¹ * (g * e * g⁻¹) = g * (b * e) * g⁻¹ by group]
    exact conj_mem_of_isClass hclass g hbeD
  · rw [show g * x * g⁻¹ * (g * e * g⁻¹) = g * (x * e) * g⁻¹ by group, orderOf_conj_eq]
    exact h4

theorem AllGates.conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {b x : G}
    (H : AllGates D b x) (g : G) : AllGates D (g * b * g⁻¹) (g * x * g⁻¹) := by
  intro a ha hba hbaD haT
  have ha'D : g⁻¹ * a * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ ha
  have hga' : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  have hba' : Commute b (g⁻¹ * a * g) := by
    rw [← Commute.conj_iff g, hga']
    exact hba
  have hba'D : b * (g⁻¹ * a * g) ∈ D := by
    have := conj_mem_of_isClass hclass g⁻¹ hbaD
    rwa [show g⁻¹ * (g * b * g⁻¹ * a) * g⁻¹⁻¹ = b * (g⁻¹ * a * g) by group] at this
  have ha'T : g⁻¹ * a * g ∉ rootSet D b := fun h' => haT (by
    rw [rootSet_conj hclass]
    exact ⟨_, h', hga'⟩)
  obtain ⟨p, hp, hpL, h4⟩ := H _ ha'D hba' hba'D ha'T
  refine ⟨g * p * g⁻¹, conj_mem_of_isClass hclass g hp, ?_, ?_⟩
  · have hmap : (rootGroup D b ⊔ rootGroup D (g⁻¹ * a * g)).map (MulAut.conj g).toMonoidHom =
        rootGroup D (g * b * g⁻¹) ⊔ rootGroup D a := by
      rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass, hga']
    rw [← hmap]
    exact ⟨p, hpL, by simp⟩
  · rw [show g * x * g⁻¹ * (g * p * g⁻¹) = g * (x * p) * g⁻¹ by group, orderOf_conj_eq]
    exact h4

theorem AllGates.of_mem_rootSet (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {b b' x x' : G} (hb : b ∈ D) (hx : x ∈ D) (hb' : b' ∈ rootSet D b) (hx' : x' ∈ rootSet D x)
    (H : AllGates D b x) : AllGates D b' x' := by
  have hD := h.root
  intro a ha hb'a hb'aD haT
  have hTb : rootSet D b' = rootSet D b := rootSet_eq_of_mem hb'
  have haT' : a ∉ rootSet D b := by rwa [← hTb]
  have hab' : a * b' ∈ D := by rw [← hb'a.eq]; exact hb'aD
  obtain ⟨hba, hbaD⟩ := collinear_of_collinear_mem_rootSet h hc hs hb hb' ha hb'a.symm hab' haT'
  obtain ⟨p, hp, hpL, h4⟩ := H a ha hba hbaD haT'
  refine ⟨p, hp, ?_, (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx' hp).2 h4⟩
  have hA : rootGroup D b' = rootGroup D b := by rw [rootGroup, rootGroup, hTb]
  rw [hA]
  exact hpL

theorem AllGates.of_stabReach (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {a x y : G} (ha : a ∈ D) (hx : x ∈ D) (H : AllGates D a x) (hR : StabReach D a x y) :
    AllGates D a y := by
  obtain ⟨g, hga, hgy⟩ := hR
  have H1 := (H.of_mem_rootSet h hc hs ha hx hga hgy).conj h.isClass g⁻¹
  rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group,
    show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at H1

theorem allGates_of_allGates {G : Type} [Group G] {D : Set G} (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    {a x y : G} (ha : a ∈ D) (hx : x ∈ D) (hy : y ∈ D) (hax : ¬ Commute a x)
    (hoddax : Odd (orderOf (a * x))) (hay : ¬ Commute a y) (hodday : Odd (orderOf (a * y)))
    (H : AllGates D a x) (hy1 : OneOpposite D a y) : AllGates D a y := by
  have hD := h.root
  obtain ⟨cy, hcy, hacy, hacyD, h4y⟩ := hy1
  have hGy := GateConfig.of h hc hs hconn hAll ha hy hcy hacy hacyD hay hodday h4y
  obtain ⟨c, hcD, hcL, h4⟩ := H cy hcy hacy hacyD hGy.hcT
  have hac : Commute a c := commute_of_mem_sup_rootGroup ha hcy hacy (left_mem_line ha) hcL
  have hac1 : a * c ≠ 1 := by
    intro h1
    have hca : c = a := (eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq ha)
    rw [hca, orderOf_mul_comm_eq] at h4
    rw [h4] at hoddax
    exact absurd hoddax (by decide)
  have hacD : a * c ∈ D := mem_of_mem_sup_rootGroup h hc hs ha hcy hacy hacyD hGy.hcT
    (Subgroup.mul_mem _ (left_mem_line ha) hcL) hac1
  have hG := GateConfig.of h hc hs hconn hAll ha hx hcD hac hacD hax hoddax h4
  have hLeq : rootGroup D a ⊔ rootGroup D c = rootGroup D a ⊔ rootGroup D cy :=
    sup_rootGroup_eq_of_mem h hc hs ha hcy hacy hacyD hGy.hcT (left_mem_line ha) hcL
      (hD.ne_one ha) (hD.ne_one hcD) hG.hcT
  have hcyL : cy ∈ rootGroup D a ⊔ rootGroup D c := by
    rw [hLeq]
    exact right_mem_line hcy
  exact H.of_stabReach h hc hs ha hx (hG.stabReach_of_gate_mem_line h hc hs hconn hAll
    rootLinesRegularStep hy hay hodday hcy hacy hacyD h4y hcyL)

theorem thinGate_or_thinAllBad {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) : ThinGate D ∨ ThinAllBad D := by
  by_cases hbad : ThinAllBad D
  · exact Or.inr hbad
  refine Or.inl ?_
  have hclass := h.isClass
  obtain ⟨a₀, ha₀, x₀, hx₀, hax₀, hodd₀, H₀⟩ : ∃ a₀ ∈ D, ∃ x₀ ∈ D, ¬ Commute a₀ x₀ ∧
      Odd (orderOf (a₀ * x₀)) ∧ AllGates D a₀ x₀ := by
    by_contra hno
    exact hbad fun b hb x hx hbx hodd _ hall => hno ⟨b, hb, x, hx, hbx, hodd, hall⟩
  intro b hb x hx hbx hoddbx h1
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass ha₀ hb)
  have hyD : g⁻¹ * x * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ hx
  have hgy : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  have hay : ¬ Commute a₀ (g⁻¹ * x * g) := by
    rw [← Commute.conj_iff g, hgy]
    exact hbx
  have hodday : Odd (orderOf (a₀ * (g⁻¹ * x * g))) := by
    rw [show a₀ * (g⁻¹ * x * g) = g⁻¹ * (g * a₀ * g⁻¹ * x) * g⁻¹⁻¹ by group, orderOf_conj_eq]
    exact hoddbx
  have hy1 : OneOpposite D a₀ (g⁻¹ * x * g) := by
    have := h1.conj hclass g⁻¹
    rwa [show g⁻¹ * (g * a₀ * g⁻¹) * g⁻¹⁻¹ = a₀ by group,
      show g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g by group] at this
  have H := (allGates_of_allGates h hc hs hconn hAll ha₀ hx₀ hyD hax₀ hodd₀ hay hodday H₀
    hy1).conj hclass g
  rw [hgy] at H
  exact H

theorem thinTwoStepE_of_thinAllBadFalse (H : ThinAllBadFalse) : ThinTwoStepE := by
  intro G _ D hH IH hl hc hs hconn h3
  refine thinOneOpposite_of_gate hH hc hs fun a ha d hd had hadD hdT hTI => ?_
  have hAll := allLinesTI_of_lineTI hH hc hs hconn ha hd had hadD hdT hTI
  rcases thinGate_or_thinAllBad hH hc hs hconn hAll with hg | hbad
  · exact hg
  · exact (H G D hH IH hl hc hs hconn h3 hAll hbad).elim

end CFSG.Timmesfeld.Bridge
