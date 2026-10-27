module

public import CFSG.Timmesfeld.Bridge.RootStructBridge

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def OneOpposite (D : Set G) (a x : G) : Prop :=
  ∃ e ∈ D, Commute a e ∧ a * e ∈ D ∧ orderOf (x * e) = 4

@[expose] def OneOppositeClosed (D : Set G) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, ∀ x ∈ D, Commute a b → a * b ∈ D → ¬ Commute a x → Odd (orderOf (a * x)) →
    ¬ Commute b x → Odd (orderOf (b * x)) → OneOpposite D b x → OneOpposite D a x

theorem oneOpposite_of_collConnected (hD : IsRootInvolutionSet D)
    (hconn : Moufang.ExcCollConnected D) (hK : OneOppositeClosed D) {a x : G} (ha : a ∈ D)
    (hx : x ∈ D) (hax : ¬ Commute a x) (hodd : Odd (orderOf (a * x))) : OneOpposite D a x := by
  have hS := hconn {b | b ∈ D ∧ (¬ Commute b x → Odd (orderOf (b * x)) → OneOpposite D b x)}
    (fun b hb => hb.1) ⟨x, hx, fun h => absurd (Commute.refl x) h⟩ (by
      rintro b ⟨hb, hbS⟩ y hy hby hbyD
      refine ⟨hy, fun hyx hoddyx => ?_⟩
      have hybD : y * b ∈ D := by rw [← hby.eq]; exact hbyD
      rcases commute_or_orderOf_mul_eq_four_or_odd hD hb hx with h1 | h1 | ⟨h1, h2⟩
      ·
        exact absurd h1.symm (not_commute_of_collinear hD hx hb (fun h => hyx h.symm)
          (by rw [orderOf_mul_comm_eq]; exact hoddyx) hby.symm hybD)
      · exact ⟨b, hb, hby.symm, hybD, (orderOf_mul_comm_eq b x).trans h1⟩
      · exact hK y hy b hb x hx hby.symm hybD hyx hoddyx h2 h1 (hbS h2 h1))
  exact (hS ha).2 hax hodd

theorem existsCommSpec_of_oneOppositeClosed (hD : IsRootInvolutionSet D)
    (hconn : Moufang.ExcCollConnected D) (hK : OneOppositeClosed D) : ExistsCommSpec D := by
  intro d hd c hc hdc hodd
  obtain ⟨e, he, hce, -, h4⟩ := oneOpposite_of_collConnected hD hconn hK hc hd
    (fun h => hdc h.symm) (by rw [orderOf_mul_comm_eq]; exact hodd)
  exact ⟨e, he, hce.symm, h4⟩

private def commMap {E : Subgroup G} (hE : ∀ u ∈ E, ∀ v ∈ E, Commute u v) (g : G)
    (hg : ∀ u ∈ E, g * u * g⁻¹ * u⁻¹ ∈ E) : E →* E where
  toFun u := ⟨g * u * g⁻¹ * u⁻¹, hg u u.2⟩
  map_one' := by ext; simp
  map_mul' u v := by
    ext
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have h1 : Commute ((u : G)⁻¹) (g * v * g⁻¹ * (v : G)⁻¹) :=
      hE _ (E.inv_mem u.2) _ (hg v v.2)
    calc g * (u * v) * g⁻¹ * ((v : G)⁻¹ * (u : G)⁻¹)
        = g * u * g⁻¹ * (g * v * g⁻¹ * (v : G)⁻¹ * (u : G)⁻¹) := by group
      _ = g * u * g⁻¹ * ((u : G)⁻¹ * (g * v * g⁻¹ * (v : G)⁻¹)) := by rw [h1.eq]
      _ = g * u * g⁻¹ * (u : G)⁻¹ * (g * v * g⁻¹ * (v : G)⁻¹) := by group

private theorem mem_ker_commMap {E : Subgroup G} (hE : ∀ u ∈ E, ∀ v ∈ E, Commute u v) {g : G}
    (hg : ∀ u ∈ E, g * u * g⁻¹ * u⁻¹ ∈ E) (u : E) :
    u ∈ (commMap hE g hg).ker ↔ Commute g u := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change g * u * g⁻¹ * (u : G)⁻¹ = 1 ↔ g * u = u * g
  constructor
  · intro h
    have := eq_of_mul_inv_eq_one h
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro h
    rw [h, mul_inv_cancel_right, mul_inv_cancel]

private theorem index_ker_commMap_le [Finite G] {E A : Subgroup G}
    (hE : ∀ u ∈ E, ∀ v ∈ E, Commute u v) {g : G} (hg : ∀ u ∈ E, g * u * g⁻¹ * u⁻¹ ∈ E)
    (hA : ∀ u ∈ E, g * u * g⁻¹ * u⁻¹ ∈ A) : (commMap hE g hg).ker.index ≤ Nat.card A := by
  rw [Subgroup.index_ker]
  have hinj : Function.Injective (fun y : (commMap hE g hg).range => (⟨((y : E) : G), by
      obtain ⟨u, hu⟩ := y.2
      rw [← hu]
      exact hA u u.2⟩ : A)) := by
    intro y₁ y₂ h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  exact Nat.card_le_card_of_injective _ hinj

theorem oneOpposite_of_plane [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hR : NCoreCommutatorInRoot D) {a b c x : G} (ha : a ∈ D)
    (hb : b ∈ D) (hc : c ∈ D) (hx : x ∈ D) (hab : Commute a b) (habD : a * b ∈ D)
    (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x))) (hax : ¬ Commute a x)
    (hoddax : Odd (orderOf (a * x))) (hxc : orderOf (x * c) = 4) {E : Subgroup G}
    (hEcomm : ∀ u ∈ E, ∀ v ∈ E, Commute u v)
    (hED : ∀ u ∈ E, u ≠ 1 → u ∈ D ∧ (u ∈ rootSet D b ∨ (Commute b u ∧ b * u ∈ D)))
    (hEb : E ≤ nCore D b) (hEc : E ≤ nCore D c) (hBE : rootGroup D b ≤ E)
    (hCE : rootGroup D c ≤ E)
    (hcard : Nat.card (rootGroup D b) * Nat.card (rootGroup D c) < Nat.card E) :
    OneOpposite D a x := by
  have hcx4 : orderOf (c * x) = 4 := (orderOf_mul_comm_eq x c).trans hxc
  obtain ⟨hdD, hcd, hxd, -⟩ := sq_mem_of_orderOf_eq_four hD hc hx hcx4
  have hcdD : c * (c * x) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four hclass hD hc hx hcx4
  have hxdD : x * (c * x) ^ 2 ∈ D := by
    rw [← mul_sq_comm_of_orderOf_eq_four hD hc hx hcx4]
    exact mul_sq_mem_of_orderOf_eq_four hclass hD hx hc hxc
  have haN : a ∈ nCore D b := mem_nCore_of_collinear hclass hD hb ha hab habD
  have hdN : (c * x) ^ 2 ∈ nCore D c :=
    mem_nCore_of_collinear hclass hD hc hdD hcd.symm (by rwa [← hcd.eq])
  have hga : ∀ u ∈ E, a * u * a⁻¹ * u⁻¹ ∈ rootGroup D b := fun u hu =>
    hR b hb a haN u (hEb hu)
  have hgd : ∀ u ∈ E, (c * x) ^ 2 * u * ((c * x) ^ 2)⁻¹ * u⁻¹ ∈ rootGroup D c := fun u hu =>
    hR c hc _ hdN u (hEc hu)
  set φa := commMap hEcomm a (fun u hu => hBE (hga u hu))
  set φd := commMap hEcomm ((c * x) ^ 2) (fun u hu => hCE (hgd u hu))
  have hia : φa.ker.index ≤ Nat.card (rootGroup D b) := index_ker_commMap_le hEcomm _ hga
  have hid : φd.ker.index ≤ Nat.card (rootGroup D c) := index_ker_commMap_le hEcomm _ hgd
  have hne : φa.ker ⊓ φd.ker ≠ ⊥ := by
    intro hbot
    have h1 : (φa.ker ⊓ φd.ker).index ≤ φa.ker.index * φd.ker.index := Subgroup.index_inf_le
    rw [hbot, Subgroup.index_bot] at h1
    have h2 : Nat.card E ≤ Nat.card (rootGroup D b) * Nat.card (rootGroup D c) :=
      h1.trans (Nat.mul_le_mul hia hid)
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hua : Commute a u := (mem_ker_commMap hEcomm _ u).1 (Subgroup.mem_inf.1 hu).1
  have hud : Commute ((c * x) ^ 2) u := (mem_ker_commMap hEcomm _ u).1 (Subgroup.mem_inf.1 hu).2
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext (Subtype.ext h))
  obtain ⟨huD, hub⟩ := hED u u.2 hu1'
  have hux : ¬ Commute (u : G) x := by
    rcases hub with hub | ⟨hbu, hbuD⟩
    · exact fun h => hbx ((hub.2 x hx).1 h)
    · intro h
      exact not_commute_of_collinear hD hx huD (fun h' => hbx h'.symm)
        (by rw [orderOf_mul_comm_eq]; exact hoddbx) hbu hbuD h.symm
  have h4 : orderOf (x * u) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD huD hx with h1 | h1 | ⟨h1, -⟩
    · exact absurd h1 hux
    · exact (orderOf_mul_comm_eq _ _).trans h1
    · exact absurd hud.symm
        (not_commute_of_collinear hD huD hdD hux h1 hxd hxdD)
  obtain ⟨y, hy, hay, hayD, hyx⟩ := Moufang.exists_collinear_special_of_commute_special hclass hD
    ha hx huD hax hoddax hua.symm h4
  exact ⟨y, hy, hay, hayD, (orderOf_mul_comm_eq y x).trans hyx⟩

end CFSG.Timmesfeld.Bridge
