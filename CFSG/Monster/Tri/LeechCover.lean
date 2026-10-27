module

public import CFSG.Monster.Tri.LeechConnected

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.VisCert CFSG.Monster.Visible CFSG.Monster.B.Short CFSG.Monster.Generated

open scoped commutatorElement

theorem exists_adj_mem_of_preconnected {β : Type*} {H : SimpleGraph β} {T : Set β}
    (hT : (H.induce T).Preconnected) (hcard : 1 < T.ncard) : ∀ t ∈ T, ∃ t' ∈ T, H.Adj t t' := by
  intro t ht
  obtain ⟨t', ht', hne⟩ := Set.exists_ne_of_one_lt_ncard hcard t
  obtain ⟨p⟩ := hT ⟨t, ht⟩ ⟨t', ht'⟩
  cases p with
  | nil => exact absurd rfl hne.symm
  | cons h _ => exact ⟨_, Subtype.property _, h⟩

theorem preconnected_induce_comap {α β : Type*} {H : SimpleGraph β} (ψ : α → β)
    (hψ : Function.Surjective ψ) {T : Set β} (hT : (H.induce T).Preconnected)
    (hnb : ∀ t ∈ T, ∃ t' ∈ T, H.Adj t t') :
    ((H.comap ψ).induce (ψ ⁻¹' T)).Preconnected := by
  have fibre : ∀ a a' : ψ ⁻¹' T, ψ a = ψ a' →
      ((H.comap ψ).induce (ψ ⁻¹' T)).Reachable a a' := by
    intro a a' h
    by_cases e : a = a'
    · rw [e]
    · obtain ⟨t', ht', hadj⟩ := hnb (ψ a) a.2
      obtain ⟨c, hc⟩ := hψ t'
      have hcT : c ∈ ψ ⁻¹' T := by
        rw [Set.mem_preimage, hc]
        exact ht'
      have h1 : ((H.comap ψ).induce (ψ ⁻¹' T)).Adj a ⟨c, hcT⟩ := by
        show H.Adj (ψ (a : α)) (ψ c)
        rw [hc]
        exact hadj
      have h2 : ((H.comap ψ).induce (ψ ⁻¹' T)).Adj a' ⟨c, hcT⟩ := by
        show H.Adj (ψ (a' : α)) (ψ c)
        rw [hc, ← h]
        exact hadj
      exact h1.reachable.trans h2.reachable.symm
  have key : ∀ (x y : T) (_ : (H.induce T).Walk x y) (a b : ψ ⁻¹' T), ψ a = x → ψ b = y →
      ((H.comap ψ).induce (ψ ⁻¹' T)).Reachable a b := by
    intro x y w
    induction w with
    | nil => exact fun a b ha hb => fibre a b (ha.trans hb.symm)
    | @cons x z y hxz _ ih =>
      intro a b ha hb
      obtain ⟨c, hc⟩ := hψ z
      have hcT : c ∈ ψ ⁻¹' T := by
        rw [Set.mem_preimage, hc]
        exact z.2
      refine (SimpleGraph.Adj.reachable ?_ :
        ((H.comap ψ).induce (ψ ⁻¹' T)).Reachable a ⟨c, hcT⟩).trans (ih ⟨c, hcT⟩ b hc hb)
      show H.Adj (ψ (a : α)) (ψ c)
      rw [ha, hc]
      exact hxz
  rintro a b
  obtain ⟨w⟩ := hT ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩
  exact key _ _ w a b rfl rfl

@[expose] noncomputable def qCls (r : Q) : L2 := phi0 (coordOf r)

theorem qCls_mul (r s : Q) : qCls (r * s) = qCls r + qCls s := by
  rw [qCls, qCls, qCls, coordOf_mul, map_add]

theorem qCls_zQ : qCls zQ = 0 := by
  rw [qCls, (mem_zpowers_zQ_iff zQ).1 (Subgroup.mem_zpowers zQ), map_zero]

theorem qCls_mul_zQ (r : Q) : qCls (r * zQ) = qCls r := by
  rw [qCls_mul, qCls_zQ, add_zero]

theorem qCls_eq_iff {r s : Q} : qCls r = qCls s ↔ s = r ∨ s = r * zQ := by
  rw [qCls, qCls, phi0_injective.eq_iff, eq_comm, coordOf_eq_iff s r]
  constructor
  · intro h
    obtain ⟨e, he⟩ := exists_eq_zQ_pow h
    rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) e with rfl | rfl
    · left
      rw [show (0 : ZMod 2).val = 0 from rfl, pow_zero, inv_mul_eq_one] at he
      exact he.symm
    · right
      rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, inv_mul_eq_iff_eq_mul] at he
      exact he
  · rintro (rfl | rfl)
    · rw [inv_mul_cancel]
      exact Subgroup.one_mem _
    · rw [inv_mul_cancel_left]
      exact Subgroup.mem_zpowers zQ

theorem qCls_surjective : Function.Surjective qCls := fun w =>
  ⟨rep (phi0Equiv.symm w), by
    rw [qCls, coordOf_rep]
    exact phi0Equiv.apply_symm_apply w⟩

theorem isShortCoord_iff_qCls {r : Q} : IsShortCoord (coordOf r) ↔ qCls r ∈ shortSet := Iff.rfl

@[expose] noncomputable def shortQGraph : SimpleGraph Q := shortGraph.comap qCls

theorem shortQGraph_adj_iff_adj {r s : Q} :
    shortQGraph.Adj r s ↔ shortGraph.Adj (qCls r) (qCls s) := Iff.rfl

theorem shortQGraph_adj_iff {r s : Q} : shortQGraph.Adj r s ↔
    IsShortCoord (coordOf r) ∧ IsShortCoord (coordOf s) ∧ IsShortCoord (coordOf (r * s)) := by
  rw [shortQGraph_adj_iff_adj, shortGraph_adj, ← qCls_mul]
  exact Iff.rfl

theorem commonNeighbors_shortQGraph (r s : Q) :
    shortQGraph.commonNeighbors r s = qCls ⁻¹' shortGraph.commonNeighbors (qCls r) (qCls s) := by
  ext t
  simp only [SimpleGraph.mem_commonNeighbors, Set.mem_preimage, shortQGraph_adj_iff_adj]

theorem neighborSet_shortQGraph (r : Q) :
    shortQGraph.neighborSet r = qCls ⁻¹' shortGraph.neighborSet (qCls r) := by
  ext t
  simp only [SimpleGraph.mem_neighborSet, Set.mem_preimage, shortQGraph_adj_iff_adj]

theorem shortQGraph_diam_le_two
    {r s : Q} (hr : IsShortCoord (coordOf r))
    (hs : IsShortCoord (coordOf s)) :
    r = s ∨ shortQGraph.Adj r s ∨ ∃ t, shortQGraph.Adj r t ∧ shortQGraph.Adj t s := by
  by_cases hrs : r = s
  · exact Or.inl hrs
  refine Or.inr ?_
  have hr' : qCls r ∈ shortSet := hr
  have hs' : qCls s ∈ shortSet := hs
  by_cases hq : qCls r = qCls s
  ·
    refine Or.inr ?_
    have hn := (preconnected_neighborSet hr').2
    obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (s := shortGraph.neighborSet (qCls r))
      (by rw [hn]; norm_num)
    obtain ⟨t, rfl⟩ := qCls_surjective w
    refine ⟨t, hw, ?_⟩
    rw [shortQGraph_adj_iff_adj, ← hq]
    exact hw.symm
  · rcases shortGraph_diam_le_two hr' hs' with h | h | ⟨w, hw⟩
    · exact absurd h hq
    · exact Or.inl h
    · obtain ⟨t, rfl⟩ := qCls_surjective w
      exact Or.inr ⟨t, hw.1, hw.2.symm⟩

theorem preconnected_mu_Q_fibre
    {r : Q} (hr : IsShortCoord (coordOf r)) :
    (shortQGraph.induce (shortQGraph.commonNeighbors r (r * zQ))).Preconnected := by
  obtain ⟨hp, hc⟩ := preconnected_neighborSet (show qCls r ∈ shortSet from hr)
  have h : shortQGraph.commonNeighbors r (r * zQ) = qCls ⁻¹' shortGraph.neighborSet (qCls r) := by
    rw [commonNeighbors_shortQGraph, qCls_mul_zQ, SimpleGraph.commonNeighbors_eq, Set.inter_self]
  rw [h]
  exact preconnected_induce_comap qCls qCls_surjective hp
    (exists_adj_mem_of_preconnected hp (by rw [hc]; norm_num))

theorem preconnected_mu_Q_three
    {r s : Q} (hr : IsShortCoord (coordOf r))
    (hs : IsShortCoord (coordOf s)) (h : qL (qCls r + qCls s) = 1) :
    (shortQGraph.induce (shortQGraph.commonNeighbors r s)).Preconnected := by
  obtain ⟨hp, hc⟩ := preconnected_mu_three (show qCls r ∈ shortSet from hr)
    (show qCls s ∈ shortSet from hs) h
  rw [commonNeighbors_shortQGraph]
  exact preconnected_induce_comap qCls qCls_surjective hp
    (exists_adj_mem_of_preconnected hp (by rw [hc]; norm_num))

theorem eq_one_or_eq_of_mem_zpowers_of_sq {G : Type*} [Group G] {g z : G} (hg : g ^ 2 = 1)
    (hz : z ∈ Subgroup.zpowers g) : z = 1 ∨ z = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, zpow_two, ← pow_two, hg, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, zpow_two, ← pow_two, hg, one_zpow, one_mul, zpow_one]

theorem mul_comm_of_sq_eq_one {G : Type*} [Group G] {r s : G} (hr : r ^ 2 = 1) (hs : s ^ 2 = 1)
    (hrs : (r * s) ^ 2 = 1) : s * r = r * s := by
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hr)
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs)
  have hrs' : (r * s)⁻¹ = r * s := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hrs)
  calc s * r = s⁻¹ * r⁻¹ := by rw [hr', hs']
    _ = (r * s)⁻¹ := (mul_inv_rev r s).symm
    _ = r * s := hrs'

theorem add_self_eq_zero_zmod {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem sq_eq_zQ_pow (g : Q) : g ^ 2 = zQ ^ (qL (qCls g)).val := by
  have h0 : coordOf (g ^ 2) = 0 := by
    rw [pow_two, coordOf_mul]
    exact add_self_eq_zero_zmod _
  obtain ⟨e, he⟩ := exists_eq_zQ_pow ((mem_zpowers_zQ_iff _).2 h0)
  have h := qL_phi_of_sq he
  rw [toAdd_phi_mk] at h
  rw [he]
  exact congrArg (fun x : ZMod 2 => zQ ^ x.val) h.symm

theorem zQ_ne_one : zQ ≠ 1 := by
  intro h
  have := orderOf_zQ
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem rhoEquiv_mem_shortClass
    {r : Q} (hr : IsShortCoord (coordOf r)) :
    rhoEquiv r ∈ shortClass := by
  obtain ⟨g, hg, h, -⟩ := exists_Gvis_conj_short isShortCoord_rStar hr
  exact ⟨g, Hmat_le_Gmat hg, h⟩

theorem rhoEquiv_mul_mem_shortClass_of_adj
    {r s : Q} (h : shortQGraph.Adj r s) :
    rhoEquiv r * rhoEquiv s ∈ shortClass := by
  obtain ⟨hr, hs, hrs⟩ := shortQGraph_adj_iff.1 h
  have hr2 : r ^ 2 = 1 := sq_eq_one_of_isShort hr
  have hs2 : s ^ 2 = 1 := sq_eq_one_of_isShort hs
  have hrs2 : (r * s) ^ 2 = 1 := sq_eq_one_of_isShort hrs
  have hcomm : s * r = r * s := mul_comm_of_sq_eq_one (G := Q) hr2 hs2 hrs2
  rw [← rhoEquiv_mul, hcomm]
  exact rhoEquiv_mem_shortClass hrs

end CFSG.Monster.Tri.Leech
