module

public import CFSG.Timmesfeld.Bridge.RootSetsRankOne
public import CFSG.Timmesfeld.RootInductionStruct

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem conj_mem_zpowers_mul {d x : G} (hd : d * d = 1) (hx : x * x = 1) {k : G}
    (hk : k ∈ Subgroup.zpowers (d * x)) : d * k * d ∈ Subgroup.zpowers (d * x) := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hr : d * (d * x) * d⁻¹ = (d * x)⁻¹ := by
    rw [hdinv, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, hdinv, ← mul_assoc, hd, one_mul]
  have key : d * (d * x) ^ n * d = ((d * x)⁻¹) ^ n := by
    rw [← hr, conj_zpow, hdinv]
  rw [key]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) n

theorem mem_zpowers_or_of_mem_closure {d x : G} (hd : d * d = 1) (hx : x * x = 1) {g : G}
    (hg : g ∈ Subgroup.closure {d, x}) :
    g ∈ Subgroup.zpowers (d * x) ∨ d * g ∈ Subgroup.zpowers (d * x) := by
  set H := Subgroup.zpowers (d * x) with hH
  have hc : ∀ k ∈ H, d * k * d ∈ H := fun k hk => conj_mem_zpowers_mul hd hx hk
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · right
      rw [hd]
      exact H.one_mem
    · rw [Set.mem_singleton_iff.1 hy]
      exact Or.inr (Subgroup.mem_zpowers _)
  | one => exact Or.inl H.one_mem
  | mul g h _ _ hg hh =>
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact Or.inl (H.mul_mem hg hh)
    · right
      have : d * (g * h) = d * g * d * (d * h) := by
        rw [show d * g * d * (d * h) = d * g * (d * d) * h by group, hd, mul_one, mul_assoc]
      rw [this]
      exact H.mul_mem (hc g hg) hh
    · right
      rw [← mul_assoc]
      exact H.mul_mem hg hh
    · left
      have : g * h = d * (d * g) * d * (d * h) := by
        rw [show d * (d * g) * d * (d * h) = (d * d) * g * (d * d) * h by group, hd, one_mul,
          mul_one]
      rw [this]
      exact H.mul_mem (hc _ hg) hh
  | inv g _ hg =>
    rcases hg with hg | hg
    · exact Or.inl (H.inv_mem hg)
    · right
      have : d * g⁻¹ = d * (d * g)⁻¹ * d := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd]
        rw [show d * (g⁻¹ * d) * d = d * g⁻¹ * (d * d) by group, hd, mul_one]
      rw [this]
      exact hc _ (H.inv_mem hg)

theorem not_orderOf_mul_eq_four_of_closure_pair {d x : G} (hd : d * d = 1) (hx : x * x = 1)
    (hodd : Odd (orderOf (d * x))) (htop : Subgroup.closure {d, x} = ⊤) {c f : G}
    (hc : orderOf c = 2) (hf : orderOf f = 2) : orderOf (c * f) ≠ 4 := by
  set H := Subgroup.zpowers (d * x) with hH
  have hnot : ∀ y : G, orderOf y = 2 → d * y ∈ H := by
    intro y hy
    rcases mem_zpowers_or_of_mem_closure hd hx (htop ▸ Subgroup.mem_top y) with h | h
    · have h2 : Odd (orderOf y) := hodd.of_dvd_nat (orderOf_dvd_of_mem_zpowers h)
      rw [hy] at h2
      exact absurd h2 (by decide)
    · exact h
  have hc2 : c * c = 1 := by rw [← pow_two, ← hc]; exact pow_orderOf_eq_one c
  have hcf : c * f = (d * c)⁻¹ * (d * f) := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hc2, inv_eq_of_mul_eq_one_right hd,
      show c * d * (d * f) = c * (d * d) * f by group, hd, mul_one]
  have hmem : c * f ∈ H := by
    rw [hcf]
    exact H.mul_mem (H.inv_mem (hnot c hc)) (hnot f hf)
  intro h4
  have h2 : Odd (orderOf (c * f)) := hodd.of_dvd_nat (orderOf_dvd_of_mem_zpowers hmem)
  rw [h4] at h2
  exact absurd h2 (by decide)

theorem closure_insert_rootSet_ne_top (h : Hyp G D)
    (hL : (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D ∧ RootMoufang D)
    {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) :
    Subgroup.closure (insert x (rootSet D d)) ≠ ⊤ := by
  intro htop
  have := h.finite
  have hD := h.root
  obtain ⟨c, hc, f, hf, h4⟩ := h.nondeg
  by_cases hlarge : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d
  · obtain ⟨hrc, hm⟩ := hL hlarge
    have hAB : rootGroup D d ⊔ rootGroup D x = ⊤ := by
      rw [eq_top_iff, ← htop, Subgroup.closure_le]
      rintro y (rfl | hy)
      · exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self hx))
      · exact Subgroup.mem_sup_left (rootSet_subset_rootGroup D d hy)
    have hxd : ¬ Commute x d := fun hc => hdx hc.symm
    have hodd' : Odd (orderOf (x * d)) := by
      rw [show x * d = (d * x)⁻¹ by rw [mul_inv_rev, hD.inv_eq hd, hD.inv_eq hx], orderOf_inv]
      exact hodd
    have hR : IsElemAbRankOne (rootGroup D d) (rootGroup D x) :=
      { gen := hAB
        ne := rootGroup_ne_of_opposite h.isClass hd hx hdx
        comm := fun a ha a' ha' => commute_of_mem_rootGroup hd ha ha'
        sq := fun a ha => mul_self_eq_one_of_mem_rootGroup hD hd ha
        moufang := fun a ha ha1 => Reduction.exists_conjSub_eq h hrc hm hd hx hdx hodd ha ha1
        moufang' := fun b hb hb1 =>
          Reduction.exists_conjSub_eq h hrc hm hx hd hxd hodd' hb hb1 }
    have hmem : ∀ y ∈ D, ∃ g : G, y ∈ (rootGroup D d).map (MulAut.conj g).toMonoidHom := by
      intro y hy
      obtain ⟨d₀, hd₀⟩ := h.isClass
      have hdy : IsConj d y := by
        rw [hd₀] at hd hy
        exact hd.symm.trans hy
      obtain ⟨g, hg⟩ := isConj_iff.1 hdy
      refine ⟨g, ?_⟩
      rw [← rootGroup_conj h.isClass, hg]
      exact rootSet_subset_rootGroup D y (mem_rootSet_self hy)
    obtain ⟨g, hcg⟩ := hmem c hc
    obtain ⟨g', hfg⟩ := hmem f hf
    by_cases hgg : (rootGroup D d).map (MulAut.conj g).toMonoidHom =
        (rootGroup D d).map (MulAut.conj g').toMonoidHom
    · rw [hgg] at hcg
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hcg
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hfg
      have hcomm := (commute_of_mem_rootGroup hd ha ha').map (MulAut.conj g').toMonoidHom
      have hsq : ((MulAut.conj g').toMonoidHom a * (MulAut.conj g').toMonoidHom a') ^ 2 = 1 := by
        rw [hcomm.mul_pow, pow_two, pow_two, hD.mul_self_eq_one hc, hD.mul_self_eq_one hf, one_mul]
      have := orderOf_dvd_of_pow_eq_one hsq
      rw [h4] at this
      exact absurd this (by decide)
    · have := hR.odd_orderOf_mul hcg (hD.ne_one hc) hfg (hD.ne_one hf) hgg
      rw [h4] at this
      exact absurd this (by decide)
  · push Not at hlarge
    have hsing : rootSet D d = {d} := rootSet_eq_singleton_of_forall hlarge hd
    rw [hsing] at htop
    exact not_orderOf_mul_eq_four_of_closure_pair (hD.mul_self_eq_one hd)
      (hD.mul_self_eq_one hx) hodd (by rw [Set.pair_comm]; exact htop) (hD.orderOf_eq_two hc)
      (hD.orderOf_eq_two hf) h4

@[expose] def RootIHGen (G : Type) [Group G] : Prop :=
  ∀ (G' : Type) [Group G'] (D' : Set G'), Hyp G' D' → Nat.card G' < Nat.card G →
    ∀ d ∈ D', ∀ x ∈ D', ¬ Commute d x → Odd (orderOf (d * x)) →
      Subgroup.closure (insert x (rootSet D' d)) ≠ ⊤

theorem rootIHGen_of {G : Type} [Group G]
    (IH : ∀ (G' : Type) [Group G'] (D' : Set G'), Hyp G' D' → Nat.card G' < Nat.card G →
      (∃ d ∈ D', ∃ e ∈ rootSet D' d, e ≠ d) → RootClosure D' ∧ RootMoufang D') :
    RootIHGen G :=
  fun G' _ D' h' hlt _ hd _ hx hdx hodd =>
    closure_insert_rootSet_ne_top h' (IH G' D' h' hlt) hd hx hdx hodd

theorem rootIHGen_of_struct {G : Type} [Group G] (IH : RootIHStruct G) : RootIHGen G :=
  rootIHGen_of fun G' _ D' h' hlt hl =>
    ⟨((IH G' D' h' hlt).2 hl).1, ((IH G' D' h' hlt).2 hl).2.2⟩

end CFSG.Timmesfeld.Bridge
