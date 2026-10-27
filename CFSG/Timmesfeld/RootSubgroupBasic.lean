module

public import CFSG.Timmesfeld.Basic

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (show g * x = g * x * g⁻¹ * g by group)).symm

theorem orderOf_mul_comm_eq (x y : G) : orderOf (y * x) = orderOf (x * y) := by
  rw [← orderOf_conj_eq x⁻¹ (x * y)]
  congr 1
  group

theorem orderOf_mul_eq_two_mul_of_odd {u v : G} (huv : Commute u v) (hu : Odd (orderOf u))
    (hv : orderOf v = 2) : orderOf (u * v) = 2 * orderOf u := by
  rw [huv.orderOf_mul_eq_mul_orderOf_of_coprime, hv, mul_comm]
  rw [hv, Nat.coprime_two_right]
  exact hu

variable {D : Set G}

theorem orderOf_mul_ne_four_of_odd (hD : IsRootInvolutionSet D) {a b x : G} (ha : a ∈ D)
    (hb : b ∈ rootSet D a) (hx : x ∈ D) (hodd : Odd (orderOf (a * x))) :
    orderOf (b * x) ≠ 4 := by
  intro h4
  have hb' : b ∈ D := hb.1
  have h4' : orderOf (x * b) = 4 := by rwa [orderOf_mul_comm_eq]
  obtain ⟨hfD, hxf, hbf, hconj⟩ := sq_mem_of_orderOf_eq_four hD hx hb' h4'
  set f := (x * b) ^ 2 with hf
  have haf : Commute a f := (hb.2 f hfD).1 hbf
  have hab : Commute a b := commute_of_mem_rootSet ha (mem_rootSet_self ha) hb
  have hbinv : b⁻¹ = b := hD.inv_eq hb'
  have h1 : a * (b * x * b) = b * (a * x) * b⁻¹ := by
    rw [hbinv, show a * (b * x * b) = a * b * x * b by group, hab.eq]
    group
  have h2 : orderOf (a * (b * x * b)) = orderOf (a * x) := by
    rw [h1, orderOf_conj_eq]
  rw [hconj, ← mul_assoc] at h2
  have hcomm : Commute (a * x) f := haf.mul_left hxf
  rw [orderOf_mul_eq_two_mul_of_odd hcomm hodd (hD.orderOf_eq_two hfD)] at h2
  have hpos : 0 < orderOf (a * x) := by
    rcases hodd with ⟨k, hk⟩
    omega
  omega

theorem orderOf_mul_eq_four_iff_of_mem_rootSet (hD : IsRootInvolutionSet D) {a b x : G}
    (ha : a ∈ D) (hb : b ∈ rootSet D a) (hx : x ∈ D) :
    orderOf (b * x) = 4 ↔ orderOf (a * x) = 4 := by
  have hb' : b ∈ D := hb.1
  have ha' : a ∈ rootSet D b := mem_rootSet_comm ha hb
  have key : ∀ {u v : G}, u ∈ D → v ∈ rootSet D u → orderOf (u * x) = 4 →
      orderOf (v * x) = 4 := by
    intro u v hu hv h4
    rcases hD.orderOf_mul hv.1 hx with h | h | h
    · exfalso
      have hvx : Commute v x :=
        (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hv.1) (hD.mul_self_eq_one hx)).2
          (by rw [← h, pow_orderOf_eq_one])
      have hux : Commute u x := (hv.2 x hx).1 hvx
      have h2 := orderOf_dvd_of_pow_eq_one
        ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hu) (hD.mul_self_eq_one hx)).1 hux)
      rw [h4] at h2
      norm_num at h2
    · exact h
    · exact absurd h4 (orderOf_mul_ne_four_of_odd hD hv.1 (mem_rootSet_comm hu hv) hx h)
  exact ⟨key hb' ha', key ha hb⟩

theorem odd_orderOf_mul_iff_of_mem_rootSet (hD : IsRootInvolutionSet D) {a b x : G}
    (ha : a ∈ D) (hb : b ∈ rootSet D a) (hx : x ∈ D) (hax : ¬ Commute a x) :
    Odd (orderOf (b * x)) ↔ Odd (orderOf (a * x)) := by
  have key : ∀ {u v : G}, u ∈ D → v ∈ rootSet D u → ¬ Commute u x → Odd (orderOf (u * x)) →
      Odd (orderOf (v * x)) := by
    intro u v hu hv hux hodd
    rcases hD.orderOf_mul hv.1 hx with h | h | h
    · exfalso
      exact hux ((hv.2 x hx).1
        ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hv.1) (hD.mul_self_eq_one hx)).2
          (by rw [← h, pow_orderOf_eq_one])))
    · rw [orderOf_mul_eq_four_iff_of_mem_rootSet hD hu hv hx] at h
      rw [h] at hodd
      exact absurd hodd (by decide)
    · exact h
  have hbx : ¬ Commute b x := fun h => hax ((hb.2 x hx).1 h)
  exact ⟨key hb.1 (mem_rootSet_comm ha hb) hbx, key ha hb hax⟩

theorem commute_or_orderOf_mul_eq_four_or_odd (hD : IsRootInvolutionSet D) {d e : G}
    (hd : d ∈ D) (he : e ∈ D) :
    Commute d e ∨ orderOf (d * e) = 4 ∨ (Odd (orderOf (d * e)) ∧ ¬ Commute d e) := by
  rcases hD.orderOf_mul hd he with h | h | h
  · exact Or.inl ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he)).2
      (by rw [← h, pow_orderOf_eq_one]))
  · exact Or.inr (Or.inl h)
  · by_cases hc : Commute d e
    · exact Or.inl hc
    · exact Or.inr (Or.inr ⟨h, hc⟩)

theorem commute_of_mem_rootSet_of_commute {d d' t t' : G} (hd' : d' ∈ D)
    (ht : t ∈ rootSet D d) (ht' : t' ∈ rootSet D d') (hdd' : Commute d d') : Commute t t' := by
  have htd' : Commute t d' := (ht.2 d' hd').2 hdd'
  exact ((ht'.2 t ht.1).2 htd'.symm).symm

theorem orderOf_mul_eq_four_of_mem_rootSet (hD : IsRootInvolutionSet D) {d d' t t' : G}
    (hd : d ∈ D) (hd' : d' ∈ D) (ht : t ∈ rootSet D d) (ht' : t' ∈ rootSet D d')
    (h4 : orderOf (d * d') = 4) : orderOf (t * t') = 4 := by
  have h1 : orderOf (t * d') = 4 := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hd ht hd').2 h4
  rw [← orderOf_mul_comm_eq] at h1 ⊢
  exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD hd' ht' ht.1).2 h1

theorem odd_orderOf_mul_of_mem_rootSet (hD : IsRootInvolutionSet D) {d d' t t' : G}
    (hd : d ∈ D) (hd' : d' ∈ D) (ht : t ∈ rootSet D d) (ht' : t' ∈ rootSet D d')
    (hodd : Odd (orderOf (d * d'))) (hc : ¬ Commute d d') :
    Odd (orderOf (t * t')) ∧ ¬ Commute t t' := by
  have h1 : Odd (orderOf (t * d')) := (odd_orderOf_mul_iff_of_mem_rootSet hD hd ht hd' hc).2 hodd
  have hc1 : ¬ Commute t d' := fun h => hc ((ht.2 d' hd').1 h)
  have hc2 : ¬ Commute d' t := fun h => hc1 h.symm
  rw [← orderOf_mul_comm_eq] at h1
  have h2 : Odd (orderOf (t' * t)) :=
    (odd_orderOf_mul_iff_of_mem_rootSet hD hd' ht' ht.1 hc2).2 h1
  rw [← orderOf_mul_comm_eq] at h2
  exact ⟨h2, fun h => hc2 ((ht'.2 t ht.1).1 h.symm)⟩

@[expose] def rootGroup (D : Set G) (d : G) : Subgroup G := Subgroup.closure (rootSet D d)

theorem rootSet_subset_rootGroup (D : Set G) (d : G) : rootSet D d ⊆ rootGroup D d :=
  Subgroup.subset_closure

theorem pairwise_commute_rootSet {d : G} (hd : d ∈ D) : (rootSet D d).Pairwise Commute :=
  fun _ ha _ hb _ => commute_of_mem_rootSet hd ha hb

theorem commute_of_mem_closure {S S' : Set G} (h : ∀ s ∈ S, ∀ s' ∈ S', Commute s s') {g g' : G}
    (hg : g ∈ Subgroup.closure S) (hg' : g' ∈ Subgroup.closure S') : Commute g g' := by
  have h1 : ∀ s ∈ S, Commute s g' := by
    intro s hs
    induction hg' using Subgroup.closure_induction with
    | mem x hx => exact h s hs x hx
    | one => exact Commute.one_right s
    | mul x y _ _ ihx ihy => exact ihx.mul_right ihy
    | inv x _ ih => exact ih.inv_right
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx
  | one => exact Commute.one_left g'
  | mul x y _ _ ihx ihy => exact ihx.mul_left ihy
  | inv x _ ih => exact ih.inv_left

theorem mul_self_eq_one_of_mem_closure {S : Set G} (hS : S.Pairwise Commute)
    (h2 : ∀ s ∈ S, s * s = 1) {g : G} (hg : g ∈ Subgroup.closure S) : g * g = 1 := by
  have hc : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := fun s hs s' hs' => by
    by_cases hss : s = s'
    · rw [hss]
    · exact hS hs hs' hss
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    rw [show x * y * (x * y) = x * x * (y * y) by
      rw [mul_assoc x y, ← mul_assoc y x, ← (commute_of_mem_closure hc hx hy).eq]; group,
      ihx, ihy, mul_one]
  | inv x hx ih => rw [← mul_inv_rev, ih, inv_one]

theorem isPGroup_closure_of_pairwise {S : Set G} (hS : S.Pairwise Commute)
    (h2 : ∀ s ∈ S, s * s = 1) : IsPGroup 2 (Subgroup.closure S) := by
  rintro ⟨g, hg⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_two]
  exact mul_self_eq_one_of_mem_closure hS h2 hg

theorem commute_of_mem_rootGroup {d g g' : G} (hd : d ∈ D) (hg : g ∈ rootGroup D d)
    (hg' : g' ∈ rootGroup D d) : Commute g g' :=
  commute_of_mem_closure (fun _ ha _ hb => commute_of_mem_rootSet hd ha hb) hg hg'

theorem mul_self_eq_one_of_mem_rootGroup (hD : IsRootInvolutionSet D) {d g : G} (hd : d ∈ D)
    (hg : g ∈ rootGroup D d) : g * g = 1 :=
  mul_self_eq_one_of_mem_closure (pairwise_commute_rootSet hd)
    (fun _ hx => hD.mul_self_eq_one hx.1) hg

theorem isPGroup_rootGroup (hD : IsRootInvolutionSet D) {d : G} (hd : d ∈ D) :
    IsPGroup 2 (rootGroup D d) :=
  isPGroup_closure_of_pairwise (pairwise_commute_rootSet hd) (fun _ hx => hD.mul_self_eq_one hx.1)

theorem commute_of_mem_rootGroup_of_commute' {d d' g g' : G} (hd' : d' ∈ D)
    (hg : g ∈ rootGroup D d) (hg' : g' ∈ rootGroup D d') (hdd' : Commute d d') : Commute g g' :=
  commute_of_mem_closure (fun _ ht _ ht' => commute_of_mem_rootSet_of_commute hd' ht ht' hdd')
    hg hg'

theorem commute_of_mem_rootGroup_of_commute {d g f : G} (hg : g ∈ rootGroup D d) (hf : f ∈ D)
    (hdf : Commute d f) : Commute g f := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (hx.2 f hf).2 hdf
  | one => exact Commute.one_left f
  | mul x y _ _ ihx ihy => exact ihx.mul_left ihy
  | inv x _ ih => exact ih.inv_left

theorem rootGroup_eq_of_mem {d e : G} (he : e ∈ rootSet D d) : rootGroup D e = rootGroup D d := by
  rw [rootGroup, rootGroup, rootSet_eq_of_mem he]

theorem mem_rootSet_of_mem_rootGroup [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {d e : G} (hd : d ∈ D) (he : e ∈ D) (heW : e ∈ rootGroup D d) : e ∈ rootSet D d :=
  (mem_rootSet_iff hclass hd).2 ⟨he, (commute_of_mem_rootGroup_of_commute heW hd
    (Commute.refl d)).symm, fun _ hf hdf => commute_of_mem_rootGroup_of_commute heW hf hdf⟩

theorem rootGroup_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g d : G) :
    rootGroup D (g * d * g⁻¹) = (rootGroup D d).map (MulAut.conj g).toMonoidHom := by
  rw [rootGroup, rootGroup, MonoidHom.map_closure, rootSet_conj hclass]
  rfl

theorem mem_of_odd_orderOf_mul (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {x w : G} (hx : x ∈ D) (hw : w * w = 1)
    (hodd : Odd (orderOf (x * w))) : w ∈ D := by
  obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hx) hw hodd
  rw [← hg]
  exact conj_mem_of_isClass hclass g hx

end CFSG.Timmesfeld
