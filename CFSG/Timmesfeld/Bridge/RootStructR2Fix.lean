module

public import CFSG.Timmesfeld.Bridge.RootStructR2Degen

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem eq_of_orderOf_mul_eq_three [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) {a' x x' x'' : G} (ha' : a' ∈ D)
    (hx : x ∈ D) (hx' : x' ∈ rootSet D x) (hx'' : x'' ∈ rootSet D x) (hax : ¬ Commute a' x)
    (h3' : orderOf (a' * x') = 3) (h3'' : orderOf (a' * x'') = 3) : x' = x'' := by
  by_contra hne
  have ha'2 := hD.mul_self_eq_one ha'
  have hx'2 := hD.mul_self_eq_one hx'.1
  have hx''2 := hD.mul_self_eq_one hx''.1
  have hinv : ∀ {u : G}, u * u = 1 → u⁻¹ = u := fun hu => inv_eq_of_mul_eq_one_right hu
  have hyT : x'' * x' ∈ rootSet D x := by
    refine mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx (Subgroup.mul_mem _
      (rootSet_subset_rootGroup D x hx'') (rootSet_subset_rootGroup D x hx')) fun h1 => hne ?_
    rw [eq_inv_of_mul_eq_one_left h1, hinv hx'2]
  have hconj : ∀ {u : G}, u ∈ rootSet D x → a' * u * a'⁻¹ ∈ rootSet D (a' * x * a'⁻¹) := by
    intro u hu
    rw [rootSet_conj hclass]
    exact ⟨u, hu, rfl⟩
  have hbraid : ∀ {u : G}, u * u = 1 → orderOf (a' * u) = 3 → a' * u * a' = u * a' * u := by
    intro u hu h3
    have h : a' * u * a' * (u * a' * u) = 1 := by
      rw [← pow_orderOf_eq_one (a' * u), h3]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, mul_inv_rev, hinv ha'2, hinv hu, mul_assoc]
  have hbraid' := hbraid hx'2 h3'
  have hbraid'' := hbraid hx''2 h3''
  have h1 : x'' * a' * x''⁻¹ ∈ rootSet D (x' * a' * x'⁻¹) := by
    have e1 : x' * a' * x'⁻¹ = a' * x' * a'⁻¹ := by
      rw [hinv hx'2, hinv ha'2, hbraid']
    have e2 : x'' * a' * x''⁻¹ = a' * x'' * a'⁻¹ := by
      rw [hinv hx''2, hinv ha'2, hbraid'']
    rw [e1, e2, rootSet_eq_of_mem (hconj hx')]
    exact hconj hx''
  have h2 : (x'' * x') * a' * (x'' * x')⁻¹ ∈ rootSet D a' := by
    have h3 : x'' * (x'' * a' * x''⁻¹) * x''⁻¹ ∈
        rootSet D (x'' * (x' * a' * x'⁻¹) * x''⁻¹) := by
      rw [rootSet_conj hclass]
      exact ⟨_, h1, rfl⟩
    have e3 : x'' * (x'' * a' * x''⁻¹) * x''⁻¹ = a' := by
      rw [hinv hx''2]
      calc x'' * (x'' * a' * x'') * x'' = (x'' * x'') * a' * (x'' * x'') := by group
        _ = a' := by rw [hx''2, one_mul, mul_one]
    have e4 : x'' * (x' * a' * x'⁻¹) * x''⁻¹ = (x'' * x') * a' * (x'' * x')⁻¹ := by group
    rw [e3, e4] at h3
    exact mem_rootSet_comm (conj_mem_of_isClass hclass _ ha') h3
  have hcomm := commute_of_conj_mem_rootSet hclass hD ha' hyT.1 h2
  exact hax ((hyT.2 a' ha').1 hcomm.symm).symm

theorem commute_of_conj_mem_rootSet_of_centralizes (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) {a x g : G} (ha : a ∈ D) (hx : x ∈ D) (hax : ¬ Commute a x)
    (hoddax : Odd (orderOf (a * x))) (hx1 : OneOpposite D a x)
    (hga : ∀ a' ∈ rootSet D a, Commute g a') (hgx : g * x * g⁻¹ ∈ rootSet D x) {x' : G}
    (hx' : x' ∈ rootSet D x) : Commute g x' := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hQ := commLambda_of_nCoreCommutatorInRoot hclass hD (nCoreCommutatorInRoot_of_hyp h hc)
  have hopp := opposite_of_mem_rootSet_of_opposite hD ha hx (mem_rootSet_self ha) hx' ⟨hax, hoddax⟩
  obtain ⟨e, he, hae, haeD, h4⟩ := hx1
  have h4' : orderOf (x' * e) = 4 :=
    (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx' he).2 h4
  have hx'a : ¬ Commute x' a := fun h' => hopp.1 h'.symm
  have hoddx'a : Odd (orderOf (x' * a)) := by rw [orderOf_mul_comm_eq]; exact hopp.2
  obtain ⟨a', ha', h3⟩ := exists_orderOf_mul_eq_three_of_oneOpposite h hc hs hQ ha hx'.1 hx'a
    hoddx'a ⟨e, he, hae, haeD, h4'⟩
  have hx'g : g * x' * g⁻¹ ∈ rootSet D x := by
    have : g * x' * g⁻¹ ∈ rootSet D (g * x * g⁻¹) := by
      rw [rootSet_conj hclass]
      exact ⟨x', hx', rfl⟩
    rwa [rootSet_eq_of_mem hgx] at this
  have ha'x : ¬ Commute a' x := fun h' => hax ((ha'.2 x hx).1 h')
  have h3a : orderOf (a' * x') = 3 := by rw [orderOf_mul_comm_eq]; exact h3
  have h3g : orderOf (a' * (g * x' * g⁻¹)) = 3 := by
    have e : a' * (g * x' * g⁻¹) = g * (a' * x') * g⁻¹ := by
      calc a' * (g * x' * g⁻¹) = (a' * g) * x' * g⁻¹ := by group
        _ = (g * a') * x' * g⁻¹ := by rw [(hga a' ha').eq]
        _ = g * (a' * x') * g⁻¹ := by group
    rw [e, orderOf_conj_eq]
    exact h3a
  have heq := eq_of_orderOf_mul_eq_three hclass hD hc ha'.1 hx hx'g hx' ha'x h3g h3a
  calc g * x' = g * x' * g⁻¹ * g := by group
    _ = x' * g := by rw [heq]

theorem commute_of_conj_mem_rootSet_of_centralizes' (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) {a x g : G} (ha : a ∈ D) (hx : x ∈ D) (hax : ¬ Commute a x)
    (hoddax : Odd (orderOf (a * x))) (hx1 : OneOpposite D a x)
    (hga : ∀ a' ∈ rootSet D a, Commute g a') (hgx : g * x * g⁻¹ ∈ rootSet D x) {u : G}
    (hu : u ∈ rootGroup D x) : Commute g u := by
  induction hu using Subgroup.closure_induction with
  | mem y hy =>
    exact commute_of_conj_mem_rootSet_of_centralizes h hc hs ha hx hax hoddax hx1 hga hgx hy
  | one => exact Commute.one_right g
  | mul y z _ _ ihy ihz => exact ihy.mul_right ihz
  | inv y _ ih => exact ih.inv_right

theorem conj_mem_rootGroup_of_commute (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a c s : G}
    (hca : Commute c a) (hs : s ∈ rootGroup D a) : c * s * c⁻¹ ∈ rootGroup D a := by
  have h1 : (rootGroup D a).map (MulAut.conj c).toMonoidHom = rootGroup D a := by
    rw [← rootGroup_conj hclass, hca.eq, mul_inv_cancel_right]
  rw [← h1]
  exact ⟨s, hs, rfl⟩

namespace LineSetting

variable (hL : LineSetting G D)
include hL

theorem commute_of_mem_lineGroup {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {g : G} (hg : g ∈ lineGroup D a d) {s : G}
    (hs : s ∈ rootGroup D a) : Commute g s := by
  have hclass := hL.hyp.isClass
  have hle : lineGroup D a d ≤ Subgroup.centralizer (rootGroup D a : Set G) := by
    refine iSup_le fun c => ?_
    have hc : Commute (c : G) a := Subgroup.mem_centralizer_singleton_iff.1 c.2
    rw [Subgroup.map_le_iff_le_comap]
    have key : ∀ u : G, (∀ t ∈ rootGroup D a, Commute u t) →
        u ∈ (Subgroup.centralizer (rootGroup D a : Set G)).comap
          (MulAut.conj (c : G)).toMonoidHom := by
      intro u hu
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : (c : G)⁻¹ * t * (c : G)⁻¹⁻¹ ∈ rootGroup D a :=
        conj_mem_rootGroup_of_commute hclass hc.inv_left ht
      have := (Commute.conj_iff (c : G)).2 (hu _ ht')
      have e : (c : G) * ((c : G)⁻¹ * t * (c : G)⁻¹⁻¹) * (c : G)⁻¹ = t := by group
      rw [e] at this
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact this.symm.eq
    refine sup_le (fun u hu => key u fun t ht => ?_) (fun u hu => key u fun t ht => ?_)
    · exact hL.commute_of_mem_nCore_of_commute ha hd had hadD hdT hu.1
        (Subgroup.mem_centralizer_singleton_iff.1 hu.2) (Subgroup.mem_sup_left ht)
    · exact commute_of_mem_nCore_of_mem_rootGroup hu ht
  exact (Subgroup.mem_centralizer_iff.1 (hle hg) s hs).symm

end LineSetting

theorem top_of_forall_not_special {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) (IH : RootIHStructE G) (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d)
    {a b x : G} (hb : b ∈ D) (ha : a ∈ D) (hba : Commute b a) (hbaD : b * a ∈ D)
    (haT : a ∉ rootSet D b) (hx : x ∈ D) (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x)))
    (h1 : OneOpposite D b x)
    (hno : ∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a → orderOf (x * p) ≠ 4) :
    rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x = ⊤ := by
  by_contra hU
  rcases gate_or_degenerate h hc hs hconn hAll IH hl hb ha hba hbaD haT hx hbx hoddbx hU with
    ⟨p, hp, hpL, h4⟩ | hdeg
  · exact hno p hp hpL h4
  · obtain ⟨e, he, f, hf, h4⟩ := degenerateGateStep G D h IH hl hc hs hconn hAll a ha b hb x hx hba
      hbaD haT hbx hoddbx h1 hno
    exact hdeg e he f hf h4

end CFSG.Timmesfeld.Bridge
