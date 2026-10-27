module

public import CFSG.Timmesfeld.Special.Basic
public import CFSG.Timmesfeld.RootSubgroupClosure

public section

open scoped commutatorElement

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem mul_sq_eq_mul_sq_comm {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h4 : orderOf (x * y) = 4) : (x * y) ^ 2 = (y * x) ^ 2 := by
  have hinv : (x * y)⁻¹ = y * x := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  have hx4 : (x * y) ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one (x * y)
  rw [← hinv, inv_pow, eq_inv_iff_mul_eq_one, ← pow_add]
  exact hx4

section Hom

variable {d e : G}

theorem commute_commutatorElement_of_mem_rootGroup (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a g g' : G}
    (ha : a ∈ rootSet D d) (hg : g ∈ rootGroup D e) (hg' : g' ∈ rootGroup D e) :
    Commute g ⁅a, g'⁆ := by
  have ha' : a ∈ D := ha.1
  have h4' : orderOf (e * a) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_mem_rootSet hD hd he ha (mem_rootSet_self he) h4
  obtain ⟨-, hef, -, hconj⟩ := sq_mem_of_orderOf_eq_four hD he ha' h4'
  have hainv : a⁻¹ = a := hD.inv_eq ha'
  have hcomm : Commute e (a * e * a⁻¹) := by
    rw [hainv, hconj]
    exact (Commute.refl e).mul_right hef
  have hmem : a * g' * a⁻¹ ∈ rootGroup D (a * e * a⁻¹) := by
    rw [rootGroup_conj hclass]
    exact ⟨g', hg', rfl⟩
  have h1 : Commute g (a * g' * a⁻¹) :=
    commute_of_mem_rootGroup_of_commute' (conj_mem_of_isClass hclass a he) hg hmem hcomm
  have h2 : Commute g g'⁻¹ := commute_of_mem_rootGroup he hg ((rootGroup D e).inv_mem hg')
  rw [commutatorElement_def]
  exact h1.mul_right h2

theorem commutatorElement_mul_of_mem_rootGroup (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a g g' : G}
    (ha : a ∈ rootSet D d) (hg : g ∈ rootGroup D e) (hg' : g' ∈ rootGroup D e) :
    ⁅a, g * g'⁆ = ⁅a, g⁆ * ⁅a, g'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc _ g, mul_assoc,
    (commute_commutatorElement_of_mem_rootGroup hclass hD hd he h4 ha hg hg').eq,
    mul_inv_cancel_right]

@[expose] def rootGroupCommutatorHom (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a : G}
    (ha : a ∈ rootSet D d) : rootGroup D e →* G where
  toFun g := ⁅a, (g : G)⁆
  map_one' := by simp
  map_mul' g g' := commutatorElement_mul_of_mem_rootGroup hclass hD hd he h4 ha g.2 g'.2

@[simp]
theorem rootGroupCommutatorHom_apply (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a : G}
    (ha : a ∈ rootSet D d) (g : rootGroup D e) :
    rootGroupCommutatorHom hclass hD hd he h4 ha g = ⁅a, (g : G)⁆ :=
  rfl

theorem rootGroupCommutatorHom_injective (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) {a : G} (ha : a ∈ rootSet D d) :
    Function.Injective (rootGroupCommutatorHom hclass hD hd he h4 ha) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  have hg1 : (g : G) ≠ 1 := fun h => hne (Subtype.ext h)
  have hgT : (g : G) ∈ rootSet D e :=
    (mem_rootSet_iff_mem_rootGroup_of_rootClosure hD hc he).2 ⟨g.2, hg1⟩
  have h4g := orderOf_mul_eq_four_of_mem_rootSet hD hd he ha hgT h4
  rw [rootGroupCommutatorHom_apply, Special.commutatorElement_eq_mul_sq (hD.mul_self_eq_one ha.1)
    (hD.mul_self_eq_one hgT.1)] at hg
  have h2 := orderOf_dvd_of_pow_eq_one hg
  rw [h4g] at h2
  norm_num at h2

theorem mul_sq_mul_eq_mul (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) {a b b' : G} (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D e)
    (hb' : b' ∈ rootSet D e) (hbb' : b ≠ b') : (a * (b * b')) ^ 2 = (a * b) ^ 2 * (a * b') ^ 2 := by
  have hbb : b * b' ∈ rootSet D e := hc e he b hb b' hb' hbb'
  have h2 := hD.mul_self_eq_one ha.1
  rw [← Special.commutatorElement_eq_mul_sq h2 (hD.mul_self_eq_one hbb.1),
    ← Special.commutatorElement_eq_mul_sq h2 (hD.mul_self_eq_one hb.1),
    ← Special.commutatorElement_eq_mul_sq h2 (hD.mul_self_eq_one hb'.1)]
  exact commutatorElement_mul_of_mem_rootGroup hclass hD hd he h4 ha
    (rootSet_subset_rootGroup D e hb) (rootSet_subset_rootGroup D e hb')

theorem mul_sq_injOn (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) {a : G} (ha : a ∈ rootSet D d) :
    Set.InjOn (fun b => (a * b) ^ 2) (rootSet D e) := by
  intro b hb b' hb' hbb'
  have h := @rootGroupCommutatorHom_injective G _ D d e hclass hD hc hd he h4 a ha
    ⟨b, rootSet_subset_rootGroup D e hb⟩ ⟨b', rootSet_subset_rootGroup D e hb'⟩
  have h2 := hD.mul_self_eq_one ha.1
  simp only [rootGroupCommutatorHom_apply, Special.commutatorElement_eq_mul_sq h2
    (hD.mul_self_eq_one hb.1), Special.commutatorElement_eq_mul_sq h2
    (hD.mul_self_eq_one hb'.1)] at h
  exact Subtype.ext_iff.mp (h hbb')

end Hom

section Intersection

variable {x y : G}

theorem commute_mul_sq_of_commute_left (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hx : x ∈ D) (hy : y ∈ D) (h4 : orderOf (x * y) = 4)
    {x' f : G} (hx' : x' ∈ rootSet D x) (hf : f ∈ D) (hxf : Commute x f)
    (hzf : Commute ((x * y) ^ 2) f) : Commute ((x' * y) ^ 2) f := by
  have h4' := orderOf_mul_eq_four_of_mem_rootSet hD hx hy hx' (mem_rootSet_self hy) h4
  obtain ⟨-, -, -, hconj⟩ := sq_mem_of_orderOf_eq_four hD hx hy h4
  obtain ⟨-, -, -, hconj'⟩ := sq_mem_of_orderOf_eq_four hD hx'.1 hy h4'
  have hy2 := hD.mul_self_eq_one hy
  have hyinv : y⁻¹ = y := hD.inv_eq hy
  have hx'f : Commute x' f := (hx'.2 f hf).2 hxf
  have h1 : Commute (y * x * y) f := by rw [hconj]; exact hxf.mul_left hzf
  have h2 : Commute x (y * f * y⁻¹) := by
    have := (Commute.conj_iff y).2 h1
    rwa [show y * (y * x * y) * y⁻¹ = x by
      rw [hyinv, ← mul_assoc, ← mul_assoc, hy2, one_mul, mul_assoc, hy2, mul_one]] at this
  have h3 : Commute x' (y * f * y⁻¹) :=
    ((hx'.2 _ (conj_mem_of_isClass hclass y hf)).2 h2)
  have h4c : Commute (y * x' * y) f := by
    have := (Commute.conj_iff y⁻¹).2 h3
    rwa [inv_inv, show y⁻¹ * x' * y = y * x' * y by rw [hyinv],
      show y⁻¹ * (y * f * y⁻¹) * y = f by group] at this
  rw [hconj'] at h4c
  have := hx'f.mul_left h4c
  rwa [← mul_assoc, hD.mul_self_eq_one hx'.1, one_mul] at this

theorem commute_mul_sq_iff_of_commute_left (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hx : x ∈ D) (hy : y ∈ D) (h4 : orderOf (x * y) = 4)
    {x' f : G} (hx' : x' ∈ rootSet D x) (hf : f ∈ D) (hxf : Commute x f) :
    Commute ((x * y) ^ 2) f ↔ Commute ((x' * y) ^ 2) f :=
  ⟨commute_mul_sq_of_commute_left hclass hD hx hy h4 hx' hf hxf,
    commute_mul_sq_of_commute_left hclass hD hx'.1 hy
      (orderOf_mul_eq_four_of_mem_rootSet hD hx hy hx' (mem_rootSet_self hy) h4)
      (mem_rootSet_comm hx hx') hf ((hx'.2 f hf).2 hxf)⟩

theorem commute_mul_sq_iff_of_commute_right (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hx : x ∈ D) (hy : y ∈ D) (h4 : orderOf (x * y) = 4)
    {y' f : G} (hy' : y' ∈ rootSet D y) (hf : f ∈ D) (hyf : Commute y f) :
    Commute ((x * y) ^ 2) f ↔ Commute ((x * y') ^ 2) f := by
  have h4y : orderOf (y * x) = 4 := by rwa [orderOf_mul_comm_eq]
  have h4' : orderOf (x * y') = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hx hy (mem_rootSet_self hx) hy' h4
  rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hy) h4,
    mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hy'.1) h4']
  exact commute_mul_sq_iff_of_commute_left hclass hD hy hx h4y hy' hf hyf

end Intersection

end CFSG.Timmesfeld
