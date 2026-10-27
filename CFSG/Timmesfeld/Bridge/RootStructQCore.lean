module

public import CFSG.Timmesfeld.Bridge.RootStructBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem opposite_of_mem_rootSet_of_opposite (hD : IsRootInvolutionSet D) {x y e f : G}
    (hx : x ∈ D) (hy : y ∈ D) (he : e ∈ rootSet D x) (hf : f ∈ rootSet D y)
    (h : ¬ Commute x y ∧ Odd (orderOf (x * y))) : ¬ Commute e f ∧ Odd (orderOf (e * f)) := by
  obtain ⟨h1, h2⟩ := odd_orderOf_mul_of_mem_rootSet hD hx hy he hf h.2 h.1
  exact ⟨h2, h1⟩

theorem conj_inv_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d g : G} (hd : d ∈ D)
    (hg : g * d * g⁻¹ ∈ rootSet D d) : g⁻¹ * d * g⁻¹⁻¹ ∈ rootSet D d := by
  have hmem : d ∈ (fun x => g * x * g⁻¹) '' rootSet D d := by
    rw [← rootSet_conj hclass, rootSet_eq_of_mem hg]
    exact mem_rootSet_self hd
  obtain ⟨y, hy, hyd⟩ := hmem
  have hy' : g⁻¹ * d * g⁻¹⁻¹ = y := by rw [← hyd]; group
  rw [hy']
  exact hy

variable [Finite G]

theorem mem_twoCore_of_forall_not_opposite (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {z x : G} (hx : x ∈ D) (hxz : Commute x z)
    (h : ∀ g : G, Commute g z →
      ¬ (¬ Commute x (g * x * g⁻¹) ∧ Odd (orderOf (x * (g * x * g⁻¹))))) :
    x ∈ Moufang.twoCore z := by
  set H := Subgroup.centralizer ({z} : Set G) with hH
  have hxH : x ∈ H := by
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro g rfl
    exact hxz.symm.eq
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, CFSG.BaerSuzuki.baer_suzuki_iff]
  intro g
  have hgz : Commute (g : G) z := (Subgroup.mem_centralizer_iff.mp g.2 z rfl).symm
  have hcD : (g : G) * x * (g : G)⁻¹ ∈ D := conj_mem_of_isClass hclass g hx
  have h1 : (⟨x, hxH⟩ : H) * ⟨x, hxH⟩ = 1 := Subtype.ext (hD.mul_self_eq_one hx)
  have h2 : (g * ⟨x, hxH⟩ * g⁻¹) * (g * ⟨x, hxH⟩ * g⁻¹) = 1 :=
    Subtype.ext (by simpa using hD.mul_self_eq_one hcD)
  have hord : orderOf (x * ((g : G) * x * (g : G)⁻¹)) =
      orderOf ((⟨x, hxH⟩ : H) * (g * ⟨x, hxH⟩ * g⁻¹)) := by
    rw [← Subgroup.orderOf_coe]
    simp
  rcases hD.orderOf_mul hx hcD with h24 | h24 | hodd
  · exact Special.isPGroup_closure_pair_of_orderOf h1 h2 (Or.inl (hord ▸ h24))
  · exact Special.isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inl (hord ▸ h24)))
  · by_cases hc : Commute x ((g : G) * x * (g : G)⁻¹)
    · have hsq := (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx)
        (hD.mul_self_eq_one hcD)).1 hc
      have h1' : orderOf (x * ((g : G) * x * (g : G)⁻¹)) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hsq) with h' | h'
        · exact h'
        · rw [h'] at hodd
          exact absurd hodd (by decide)
      exact Special.isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inr (hord ▸ h1')))
    · exact absurd ⟨hc, hodd⟩ (h g hgz)

theorem mem_twoCore_of_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {z x e : G} (hz : z ∈ D) (hx : x ∈ D)
    (hxQ : x ∈ Moufang.twoCore z) (he : e ∈ rootSet D x) : e ∈ Moufang.twoCore z := by
  have hez : Commute e z := (he.2 z hz).2 (Moufang.commute_of_mem_twoCore hxQ)
  refine mem_twoCore_of_forall_not_opposite hclass hD he.1 hez fun g hg hopp => ?_
  have hx'Q : g * x * g⁻¹ ∈ Moufang.twoCore z := Moufang.conj_mem_twoCore hg hxQ
  have he' : g * e * g⁻¹ ∈ rootSet D (g * x * g⁻¹) := by
    rw [rootSet_conj hclass]
    exact ⟨e, he, rfl⟩
  exact not_opposite_of_mem_twoCore hxQ hx'Q (opposite_of_mem_rootSet_of_opposite hD he.1
    (conj_mem_of_isClass hclass g he.1) (mem_rootSet_comm hx he)
    (mem_rootSet_comm (conj_mem_of_isClass hclass g hx) he') hopp)

theorem mem_twoCore_of_mem_rootSet_self (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d d' x : G} (hd' : d' ∈ rootSet D d) (hx : x ∈ D)
    (hxQ : x ∈ Moufang.twoCore d) : x ∈ Moufang.twoCore d' := by
  have hxd : Commute x d := Moufang.commute_of_mem_twoCore hxQ
  have hxd' : Commute x d' := ((hd'.2 x hx).2 hxd.symm).symm
  refine mem_twoCore_of_forall_not_opposite hclass hD hx hxd' fun g hg hopp => ?_
  have hcD : g * x * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hx
  have hcd' : Commute (g * x * g⁻¹) d' := (hg.mul_left hxd').mul_left hg.inv_left
  have hcd : Commute (g * x * g⁻¹) d := ((hd'.2 _ hcD).1 hcd'.symm).symm
  exact not_opposite_of_mem_twoCore_of_commute hD hxQ hcD hcd hopp

theorem nCore_eq_of_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d d' : G} (hd : d ∈ D) (hd' : d' ∈ rootSet D d) :
    nCore D d' = nCore D d := by
  have hd'' : d ∈ rootSet D d' := mem_rootSet_comm hd hd'
  refine congrArg Subgroup.closure (Set.ext fun x => ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩)
  · exact mem_twoCore_of_mem_rootSet_self hclass hD hd'' h.1 h.2
  · exact mem_twoCore_of_mem_rootSet_self hclass hD hd' h.1 h.2

theorem conj_mem_nCore_of_conj_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d g x : G} (hd : d ∈ D) (hg : g * d * g⁻¹ ∈ rootSet D d)
    (hx : x ∈ nCore D d) : g * x * g⁻¹ ∈ nCore D d := by
  unfold nCore at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine mem_nCore_of_mem_twoCore (conj_mem_of_isClass hclass g hx.1) ?_
    exact mem_twoCore_of_mem_rootSet_self hclass hD (mem_rootSet_comm hd hg)
      (conj_mem_of_isClass hclass g hx.1) (Moufang.mem_twoCore_conj hx.2 g)
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ihx

theorem conj_mem_upperCentralSeries_nCore_of_conj_mem_rootSet
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) {d g x : G}
    (hd : d ∈ D) (hg : g * d * g⁻¹ ∈ rootSet D d) (hx : x ∈ nCore D d) {k : ℕ}
    (hxk : (⟨x, hx⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) k) :
    (⟨g * x * g⁻¹, conj_mem_nCore_of_conj_mem_rootSet hclass hD hd hg hx⟩ : nCore D d) ∈
      Subgroup.upperCentralSeries (nCore D d) k := by
  have hg' := conj_inv_mem_rootSet hclass hd hg
  let φ : nCore D d ≃* nCore D d :=
    { toFun := fun y => ⟨g * y * g⁻¹, conj_mem_nCore_of_conj_mem_rootSet hclass hD hd hg y.2⟩
      invFun := fun y => ⟨g⁻¹ * y * g, by
        simpa using conj_mem_nCore_of_conj_mem_rootSet hclass hD hd hg' y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
  exact Subgroup.characteristic_iff_map_le.mp inferInstance φ ⟨⟨x, hx⟩, hxk, rfl⟩

theorem rootSet_subset_nCore (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ rootSet D d) :
    e ∈ nCore D d :=
  mem_nCore_of_mem_twoCore he.1 (mem_twoCore_of_mem_rootSet hclass hD hd hd
    (self_mem_twoCore (hD.orderOf_eq_two hd)) he)

theorem commute_of_mem_nCore_of_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d e x : G} (hd : d ∈ D) (he : e ∈ rootSet D d)
    (hx : x ∈ nCore D d) : Commute x e := by
  rw [← nCore_eq_of_mem_rootSet hclass hD hd he] at hx
  exact commute_of_mem_nCore hx

end CFSG.Timmesfeld.Bridge
