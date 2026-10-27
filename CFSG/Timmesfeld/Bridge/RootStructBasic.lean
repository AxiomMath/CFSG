module

public import CFSG.Timmesfeld.RootInduction
public import CFSG.Timmesfeld.Exceptional.Polar
public import CFSG.Timmesfeld.Closure.LS

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

@[expose] def OppositeDetermines (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ e ∈ D, (∀ x ∈ D, (¬ Commute d x ∧ Odd (orderOf (d * x))) ↔
    (¬ Commute e x ∧ Odd (orderOf (e * x)))) → e ∈ rootSet D d

@[expose] def OppositeDeterminesStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → OppositeDetermines D

@[expose] def nCore (D : Set G) (d : G) : Subgroup G :=
  Subgroup.closure {x | x ∈ D ∧ x ∈ Moufang.twoCore d}

theorem closure_eq_nCore (D : Set G) (d : G) :
    Subgroup.closure {x | x ∈ D ∧ x ∈ Moufang.twoCore d} = nCore D d :=
  rfl

theorem subset_nCore (D : Set G) (d : G) : {x | x ∈ D ∧ x ∈ Moufang.twoCore d} ⊆ nCore D d :=
  Subgroup.subset_closure

theorem mem_nCore_of_mem_twoCore {d x : G} (hx : x ∈ D) (hxQ : x ∈ Moufang.twoCore d) :
    x ∈ nCore D d :=
  Subgroup.subset_closure ⟨hx, hxQ⟩

theorem nCore_le_twoCore (D : Set G) (d : G) : nCore D d ≤ Moufang.twoCore d :=
  (Subgroup.closure_le _).2 fun _ hx => hx.2

theorem mem_twoCore_of_mem_nCore {d x : G} (hx : x ∈ nCore D d) : x ∈ Moufang.twoCore d :=
  nCore_le_twoCore D d hx

theorem commute_of_mem_nCore {d x : G} (hx : x ∈ nCore D d) : Commute x d :=
  Moufang.commute_of_mem_twoCore (mem_twoCore_of_mem_nCore hx)

theorem isPGroup_nCore [Finite G] (D : Set G) (d : G) : IsPGroup 2 (nCore D d) :=
  (Moufang.isPGroup_twoCore d).to_le (nCore_le_twoCore D d)

theorem isNilpotent_nCore [Finite G] (D : Set G) (d : G) : Group.IsNilpotent (nCore D d) :=
  (isPGroup_nCore D d).isNilpotent

theorem mem_twoCore_of_collinear [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hxd : Commute x d)
    (hxdD : x * d ∈ D) : x ∈ Moufang.twoCore d :=
  mem_map_pCore_centralizer hclass hD hd hx hxd (Or.inl hxdD)

theorem mem_nCore_of_collinear [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hxd : Commute x d)
    (hxdD : x * d ∈ D) : x ∈ nCore D d :=
  mem_nCore_of_mem_twoCore hx (mem_twoCore_of_collinear hclass hD hd hx hxd hxdD)

theorem self_mem_twoCore {d : G} (hd : orderOf d = 2) : d ∈ Moufang.twoCore d := by
  set H := Subgroup.centralizer ({d} : Set G)
  have hdH : d ∈ H := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hn : (Subgroup.zpowers (⟨d, hdH⟩ : H)).Normal := ⟨fun n hn g => by
    have hc : g * (⟨d, hdH⟩ : H) = ⟨d, hdH⟩ * g :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨d, hdH⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hd, pow_one])
  have hle : Subgroup.zpowers (⟨d, hdH⟩ : H) ≤ CFSG.pCore 2 H := le_sSup ⟨hn, hp⟩
  exact ⟨⟨d, hdH⟩, hle (Subgroup.mem_zpowers _), rfl⟩

theorem self_mem_nCore (hD : IsRootInvolutionSet D) {d : G} (hd : d ∈ D) : d ∈ nCore D d :=
  mem_nCore_of_mem_twoCore hd (self_mem_twoCore (hD.orderOf_eq_two hd))

theorem collinear_conj_of_orderOf_eq_four (hD : IsRootInvolutionSet D) {c d : G} (hc : c ∈ D)
    (hd : d ∈ D) (h4 : orderOf (c * d) = 4) :
    Commute (c * d * c) d ∧ c * d * c * d ∈ D := by
  have h4' : orderOf (d * c) = 4 := by rwa [orderOf_mul_comm_eq]
  obtain ⟨hsqD, hdsq, -, hcdc⟩ := sq_mem_of_orderOf_eq_four hD hd hc h4'
  rw [hcdc]
  refine ⟨(Commute.refl d).mul_left hdsq.symm, ?_⟩
  rwa [mul_assoc, ← hdsq.eq, ← mul_assoc, hD.mul_self_eq_one hd, one_mul]

theorem conj_mem_twoCore_of_orderOf_eq_four [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {c d : G} (hc : c ∈ D) (hd : d ∈ D)
    (h4 : orderOf (c * d) = 4) : c * d * c ∈ Moufang.twoCore d := by
  obtain ⟨hcom, hmul⟩ := collinear_conj_of_orderOf_eq_four hD hc hd h4
  have hw : c * d * c ∈ D := by simpa [hD.inv_eq hc] using conj_mem_of_isClass hclass c hd
  exact mem_twoCore_of_collinear hclass hD hd hw hcom hmul

theorem conj_mem_nCore (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d g x : G}
    (hg : Commute g d) (hx : x ∈ nCore D d) : g * x * g⁻¹ ∈ nCore D d := by
  unfold nCore at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    exact mem_nCore_of_mem_twoCore (conj_mem_of_isClass hclass g hx.1)
      (Moufang.conj_mem_twoCore hg hx.2)
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ihx

theorem conj_mem_upperCentralSeries_nCore (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {d g x : G} (hg : Commute g d) (hx : x ∈ nCore D d) {k : ℕ}
    (hxk : (⟨x, hx⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) k) :
    (⟨g * x * g⁻¹, conj_mem_nCore hclass hg hx⟩ : nCore D d) ∈
      Subgroup.upperCentralSeries (nCore D d) k := by
  have hg' : Commute g⁻¹ d := hg.inv_left
  let φ : nCore D d ≃* nCore D d :=
    { toFun := fun y => ⟨g * y * g⁻¹, conj_mem_nCore hclass hg y.2⟩
      invFun := fun y => ⟨g⁻¹ * y * g, by simpa using conj_mem_nCore hclass hg' y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
  exact Subgroup.characteristic_iff_map_le.mp inferInstance φ ⟨⟨x, hx⟩, hxk, rfl⟩

theorem mem_center_nCore_iff {d x : G} (hx : x ∈ nCore D d) :
    (⟨x, hx⟩ : nCore D d) ∈ Subgroup.center (nCore D d) ↔
      ∀ s ∈ D, s ∈ Moufang.twoCore d → Commute x s := by
  constructor
  · intro hZ s hs hsQ
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hZ ⟨s, mem_nCore_of_mem_twoCore hs hsQ⟩)).symm
  · intro h
    have hle : nCore D d ≤ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.closure_le _).2 fun s hs =>
        Subgroup.mem_centralizer_singleton_iff.2 (h s hs.1 hs.2).eq.symm
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle y.2))

theorem not_opposite_of_mem_twoCore [Finite G] {d x y : G} (hxQ : x ∈ Moufang.twoCore d)
    (hyQ : y ∈ Moufang.twoCore d) : ¬ (¬ Commute x y ∧ Odd (orderOf (x * y))) := by
  rintro ⟨hxy, hodd⟩
  have h1 := Special.eq_one_of_mem_of_isPGroup (Moufang.isPGroup_twoCore d)
    ((Moufang.twoCore d).mul_mem hxQ hyQ) hodd
  apply hxy
  rw [eq_inv_of_mul_eq_one_right h1]
  exact (Commute.refl x).inv_right

theorem not_opposite_of_mem_twoCore_of_commute [Finite G] (hD : IsRootInvolutionSet D)
    {d s c : G} (hsQ : s ∈ Moufang.twoCore d) (hc : c ∈ D) (hcd : Commute c d) :
    ¬ (¬ Commute s c ∧ Odd (orderOf (s * c))) := by
  rintro ⟨hsc, hodd⟩
  have hmem : s * (c * s * c⁻¹) ∈ Moufang.twoCore d :=
    (Moufang.twoCore d).mul_mem hsQ (Moufang.conj_mem_twoCore hcd hsQ)
  rw [hD.inv_eq hc, show s * (c * s * c) = (s * c) ^ 2 by rw [sq]; simp only [mul_assoc]] at hmem
  have h1 := Special.eq_one_of_mem_of_isPGroup (Moufang.isPGroup_twoCore d) hmem
    (Odd.of_dvd_nat hodd (orderOf_pow_dvd 2))
  have h2 : orderOf (s * c) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  apply hsc
  rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h2)]
  exact (Commute.refl s).inv_right

theorem eq_one_of_mem_twoCore_of_inv [Finite G] {u a r : G} (ha : a ∈ Moufang.twoCore u)
    (hr : Commute r u) (hinv : a * r * a⁻¹ = r⁻¹) (hodd : Odd (orderOf r)) : r = 1 := by
  have hmem : a * (r * a * r⁻¹)⁻¹ ∈ Moufang.twoCore u :=
    (Moufang.twoCore u).mul_mem ha ((Moufang.twoCore u).inv_mem (Moufang.conj_mem_twoCore hr ha))
  rw [show a * (r * a * r⁻¹)⁻¹ = a * r * a⁻¹ * r⁻¹ by group, hinv, ← sq] at hmem
  have hodd' : Odd (orderOf (r⁻¹ ^ 2)) :=
    Odd.of_dvd_nat (by rwa [orderOf_inv]) (orderOf_pow_dvd 2)
  have h1 := Special.eq_one_of_mem_of_isPGroup (Moufang.isPGroup_twoCore u) hmem hodd'
  rw [inv_pow, inv_eq_one] at h1
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem mul_sq_mem_twoCore (hD : IsRootInvolutionSet D) {d s t : G} (hs : s ∈ D) (ht : t ∈ D)
    (hsQ : s ∈ Moufang.twoCore d) (htQ : t ∈ Moufang.twoCore d) (h4 : orderOf (s * t) = 4) :
    (s * t) ^ 2 ∈ D ∧ (s * t) ^ 2 ∈ Moufang.twoCore d :=
  ⟨hD.sq_mem hs ht h4, (Moufang.twoCore d).pow_mem ((Moufang.twoCore d).mul_mem hsQ htQ) 2⟩

theorem commutatorElement_eq_one_or_mem_twoCore [Finite G] (hD : IsRootInvolutionSet D)
    {d s t : G} (hs : s ∈ D) (ht : t ∈ D) (hsQ : s ∈ Moufang.twoCore d)
    (htQ : t ∈ Moufang.twoCore d) :
    ⁅s, t⁆ = 1 ∨ (⁅s, t⁆ ∈ D ∧ ⁅s, t⁆ ∈ Moufang.twoCore d) := by
  rw [show ⁅s, t⁆ = (s * t) ^ 2 by
    rw [commutatorElement_def, hD.inv_eq hs, hD.inv_eq ht, sq, ← mul_assoc]]
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hs ht with h | h | ⟨h, h'⟩
  · exact Or.inl
      ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hs) (hD.mul_self_eq_one ht)).1 h)
  · exact Or.inr (mul_sq_mem_twoCore hD hs ht hsQ htQ h)
  · exact absurd ⟨h', h⟩ (not_opposite_of_mem_twoCore hsQ htQ)

theorem not_commute_of_opposite_of_line (hD : IsRootInvolutionSet D) {u v c : G} (hu : u ∈ D)
    (hv : v ∈ D) (huv : Commute u v) (huvD : u * v ∈ D) (hc : c ∈ D) (huc : ¬ Commute u c)
    (hodd : Odd (orderOf (u * c))) : ¬ Commute v c ∧ ¬ Commute (u * v) c := by
  have hodd' : Odd (orderOf (c * u)) := by rwa [orderOf_mul_comm_eq]
  have key : ∀ w ∈ D, Commute u w → u * w ∈ D → ¬ Commute w c := by
    intro w hw huw huwD hwc
    have h1 := Moufang.eq_of_collinear_of_odd hD hw huw huwD hc hwc.symm hodd'
    apply huc
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (Commute.refl u).inv_right
  refine ⟨key v hv huv huvD, key (u * v) huvD ((Commute.refl u).mul_right huv) ?_⟩
  rwa [← mul_assoc, hD.mul_self_eq_one hu, one_mul]

theorem opposite_of_opposite_of_special_of_line (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {u v c : G} (hu : u ∈ D) (hv : v ∈ D) (huv : Commute u v)
    (huvD : u * v ∈ D) (hc : c ∈ D) (huc : ¬ Commute u c) (hodd : Odd (orderOf (u * c)))
    (h4 : orderOf (c * v) = 4) : ¬ Commute (u * v) c ∧ Odd (orderOf (u * v * c)) := by
  have hnc := (not_commute_of_opposite_of_line hD hu hv huv huvD hc huc hodd).2
  refine ⟨hnc, ?_⟩
  rcases commute_or_orderOf_mul_eq_four_or_odd hD huvD hc with h | h | ⟨h, -⟩
  · exact absurd h hnc
  · rw [orderOf_mul_comm_eq] at h
    exact (Closure.not_special_special_of_opposite hclass hD hu hv huv hc huc hodd h4 h).elim
  · exact h

end CFSG.Timmesfeld.Bridge
