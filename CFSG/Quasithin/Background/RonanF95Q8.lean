module

public import CFSG.Quasithin.H13.L32NQ8Pow

public section

namespace CFSG.Quasithin.RonanF95

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_mul_of_sup_eq {V₁ P Xg Yg : Subgroup G} (hV₁X : V₁ ≤ Xg) (hXP : Xg ≤ P)
    (hYP : Yg ≤ P) (hXYs : Xg ⊔ Yg = P) (hcomm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁)
    {g : G} (hg : g ∈ P) : ∃ x ∈ Xg, ∃ y ∈ Yg, g = x * y := by
  have hYX : ∀ y ∈ Yg, ∀ x ∈ Xg, ∃ x' ∈ Xg, ∃ y' ∈ Yg, y * x = x' * y' := by
    intro y hy x hx
    refine ⟨(x * y * x⁻¹ * y⁻¹)⁻¹ * x,
      Xg.mul_mem (Xg.inv_mem (hV₁X (hcomm x (hXP hx) y (hYP hy)))) hx, y, hy, ?_⟩
    group
  let K : Subgroup G :=
    { carrier := {g | ∃ x ∈ Xg, ∃ y ∈ Yg, g = x * y}
      one_mem' := ⟨1, Xg.one_mem, 1, Yg.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
        obtain ⟨x', hx', y', hy', h⟩ := hYX y₁ hy₁ x₂ hx₂
        refine ⟨x₁ * x', Xg.mul_mem hx₁ hx', y' * y₂, Yg.mul_mem hy' hy₂, ?_⟩
        calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
          _ = x₁ * (x' * y') * y₂ := by rw [h]
          _ = x₁ * x' * (y' * y₂) := by group
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        obtain ⟨x', hx', y', hy', h⟩ := hYX y⁻¹ (Yg.inv_mem hy) x⁻¹ (Xg.inv_mem hx)
        exact ⟨x', hx', y', hy', by rw [mul_inv_rev]; exact h⟩ }
  have hXK : Xg ≤ K := fun x hx => ⟨x, hx, 1, Yg.one_mem, (mul_one x).symm⟩
  have hYK : Yg ≤ K := fun y hy => ⟨1, Xg.one_mem, y, hy, (one_mul y).symm⟩
  have hPK : P ≤ K := by
    rw [← hXYs]
    exact sup_le hXK hYK
  obtain ⟨x, hx, y, hy, h⟩ := hPK hg
  exact ⟨x, hx, y, hy, h⟩

theorem card_fiber_eq_card {V₁ Xg Yg : Subgroup G} (hV₁X : V₁ ≤ Xg) (hV₁Y : V₁ ≤ Yg)
    (hXY : Xg ⊓ Yg = V₁) {b : G} (a₀ : ↥Xg × ↥Yg) (hb : (a₀.1 : G) * (a₀.2 : G) = b) :
    Nat.card {a : ↥Xg × ↥Yg // (a.1 : G) * (a.2 : G) = b} = Nat.card V₁ := by
  have e1 : ∀ a : {a : ↥Xg × ↥Yg // (a.1 : G) * (a.2 : G) = b},
      (a₀.1 : G) = (a.1.1 : G) * (a.1.2 : G) * (a₀.2 : G)⁻¹ := by
    intro a
    rw [a.2, ← hb]
    group
  have hκ : ∀ a : {a : ↥Xg × ↥Yg // (a.1 : G) * (a.2 : G) = b},
      (a.1.2 : G) * (a₀.2 : G)⁻¹ ∈ V₁ := by
    intro a
    rw [← hXY]
    refine Subgroup.mem_inf.mpr ⟨?_, Yg.mul_mem a.1.2.2 (Yg.inv_mem a₀.2.2)⟩
    have key : (a.1.2 : G) * (a₀.2 : G)⁻¹ = (a.1.1 : G)⁻¹ * (a₀.1 : G) := by
      rw [e1 a]
      group
    rw [key]
    exact Xg.mul_mem (Xg.inv_mem a.1.1.2) a₀.1.2
  have hι1 : ∀ v : V₁, (a₀.1 : G) * (v : G)⁻¹ ∈ Xg := fun v =>
    Xg.mul_mem a₀.1.2 (Xg.inv_mem (hV₁X v.2))
  have hι2 : ∀ v : V₁, (v : G) * (a₀.2 : G) ∈ Yg := fun v =>
    Yg.mul_mem (hV₁Y v.2) a₀.2.2
  have hι3 : ∀ v : V₁, (a₀.1 : G) * (v : G)⁻¹ * ((v : G) * (a₀.2 : G)) = b := fun v => by
    rw [← hb]
    group
  refine Nat.card_congr
    { toFun := fun a => ⟨(a.1.2 : G) * (a₀.2 : G)⁻¹, hκ a⟩
      invFun := fun v => ⟨(⟨(a₀.1 : G) * (v : G)⁻¹, hι1 v⟩, ⟨(v : G) * (a₀.2 : G), hι2 v⟩), hι3 v⟩
      left_inv := fun a => ?_
      right_inv := fun v => ?_ }
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      show (a₀.1 : G) * ((a.1.2 : G) * (a₀.2 : G)⁻¹)⁻¹ = (a.1.1 : G)
      rw [e1 a]
      group
    · apply Subtype.ext
      show (a.1.2 : G) * (a₀.2 : G)⁻¹ * (a₀.2 : G) = (a.1.2 : G)
      group
  · apply Subtype.ext
    show (v : G) * (a₀.2 : G) * (a₀.2 : G)⁻¹ = (v : G)
    group

theorem card_eq_card_mul_of_fiber {α β : Type*} [Finite α] [Finite β] (f : α → β) (k : ℕ)
    (h : ∀ b, Nat.card {a // f a = b} = k) : Nat.card α = Nat.card β * k := by
  haveI : Fintype β := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem card_mul_card_eq [Finite G] {V₁ P Xg Yg : Subgroup G} (hV₁X : V₁ ≤ Xg) (hV₁Y : V₁ ≤ Yg)
    (hXY : Xg ⊓ Yg = V₁) (hXP : Xg ≤ P) (hYP : Yg ≤ P) (hXYs : Xg ⊔ Yg = P)
    (hcomm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁) :
    Nat.card Xg * Nat.card Yg = Nat.card P * Nat.card V₁ := by
  let f : ↥Xg × ↥Yg → ↥P := fun a => ⟨(a.1 : G) * (a.2 : G), P.mul_mem (hXP a.1.2) (hYP a.2.2)⟩
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_sup_eq hV₁X hXP hYP hXYs hcomm b.2
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy.symm⟩
  have hfib : ∀ b : ↥P, Nat.card {a // f a = b} = Nat.card V₁ := by
    intro b
    obtain ⟨a₀, ha₀⟩ := hsurj b
    have hb : (a₀.1 : G) * (a₀.2 : G) = (b : G) := congrArg Subtype.val ha₀
    have hiff : ∀ a : ↥Xg × ↥Yg, f a = b ↔ (a.1 : G) * (a.2 : G) = (b : G) :=
      fun a => Subtype.ext_iff
    exact (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans
      (card_fiber_eq_card hV₁X hV₁Y hXY a₀ hb)
  have h := card_eq_card_mul_of_fiber f (Nat.card V₁) hfib
  rw [Nat.card_prod] at h
  exact h

theorem isExtraspecial_of_pairing {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    {Z : Subgroup Q} (hZ : Nat.card Z = 2) (hZc : Z ≤ Subgroup.center Q)
    (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Z) (hsq : ∀ x : Q, x ^ 2 ∈ Z)
    (hcent : ∀ x : Q, (∀ y : Q, x * y = y * x) → x ∈ Z) (hnab : ∃ x : Q, x ∉ Z) :
    CFSG.IsExtraspecialPGroup 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hcenter : Subgroup.center Q = Z := by
    refine le_antisymm (fun x hx => hcent x fun y => ?_) hZc
    exact (Subgroup.mem_center_iff.mp hx y).symm
  have hcom_le : _root_.commutator Q ≤ Z := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcomm x y
  have hcom : _root_.commutator Q = Z := by
    refine le_antisymm hcom_le ?_
    obtain ⟨x, hx⟩ := hnab
    have hnc : ¬ ∀ y : Q, x * y = y * x := fun h => hx (hcent x h)
    push Not at hnc
    obtain ⟨y, hy⟩ := hnc
    have hg1 : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hgZ : ⁅x, y⁆ ∈ Z := hcomm x y
    have hgc : ⁅x, y⁆ ∈ _root_.commutator Q := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hzp : Subgroup.zpowers ⁅x, y⁆ = Z := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgZ) ?_
      rw [hZ, Nat.card_zpowers]
      have h2 : orderOf ⁅x, y⁆ ∣ 2 := by
        have := orderOf_dvd_natCard (⟨_, hgZ⟩ : Z)
        rwa [hZ, Subgroup.orderOf_mk] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h.ge
    rw [← hzp]
    exact (Subgroup.zpowers_le).mpr hgc
  have hfr : frattini Q = Z := by
    refine le_antisymm ?_ (hcom ▸ CFSG.commutator_le_frattini_of_isPGroup (R := Q) (p := 2))
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (hx | ⟨y, rfl⟩)
    · exact hcom_le hx
    · exact hsq y
  refine ⟨hQ, ?_, ?_, ?_⟩
  · rw [hcom, hcenter]
  · rw [hfr, hcenter]
  · rw [hcenter]
    exact hZ

theorem isQ8CentralPow_of_special [Finite G] {V₁ P Xg Yg : Subgroup G}
    (hcard : Nat.card V₁ = 2) (hV₁P : V₁ ≤ P) (hcen : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p)
    (hsq : ∀ p ∈ P, p * p ∈ V₁) (hcomm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁)
    (hnd : ∀ p ∈ P, (∀ r ∈ P, p * r = r * p) → p ∈ V₁)
    (hXP : Xg ≤ P) (hYP : Yg ≤ P) (hV₁X : V₁ ≤ Xg) (hV₁Y : V₁ ≤ Yg)
    (hXY : Xg ⊓ Yg = V₁) (hXYs : Xg ⊔ Yg = P)
    (hXe : ∀ x ∈ Xg, x * x = 1) (hXc : ∀ x ∈ Xg, ∀ x' ∈ Xg, x * x' = x' * x)
    (hYe : ∀ y ∈ Yg, y * y = 1) (hYc : ∀ y ∈ Yg, ∀ y' ∈ Yg, y * y' = y' * y)
    (hXYcard : Nat.card Xg = Nat.card Yg) {j : ℕ} (hj : 0 < j) (hX : Nat.card Xg = 2 ^ (2 * j + 1))
    (hnab : ∃ p ∈ P, ∃ r ∈ P, p * r ≠ r * p) :
    CFSG.Quasithin.H13.IsQ8CentralPow (2 * j) ↥P := by
  have hcenter : CFSG.Quasithin.centerOf P = V₁ := by
    apply le_antisymm
    · intro x hx
      unfold CFSG.Quasithin.centerOf at hx
      obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_centralizer_iff] at hxC
      exact hnd x hxP fun r hr => (hxC r hr).symm
    · intro z hz
      unfold CFSG.Quasithin.centerOf
      exact Subgroup.mem_inf.mpr
        ⟨hV₁P hz, Subgroup.mem_centralizer_iff.mpr fun h hh => hcen z hz h hh⟩
  have hZA : CFSG.Quasithin.centerOf P ≤ Xg := by
    rw [hcenter]
    exact hV₁X
  have hcount : Nat.card Xg * Nat.card Yg = Nat.card P * 2 := by
    rw [card_mul_card_eq hV₁X hV₁Y hXY hXP hYP hXYs hcomm, hcard]
  have hYcard : Nat.card Yg = 2 ^ (2 * j + 1) := hXYcard.symm.trans hX
  have hPcard : Nat.card P = 2 ^ (4 * j + 1) := by
    have h2 : Nat.card P * 2 = 2 ^ (4 * j + 1) * 2 := by
      rw [← hcount, hX, hYcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hext : CFSG.IsExtraspecialPGroup 2 ↥P := by
    have hZ : Nat.card ↥(V₁.subgroupOf P) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁P).toEquiv, hcard]
    have hZc : V₁.subgroupOf P ≤ Subgroup.center ↥P := by
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcen (z : G) hz (g : G) g.2)
    have hcomm' : ∀ x y : ↥P, ⁅x, y⁆ ∈ V₁.subgroupOf P := by
      intro x y
      rw [Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using hcomm (x : G) x.2 (y : G) y.2
    have hsq' : ∀ x : ↥P, x ^ 2 ∈ V₁.subgroupOf P := by
      intro x
      rw [Subgroup.mem_subgroupOf]
      simpa [pow_two] using hsq (x : G) x.2
    have hcent' : ∀ x : ↥P, (∀ y : ↥P, x * y = y * x) → x ∈ V₁.subgroupOf P := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hnd (x : G) x.2 fun r hr => congrArg Subtype.val (hx ⟨r, hr⟩)
    have hnab' : ∃ x : ↥P, x ∉ V₁.subgroupOf P := by
      obtain ⟨p, hp, r, hr, hpr⟩ := hnab
      refine ⟨⟨p, hp⟩, fun h => hpr ?_⟩
      rw [Subgroup.mem_subgroupOf] at h
      exact (hcen p h r hr).symm
    exact isExtraspecial_of_pairing (IsPGroup.of_card hPcard) hZ hZc hcomm' hsq' hcent' hnab'
  exact CFSG.Quasithin.H13.Q8Pow.isQ8CentralPow_of_elemAbelian hext hXP hZA hXc hXe hj hX hPcard

end CFSG.Quasithin.RonanF95
