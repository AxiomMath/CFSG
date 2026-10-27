module

public import CFSG.GroupTheory.FourGroupOddOrderIdentity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Walter.J1

variable {G : Type*} [Group G]

theorem orderOf_eq_two_iff {x : G} : orderOf x = 2 ↔ x * x = 1 ∧ x ≠ 1 := by
  constructor
  · intro hx
    refine ⟨by rw [← pow_two, ← hx, pow_orderOf_eq_one], fun h1 => ?_⟩
    rw [h1, orderOf_one] at hx
    omega
  · rintro ⟨h2, h1⟩
    exact orderOf_eq_prime (by rwa [pow_two]) h1

theorem mem_zpowers_of_orderOf_eq_two {v x : G} (hv : orderOf v = 2) :
    x ∈ Subgroup.zpowers v ↔ x = 1 ∨ x = v := by
  have h2 : v ^ (2 : ℤ) = 1 := by
    have := pow_orderOf_eq_one v
    rw [hv] at this
    rw [zpow_ofNat, this]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change v ^ k = 1
      rw [← Int.ediv_mul_add_emod k 2, hk, add_zero, mul_comm, zpow_mul, h2, one_zpow]
    · right
      change v ^ k = v
      rw [← Int.ediv_mul_add_emod k 2, hk, zpow_add, mul_comm, zpow_mul, h2, one_zpow,
        one_mul, zpow_one]
  · rintro (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers v

theorem eq_zpowers_of_card_prime {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hX : Nat.card X = p)
    {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) : X = Subgroup.zpowers x := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; exact hp.ne_zero)
  have hdvd : orderOf x ∣ p := hX ▸ Subgroup.orderOf_dvd_natCard X hx
  have hne1 : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
  have hord : orderOf x = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hne1
  refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hx) ?_).symm
  rw [Nat.card_zpowers, hord, hX]

theorem exists_ne_one_of_card {X : Subgroup G} {p : ℕ} (hX : Nat.card X = p) (hp : 1 < p) :
    ∃ x ∈ X, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : X = ⊥ := (Subgroup.eq_bot_iff_forall X).mpr hcon
  rw [this, Subgroup.card_bot] at hX
  omega

theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (H : Subgroup G) : H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  conv_rhs => rw [← Subgroup.map_id H]
  congr 1
  ext x
  simp

theorem map_conj_inv_map_conj (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [← map_conj_mul, inv_mul_cancel, map_conj_one]

theorem mem_map_conj {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conj_mem_map_conj {H : Subgroup G} {g x : G} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  let φ : H → H := fun y => ⟨g * y * g⁻¹, hg y y.2⟩
  have hφ : Function.Injective φ := by
    intro y z hyz
    have := congrArg Subtype.val hyz
    change g * y * g⁻¹ = g * z * g⁻¹ at this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨_, hx⟩
  have := congrArg Subtype.val hy
  change g * y * g⁻¹ = g * x * g⁻¹ at this
  have hyx : (y : G) = x := by simpa using this
  rw [← hyx]
  exact y.2

theorem inv_of_inf_centralizer_eq_bot [Finite G] {u : G} (hu : u * u = 1) {K : Subgroup G}
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (hfix : K ⊓ Subgroup.centralizer ({u} : Set G) = ⊥) :
    ∀ x ∈ K, u * x * u⁻¹ = x⁻¹ := by
  classical
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hconjK : ∀ x ∈ K, u * x * u⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp huK x).mp hx
  let φ : K → K := fun k => ⟨k⁻¹ * (u * k * u⁻¹), K.mul_mem (K.inv_mem k.2) (hconjK _ k.2)⟩
  have hφ : Function.Injective φ := by
    intro k l hkl
    have h : (k : G)⁻¹ * (u * k * u⁻¹) = (l : G)⁻¹ * (u * l * u⁻¹) := congrArg Subtype.val hkl
    have hm : (l : G) * (k : G)⁻¹ ∈ K ⊓ Subgroup.centralizer ({u} : Set G) := by
      refine ⟨K.mul_mem l.2 (K.inv_mem k.2), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h' : u * ((l : G) * (k : G)⁻¹) * u⁻¹ = (l : G) * (k : G)⁻¹ := by
        calc u * ((l : G) * (k : G)⁻¹) * u⁻¹ = (u * l * u⁻¹) * (u * k * u⁻¹)⁻¹ := by group
          _ = (l : G) * (k : G)⁻¹ := by
            have : u * (l : G) * u⁻¹ = l * ((k : G)⁻¹ * (u * k * u⁻¹)) := by
              rw [h]; group
            rw [this]; group
      calc ((l : G) * (k : G)⁻¹) * u = u * ((l : G) * (k : G)⁻¹) * u⁻¹ * u := by rw [h']
        _ = u * ((l : G) * (k : G)⁻¹) := by group
    rw [hfix, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact Subtype.ext hm.symm
  have hφs : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ
  intro x hx
  obtain ⟨k, hk⟩ := hφs ⟨x, hx⟩
  have hk' : (k : G)⁻¹ * (u * k * u⁻¹) = x := congrArg Subtype.val hk
  rw [← hk']
  rw [huinv, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, huinv]
  simp only [mul_assoc, hu, mul_one]

theorem le_centralizer_of_inv {u : G} {K : Subgroup G}
    (hinv : ∀ x ∈ K, u * x * u⁻¹ = x⁻¹) : K ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hinv _ (K.mul_mem hx hy)
  rw [show u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) by group, hinv x hx,
    hinv y hy, mul_inv_rev] at h1
  have := congrArg (·⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at this
  exact this

section BrauerWielandt

@[expose, reducible] def conjAct (V K : Subgroup G)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) : MulDistribMulAction V K where
  smul v k := ⟨v * k * (v : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hVK v.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by
    change ((1 : V) : G) * k * ((1 : V) : G)⁻¹ = k
    simp)
  mul_smul a b k := Subtype.ext (by
    change ((a : G) * b) * k * ((a : G) * b)⁻¹ = a * (b * k * (b : G)⁻¹) * (a : G)⁻¹
    group)
  smul_mul a x y := Subtype.ext (by
    change (a : G) * (x * y) * (a : G)⁻¹ = (a * x * (a : G)⁻¹) * (a * y * (a : G)⁻¹)
    group)
  smul_one a := Subtype.ext (by
    change (a : G) * 1 * (a : G)⁻¹ = 1
    group)

theorem inf_centralizer_zpowers (K : Subgroup G) (x : G) :
    K ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      K ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, h x (Subgroup.mem_zpowers x)⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left h k).eq)

theorem card_fixedPointSubgroup_conjAct (V K : Subgroup G)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (S : Subgroup V) :
    letI := conjAct V K hVK
    Nat.card (fixedPointSubgroup S K) =
      Nat.card (K ⊓ Subgroup.centralizer ((S.map V.subtype : Subgroup G) : Set G) :
        Subgroup G) := by
  let := conjAct V K hVK
  have key : (fixedPointSubgroup S K).map K.subtype =
      K ⊓ Subgroup.centralizer ((S.map V.subtype : Subgroup G) : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe, Subgroup.coe_subtype]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have h := congrArg Subtype.val (hk ⟨s, hs⟩)
      change (s : G) * k * (s : G)⁻¹ = k at h
      calc (s : G) * k = ((s : G) * k * (s : G)⁻¹) * s := by group
        _ = k * s := by rw [h]
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rintro ⟨s, hs⟩
      apply Subtype.ext
      change (s : G) * x * (s : G)⁻¹ = x
      rw [h _ ⟨s, hs, rfl⟩, mul_inv_cancel_right]
  rw [← key, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_fixedPointSubgroup_conjAct_top (V K : Subgroup G)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) :
    letI := conjAct V K hVK
    Nat.card (fixedPointSubgroup V K) =
      Nat.card (K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  let := conjAct V K hVK
  have key : (fixedPointSubgroup V K).map K.subtype =
      K ⊓ Subgroup.centralizer (V : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe, Subgroup.coe_subtype]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, fun s hs => ?_⟩
      have h := congrArg Subtype.val (hk ⟨s, hs⟩)
      change (s : G) * k * (s : G)⁻¹ = k at h
      calc (s : G) * k = ((s : G) * k * (s : G)⁻¹) * s := by group
        _ = k * s := by rw [h]
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rintro ⟨s, hs⟩
      apply Subtype.ext
      change (s : G) * x * (s : G)⁻¹ = x
      rw [h _ hs, mul_inv_cancel_right]
  rw [← key, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_mul_card_sq_eq_mul [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : Commute a b) (K : Subgroup G)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hK : Odd (Nat.card K)) :
    Nat.card K * Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) ⊓
        Subgroup.centralizer ({b} : Set G) : Subgroup G) ^ 2 =
      Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) *
        Nat.card (K ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) *
        Nat.card (K ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) := by
  classical
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hc
  have hV : IsKleinFour V :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hab hc
  have hmemV : ∀ x : G, x ∈ V ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := fun x => by
    change x ∈ ({a * b, a, b, 1} : Set G) ↔ _
    simp
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    rw [← mul_one a, ← h, ← mul_assoc, ha, one_mul]
  have haab : a ≠ a * b := by
    intro h
    apply hb1
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm
  have hbab : b ≠ a * b := by
    intro h
    apply ha1
    have := congrArg (· * b⁻¹) h
    simpa using this.symm
  have hVK : V ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rcases (hmemV x).mp hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ haK hbK
    · exact haK
    · exact hbK
    · exact Subgroup.one_mem _
  let := conjAct V K hVK
  let : Fintype V := Fintype.ofFinite V
  have h := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
    (A := V) (X := K) hK).1
  rw [card_fixedPointSubgroup_conjAct_top] at h
  set a' : V := ⟨a, (hmemV a).mpr (Or.inr (Or.inl rfl))⟩
  set b' : V := ⟨b, (hmemV b).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
  set c' : V := ⟨a * b, (hmemV _).mpr (Or.inl rfl)⟩
  have herase : Finset.univ.erase (1 : V) = {a', b', c'} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      rcases (hmemV x).mp x.2 with h1 | h1 | h1 | h1
      · exact Or.inr (Or.inr (Subtype.ext h1))
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Or.inl (Subtype.ext h1))
      · exact absurd (Subtype.ext h1) hx
    · rintro (rfl | rfl | rfl) h1
      · exact ha1 (congrArg Subtype.val h1)
      · exact hb1 (congrArg Subtype.val h1)
      · exact hab1 (congrArg Subtype.val h1)
  have hne1 : a' ≠ b' := fun h1 => hab (congrArg Subtype.val h1)
  have hne2 : a' ≠ c' := fun h1 => haab (congrArg Subtype.val h1)
  have hne3 : b' ≠ c' := fun h1 => hbab (congrArg Subtype.val h1)
  rw [herase, Finset.prod_insert (by simp [hne1, hne2]), Finset.prod_insert (by simp [hne3]),
    Finset.prod_singleton] at h
  have hcz : ∀ x : V, Nat.card (fixedPointSubgroup (Subgroup.zpowers x) K) =
      Nat.card (K ⊓ Subgroup.centralizer ({(x : G)} : Set G) : Subgroup G) := by
    intro x
    rw [card_fixedPointSubgroup_conjAct, MonoidHom.map_zpowers, inf_centralizer_zpowers]
    rfl
  rw [hcz, hcz, hcz] at h
  have hcV : K ⊓ Subgroup.centralizer (V : Set G) =
      K ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨hx, h1⟩
      exact ⟨⟨hx, h1 a ((hmemV a).mpr (Or.inr (Or.inl rfl)))⟩,
        h1 b ((hmemV b).mpr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · rintro ⟨⟨hx, h1⟩, h2⟩
      refine ⟨hx, fun y hy => ?_⟩
      rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
      · rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
      · exact h1
      · exact h2
      · simp
  rw [hcV] at h
  rw [h]
  ring

end BrauerWielandt

end CFSG.Walter.J1
