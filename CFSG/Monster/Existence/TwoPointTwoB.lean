module

public import CFSG.Monster.Existence.Co2Bridge
public import CFSG.Monster.Existence.InvolutionClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

section Generic

variable {G : Type*} [Group G]

theorem isElementaryAbelian_two_of_mul_self {K : Type*} [Group K] (h : ∀ a : K, a * a = 1) :
    IsElementaryAbelian 2 K where
  toIsMulCommutative := ⟨⟨fun a b => by
    have hinv : ∀ g : K, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by rw [pow_two, h a]

theorem isElementaryAbelian_two_quotient {N : Type*} [Group N] (K : Subgroup N) [K.Normal]
    (hsq : ∀ a : N, a * a ∈ K) : IsElementaryAbelian 2 (N ⧸ K) := by
  refine isElementaryAbelian_two_of_mul_self fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hsq a

@[expose] def kleinSubgroup (x t : G) (hx : x * x = 1) (ht : t * t = 1) (hxt : x * t = t * x) :
    Subgroup G where
  carrier := {1, x, t, x * t}
  mul_mem' := by
    have hx2 : ∀ a, x * (x * a) = a := fun a => by rw [← mul_assoc, hx, one_mul]
    have hc1 : t * x = x * t := hxt.symm
    have hc2 : ∀ a, t * (x * a) = x * (t * a) := fun a => by rw [← mul_assoc, hc1, mul_assoc]
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [mul_assoc, mul_one, one_mul, hx, hx2, ht, hc1, hc2] <;> simp
  one_mem' := Set.mem_insert _ _
  inv_mem' := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · simp [hxi]
    · simp [hti]
    · right; right; right
      rw [mul_inv_rev, hxi, hti, hxt]

variable {x t : G} {hx : x * x = 1} {ht : t * t = 1} {hxt : x * t = t * x}

theorem mem_kleinSubgroup {g : G} :
    g ∈ kleinSubgroup x t hx ht hxt ↔ g = 1 ∨ g = x ∨ g = t ∨ g = x * t := Iff.rfl

theorem left_mem_kleinSubgroup : x ∈ kleinSubgroup x t hx ht hxt := by
  rw [mem_kleinSubgroup]; simp

theorem right_mem_kleinSubgroup : t ∈ kleinSubgroup x t hx ht hxt := by
  rw [mem_kleinSubgroup]; simp

theorem mul_self_of_mem_kleinSubgroup {g : G} (hg : g ∈ kleinSubgroup x t hx ht hxt) :
    g * g = 1 := by
  rcases mem_kleinSubgroup.1 hg with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact hx
  · exact ht
  · calc x * t * (x * t) = x * (t * x) * t := by group
      _ = 1 := by rw [← hxt, ← mul_assoc, hx, one_mul, ht]

theorem isElementaryAbelian_kleinSubgroup :
    IsElementaryAbelian 2 (kleinSubgroup x t hx ht hxt) :=
  isElementaryAbelian_two_of_mul_self fun g =>
    Subtype.ext (mul_self_of_mem_kleinSubgroup g.2)

theorem natCard_kleinSubgroup (h1 : x ≠ 1) (h2 : t ≠ 1) (h3 : x ≠ t) :
    Nat.card (kleinSubgroup x t hx ht hxt) = 4 := by
  have hxt1 : x * t ≠ 1 := fun h => h3 (by
    have := congrArg (x * ·) h
    simp only [mul_one, ← mul_assoc, hx, one_mul] at this
    exact this.symm)
  have hxt2 : x * t ≠ x := fun h => h2 (by simpa using h)
  have hxt3 : x * t ≠ t := fun h => h1 (by simpa using h)
  have e1 : (1 : G) ∉ ({x, t, x * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h1 h.symm, fun h => h2 h.symm, fun h => hxt1 h.symm⟩
  have e2 : x ∉ ({t, x * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h3, fun h => hxt2 h.symm⟩
  change Nat.card ↥({1, x, t, x * t} : Set G) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem e1, Set.ncard_insert_of_notMem e2,
    Set.ncard_pair hxt3.symm]

theorem kleinSubgroup_le_center (hxc : x ∈ Subgroup.center G) (htc : t ∈ Subgroup.center G) :
    kleinSubgroup x t hx ht hxt ≤ Subgroup.center G := by
  intro g hg
  rcases mem_kleinSubgroup.1 hg with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hxc
  · exact htc
  · exact Subgroup.mul_mem _ hxc htc

theorem normal_of_le_center {K : Subgroup G} (h : K ≤ Subgroup.center G) : K.Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.1 (h hn) g, mul_inv_cancel_right]
    exact hn⟩

end Generic

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    [hK : IsElementaryAbelian p K] : IsElementaryAbelian p K' where
  toIsMulCommutative := ⟨⟨fun a b => e.symm.injective (by
    rw [map_mul, map_mul]
    exact hK.toIsMulCommutative.is_comm.comm _ _)⟩⟩
  exponent_dvd_p := (Monoid.exponent_eq_of_mulEquiv e).symm ▸ IsElementaryAbelian.exponent_dvd_p p K

noncomputable def quotientMapEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (N N₀ : Subgroup K) [(N₀.subgroupOf N).Normal]
    [((N₀.map e.toMonoidHom).subgroupOf (N.map e.toMonoidHom)).Normal] :
    N ⧸ N₀.subgroupOf N ≃*
      ↥(N.map e.toMonoidHom) ⧸ (N₀.map e.toMonoidHom).subgroupOf (N.map e.toMonoidHom) :=
  QuotientGroup.congr _ _ (N.equivMapOfInjective e.toMonoidHom e.injective) (by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
    · rintro ⟨n₀, hn₀, hy⟩
      obtain ⟨n, hnN, hn⟩ := y.2
      have hnn : n = n₀ := e.injective (hn.trans hy.symm)
      subst hnn
      refine ⟨⟨n, hnN⟩, hn₀, Subtype.ext ?_⟩
      exact hn)

theorem HasLayeredTwoShape.of_mulEquiv {H : Subgroup G} {H' : Subgroup G'} (e : H ≃* H')
    {a b : ℕ} {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → P X → P Y)
    (h : HasLayeredTwoShape H a b P) : HasLayeredTwoShape H' a b P := by
  obtain ⟨N, hN, N₀, hN₀, hle, hE, hc₀, hQ, hc, hP'⟩ := h
  have := hN.map e.toMonoidHom e.surjective
  have := hN₀.map e.toMonoidHom e.surjective
  refine ⟨N.map e.toMonoidHom, hN.map _ e.surjective, N₀.map e.toMonoidHom,
    hN₀.map _ e.surjective, Subgroup.map_mono hle, ?_, ?_, ?_, ?_, ?_⟩
  · exact isElementaryAbelian_of_mulEquiv (N₀.equivMapOfInjective e.toMonoidHom e.injective)
  · rw [Subgroup.card_map_of_injective e.injective, hc₀]
  · exact isElementaryAbelian_of_mulEquiv (quotientMapEquiv e N N₀)
  · rw [Subgroup.card_map_of_injective e.injective, hc]
  · exact hP _ _ (QuotientGroup.congr N _ e rfl) hP'

theorem HasTwoShape.of_mulEquiv {H : Subgroup G} {H' : Subgroup G'} (e : H ≃* H') {k : ℕ}
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → P X → P Y)
    (h : HasTwoShape H k P) : HasTwoShape H' k P := by
  obtain ⟨N, hN, hc, hP'⟩ := h
  have := hN.map e.toMonoidHom e.surjective
  exact ⟨N.map e.toMonoidHom, hN.map _ e.surjective,
    by rw [Subgroup.card_map_of_injective e.injective, hc],
    hP _ _ (QuotientGroup.congr N _ e rfl) hP'⟩

end Transport

theorem xmat_mem_center_Jmat : xJ rStar ∈ Subgroup.center (Jmat rStar) := by
  rw [Subgroup.mem_center_iff]
  intro f
  apply Subtype.ext
  have hv : (f : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Hmat := Jmat_le_Gvis rStar f.2
  rw [← Gmat_inf_centralizer_xmat, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff] at hv
  exact hv.2

theorem xJ_mul_self : xJ rStar * xJ rStar = 1 :=
  Subtype.ext (by
    change xmat * xmat = 1
    rw [← pow_two, ← orderOf_xmat, pow_orderOf_eq_one])

theorem tJ_mul_self' : tJ rStar * tJ rStar = 1 := tJ_mul_self isShortCoord_rStar

theorem xJ_mul_tJ : xJ rStar * tJ rStar = tJ rStar * xJ rStar :=
  (Subgroup.mem_center_iff.1 xmat_mem_center_Jmat (tJ rStar)).symm

noncomputable abbrev N0J : Subgroup (Jmat rStar) :=
  kleinSubgroup (xJ rStar) (tJ rStar) xJ_mul_self tJ_mul_self' xJ_mul_tJ

noncomputable abbrev NJ : Subgroup (Jmat rStar) := (rhoCent rStar).subgroupOf (Jmat rStar)

instance normal_NJ : NJ.Normal := by
  rw [NJ, ← ker_piJ]
  infer_instance

instance normal_N0J : N0J.Normal :=
  normal_of_le_center (kleinSubgroup_le_center xmat_mem_center_Jmat (tJ_mem_center rStar))

theorem xJ_ne_tJ : xJ rStar ≠ tJ rStar := by
  intro h
  have h' : xmat = tStar := congrArg Subtype.val h
  have := trace_xmat
  rw [h', trace_tStar] at this
  norm_num at this

theorem xJ_ne_one : xJ rStar ≠ 1 := by
  intro h
  have h' : xmat = 1 := congrArg Subtype.val h
  have := orderOf_xmat
  rw [h', orderOf_one] at this
  norm_num at this

theorem tJ_ne_one' : tJ rStar ≠ 1 := tJ_ne_one isShortCoord_rStar

theorem natCard_N0J : Nat.card N0J = 2 ^ 2 :=
  natCard_kleinSubgroup xJ_ne_one tJ_ne_one' xJ_ne_tJ

theorem isElementaryAbelian_N0J : IsElementaryAbelian 2 N0J := isElementaryAbelian_kleinSubgroup

theorem xJ_mem_NJ : xJ rStar ∈ NJ := by
  rw [NJ, Subgroup.mem_subgroupOf, rhoCent, Subgroup.mem_map]
  refine ⟨zQ, ?_, rhoHom_zQ⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hz : zQ ∈ Subgroup.center Q := by rw [center_Q]; exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_center_iff.1 hz rStar).symm

theorem N0J_le_NJ : N0J ≤ NJ := by
  intro g hg
  rcases mem_kleinSubgroup.1 hg with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact xJ_mem_NJ
  · exact tJ_mem_rhoCent rStar
  · exact Subgroup.mul_mem _ xJ_mem_NJ (tJ_mem_rhoCent rStar)

theorem natCard_NJ : Nat.card NJ = 2 ^ (2 + 22) := by
  rw [NJ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rhoCent_le_Jmat rStar)).toEquiv,
    natCard_rhoCent, natCard_centralizer_Q isShortCoord_rStar]

theorem mul_self_mem_zpowers_zQ (q : Q) : q * q ∈ Subgroup.zpowers zQ := by
  have hE := isExtraspecialPGroup_Q
  have : Fact (IsPGroup 2 Q) := ⟨hE.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.pth_power_mem_frattini_of_isPGroup (R := Q) (p := 2) q
  rw [hE.2.2.1, center_Q, pow_two] at h
  exact h

theorem mul_self_mem_N0J (a : NJ) : a * a ∈ N0J.subgroupOf NJ := by
  rw [Subgroup.mem_subgroupOf]
  have ha : ((a : Jmat rStar) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoCent rStar :=
    Subgroup.mem_subgroupOf.1 a.2
  rw [rhoCent, Subgroup.mem_map] at ha
  obtain ⟨q, -, hq⟩ := ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mul_self_mem_zpowers_zQ q)
  have : ((a * a : NJ) : Jmat rStar) = xJ rStar ^ k := by
    apply Subtype.ext
    change ((a : Jmat rStar) : SpaceB ≃ₗ[ℚ] SpaceB) * ((a : Jmat rStar) : SpaceB ≃ₗ[ℚ] SpaceB) =
      ((xJ rStar ^ k : Jmat rStar) : SpaceB ≃ₗ[ℚ] SpaceB)
    rw [Subgroup.coe_zpow, ← hq, ← map_mul, ← hk, map_zpow, rhoHom_zQ]
    rfl
  rw [this]
  exact Subgroup.zpow_mem _ left_mem_kleinSubgroup k

theorem isElementaryAbelian_NJ_quot : IsElementaryAbelian 2 (NJ ⧸ N0J.subgroupOf NJ) :=
  isElementaryAbelian_two_quotient _ mul_self_mem_N0J

noncomputable def jQuotEquivCo2 :
    Jmat rStar ⧸ NJ ≃* Blueprint.NativeSporadic.Co2 :=
  (QuotientGroup.quotientMulEquivOfEq (M := NJ) (N := (piJ rStar).ker) (ker_piJ rStar).symm).trans
    ((QuotientGroup.quotientKerEquivRange (piJ rStar)).trans
      ((MulEquiv.subgroupCongr (range_piJ isShortCoord_rStar)).trans
        ((opSubgroupEquiv _).trans
          ((MulEquiv.subgroupCongr (congrArg Kstab phi0_coordOf_rStar)).trans
            Co2Bridge.kvEquivCo2))))

theorem Jmat_shape :
    HasLayeredTwoShape (Jmat rStar) 2 22 fun X _ => Nonempty (X ≃* Blueprint.NativeSporadic.Co2) :=
  ⟨NJ, inferInstance, N0J, inferInstance, N0J_le_NJ, isElementaryAbelian_N0J, natCard_N0J,
    isElementaryAbelian_NJ_quot, natCard_NJ, ⟨jQuotEquivCo2⟩⟩

theorem cent2_eq_cent_inf_cent {K : Type} [Group K] (α y : K) :
    cent2 α (α * y) = cent α ⊓ cent y := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, mul_left_cancel (a := α) ?_⟩
    calc α * (g * y) = g * α * y := by rw [← mul_assoc, ← h1]
      _ = g * (α * y) := mul_assoc _ _ _
      _ = α * y * g := h2
      _ = α * (y * g) := mul_assoc _ _ _
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc g * (α * y) = g * α * y := (mul_assoc _ _ _).symm
      _ = α * g * y := by rw [h1]
      _ = α * (g * y) := mul_assoc _ _ _
      _ = α * (y * g) := by rw [h2]
      _ = α * y * g := (mul_assoc _ _ _).symm

theorem map_cent2_tGriess :
    (cent2 tGriess (tGriess * xGriess)).map CFSG.Monster.Griess.AutO.subtype = Jmat rStar := by
  rw [cent2_eq_cent_inf_cent, Subgroup.map_inf_eq _ _ _ CFSG.Monster.Griess.AutO.subtype_injective,
    map_cent_tGriess, map_cent_xGriess, ← Jstar_eq_Jmat]
  ext f
  simp only [Subgroup.mem_inf, CfullA, Jstar]
  constructor
  · rintro ⟨⟨-, h⟩, hv⟩
    exact ⟨hv, h⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨Gmat_le_AutO (Hmat_le_Gmat hv), h⟩, hv⟩

noncomputable def cent2EquivJmat : cent2 tGriess (tGriess * xGriess) ≃* Jmat rStar :=
  ((cent2 tGriess (tGriess * xGriess)).equivMapOfInjective _
    CFSG.Monster.Griess.AutO.subtype_injective).trans (MulEquiv.subgroupCongr map_cent2_tGriess)

theorem twoPointShape_tGriess_mul_xGriess :
    TwoPointShape (cent2 tGriess (tGriess * xGriess)) 2 :=
  HasLayeredTwoShape.of_mulEquiv cent2EquivJmat.symm
    (fun _ _ _ _ e ⟨e'⟩ => ⟨e.symm.trans e'⟩) Jmat_shape

end CFSG.Monster.Existence
