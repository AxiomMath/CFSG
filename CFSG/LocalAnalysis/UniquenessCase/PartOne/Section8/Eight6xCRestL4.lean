module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

open scoped Pointwise

private theorem k1566l4a_mulAut_conj_injective {Y : Type*} [Group Y]
    (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : a ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun σ : MulAut Y => σ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * a = a * g * a⁻¹ * a := by rw [h]
      _ = a * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

private theorem k1566l4a_conj_mul_conj {Y : Type*} [Group Y] (φ : MulAut Y) (q : Y) :
    φ * MulAut.conj q * φ⁻¹ = MulAut.conj (φ q) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem k1566l4a_zpow_mod_three {G : Type*} [Group G] {φ : G}
    (hφ3 : φ ^ 3 = 1) (m : ℤ) : ∃ j : ℕ, j < 3 ∧ φ ^ m = φ ^ j := by
  refine ⟨(m % 3).toNat, ?_, ?_⟩
  · have h1 : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
    have h2 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
    omega
  · rw [zpow_eq_zpow_emod' m hφ3, ← Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))]
    exact zpow_natCast φ _

private theorem k1566l4a_mem_sup_map_conj_zpowers {Y : Type*} [Group Y] [Finite Y]
    {Q : Subgroup Y} {φ : MulAut Y} (hφQ : ∀ q ∈ Q, φ q ∈ Q) (hφ3 : φ ^ 3 = 1)
    {x : MulAut Y} :
    x ∈ Q.map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers φ ↔
      ∃ t ∈ Q, ∃ j : ℕ, j < 3 ∧ MulAut.conj t * φ ^ j = x := by
  have hInnQle : (Q.map (MulAut.conj : Y →* MulAut Y)).map (MulAut.conj φ) ≤
      Q.map (MulAut.conj : Y →* MulAut Y) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hy
    change (MulAut.conj φ) (MulAut.conj q) ∈ Q.map (MulAut.conj : Y →* MulAut Y)
    rw [MulAut.conj_apply, k1566l4a_conj_mul_conj]
    exact Subgroup.mem_map.mpr ⟨φ q, hφQ q hq, rfl⟩
  have hcard : Nat.card (Q.map (MulAut.conj : Y →* MulAut Y)) ≤
      Nat.card ((Q.map (MulAut.conj : Y →* MulAut Y)).map
        (MulAut.conj φ : MulAut Y →* MulAut Y)) := by
    rw [Subgroup.card_map_of_injective
      (f := (MulAut.conj φ : MulAut Y →* MulAut Y)) (MulAut.conj φ).injective]
  have hInnQ_eq : (Q.map (MulAut.conj : Y →* MulAut Y)).map
      (MulAut.conj φ : MulAut Y →* MulAut Y) =
      Q.map (MulAut.conj : Y →* MulAut Y) :=
    Subgroup.eq_of_le_of_card_ge hInnQle hcard
  have hzp_le : Subgroup.zpowers φ ≤
      Subgroup.normalizer (Q.map (MulAut.conj : Y →* MulAut Y)) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hInnQ_eq)
  change x ∈ (↑(Q.map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers φ) : Set (MulAut Y)) ↔
    ∃ t ∈ Q, ∃ j : ℕ, j < 3 ∧ MulAut.conj t * φ ^ j = x
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzp_le, Set.mem_mul]
  constructor
  · rintro ⟨y, ⟨q, hq, rfl⟩, z, hz, hz_eq⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨j, hj, hjm⟩ := k1566l4a_zpow_mod_three hφ3 m
    exact ⟨q, hq, j, hj, by rw [← hz_eq, ← hm, hjm]⟩
  · rintro ⟨t, ht, j, hj, rfl⟩
    exact ⟨MulAut.conj t, Subgroup.mem_map.mpr ⟨t, ht, rfl⟩, φ ^ j,
      Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by rw [zpow_natCast]⟩, rfl⟩

private theorem k1566l4a_relIndex_sup_eq_inf {G : Type*} [Group G] [Finite G]
    {K N : Subgroup G} (hK : K.Normal) :
    N.relIndex (K ⊔ N) = (K ⊓ N).relIndex K := by
  have hpos : 0 < K.relIndex (K ⊔ N) := by
    refine Nat.pos_of_ne_zero ?_
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h1 : (N ⊓ K).relIndex K * K.relIndex (K ⊔ N) = (N ⊓ K).relIndex (K ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (N ⊓ K) K (K ⊔ N) inf_le_right le_sup_left
  have h2 : (N ⊓ K).relIndex N * N.relIndex (K ⊔ N) = (N ⊓ K).relIndex (K ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (N ⊓ K) N (K ⊔ N) inf_le_left le_sup_right
  have h3 : (N ⊓ K).relIndex N = K.relIndex N := Subgroup.inf_relIndex_left N K
  have h4 : K.relIndex (K ⊔ N) = K.relIndex N :=
    @Subgroup.relIndex_sup_left G _ N K hK
  rw [← h2, h3, ← h4] at h1
  rw [mul_comm (K.relIndex (K ⊔ N)) (N.relIndex (K ⊔ N))] at h1
  have hthis : (N ⊓ K).relIndex K = N.relIndex (K ⊔ N) := Nat.eq_of_mul_eq_mul_right hpos h1
  rw [inf_comm] at hthis
  exact hthis.symm

private theorem k1566l4b_mul_comm_of_mem {H : Type} [Group H] {T : Subgroup H}
    (hT : IsMulCommutative ↥T) {a b : H} (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a :=
  congrArg Subtype.val (hT.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem k1566l4b_zpow_eq_self_of_pow_three {G : Type} [Group G] {v : G} {k : ℤ}
    (hv : v ^ 3 = 1) (hk3 : (k : ZMod 3) = 1) : v ^ k = v := by
  have hdvd : (3 : ℤ) ∣ k - 1 := by
    have h0 : ((k - 1 : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [hk3]
      norm_num
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).mp h0
  have hdvd' : (orderOf v : ℤ) ∣ k - 1 := by
    have h : orderOf v ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hv
    exact dvd_trans (by exact_mod_cast h) hdvd
  have h1 : v ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp hdvd'
  have hk : k = (k - 1) + 1 := by ring
  rw [hk, zpow_add, h1, one_mul, zpow_one]

private theorem k1566l4b_phi_pow_apply {Y : Type} [Group Y] {φ : MulAut Y} {T : Subgroup Y}
    {y : Y} {k : ℤ} (hsc : ScalarAction T φ y k) {s : Y} (hsT : s ∈ T) (j : ℕ) :
    (φ ^ j) s = s ^ (k ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, hsc.2 _ (T.zpow_mem hsT _), ← zpow_mul,
        pow_succ k j]

private theorem k1566l4b_beta_apply_of_mem {Y : Type} [Group Y] {T : Subgroup Y}
    {φ : MulAut Y} {k : ℤ} {y t : Y} {j : ℕ}
    (hsc : ScalarAction T φ y k) (hTcomm : IsMulCommutative ↥T)
    (htT : t ∈ T) {s : Y} (hsT : s ∈ T) :
    (MulAut.conj t * φ ^ j) s = s ^ (k ^ j) := by
  have hphi := k1566l4b_phi_pow_apply hsc hsT j
  have hmem : s ^ (k ^ j) ∈ T := T.zpow_mem hsT _
  rw [MulAut.mul_apply, hphi, MulAut.conj_apply,
    k1566l4b_mul_comm_of_mem hTcomm htT hmem]
  group

private theorem k1566l4b_isCoprime_three_add {k : ℤ} (hk3 : (k : ZMod 3) = 1) :
    IsCoprime (3 : ℤ) (k + 1) := by
  have hnot : ¬ (3 : ℤ) ∣ k + 1 := by
    intro h
    have h0 : ((k + 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (k + 1) 3).mpr h
    have h2 : ((k + 1 : ℤ) : ZMod 3) = 2 := by
      push_cast
      rw [hk3]
      norm_num
    rw [h2] at h0
    exact (by decide : (2 : ZMod 3) ≠ 0) h0
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hdvd : Int.gcd 3 (k + 1) ∣ 3 := by
    have h := Int.gcd_dvd_left 3 (k + 1)
    exact_mod_cast h
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact h1
  · exfalso
    apply hnot
    have hg : ((Int.gcd 3 (k + 1) : ℕ) : ℤ) ∣ k + 1 := Int.gcd_dvd_right 3 (k + 1)
    rw [h3] at hg
    simpa using hg

private theorem k1566l4b_pow_max_exp {Y : Type} [Group Y] {T : Subgroup Y} {e1 e2 : ℕ}
    (hiso : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T)) :
    ∀ t ∈ T, t ^ (3 ^ max e1 e2) = 1 := by
  obtain ⟨eT⟩ := hiso
  have hexp : Monoid.exponent
      (Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) = 3 ^ max e1 e2 := by
    rw [Monoid.exponent_prod, Monoid.exponent_multiplicative, Monoid.exponent_multiplicative,
      ZMod.exponent, ZMod.exponent]
    rcases le_total e1 e2 with h | h
    · rw [max_eq_right h]
      exact Nat.lcm_eq_right (pow_dvd_pow 3 h)
    · rw [max_eq_left h]
      exact Nat.lcm_eq_left (pow_dvd_pow 3 h)
  have hsource : ∀ x : Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2)),
      x ^ (3 ^ max e1 e2) = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (hexp ▸ dvd_refl _)
  intro t ht
  have hx := hsource (eT.symm ⟨t, ht⟩)
  have h := congrArg (fun z => eT z) hx
  rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h
  simpa using congrArg Subtype.val h

private theorem k1566l4b_exists_order_max {Y : Type} [Group Y] {T : Subgroup Y} {e1 e2 : ℕ}
    (hiso : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T)) :
    ∃ s ∈ T, orderOf s = 3 ^ max e1 e2 := by
  obtain ⟨eT⟩ := hiso
  rcases le_total e1 e2 with hle | hle
  · let x : Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2)) :=
      (1, Multiplicative.ofAdd (1 : ZMod (3 ^ e2)))
    have hx2 : orderOf (Multiplicative.ofAdd (1 : ZMod (3 ^ e2))) = 3 ^ e2 := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    have hx : orderOf x = 3 ^ e2 := by
      simp only [x, Prod.orderOf, orderOf_one, hx2, Nat.lcm_one_left]
    refine ⟨(eT x : ↥T), (eT x).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx, max_eq_right hle]
  · let x : Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2)) :=
      (Multiplicative.ofAdd (1 : ZMod (3 ^ e1)), 1)
    have hx1 : orderOf (Multiplicative.ofAdd (1 : ZMod (3 ^ e1))) = 3 ^ e1 := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    have hx : orderOf x = 3 ^ e1 := by
      simp only [x, Prod.orderOf, orderOf_one, hx1, Nat.lcm_one_right]
    refine ⟨(eT x : ↥T), (eT x).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx, max_eq_left hle]

private theorem k1566l4b_quadratic_subgroup_of_abelian
    {Y : Type} [Group Y] [Finite Y] {T₀ : Subgroup Y} {β : MulAut Y} (e : ℕ)
    (hcomm : IsMulCommutative ↥T₀) (hkill : ∀ t ∈ T₀, t ^ (3 ^ e) = 1)
    (hβT : ∀ t ∈ T₀, β t ∈ T₀) (hβ3 : β ^ 3 = 1) (hmov : ∃ t ∈ T₀, β t ≠ t) :
    ∃ R : Subgroup Y, IsPGroup 3 R ∧ IsMulCommutative ↥R ∧
      (∀ r ∈ R, β r ∈ R) ∧
      (∀ r ∈ R, β (β r * r⁻¹) = β r * r⁻¹) ∧
      (∃ r ∈ R, β r ≠ r) := by
  obtain ⟨v, hvT, hvne, hvc⟩ := exists_quadratic_element e hcomm hkill hβT hβ3 hmov
  set c : Y := β v * v⁻¹ with hcdef
  have hcT : c ∈ T₀ := T₀.mul_mem (hβT v hvT) (T₀.inv_mem hvT)
  have hβc : β c = c := hvc
  have hβv : β v = c * v := by rw [hcdef]; group
  let _ : CommGroup ↥T₀ :=
    { (inferInstance : Group ↥T₀) with mul_comm := fun a b => hcomm.is_comm.comm a b }
  let v' : ↥T₀ := ⟨v, hvT⟩
  let c' : ↥T₀ := ⟨c, hcT⟩
  let R' : Subgroup ↥T₀ := Subgroup.zpowers v' ⊔ Subgroup.zpowers c'
  let R : Subgroup Y := R'.map T₀.subtype
  have hRle : R ≤ T₀ := by
    intro r hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨x, _, rfl⟩ := hr
    exact x.2
  have hdecomp : ∀ x ∈ R', ∃ i j : ℤ, x = v' ^ i * c' ^ j := by
    intro x hx
    rw [Subgroup.mem_sup] at hx
    obtain ⟨p, hp, q, hq, hpq⟩ := hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    exact ⟨i, j, hpq.symm⟩
  have hβx : ∀ x ∈ R', ∃ i : ℤ, β (T₀.subtype x) = c ^ i * T₀.subtype x := by
    intro x hx
    obtain ⟨i, j, hxij⟩ := hdecomp x hx
    refine ⟨i, ?_⟩
    have hxy : T₀.subtype x = v ^ i * c ^ j := by
      rw [hxij]
      show T₀.subtype (v' ^ i * c' ^ j) = v ^ i * c ^ j
      rw [map_mul, map_zpow, map_zpow]
      rfl
    have hcv : Commute c v := k1566l4b_mul_comm_of_mem hcomm hcT hvT
    calc β (T₀.subtype x) = β (v ^ i * c ^ j) := by rw [hxy]
      _ = (β v) ^ i * (β c) ^ j := by rw [map_mul, map_zpow, map_zpow]
      _ = (c * v) ^ i * c ^ j := by rw [hβv, hβc]
      _ = (c ^ i * v ^ i) * c ^ j := by rw [hcv.mul_zpow]
      _ = c ^ i * (v ^ i * c ^ j) := by rw [mul_assoc]
      _ = c ^ i * T₀.subtype x := by rw [← hxy]
  have hc'R' : c' ∈ R' := Subgroup.mem_sup_right (Subgroup.mem_zpowers c')
  have hstab : ∀ r ∈ R, β r ∈ R := by
    intro r hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨x, hx, hxr⟩ := hr
    obtain ⟨i, hi⟩ := hβx x hx
    rw [← hxr, Subgroup.mem_map]
    refine ⟨c' ^ i * x, ?_, ?_⟩
    · exact R'.mul_mem (R'.zpow_mem hc'R' i) hx
    · rw [map_mul, map_zpow]
      exact hi.symm
  have hquad : ∀ r ∈ R, β (β r * r⁻¹) = β r * r⁻¹ := by
    intro r hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨x, hx, hxr⟩ := hr
    obtain ⟨i, hi⟩ := hβx x hx
    rw [← hxr]
    have hβfixi : β (c ^ i) = c ^ i := by rw [map_zpow, hβc]
    have hdiff : β (T₀.subtype x) * (T₀.subtype x)⁻¹ = c ^ i := by
      rw [hi]; group
    rw [hdiff, hβfixi]
  refine ⟨R, ?_, ?_, hstab, hquad, ?_⟩
  · have hTp : IsPGroup 3 ↥T₀ := IsPGroup.of_exponent_dvd_pow
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x : ↥T₀ => Subtype.ext (hkill x.1 x.2)))
    have hR'p : IsPGroup 3 ↥R' := hTp.of_injective R'.subtype Subtype.coe_injective
    exact hR'p.map T₀.subtype
  · refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val (hcomm.is_comm.comm ⟨a.1, hRle a.2⟩ ⟨b.1, hRle b.2⟩)
  · refine ⟨v, ?_, hvne⟩
    rw [Subgroup.mem_map]
    exact ⟨v', Subgroup.mem_sup_left (Subgroup.mem_zpowers v'), rfl⟩

private theorem k1566l4b_transport_quadratic
    {Y : Type} [Group Y] {β α : MulAut Y} {l : Y}
    (hconj : MulAut.conj l * α * (MulAut.conj l)⁻¹ = β)
    {R₀ : Subgroup Y} (hR0p : IsPGroup 3 R₀) (hR0c : IsMulCommutative ↥R₀)
    (hstab : ∀ r ∈ R₀, β r ∈ R₀)
    (hquad : ∀ r ∈ R₀, β (β r * r⁻¹) = β r * r⁻¹)
    (hmov : ∃ r ∈ R₀, β r ≠ r) :
    ∃ R : Subgroup Y, IsPGroup 3 R ∧ IsMulCommutative ↥R ∧ (∀ r ∈ R, α r ∈ R) ∧
      (∀ r ∈ R, α (α r * r⁻¹) = α r * r⁻¹) ∧ (∃ r ∈ R, α r ≠ r) := by
  let f : Y →* Y := (MulAut.conj l).symm
  have hαeq : α = (MulAut.conj l).symm * β * MulAut.conj l := by
    rw [← hconj]
    show α = (MulAut.conj l)⁻¹ * (MulAut.conj l * α * (MulAut.conj l)⁻¹) * MulAut.conj l
    group
  let R : Subgroup Y := R₀.map f
  have hαapply : ∀ x : Y, α (f x) = f (β x) := by
    intro x
    have hfx : MulAut.conj l (f x) = x := by
      show MulAut.conj l ((MulAut.conj l).symm x) = x
      rw [MulEquiv.apply_symm_apply]
    rw [hαeq, MulAut.mul_apply, MulAut.mul_apply, hfx]
    rfl
  have hstabR : ∀ r ∈ R, α r ∈ R := by
    intro r hr
    rw [Subgroup.mem_map] at hr ⊢
    obtain ⟨x, hx, hxr⟩ := hr
    rw [← hxr]
    exact ⟨β x, hstab x hx, (hαapply x).symm⟩
  have hquadR : ∀ r ∈ R, α (α r * r⁻¹) = α r * r⁻¹ := by
    intro r hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨x, hx, hxr⟩ := hr
    rw [← hxr]
    have hmem : β x * x⁻¹ ∈ R₀ := R₀.mul_mem (hstab x hx) (R₀.inv_mem hx)
    have h2 : α (α (f x) * (f x)⁻¹) = f (β (β x * x⁻¹)) := by
      rw [hαapply x, ← map_inv, ← map_mul, hαapply (β x * x⁻¹)]
    rw [h2, hquad x hx, hαapply x, ← map_inv, ← map_mul]
  have hmovR : ∃ r ∈ R, α r ≠ r := by
    obtain ⟨x, hx, hxne⟩ := hmov
    refine ⟨f x, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨x, hx, rfl⟩
    · intro heq
      have h := congrArg (MulAut.conj l) heq
      rw [hαapply x] at h
      simp [f] at h
      exact hxne h
  refine ⟨R, hR0p.map f, ?_, hstabR, hquadR, hmovR⟩
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
  show a.1 * b.1 = b.1 * a.1
  rw [← hxa, ← hyb, ← map_mul, ← map_mul, k1566l4b_mul_comm_of_mem hR0c hx hy]

theorem exists_conj_into_sylow_of_outer {Y : Type} [Group Y] [Finite Y]
    (hZ : Subgroup.center Y = ⊥)
    {Q : Subgroup Y} (hQ : IsPGroup 3 Q) (hQi : ¬ 3 ∣ Q.index)
    {φ : MulAut Y} (hφ3 : φ ^ 3 = 1) (hφQ : ∀ q ∈ Q, φ q ∈ Q)
    {α : MulAut Y} (hα3 : α ^ 3 = 1) (hα : ∃ (g : Y) (j : ℕ), α = MulAut.conj g * φ ^ j) :
    ∃ (l t : Y) (j : ℕ), t ∈ Q ∧ j < 3 ∧
      MulAut.conj l * α * (MulAut.conj l)⁻¹ = MulAut.conj t * φ ^ j := by
  classical
  set Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range with hInn
  set InnQ : Subgroup (MulAut Y) := Q.map (MulAut.conj : Y →* MulAut Y) with hInnQ
  set A : Subgroup (MulAut Y) := Inn ⊔ Subgroup.zpowers φ with hA
  set PA : Subgroup (MulAut Y) := InnQ ⊔ Subgroup.zpowers φ with hPA
  have hInn_normal : Inn.Normal := by
    rw [hInn]
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Y
  have hconj_inj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    k1566l4a_mulAut_conj_injective hZ
  have hInnQle : InnQ.map (MulAut.conj φ : MulAut Y →* MulAut Y) ≤ InnQ := by
    rw [hInnQ]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hy
    change (MulAut.conj φ) (MulAut.conj q) ∈ Q.map (MulAut.conj : Y →* MulAut Y)
    rw [MulAut.conj_apply, k1566l4a_conj_mul_conj]
    exact Subgroup.mem_map.mpr ⟨φ q, hφQ q hq, rfl⟩
  have hInnQ_eq : InnQ.map (MulAut.conj φ : MulAut Y →* MulAut Y) = InnQ := by
    refine Subgroup.eq_of_le_of_card_ge hInnQle ?_
    rw [Subgroup.card_map_of_injective
      (f := (MulAut.conj φ : MulAut Y →* MulAut Y)) (MulAut.conj φ).injective]
  have hzp_le : Subgroup.zpowers φ ≤ Subgroup.normalizer InnQ :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hInnQ_eq)
  have hInnQ_pg : IsPGroup 3 InnQ := by
    rw [hInnQ]
    exact hQ.map (MulAut.conj : Y →* MulAut Y)
  have hzp_pg : IsPGroup 3 (Subgroup.zpowers φ) := by
    have hord : orderOf φ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hφ3
    rw [Nat.dvd_prime Nat.prime_three] at hord
    rcases hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; norm_num)
  have hPA_pg : IsPGroup 3 PA := by
    rw [hPA]
    exact IsPGroup.to_sup_of_normal_left' hInnQ_pg hzp_pg hzp_le
  have hInnQ_index : InnQ.relIndex Inn = Q.index := by
    rw [hInnQ, hInn, ← Subgroup.map_top (MulAut.conj : Y →* MulAut Y),
      Subgroup.relIndex_map_map_of_injective Q ⊤ hconj_inj, Subgroup.relIndex_top_right]
  have hInnQ_le_Inn : InnQ ≤ Inn := by
    rw [hInnQ, hInn]
    exact Subgroup.map_le_range _ _
  have hInnQ_le_inf : InnQ ≤ Inn ⊓ PA :=
    le_inf hInnQ_le_Inn (by rw [hPA]; exact le_sup_left)
  have hA_eq : A = Inn ⊔ PA := by
    rw [hA, hPA, ← sup_assoc, sup_eq_left.mpr hInnQ_le_Inn]
  have hPA_index : ¬ 3 ∣ PA.relIndex A := by
    have hdiv : PA.relIndex A ∣ InnQ.relIndex Inn := by
      rw [hA_eq, k1566l4a_relIndex_sup_eq_inf (K := Inn) (N := PA) hInn_normal]
      exact Subgroup.relIndex_dvd_of_le_left Inn hInnQ_le_inf
    intro h3
    rw [hInnQ_index] at hdiv
    exact hQi (dvd_trans h3 hdiv)
  have hPA_le_A : PA ≤ A := by rw [hA_eq]; exact le_sup_right
  have hP_pg : IsPGroup 3 (PA.subgroupOf A) :=
    hPA_pg.comap_of_injective A.subtype A.subtype_injective
  have hP_index : ¬ 3 ∣ (PA.subgroupOf A).index := by
    simpa only [Subgroup.relIndex] using hPA_index
  set Syl : Sylow 3 ↥A := hP_pg.toSylow hP_index with hSyl
  have hSyl_coe : (Syl : Subgroup ↥A) = PA.subgroupOf A := by
    rw [hSyl]
    exact IsPGroup.toSylow_coe hP_pg hP_index
  obtain ⟨g, j, hgj⟩ := hα
  have hαA : α ∈ A := by
    rw [hgj, hA]
    exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      (Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by rw [zpow_natCast]⟩)
  have hα3' : (⟨α, hαA⟩ : ↥A) ^ 3 = 1 := by
    apply Subtype.ext
    simp [hα3]
  have hS_pg : IsPGroup 3 (Subgroup.zpowers (⟨α, hαA⟩ : ↥A)) := by
    have hord : orderOf (⟨α, hαA⟩ : ↥A) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hα3'
    rw [Nat.dvd_prime Nat.prime_three] at hord
    rcases hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; norm_num)
  obtain ⟨Q', hSQ'⟩ := IsPGroup.exists_le_sylow hS_pg
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (↥A) Q' Syl
  have hαQ' : (⟨α, hαA⟩ : ↥A) ∈ Q' := hSQ' (Subgroup.mem_zpowers _)
  have hmemSyl : (MulAut.conj a) (⟨α, hαA⟩ : ↥A) ∈ Syl := by
    have h1 : (MulAut.conj a) (⟨α, hαA⟩ : ↥A) ∈ (MulAut.conj a) • (Q' : Subgroup ↥A) :=
      Subgroup.smul_mem_pointwise_smul (⟨α, hαA⟩ : ↥A) (MulAut.conj a) (Q' : Subgroup ↥A) hαQ'
    rwa [← Sylow.coe_subgroup_smul, ha] at h1
  have hconjA : (a : MulAut Y) * α * (a : MulAut Y)⁻¹ ∈ PA := by
    have h2 : (MulAut.conj a) (⟨α, hαA⟩ : ↥A) ∈ PA.subgroupOf A := by
      rw [← hSyl_coe]
      exact hmemSyl
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa [MulAut.conj_apply] using h3
  have ha_mem : (a : MulAut Y) ∈ (PA : Set (MulAut Y)) * (Inn : Set (MulAut Y)) := by
    rw [← @Subgroup.mul_normal (MulAut Y) _ PA Inn hInn_normal, sup_comm, ← hA_eq]
    exact a.2
  obtain ⟨p, hp, c, hc, hpc⟩ := Set.mem_mul.mp ha_mem
  rw [hInn] at hc
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hc
  have hcα : c * α * c⁻¹ ∈ PA := by
    have heq : c * α * c⁻¹ = p⁻¹ * ((a : MulAut Y) * α * (a : MulAut Y)⁻¹) * p := by
      rw [← hpc]
      group
    rw [heq]
    exact mul_mem (mul_mem (inv_mem hp) hconjA) hp
  have hmain : MulAut.conj l * α * (MulAut.conj l)⁻¹ ∈ PA := by
    rw [hl]
    exact hcα
  have hchar : ∃ t ∈ Q, ∃ j' : ℕ, j' < 3 ∧
      MulAut.conj t * φ ^ j' = MulAut.conj l * α * (MulAut.conj l)⁻¹ := by
    rw [hPA, hInnQ] at hmain
    exact (k1566l4a_mem_sup_map_conj_zpowers hφQ hφ3).mp hmain
  obtain ⟨t, ht, j', hj', htj'⟩ := hchar
  exact ⟨l, t, j', ht, hj', htj'.symm⟩

theorem exists_quadratic_subgroup_of_outerTorusDatum {Y : Type} [Group Y] [Finite Y]
    {φ : MulAut Y} {Q T V : Subgroup Y} {y : Y} {e1 e2 : ℕ} {k : ℤ}
    (hSD : SD3 Y Q T V y e1 e2) (hsc : ScalarAction T φ y k) (hk3 : (k : ZMod 3) = 1)
    (hk : ¬ (3 : ℤ) ^ max e1 e2 ∣ k - 1)
    {α : MulAut Y} (hα3 : α ^ 3 = 1) (l t : Y) (j : ℕ) (htQ : t ∈ Q) (hj : j = 1 ∨ j = 2)
    (hconj : MulAut.conj l * α * (MulAut.conj l)⁻¹ = MulAut.conj t * φ ^ j) :
    ∃ R : Subgroup Y, IsPGroup 3 R ∧ IsMulCommutative ↥R ∧ (∀ r ∈ R, α r ∈ R) ∧
      (∀ r ∈ R, α (α r * r⁻¹) = α r * r⁻¹) ∧ (∃ r ∈ R, α r ≠ r) := by
  obtain ⟨hQp, hQidx, hTQ, hTnorm, hTcomm, hVT, hVelem, hVT3, hQeq, hVtrans, hyVmov, hQmove,
    hVcard, hyord, hiso⟩ := hSD
  let β : MulAut Y := MulAut.conj t * φ ^ j
  have hβ3 : β ^ 3 = 1 := by
    have h : (MulAut.conj l * α * (MulAut.conj l)⁻¹) ^ 3
        = MulAut.conj l * α ^ 3 * (MulAut.conj l)⁻¹ := conj_pow
    show β ^ 3 = 1
    rw [show β = MulAut.conj t * φ ^ j from rfl, ← hconj, h, hα3]
    group
  have hTnormV : T ≤ Subgroup.normalizer (V : Set Y) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have hab : a * b * a⁻¹ = b := by
      rw [k1566l4b_mul_comm_of_mem hTcomm ha (hVT hb)]
      group
    rw [hab]
    exact hb
  have hyN : y ∈ Subgroup.normalizer (V : Set Y) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro w hw
      rw [Subgroup.mem_map] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      change y * u * y⁻¹ ∈ V
      have hc := (hVtrans u hu).1
      rw [show y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u by group]
      exact V.mul_mem hc hu
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj y))]
  have hQnorm : Q ≤ Subgroup.normalizer (V : Set Y) := by
    rw [hQeq]
    exact sup_le hTnormV (Subgroup.zpowers_le.mpr hyN)
  have hφjV : ∀ v ∈ V, (φ ^ j) v = v := by
    intro v hv
    have hφv : φ v = v := by
      have h := hsc.2 v (hVT hv)
      rwa [k1566l4b_zpow_eq_self_of_pow_three (hVelem.2 v hv) hk3] at h
    rcases hj with rfl | rfl
    · simpa using hφv
    · rw [pow_two, MulAut.mul_apply, hφv, hφv]
  by_cases htT : t ∈ T
  · have hkillT : ∀ s ∈ T, s ^ (3 ^ max e1 e2) = 1 := k1566l4b_pow_max_exp hiso
    have hβT : ∀ s ∈ T, β s ∈ T := by
      intro s hs
      rw [show β = MulAut.conj t * φ ^ j from rfl,
        k1566l4b_beta_apply_of_mem hsc hTcomm htT hs]
      exact T.zpow_mem hs _
    have hmovT : ∃ s ∈ T, β s ≠ s := by
      obtain ⟨s, hsT, hsord⟩ := k1566l4b_exists_order_max hiso
      refine ⟨s, hsT, ?_⟩
      intro hfix
      have hβs : β s = s ^ (k ^ j) := k1566l4b_beta_apply_of_mem hsc hTcomm htT hsT
      have hfix' : s ^ (k ^ j) = s := by rw [← hβs]; exact hfix
      have hsordZ : (orderOf s : ℤ) = (3 : ℤ) ^ max e1 e2 := by
        rw [hsord]; push_cast; ring
      rcases hj with hj1 | hj2
      · subst hj1
        rw [pow_one] at hfix'
        have h1 : s ^ (k - 1) = 1 := by
          have h2 : s ^ (k - 1) * s = s := by
            rw [← zpow_add_one, show k - 1 + 1 = k by ring, hfix']
          calc s ^ (k - 1) = s ^ (k - 1) * s * s⁻¹ := by group
            _ = s * s⁻¹ := by rw [h2]
            _ = 1 := by group
        have hdvd : (3 : ℤ) ^ max e1 e2 ∣ k - 1 := by
          rw [← hsordZ]
          exact orderOf_dvd_iff_zpow_eq_one.mpr h1
        exact hk hdvd
      · subst hj2
        have h1 : s ^ (k ^ 2 - 1) = 1 := by
          have h2 : s ^ (k ^ 2 - 1) * s = s := by
            rw [← zpow_add_one, show k ^ 2 - 1 + 1 = k ^ 2 by ring, hfix']
          calc s ^ (k ^ 2 - 1) = s ^ (k ^ 2 - 1) * s * s⁻¹ := by group
            _ = s * s⁻¹ := by rw [h2]
            _ = 1 := by group
        have hdvd : (3 : ℤ) ^ max e1 e2 ∣ k ^ 2 - 1 := by
          rw [← hsordZ]
          exact orderOf_dvd_iff_zpow_eq_one.mpr h1
        rw [show k ^ 2 - 1 = (k - 1) * (k + 1) by ring] at hdvd
        have hcop : IsCoprime ((3 : ℤ) ^ max e1 e2) (k + 1) :=
          (k1566l4b_isCoprime_three_add hk3).pow_left
        exact hk (hcop.dvd_of_dvd_mul_right hdvd)
    obtain ⟨R₀, hR0p, hR0c, hstab, hquad, hmov0⟩ :=
      k1566l4b_quadratic_subgroup_of_abelian (β := β) (max e1 e2) hTcomm hkillT hβT hβ3 hmovT
    exact k1566l4b_transport_quadratic (β := β) hconj hR0p hR0c hstab hquad hmov0
  · have hkillV : ∀ v ∈ V, v ^ (3 ^ 1) = 1 := by
      intro v hv
      simpa using hVelem.2 v hv
    have hβV : ∀ v ∈ V, β v ∈ V := by
      intro v hv
      have hβv : β v = t * v * t⁻¹ := by
        rw [show β = MulAut.conj t * φ ^ j from rfl, MulAut.mul_apply, hφjV v hv,
          MulAut.conj_apply]
      rw [hβv]
      exact (Subgroup.mem_normalizer_iff.mp (hQnorm htQ) v).mp hv
    have hmovV : ∃ v ∈ V, β v ≠ v := by
      obtain ⟨v, hv, hne⟩ := hQmove t htQ htT
      refine ⟨v, hv, ?_⟩
      have hβv : β v = t * v * t⁻¹ := by
        rw [show β = MulAut.conj t * φ ^ j from rfl, MulAut.mul_apply, hφjV v hv,
          MulAut.conj_apply]
      rw [hβv]
      exact hne
    obtain ⟨R₀, hR0p, hR0c, hstab, hquad, hmov0⟩ :=
      k1566l4b_quadratic_subgroup_of_abelian (β := β) 1 hVelem.1 hkillV hβV hβ3 hmovV
    exact k1566l4b_transport_quadratic (β := β) hconj hR0p hR0c hstab hquad hmov0

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
