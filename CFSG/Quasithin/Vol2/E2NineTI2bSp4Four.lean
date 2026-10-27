module

public import CFSG.Quasithin.Vol2.E2NineTI2bSp4Torus
public import CFSG.Quasithin.Vol2.Ch3E213MP5F
public import CFSG.Quasithin.Vol2.Ch3E213MP5H
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.E2.TI2b.Sp4

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

private theorem exists_ne_zero_ne_one_E29 {k : Type} [Field k] [Finite k] (hk : 4 ≤ Nat.card k) :
    ∃ t : k, t ≠ 0 ∧ t ≠ 1 := by
  classical
  haveI := Fintype.ofFinite k
  have hcard : ({0, 1} : Finset k).card < (Finset.univ : Finset k).card := by
    have h1 : ({0, 1} : Finset k).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  exact ⟨t, ht.1, ht.2⟩

private theorem eq_zero_of_mul_eq_self_E29 {k : Type} [Field k] {t x : k} (ht : t ≠ 1)
    (h : t * x = x) : x = 0 := by
  have h1 : (t - 1) * x = 0 := by linear_combination h
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr ht)

private theorem eq_zero_of_sq_mul_eq_self_E29 {k : Type} [Field k] [CharP k 2] {t x : k}
    (ht : t ≠ 1) (h : t ^ 2 * x = x) : x = 0 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have h1 : (t - 1) ^ 2 * x = 0 := by linear_combination h + (x - t * x) * h2
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr ht))

private theorem eq_one_of_dd_fixed {k : Type} [Field k] [CharP k 2] [Finite k]
    (hk : 4 ≤ Nat.card k) {v : antiSp k} (hv : v ∈ antiUnipotent k)
    (hfix : ∀ x y : kˣ, dd x y * v * (dd x y)⁻¹ = v) : v = 1 := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_E29 hk
  obtain ⟨a, b, c, d, rfl⟩ := hv
  have hx := hfix (Units.mk0 t ht0) 1
  have hy := hfix 1 (Units.mk0 t ht0)
  rw [dd_conj_uElt] at hx hy
  obtain ⟨h1, h2, h3, -⟩ := CFSG.QuasithinUnique.Setup.X7b.uElt_inj hx
  obtain ⟨-, -, -, h4⟩ := CFSG.QuasithinUnique.Setup.X7b.uElt_inj hy
  simp only [Units.val_mk0, Units.val_one, inv_one, mul_one, one_mul, one_pow] at h1 h2 h3 h4
  have ha : a = 0 := eq_zero_of_mul_eq_self_E29 ht1 h1
  have hb : b = 0 := eq_zero_of_mul_eq_self_E29 ht1 h2
  have hc : c = 0 := eq_zero_of_sq_mul_eq_self_E29 ht1 h3
  have hd : d = 0 := eq_zero_of_sq_mul_eq_self_E29 ht1 h4
  subst ha hb hc hd
  exact CFSG.QuasithinUnique.Setup.X7b.uElt_zero_eq_one

private theorem conjSub_eq_map_conj {G : Type} [Group G] (g : G) (X : Subgroup G) :
    CFSG.Quasithin.B6.conjSub g X = X.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [CFSG.Quasithin.B6.mem_conjSub, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy

private theorem eq_of_card_two_of_ne_one {G : Type} [Group G] {H : Subgroup G}
    (h2 : Nat.card H = 2) {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
  have h1 : (⟨a, ha⟩ : H) = y := huniq _ (fun h => ha1 (congrArg Subtype.val h))
  have h1' : (⟨b, hb⟩ : H) = y := huniq _ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h1'.symm)

private theorem exists_coord_sp4 {A : Type} [Group A] [Finite A] {Ts Ms K : Subgroup A} [K.Normal]
    {n : ℕ} (hn2 : 2 ≤ n) (hTs : IsSylowTwoOf Ts ⊤) (hSp : IsSp4Prime n ↥K)
    (hMK : Ms ⊓ K = K ⊓ Subgroup.normalizer ((Ts ⊓ K : Subgroup A) : Set A)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (θ : ↥K ≃* antiSp k),
      Nat.card k = 2 ^ n ∧
        ((Ms ⊓ K).subgroupOf K).map θ.toMonoidHom =
          Subgroup.normalizer ((antiUnipotent k : Subgroup (antiSp k)) : Set (antiSp k)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp' : IsPSp4 2 n ↥K := by
    have h' := hSp
    unfold IsSp4Prime at h'
    rwa [ite_eq_right (show ¬ n = 1 by omega)] at h'
  obtain ⟨-, k, _, _, hk, ⟨φ⟩⟩ := hSp'
  have : CharP k 2 := by
    have : Fintype k := Fintype.ofFinite k
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  let θ₁ : ↥K ≃* antiSp k :=
    φ.trans ((CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := k) (n := 2) (by norm_num)).trans
      (antiSpEquiv k).symm)
  have hS : IsSylowTwoOf (Ts ⊓ K) K :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hTs le_top
      (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  have hS' : IsSylowTwoOf ((Ts ⊓ K).subgroupOf K) ⊤ :=
    CFSG.Quasithin.Ch3E213M.P5.isSylowTwoOf_subgroupOf_top hS
  have hP : IsSylowTwoOf (((Ts ⊓ K).subgroupOf K).map θ₁.toMonoidHom) ⊤ := by
    have h := CFSG.Quasithin.Ch3E213M.P5.isSylowTwoOf_map_equiv θ₁ hS'
    rwa [Subgroup.map_top_of_surjective θ₁.toMonoidHom θ₁.surjective] at h
  have hT : IsSylowTwoOf (antiUnipotent k) ⊤ :=
    (CFSG.QuasithinUnique.Setup.X7b.card_and_isSylowTwoOf_antiUnipotent (K := k)).2
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hP hT
  let θ : ↥K ≃* antiSp k := θ₁.trans (MulAut.conj g)
  have hθU : ((Ts ⊓ K).subgroupOf K).map θ.toMonoidHom = antiUnipotent k := by
    rw [hg, conjSub_eq_map_conj, Subgroup.map_map]
    rfl
  have hB : ((Ms ⊓ K).subgroupOf K).map θ.toMonoidHom =
      Subgroup.normalizer ((antiUnipotent k : Subgroup (antiSp k)) : Set (antiSp k)) := by
    rw [CFSG.Quasithin.Ch3E213M.P5.subgroupOf_eq_normalizer hMK,
      Subgroup.map_equiv_normalizer_eq, hθU]
  exact ⟨k, inferInstance, inferInstance, inferInstance, θ, hk, hB⟩

private theorem centralizes_of_coord {A : Type} [Group A] {K Ms : Subgroup A} [K.Normal]
    {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ} (hn2 : 2 ≤ n) (hk : Nat.card k = 2 ^ n)
    (θ : ↥K ≃* antiSp k)
    (hB : ((Ms ⊓ K).subgroupOf K).map θ.toMonoidHom =
      Subgroup.normalizer ((antiUnipotent k : Subgroup (antiSp k)) : Set (antiSp k)))
    {e : A} (hcomm : ∀ m ∈ Ms, e * m * e⁻¹ = m) :
    ∀ x : ↥K, e * (x : A) * e⁻¹ = (x : A) := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  set α : MulAut (antiSp k) := MulAut.congr θ (MulAut.conjNormal e) with hα_def
  have hαθ : ∀ x : ↥K, α (θ x) = θ (MulAut.conjNormal e x) := by
    intro x
    rw [hα_def, MulAut.congr_apply]
    simp
  have hfix : ∀ u ∈ Subgroup.normalizer ((antiUnipotent k : Subgroup (antiSp k)) : Set (antiSp k)),
      α u = u := by
    intro u hu
    have hu' : u ∈ ((Ms ⊓ K).subgroupOf K).map θ.toMonoidHom := by
      rw [hB]
      exact hu
    obtain ⟨y, hy, hyu⟩ := hu'
    have hy' : (y : A) ∈ Ms ⊓ K := Subgroup.mem_subgroupOf.mp hy
    have hyK : MulAut.conjNormal e y = y :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hcomm _ (Subgroup.mem_inf.mp hy').1)
    subst hyu
    show α (θ y) = θ y
    rw [hαθ, hyK]
  have heU : (antiUnipotent k).map α.toMonoidHom = antiUnipotent k := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hfix y (Subgroup.le_normalizer hy)]
      exact hy
    · intro hx
      exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, hfix x (Subgroup.le_normalizer hx)]⟩
  have htriv : ∀ u ∈ antiUnipotent k, α u * u⁻¹ ∈ antiUnipotentCenter k := by
    intro u hu
    rw [hfix u (Subgroup.le_normalizer hu), mul_inv_cancel]
    exact Subgroup.one_mem _
  obtain ⟨v, hv, hαv⟩ :=
    CFSG.Quasithin.SteinbergBS.exists_eq_conj_of_trivial_mod_center_sp (f := n) (by omega) hk
      heU htriv
  have hdd : ∀ x y : kˣ, dd x y * v * (dd x y)⁻¹ = v := by
    intro x y
    have h1 := hfix (dd x y) (dd_mem_normalizer x y)
    rw [hαv, MulAut.conj_apply] at h1
    have h2 : v * dd x y = dd x y * v := mul_inv_eq_iff_eq_mul.mp h1
    rw [← h2, mul_inv_cancel_right]
  have hv1 : v = 1 := eq_one_of_dd_fixed hk4 hv hdd
  have hαid : ∀ x : ↥K, α (θ x) = θ x := by
    intro x
    rw [hαv, hv1, MulAut.conj_apply, inv_one, one_mul, mul_one]
  intro x
  have h1 := hαθ x
  rw [hαid x] at h1
  have h2 : MulAut.conjNormal e x = x := θ.injective h1.symm
  have h3 := congrArg Subtype.val h2
  rwa [MulAut.conjNormal_apply] at h3

theorem four_le_card_of_sp4 {A : Type} [Group A] [Finite A] {Ts Ms K Es : Subgroup A} [K.Normal]
    {n : ℕ} (hn2 : 2 ≤ n) (hTs : IsSylowTwoOf Ts ⊤)
    (hC : Subgroup.centralizer (K : Set A) = ⊥) (hSp : IsSp4Prime n ↥K)
    (hMK : Ms ⊓ K = K ⊓ Subgroup.normalizer ((Ts ⊓ K : Subgroup A) : Set A))
    (hMsE : Ms ≤ Subgroup.normalizer (Es : Set A)) (hEs : IsPGroup 2 Es) (hEs1 : Es ≠ ⊥) :
    4 ≤ Nat.card Es := by
  by_contra hlt
  replace hlt : Nat.card Es < 4 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he, he1⟩ : ∃ e ∈ Es, e ≠ 1 := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEs1
    exact ⟨(a : A), a.2, fun h => ha1 (Subtype.ext h)⟩
  have hgt : 1 < Nat.card Es := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact nontrivial_of_ne (1 : ↥Es) ⟨e, he⟩ (fun h => he1 (congrArg Subtype.val h).symm)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hEs
  have h2 : Nat.card Es = 2 := by
    rcases j with _ | _ | j
    · rw [pow_zero] at hj
      omega
    · simpa using hj
    · exfalso
      have h4 : 4 ≤ 2 ^ (j + 1 + 1) := by
        rw [pow_succ, pow_succ]
        have : 0 < 2 ^ j := by positivity
        omega
      omega
  have hcomm : ∀ m ∈ Ms, e * m * e⁻¹ = m := by
    intro m hm
    have hg : m * e * m⁻¹ ∈ Es := (Subgroup.mem_normalizer_iff.mp (hMsE hm) e).mp he
    have hg1 : m * e * m⁻¹ ≠ 1 := by
      intro h
      apply he1
      have := congrArg (fun x => m⁻¹ * x * m) h
      simpa [mul_assoc] using this
    have hge : m * e * m⁻¹ = e := eq_of_card_two_of_ne_one h2 hg he hg1 he1
    have h3 : m * e = e * m := mul_inv_eq_iff_eq_mul.mp hge
    rw [← h3, mul_inv_cancel_right]
  obtain ⟨k, hk, hfin, hchar, θ, hkcard, hB⟩ := exists_coord_sp4 hn2 hTs hSp hMK
  have hcent := centralizes_of_coord hn2 hkcard θ hB hcomm
  apply he1
  have hmem : e ∈ Subgroup.centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : e * h = h * e := mul_inv_eq_iff_eq_mul.mp (hcent ⟨h, hh⟩)
    exact h1.symm
  rw [hC, Subgroup.mem_bot] at hmem
  exact hmem

end CFSG.Quasithin.E2.TI2b.Sp4
