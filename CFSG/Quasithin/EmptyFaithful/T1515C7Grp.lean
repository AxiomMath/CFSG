module

public import CFSG.Quasithin.EmptyFaithful.T1515C7Mod
public import CFSG.Quasithin.Background.A1cA132Struct
public import CFSG.Quasithin.Background.G2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section SevenGrp

variable {V : Type} [CommGroup V]

structure SevenCtx (A Tb : Subgroup (MulAut V)) (t : MulAut V) : Prop where
  sq : ∀ v : V, v * v = 1
  card_V : Nat.card V = 64
  P1 : IsPOnePlusTwo 3 ↥(oTwoUpper A)
  Tb_le : Tb ≤ A
  syl : IsSylowTwoOf Tb A
  t_mem : t ∈ A
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_inv : ∀ x ∈ oTwoUpper A, t * x * t⁻¹ * x ∈ frattiniIn (oTwoUpper A)
  irr : IsIrredOnSection Tb (oTwoUpper A) (frattiniIn (oTwoUpper A))

theorem comm_adjust {G : Type*} [Group G] {x y c₁ c₂ : G} (h1x : Commute c₁ x)
    (h1y : Commute c₁ y) (h2x : Commute c₂ x) (h2y : Commute c₂ y) (h12 : Commute c₁ c₂) :
    (c₁ * x) * (c₂ * y) * (c₁ * x)⁻¹ * (c₂ * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hv : Commute c₁⁻¹ (x * y) := (h1x.mul_right h1y).inv_left
  have hxi : x⁻¹ * c₁⁻¹ = c₁⁻¹ * x⁻¹ := by
    have := (h1x.inv_inv).eq
    exact this.symm
  have hW : Commute c₂ (x * y * x⁻¹ * y⁻¹) :=
    ((h2x.mul_right h2y).mul_right h2x.inv_right).mul_right h2y.inv_right
  calc (c₁ * x) * (c₂ * y) * (c₁ * x)⁻¹ * (c₂ * y)⁻¹
      = c₁ * (x * c₂) * y * (x⁻¹ * c₁⁻¹) * (y⁻¹ * c₂⁻¹) := by group
    _ = c₁ * (c₂ * x) * y * (c₁⁻¹ * x⁻¹) * (y⁻¹ * c₂⁻¹) := by rw [h2x.eq, hxi]
    _ = (c₁ * c₂) * ((x * y) * c₁⁻¹) * x⁻¹ * y⁻¹ * c₂⁻¹ := by group
    _ = (c₁ * c₂) * (c₁⁻¹ * (x * y)) * x⁻¹ * y⁻¹ * c₂⁻¹ := by rw [hv.eq.symm]
    _ = (c₁ * c₂ * c₁⁻¹) * (x * y * x⁻¹ * y⁻¹) * c₂⁻¹ := by group
    _ = c₂ * (x * y * x⁻¹ * y⁻¹) * c₂⁻¹ := by rw [h12.eq]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hW.eq]; group

theorem comm_inv_inv {G : Type*} [Group G] {x y z : G} (hz : z = x * y * x⁻¹ * y⁻¹)
    (hzx : Commute z x) (hzy : Commute z y) : x⁻¹ * y⁻¹ * x * y = z := by
  have e1 : x * y = z * y * x := by rw [hz]; group
  calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by group
    _ = x⁻¹ * (y⁻¹ * z) * y * x := by rw [e1]; group
    _ = x⁻¹ * (z * y⁻¹) * y * x := by rw [hzy.inv_right.eq]
    _ = x⁻¹ * z * x := by group
    _ = z * x⁻¹ * x := by rw [hzx.inv_right.eq]
    _ = z := by group

namespace SevenCtx

variable {A Tb : Subgroup (MulAut V)} {t : MulAut V} [Finite V] (h : SevenCtx A Tb t)
include h

omit [Finite V] in
theorem card_P : Nat.card (oTwoUpper A) = 27 := by
  have := h.P1.2.1
  norm_num at this
  exact this

omit [Finite V] in
theorem exp_P : ∀ x ∈ oTwoUpper A, x ^ 3 = 1 := by
  intro x hx
  have := h.P1.2.2 ⟨x, hx⟩
  exact congrArg Subtype.val this

theorem mem_Z_iff {c : MulAut V} :
    c ∈ frattiniIn (oTwoUpper A) ↔ c ∈ oTwoUpper A ∧ ∀ p ∈ oTwoUpper A, p * c = c * p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfr := A1c.frattini_eq_center_of_isPOnePlusTwo h.P1
  unfold frattiniIn
  rw [hfr]
  constructor
  · rintro ⟨c', hc', rfl⟩
    refine ⟨c'.2, fun p hp => ?_⟩
    have := Subgroup.mem_center_iff.mp hc' ⟨p, hp⟩
    exact congrArg Subtype.val this
  · rintro ⟨hcP, hcc⟩
    refine ⟨⟨c, hcP⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hcc g.1 g.2)

theorem Z_le_P : frattiniIn (oTwoUpper A) ≤ oTwoUpper A := fun _ hc => ((h.mem_Z_iff).mp hc).1

theorem card_Z : Nat.card (frattiniIn (oTwoUpper A)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have _ : CFSG.IsExtraspecial 3 ↥(oTwoUpper A) := h.P1.1
  have hfr := A1c.frattini_eq_center_of_isPOnePlusTwo h.P1
  have hc := CFSG.IsExtraspecial.center_order_p 3 ↥(oTwoUpper A)
  unfold frattiniIn
  rw [hfr, Subgroup.card_map_of_injective (oTwoUpper A).subtype_injective]
  exact hc

omit [Finite V] h in
theorem P_conj {a x : MulAut V} (ha : a ∈ A) (hx : x ∈ oTwoUpper A) : a * x * a⁻¹ ∈ oTwoUpper A :=
  conj_mem_oTwoUpper (Subgroup.le_normalizer ha) hx

theorem Z_central {c : MulAut V} (hc : c ∈ frattiniIn (oTwoUpper A)) {p : MulAut V}
    (hp : p ∈ oTwoUpper A) : p * c = c * p := ((h.mem_Z_iff).mp hc).2 p hp

theorem Z_conj {a c : MulAut V} (ha : a ∈ A) (hc : c ∈ frattiniIn (oTwoUpper A)) :
    a * c * a⁻¹ ∈ frattiniIn (oTwoUpper A) := by
  rw [h.mem_Z_iff] at hc ⊢
  refine ⟨P_conj ha hc.1, fun p hp => ?_⟩
  have hp' : a⁻¹ * p * a ∈ oTwoUpper A := by
    have := P_conj (A.inv_mem ha) hp
    simpa using this
  have := hc.2 _ hp'
  calc p * (a * c * a⁻¹) = a * ((a⁻¹ * p * a) * c) * a⁻¹ := by group
    _ = a * (c * (a⁻¹ * p * a)) * a⁻¹ := by rw [this]
    _ = (a * c * a⁻¹) * p := by group

theorem comm_mem_Z {p q : MulAut V} (hp : p ∈ oTwoUpper A) (hq : q ∈ oTwoUpper A) :
    p * q * p⁻¹ * q⁻¹ ∈ frattiniIn (oTwoUpper A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnc := A1c.exists_not_commute_of_isPOnePlusTwo h.P1
  have hstruct := CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure
    (S := ↥(oTwoUpper A)) (p := 3) (by rw [h.card_P]; norm_num) hnc
  have hcomm : ⁅(⟨p, hp⟩ : ↥(oTwoUpper A)), ⟨q, hq⟩⁆ ∈ Subgroup.center ↥(oTwoUpper A) := by
    rw [← hstruct.1]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [h.mem_Z_iff]
  refine ⟨(oTwoUpper A).mul_mem ((oTwoUpper A).mul_mem ((oTwoUpper A).mul_mem hp hq)
    ((oTwoUpper A).inv_mem hp)) ((oTwoUpper A).inv_mem hq), fun r hr => ?_⟩
  have := Subgroup.mem_center_iff.mp hcomm ⟨r, hr⟩
  exact congrArg Subtype.val this

omit [Finite V] in
theorem P_inf_Tb : oTwoUpper A ⊓ Tb = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxT⟩
  have h3 := h.exp_P x hxP
  obtain ⟨k, hk⟩ := h.syl.2.1 ⟨x, hxT⟩
  have hk' : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hd : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one hk')
  have : Nat.gcd 3 (2 ^ k) = 1 := by
    apply Nat.Coprime.pow_right
    norm_num
  rw [this] at hd
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))

theorem eq_sup_sylow : A = oTwoUpper A ⊔ Tb := by
  classical
  have hNH : A ≤ Subgroup.normalizer (oTwoUpper A : Set (MulAut V)) := le_normalizer_oTwoUpper A
  have hnorm : ((oTwoUpper A).subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNH
  have hQ : IsPGroup 2 (↥A ⧸ (oTwoUpper A).subgroupOf A) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper A x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  set f : ↥A →* (↥A ⧸ (oTwoUpper A).subgroupOf A) := QuotientGroup.mk' _ with hf
  have hdvd := Subgroup.index_map_dvd (H := Tb.subgroupOf A) (f := f)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ.index ((Tb.subgroupOf A).map f)
  have hodd : ¬ 2 ∣ (Tb.subgroupOf A).index := h.syl.2.2
  have h1 : ((Tb.subgroupOf A).map f).index = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exfalso
      refine hodd ?_
      rw [hn] at hdvd
      exact (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
  rw [Subgroup.index_eq_one] at h1
  refine le_antisymm (fun x hx => ?_) (sup_le (oTwoUpper_le A) h.syl.1)
  have hmem : f ⟨x, hx⟩ ∈ (Tb.subgroupOf A).map f := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨t', ht, hteq⟩ := Subgroup.mem_map.mp hmem
  have h2 : (t' : ↥A)⁻¹ * ⟨x, hx⟩ ∈ (oTwoUpper A).subgroupOf A := by
    rw [← QuotientGroup.eq]
    exact hteq
  have h3 : (t' : MulAut V)⁻¹ * x ∈ oTwoUpper A := Subgroup.mem_subgroupOf.mp h2
  have h4 : x = (t' : MulAut V) * ((t' : MulAut V)⁻¹ * x) := by group
  have h5 : x ∈ Tb ⊔ oTwoUpper A := by
    rw [h4]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp ht) h3
  rwa [sup_comm] at h5

theorem mem_A {a : MulAut V} (ha : a ∈ A) : ∃ p ∈ oTwoUpper A, ∃ u ∈ Tb, a = p * u := by
  have hle : Tb ≤ Subgroup.normalizer (oTwoUpper A : Set (MulAut V)) :=
    h.Tb_le.trans (le_normalizer_oTwoUpper A)
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper A) Tb hle
  have ha' : a ∈ ((oTwoUpper A ⊔ Tb : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← h.eq_sup_sylow]
    exact ha
  rw [hset] at ha'
  obtain ⟨p, hp, u, hu, rfl⟩ := ha'
  exact ⟨p, hp, u, hu, rfl⟩

theorem exists_tau0 : ∃ τ₀ ∈ Tb, ∃ p ∈ oTwoUpper A, t = p * τ₀ ∧ τ₀ * τ₀ = 1 ∧ τ₀ ≠ 1 ∧
    ∀ q ∈ oTwoUpper A, τ₀ * q * τ₀⁻¹ * q ∈ frattiniIn (oTwoUpper A) := by
  obtain ⟨p, hp, u, hu, htu⟩ := h.mem_A h.t_mem
  have hpi : p⁻¹ ∈ oTwoUpper A := (oTwoUpper A).inv_mem hp
  have hut : u = p⁻¹ * t := by rw [htu]; group
  have huu : u * u = 1 := by
    have h1 : u * u ∈ oTwoUpper A := by
      have e : u * u = p⁻¹ * (t * p⁻¹ * t⁻¹) := by
        rw [hut]
        calc p⁻¹ * t * (p⁻¹ * t) = p⁻¹ * (t * p⁻¹ * t⁻¹) * (t * t) := by group
          _ = p⁻¹ * (t * p⁻¹ * t⁻¹) := by rw [h.t_sq]; group
      rw [e]
      exact (oTwoUpper A).mul_mem hpi (P_conj h.t_mem hpi)
    have h2 : u * u ∈ Tb := Tb.mul_mem hu hu
    have h3 : u * u ∈ oTwoUpper A ⊓ Tb := ⟨h1, h2⟩
    rw [h.P_inf_Tb] at h3
    exact Subgroup.mem_bot.mp h3
  have hu1 : u ≠ 1 := by
    intro h1
    apply h.t_ne
    have htp : t = p := by rw [htu, h1, mul_one]
    have h3 : p ^ 3 = 1 := h.exp_P p hp
    rw [← htp] at h3
    calc t = t ^ 3 * (t * t)⁻¹ := by group
      _ = 1 := by rw [h3, h.t_sq]; group
  refine ⟨u, hu, p, hp, htu, huu, hu1, fun q hq => ?_⟩
  have hc := h.t_inv q hq
  set c : MulAut V := t * q * t⁻¹ * q with hcdef
  have hqi : q⁻¹ ∈ oTwoUpper A := (oTwoUpper A).inv_mem hq
  have hcomm := h.comm_mem_Z hpi hqi
  have e1 : u * q * u⁻¹ * q = p⁻¹ * c * (q⁻¹ * p * q) := by rw [hut, hcdef]; group
  have e2 : p⁻¹ * c = c * p⁻¹ := h.Z_central hc hpi
  have e3 : u * q * u⁻¹ * q = c * (p⁻¹ * q⁻¹ * (p⁻¹)⁻¹ * (q⁻¹)⁻¹) := by
    rw [e1, e2]; group
  rw [e3]
  exact (frattiniIn (oTwoUpper A)).mul_mem hc hcomm

end SevenCtx

namespace SevenCtx

variable {A Tb : Subgroup (MulAut V)} {t : MulAut V} [Finite V] (h : SevenCtx A Tb t)
include h

theorem exists_gens : ∃ τ₀ x y z p₀ : MulAut V, τ₀ ∈ Tb ∧ τ₀ * τ₀ = 1 ∧ τ₀ ≠ 1 ∧
    x ∈ oTwoUpper A ∧ y ∈ oTwoUpper A ∧ z ∈ frattiniIn (oTwoUpper A) ∧ z ≠ 1 ∧
    τ₀ * x * τ₀⁻¹ = x⁻¹ ∧ τ₀ * y * τ₀⁻¹ = y⁻¹ ∧ τ₀ * z = z * τ₀ ∧ z = x * y * x⁻¹ * y⁻¹ ∧
    (∀ p ∈ oTwoUpper A, τ₀ * p * τ₀⁻¹ * p ∈ frattiniIn (oTwoUpper A)) ∧
    p₀ ∈ oTwoUpper A ∧ t = p₀ * τ₀ := by
  obtain ⟨τ₀, hτT, p₀, hp₀, ht₀, hτ2, hτ1, hτinv⟩ := h.exists_tau0
  obtain ⟨a₀, b₀, hab⟩ := A1c.exists_not_commute_of_isPOnePlusTwo h.P1
  set a : MulAut V := (a₀ : MulAut V) with ha
  set b : MulAut V := (b₀ : MulAut V) with hb
  have haP : a ∈ oTwoUpper A := a₀.2
  have hbP : b ∈ oTwoUpper A := b₀.2
  have hab' : a * b ≠ b * a := fun h' => hab (Subtype.ext h')
  set z₀ : MulAut V := a * b * a⁻¹ * b⁻¹ with hz₀
  have hz₀Z : z₀ ∈ frattiniIn (oTwoUpper A) := h.comm_mem_Z haP hbP
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    apply hab'
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [← hz₀, h1]; group
  have hz₀P : z₀ ∈ oTwoUpper A := h.Z_le_P hz₀Z
  have hZc : ∀ c ∈ frattiniIn (oTwoUpper A), ∀ p ∈ oTwoUpper A, Commute c p :=
    fun c hc p hp => (h.Z_central hc hp).symm
  set ca : MulAut V := τ₀ * a * τ₀⁻¹ * a with hca
  set cb : MulAut V := τ₀ * b * τ₀⁻¹ * b with hcb
  have hcaZ := hτinv a haP
  have hcbZ := hτinv b hbP
  have hτa : τ₀ * a * τ₀⁻¹ = ca * a⁻¹ := by rw [hca]; group
  have hτb : τ₀ * b * τ₀⁻¹ = cb * b⁻¹ := by rw [hcb]; group
  have hz₀c : τ₀ * z₀ * τ₀⁻¹ = z₀ := by
    have e1 : τ₀ * z₀ * τ₀⁻¹ = (τ₀ * a * τ₀⁻¹) * (τ₀ * b * τ₀⁻¹) * (τ₀ * a * τ₀⁻¹)⁻¹ *
        (τ₀ * b * τ₀⁻¹)⁻¹ := by rw [hz₀]; group
    rw [e1, hτa, hτb]
    have e2 := comm_adjust (x := a⁻¹) (y := b⁻¹) (c₁ := ca) (c₂ := cb)
      (hZc _ hcaZ _ ((oTwoUpper A).inv_mem haP)) (hZc _ hcaZ _ ((oTwoUpper A).inv_mem hbP))
      (hZc _ hcbZ _ ((oTwoUpper A).inv_mem haP)) (hZc _ hcbZ _ ((oTwoUpper A).inv_mem hbP))
      (hZc _ hcaZ _ (h.Z_le_P hcbZ))
    rw [e2]
    exact comm_inv_inv hz₀ (hZc _ hz₀Z _ haP) (hZc _ hz₀Z _ hbP)
  have hz₀3 : z₀ ^ 3 = 1 := h.exp_P z₀ hz₀P
  have hZeq : frattiniIn (oTwoUpper A) = Subgroup.zpowers z₀ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hz₀Z
    · rw [h.card_Z, card_pow_gen hz₀3 hz₀1]
  have hτZ : ∀ c ∈ frattiniIn (oTwoUpper A), τ₀ * c = c * τ₀ := by
    intro c hc
    rw [hZeq] at hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have e : τ₀ * z₀ ^ m * τ₀⁻¹ = z₀ ^ m := by rw [← conj_zpow, hz₀c]
    calc τ₀ * z₀ ^ m = (τ₀ * z₀ ^ m * τ₀⁻¹) * τ₀ := by group
      _ = z₀ ^ m * τ₀ := by rw [e]
  have hcaP : ca ∈ oTwoUpper A := h.Z_le_P hcaZ
  have hcbP : cb ∈ oTwoUpper A := h.Z_le_P hcbZ
  have hca3 : ca ^ 3 = 1 := h.exp_P ca hcaP
  have hcb3 : cb ^ 3 = 1 := h.exp_P cb hcbP
  have hc2 : ∀ c : MulAut V, c ^ 3 = 1 → c * c = c⁻¹ := by
    intro c hc3
    refine eq_inv_of_mul_eq_one_left ?_
    have : c ^ 3 = c * c * c := by rw [pow_succ, pow_succ, pow_one]
    rwa [this] at hc3
  have hτc : ∀ c ∈ frattiniIn (oTwoUpper A), τ₀ * c * τ₀⁻¹ = c := fun c hc => by
    rw [hτZ c hc]; group
  have hadj : ∀ p c : MulAut V, p ∈ oTwoUpper A → c ∈ frattiniIn (oTwoUpper A) →
      τ₀ * p * τ₀⁻¹ = c * p⁻¹ → τ₀ * (p * c) * τ₀⁻¹ = (p * c)⁻¹ := by
    intro p c hp hc hτp
    have hcP := h.Z_le_P hc
    have hc3 := h.exp_P c hcP
    calc τ₀ * (p * c) * τ₀⁻¹ = (τ₀ * p * τ₀⁻¹) * (τ₀ * c * τ₀⁻¹) := by group
      _ = (c * p⁻¹) * c := by rw [hτp, hτc c hc]
      _ = c * (p⁻¹ * c) := by group
      _ = c * (c * p⁻¹) := by rw [(hZc c hc p⁻¹ ((oTwoUpper A).inv_mem hp)).eq.symm]
      _ = (c * c) * p⁻¹ := by group
      _ = c⁻¹ * p⁻¹ := by rw [hc2 c hc3]
      _ = (p * c)⁻¹ := by group
  have hxP : a * ca ∈ oTwoUpper A := (oTwoUpper A).mul_mem haP hcaP
  have hyP : b * cb ∈ oTwoUpper A := (oTwoUpper A).mul_mem hbP hcbP
  have hzxy : z₀ = (a * ca) * (b * cb) * (a * ca)⁻¹ * (b * cb)⁻¹ := by
    have e1 : a * ca = ca * a := (hZc ca hcaZ a haP).eq.symm
    have e2 : b * cb = cb * b := (hZc cb hcbZ b hbP).eq.symm
    rw [e1, e2, comm_adjust (hZc ca hcaZ a haP) (hZc ca hcaZ b hbP) (hZc cb hcbZ a haP)
      (hZc cb hcbZ b hbP) (hZc ca hcaZ cb hcbP)]
  exact ⟨τ₀, a * ca, b * cb, z₀, p₀, hτT, hτ2, hτ1, hxP, hyP, hz₀Z, hz₀1,
    hadj a ca haP hcaZ hτa, hadj b cb hbP hcbZ hτb, hτZ z₀ hz₀Z, hzxy, hτinv, hp₀, ht₀⟩

end SevenCtx

structure SevenGen (A Tb : Subgroup (MulAut V)) (τ x y z : MulAut V) : Prop where
  tau_mem : τ ∈ Tb
  tau_sq : τ * τ = 1
  tau_ne : τ ≠ 1
  xP : x ∈ oTwoUpper A
  yP : y ∈ oTwoUpper A
  zZ : z ∈ frattiniIn (oTwoUpper A)
  z1 : z ≠ 1
  tau_x : τ * x * τ⁻¹ = x⁻¹
  tau_y : τ * y * τ⁻¹ = y⁻¹
  tau_z : τ * z = z * τ
  zdef : z = x * y * x⁻¹ * y⁻¹
  tau_inv : ∀ p ∈ oTwoUpper A, τ * p * τ⁻¹ * p ∈ frattiniIn (oTwoUpper A)

namespace SevenGen

variable {A Tb : Subgroup (MulAut V)} {t τ x y z : MulAut V}

theorem exists_gen' [Finite V] (h : SevenCtx A Tb t) :
    ∃ τ x y z p, SevenGen A Tb τ x y z ∧ p ∈ oTwoUpper A ∧ t = p * τ := by
  obtain ⟨τ, x, y, z, p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    h.exists_gens
  exact ⟨τ, x, y, z, p, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, h13, h14⟩

theorem y_tau_rel (g : SevenGen A Tb τ x y z) : y * τ = τ * y⁻¹ := by
  have h0 : τ * y⁻¹ * τ⁻¹ = y := by
    have := congrArg (fun q => q⁻¹) g.tau_y
    simpa [mul_assoc] using this
  calc y * τ = (τ * y⁻¹ * τ⁻¹) * τ := by rw [h0]
    _ = τ * y⁻¹ := by group

theorem x_tau_rel (g : SevenGen A Tb τ x y z) : x * τ = τ * x⁻¹ := by
  have h0 : τ * x⁻¹ * τ⁻¹ = x := by
    have := congrArg (fun q => q⁻¹) g.tau_x
    simpa [mul_assoc] using this
  calc x * τ = (τ * x⁻¹ * τ⁻¹) * τ := by rw [h0]
    _ = τ * x⁻¹ := by group

section Rel

variable [Finite V] (h : SevenCtx A Tb t) (g : SevenGen A Tb τ x y z)
include h g

omit [Finite V] in
theorem x3 : x ^ 3 = 1 := h.exp_P x g.xP

omit [Finite V] in
theorem y3 : y ^ 3 = 1 := h.exp_P y g.yP

theorem z3 : z ^ 3 = 1 := h.exp_P z (h.Z_le_P g.zZ)

theorem xz : x * z = z * x := (h.Z_central g.zZ g.xP)

theorem yz : y * z = z * y := (h.Z_central g.zZ g.yP)

theorem xy_rel : x * y * x⁻¹ = y * z ^ 1 := by
  have h1 : z * y = y * z := (yz h g).symm
  calc x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    _ = z * y := by rw [← g.zdef]
    _ = y * z ^ 1 := by rw [h1, pow_one]

theorem yx_rel : y * x * y⁻¹ = x * z ^ 2 := by
  have hz3 := z3 h g
  have hxz : x * z = z * x := xz h g
  have e1 : x * y = z * y * x := by rw [g.zdef]; group
  have hzi : z⁻¹ = z ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    have : z ^ 3 = z * z ^ 2 := by rw [pow_succ']
    rwa [this] at hz3
  calc y * x * y⁻¹ = z⁻¹ * (z * y * x) * y⁻¹ := by group
    _ = z⁻¹ * (x * y) * y⁻¹ := by rw [e1]
    _ = z⁻¹ * x := by group
    _ = x * z ^ 2 := by rw [(show Commute z x from (xz h g).symm).inv_left.eq, hzi]

theorem fpf_z' : ∀ w : V, z w = w → w = 1 :=
  fpf_z h.sq (y3 h g) (z3 h g) (x3 h g) (yz h g) (xz h g) (e := 1) (by norm_num) (xy_rel h g)
    h.card_V g.z1

theorem card_fix_y' :
    Nat.card (fixOf y) = 4 ∧ Nat.card (fixOf (y * z)) = 4 ∧ Nat.card (fixOf (y * z ^ 2)) = 4 :=
  card_fix_y h.sq (y3 h g) (z3 h g) (x3 h g) (yz h g) (xz h g) (e := 1) (by norm_num)
    (xy_rel h g) h.card_V g.z1

theorem card_fix_x : Nat.card (fixOf x) = 4 :=
  (card_fix_y h.sq (x3 h g) (z3 h g) (y3 h g) (xz h g) (yz h g) (e := 2) (by norm_num)
    (yx_rel h g) h.card_V g.z1).1

theorem tau_fix_y : ∀ c ∈ fixOf y, τ c = c := by
  refine klein_trivial (card_fix_y' h g).1 (z3 h g)
    (fun c hc => apply_mem_fixOf_of_commute (yz h g).symm hc)
    (fun c _ hzc => fpf_z' h g c hzc) ?_ g.tau_z (k := 1) ?_
  · intro c hc
    have hc' : y c = c := hc
    have hyi : y⁻¹ c = c := by
      calc y⁻¹ c = y⁻¹ (y c) := by rw [hc']
        _ = c := by simp
    show y (τ c) = τ c
    calc y (τ c) = (y * τ) c := rfl
      _ = (τ * y⁻¹) c := by rw [y_tau_rel g]
      _ = τ (y⁻¹ c) := rfl
      _ = τ c := by rw [hyi]
  · rw [pow_one, pow_two]
    exact g.tau_sq

theorem tau_fix_x : ∀ c ∈ fixOf x, τ c = c := by
  refine klein_trivial (card_fix_x h g) (z3 h g)
    (fun c hc => apply_mem_fixOf_of_commute (xz h g).symm hc)
    (fun c _ hzc => fpf_z' h g c hzc) ?_ g.tau_z (k := 1) ?_
  · intro c hc
    have hc' : x c = c := hc
    have hxi : x⁻¹ c = c := by
      calc x⁻¹ c = x⁻¹ (x c) := by rw [hc']
        _ = c := by simp
    show x (τ c) = τ c
    calc x (τ c) = (x * τ) c := rfl
      _ = (τ * x⁻¹) c := by rw [x_tau_rel g]
      _ = τ (x⁻¹ c) := rfl
      _ = τ c := by rw [hxi]
  · rw [pow_one, pow_two]
    exact g.tau_sq

theorem eq_one_of_comm {u : MulAut V} (hu : u ∈ Tb) (huz : u * z = z * u) {j : ℕ}
    (huy : u * y * u⁻¹ = y * z ^ j) : u = 1 := by
  obtain ⟨k, hk⟩ := h.syl.2.1 ⟨u, hu⟩
  have hk' : u ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hz3 := z3 h g
  have hzo : orderOf z = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hz3 g.z1
  have hpow : ∀ n : ℕ, u ^ n * y * (u ^ n)⁻¹ = y * z ^ (n * j) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have hcz : ∀ q : ℕ, u * z ^ q * u⁻¹ = z ^ q := by
        intro q
        have : u * z ^ q = z ^ q * u := (Commute.pow_right (show Commute u z from huz) q).eq
        rw [this]; group
      calc u ^ (m + 1) * y * (u ^ (m + 1))⁻¹ = u * (u ^ m * y * (u ^ m)⁻¹) * u⁻¹ := by
            rw [pow_succ']; group
        _ = u * (y * z ^ (m * j)) * u⁻¹ := by rw [ih]
        _ = (u * y * u⁻¹) * (u * z ^ (m * j) * u⁻¹) := by group
        _ = y * z ^ j * z ^ (m * j) := by rw [huy, hcz]
        _ = y * z ^ ((m + 1) * j) := by rw [mul_assoc, ← pow_add]; congr 2; ring
  have h2k := hpow (2 ^ k)
  rw [hk', one_mul, inv_one, mul_one] at h2k
  have hz1 : z ^ (2 ^ k * j) = 1 := by
    have : y = y * z ^ (2 ^ k * j) := h2k
    exact (mul_eq_left.mp this.symm)
  have h3 : 3 ∣ 2 ^ k * j := by
    rw [← hzo]
    exact orderOf_dvd_of_pow_eq_one hz1
  have h3j : 3 ∣ j := by
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h3
  have hzj : z ^ j = 1 := by
    obtain ⟨q, rfl⟩ := h3j
    rw [pow_mul, hz3, one_pow]
  rw [hzj, mul_one] at huy
  have huy' : u * y = y * u := by
    calc u * y = (u * y * u⁻¹) * u := by group
      _ = y * u := by rw [huy]
  have hfix : ∀ j' : ℕ, j' < 3 → ∀ c ∈ fixOf (y * z ^ j'), u c = c := by
    intro j' hj' c hc
    have hC4 : Nat.card (fixOf (y * z ^ j')) = 4 := by
      obtain ⟨c0, c1, c2⟩ := card_fix_y' h g
      interval_cases j'
      · simpa using c0
      · simpa using c1
      · exact c2
    refine klein_trivial hC4 hz3
      (fun c hc => apply_mem_fixOf_of_commute ?_ hc)
      (fun c _ hzc => fpf_z' h g c hzc)
      (fun c hc => commute_preserves_fix huy' huz j' hc) huz (k := k) hk' c hc
    have : z * (y * z ^ j') = (y * z ^ j') * z := by
      have h1 : z * y = y * z := (yz h g).symm
      have h2 : z * z ^ j' = z ^ j' * z := (Commute.pow_right (Commute.refl z) j').eq
      calc z * (y * z ^ j') = (z * y) * z ^ j' := by group
        _ = y * (z * z ^ j') := by rw [h1]; group
        _ = y * (z ^ j' * z) := by rw [h2]
        _ = (y * z ^ j') * z := by group
    exact this
  ext v
  have hdec := exists_decomp_E h.sq hz3 (yz h g) (W := ⊤) (fun w _ => trivial) (fun w _ hzw => fpf_z' h g w hzw)
    (w := v) trivial
  have hm : ∀ j' : ℕ, j' < 3 → u (normOf (y * z ^ j') v) = normOf (y * z ^ j') v := fun j' hj' =>
    hfix j' hj' _ (normOf_mem_fixOf (cube_yz (y3 h g) hz3 (yz h g) j') v)
  have hu : u v = v := by
    calc u v = u (normOf (y * z ^ 0) v * normOf (y * z ^ 1) v * normOf (y * z ^ 2) v) := by
          rw [← hdec]
      _ = u (normOf (y * z ^ 0) v) * u (normOf (y * z ^ 1) v) * u (normOf (y * z ^ 2) v) := by
          simp only [map_mul]
      _ = v := by rw [hm 0 (by norm_num), hm 1 (by norm_num), hm 2 (by norm_num), ← hdec]
  simpa using hu

theorem Z_eq_zpowers : frattiniIn (oTwoUpper A) = Subgroup.zpowers z := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr g.zZ)
  rw [h.card_Z, card_pow_gen (z3 h g) g.z1]

theorem Z_pow {c : MulAut V} (hc : c ∈ frattiniIn (oTwoUpper A)) : ∃ j : ℕ, c = z ^ j := by
  rw [Z_eq_zpowers h g] at hc
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨j, hj⟩ := exists_nat_pow_eq_zpow (z3 h g) g.z1 m
  exact ⟨j, hj⟩

theorem tau_Z {c : MulAut V} (hc : c ∈ frattiniIn (oTwoUpper A)) : τ * c = c * τ := by
  obtain ⟨j, rfl⟩ := Z_pow h g hc
  calc τ * z ^ j = z ^ j * τ := (Commute.pow_right (show Commute τ z from g.tau_z) j).eq

theorem tau_central : ∀ u ∈ Tb, u * τ = τ * u := by
  intro u hu
  have hτ2 := g.tau_sq
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have huA : u ∈ A := h.Tb_le hu
  have hτA : τ ∈ A := h.Tb_le g.tau_mem
  set τ' : MulAut V := u * τ * u⁻¹ with hτ'
  set κ : MulAut V := τ * τ' with hκ
  have hκT : κ ∈ Tb := Tb.mul_mem g.tau_mem
    (Tb.mul_mem (Tb.mul_mem hu g.tau_mem) (Tb.inv_mem hu))
  have hτ'z : τ' * z = z * τ' := by
    have hc : u⁻¹ * z * u ∈ frattiniIn (oTwoUpper A) := by
      have := h.Z_conj (A.inv_mem huA) g.zZ
      simpa using this
    have e := tau_Z h g hc
    calc τ' * z = u * (τ * (u⁻¹ * z * u)) * u⁻¹ := by rw [hτ']; group
      _ = u * ((u⁻¹ * z * u) * τ) * u⁻¹ := by rw [e]
      _ = z * τ' := by rw [hτ']; group
  have hκz : κ * z = z * κ := by
    calc κ * z = τ * (τ' * z) := by rw [hκ]; group
      _ = τ * (z * τ') := by rw [hτ'z]
      _ = (τ * z) * τ' := by group
      _ = (z * τ) * τ' := by rw [g.tau_z]
      _ = z * κ := by rw [hκ]; group
  have hτ'inv : τ' * y * τ'⁻¹ * y ∈ frattiniIn (oTwoUpper A) := by
    have hy' : u⁻¹ * y * u ∈ oTwoUpper A := by
      have := SevenCtx.P_conj (A.inv_mem huA) g.yP
      simpa using this
    have := h.Z_conj huA (g.tau_inv _ hy')
    convert this using 1
    rw [hτ']
    group
  set c : MulAut V := τ' * y * τ'⁻¹ * y with hc
  have hcZ : c ∈ frattiniIn (oTwoUpper A) := hτ'inv
  have hτ'y : τ' * y * τ'⁻¹ = c * y⁻¹ := by rw [hc]; group
  have hκy : κ * y * κ⁻¹ = c * y := by
    have hτc : τ * c * τ⁻¹ = c := by rw [tau_Z h g hcZ]; group
    have hτy' : τ * y⁻¹ * τ⁻¹ = y := by
      have := congrArg (fun q => q⁻¹) g.tau_y
      simpa [mul_assoc] using this
    calc κ * y * κ⁻¹ = τ * (τ' * y * τ'⁻¹) * τ⁻¹ := by rw [hκ]; group
      _ = τ * (c * y⁻¹) * τ⁻¹ := by rw [hτ'y]
      _ = (τ * c * τ⁻¹) * (τ * y⁻¹ * τ⁻¹) := by group
      _ = c * y := by rw [hτc, hτy']
  obtain ⟨j, hj⟩ := Z_pow h g hcZ
  have hcy : c * y = y * z ^ j := by
    have e := (h.Z_central hcZ g.yP).symm
    rw [hj] at e ⊢
    exact e
  have hκ1 : κ = 1 := eq_one_of_comm h g hκT hκz (by rw [hκy, hcy])
  have : τ' = τ := by
    have h1 : τ * τ' = 1 := hκ1
    calc τ' = τ⁻¹ * (τ * τ') := by group
      _ = τ⁻¹ := by rw [h1]; group
      _ = τ := hτi
  calc u * τ = (u * τ * u⁻¹) * u := by group
    _ = τ * u := by rw [← hτ', this]

end Rel

end SevenGen

end SevenGrp

end CFSG.Quasithin
