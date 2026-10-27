module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructBase
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement IsMulCommutative
open CFSG.ABGLocalTools

theorem centerless_range49_center_eq_bot {Γ : Type} [Group Γ] (h : IsAlt Γ 5) :
    Subgroup.center Γ = ⊥ := by
  obtain ⟨e⟩ := h
  have h1 : (Subgroup.center Γ).map e.toMonoidHom =
      Subgroup.center (alternatingGroup (Fin 5)) := Subgroup.map_center_eq e
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem centerless_range49_ker_le_pCore {L : Subgroup G} {K : Type*} [Monoid K]
    (φ : ↥L →* K) (hL : IsAlt (Bar2 L) 5)
    (hker : ∀ g : ↥L, g ∈ CFSG.pCore 2 ↥L → φ g = 1)
    (hφ : ∃ g : ↥L, φ g ≠ 1) :
    φ.ker ≤ CFSG.pCore 2 ↥L := by
  have hpCore_le : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact hker g hg
  intro g hg
  by_contra hgpc
  let q : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hqg_ne : q g ≠ 1 := by
    intro h1
    apply hgpc
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker]
    exact h1
  have hmem : q g ∈ φ.ker.map q := Subgroup.mem_map_of_mem q hg
  haveI : (φ.ker.map q).Normal :=
    (MonoidHom.normal_ker φ).map q (QuotientGroup.mk'_surjective _)
  have htop : φ.ker.map q = ⊤ := normal_eq_top_of_isAlt_five hL hmem hqg_ne
  have htopker : φ.ker = ⊤ := by
    rw [eq_top_iff]
    intro l _
    have hql : q l ∈ φ.ker.map q := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hql
    have hkl : k⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
      have hq1 : q (k⁻¹ * l) = 1 := by rw [map_mul, map_inv, hkq, inv_mul_cancel]
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker]
      exact hq1
    have hklker : k⁻¹ * l ∈ φ.ker := hpCore_le hkl
    have heq : l = k * (k⁻¹ * l) := by group
    rw [heq]
    exact φ.ker.mul_mem hk hklker
  obtain ⟨g0, hg0⟩ := hφ
  apply hg0
  have hg0ker : g0 ∈ φ.ker := by rw [htopker]; exact Subgroup.mem_top _
  rwa [MonoidHom.mem_ker] at hg0ker

theorem centerless_range49 {L : Subgroup G} {K : Type*} [Monoid K] (φ : ↥L →* K)
    (hL : IsAlt (Bar2 L) 5) (hker : ∀ g : ↥L, g ∈ CFSG.pCore 2 ↥L → φ g = 1)
    (hφ : ∃ g : ↥L, φ g ≠ 1) :
    (∀ g : ↥L, φ g = 1 → g ∈ CFSG.pCore 2 ↥L) ∧
      ∀ g₀ : ↥L, (∀ g : ↥L, φ g₀ * φ g = φ g * φ g₀) → φ g₀ = 1 := by
  have hker_le := centerless_range49_ker_le_pCore φ hL hker hφ
  refine ⟨fun g hg => hker_le (MonoidHom.mem_ker.mpr hg), fun g₀ hcomm => ?_⟩
  let q : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hcenter : q g₀ ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) h
    change q g * q g₀ = q g₀ * q g
    have h1 : φ g₀ * φ g₀⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : φ g * φ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hcom : φ ⁅g₀, g⁆ = 1 := by
      rw [commutatorElement_def]
      simp only [map_mul]
      rw [hcomm g, mul_assoc (φ g) (φ g₀) (φ g₀⁻¹), h1, mul_one, h2]
    have hcom_pc : ⁅g₀, g⁆ ∈ CFSG.pCore 2 ↥L := hker_le (MonoidHom.mem_ker.mpr hcom)
    have hq1 : q ⁅g₀, g⁆ = 1 := by
      have hmem : ⁅g₀, g⁆ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
        rw [QuotientGroup.ker_mk']
        exact hcom_pc
      rwa [MonoidHom.mem_ker] at hmem
    have hq_com : ⁅q g₀, q g⁆ = 1 := by rw [← map_commutatorElement q]; exact hq1
    exact (commutatorElement_eq_one_iff_mul_comm.mp hq_com).symm
  rw [centerless_range49_center_eq_bot hL, Subgroup.mem_bot] at hcenter
  have hg0pc : g₀ ∈ CFSG.pCore 2 ↥L := by
    have hmem : g₀ ∈ q.ker := MonoidHom.mem_ker.mpr hcenter
    rwa [show q.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)] at hmem
  exact hker g₀ hg0pc

theorem pow_five_eq_one_of_orderOf {Γ : Type*} [Monoid Γ] {b : Γ}
    (hb : orderOf b = 5) : b ^ 5 = 1 := by
  rw [← hb, pow_orderOf_eq_one]

theorem orderOf_map_eq_five {Γ P : Type*} [Group Γ] [Group P] (φ : Γ →* P) {b : Γ}
    (hb : orderOf b = 5) (hne : φ b ≠ 1) : orderOf (φ b) = 5 := by
  have hdvd : orderOf (φ b) ∣ 5 := by
    simpa [hb] using orderOf_map_dvd φ b
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h5

theorem five_dvd_card_of_isAlt {L' : Subgroup G} (hL : IsAlt (Bar2 L') 5) :
    5 ∣ Nat.card ↥L' := by
  have hcard : Nat.card (Bar2 L') = 60 := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h5index : 5 ∣ (CFSG.pCore 2 ↥L').index := by
    rw [Subgroup.index_eq_card]
    change 5 ∣ Nat.card (Bar2 L')
    rw [hcard]
    norm_num
  calc 5 ∣ Nat.card ↥(CFSG.pCore 2 ↥L') * (CFSG.pCore 2 ↥L').index :=
        dvd_mul_of_dvd_right h5index _
    _ = Nat.card ↥L' := Subgroup.card_mul_index (H := CFSG.pCore 2 ↥L')

theorem exists_order_five_of_isAlt {L' : Subgroup G} (hL : IsAlt (Bar2 L') 5) :
    ∃ b : ↥L', orderOf b = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact exists_prime_orderOf_dvd_card' 5 (five_dvd_card_of_isAlt hL)

theorem eq_one_of_mem_pCore_pow_five {Γ : Type*} [Group Γ] {x : Γ}
    (hx : x ∈ CFSG.pCore 2 Γ) (hx5 : x ^ 5 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := Γ) (p := 2)) ⟨x, hx⟩
  have hx2 : x ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) 5 := (by norm_num : Nat.Coprime 2 5).pow_left k
  have h1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_iff_pow_eq_one.mpr hx2)
      (orderOf_dvd_iff_pow_eq_one.mpr hx5)
  exact orderOf_eq_one_iff.mp h1

theorem zmod5_eq_one_of_pow_eq_one {Γ : Type*} [Monoid Γ] {b : Γ}
    (hb : orderOf b = 5) {n : Multiplicative (ZMod 5)} (h : b ^ n.toAdd.val = 1) :
    n = 1 := by
  have hdvd : 5 ∣ n.toAdd.val := by
    have := orderOf_dvd_iff_pow_eq_one.mpr h
    rwa [hb] at this
  have hval : n.toAdd.val = 0 := by
    have := ZMod.val_lt n.toAdd
    omega
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact (ZMod.val_eq_zero n.toAdd).mp hval

@[expose] def powHom {M : Type*} [Monoid M] (T : M) (hT : T ^ 5 = 1) :
    Multiplicative (ZMod 5) →* M where
  toFun n := T ^ n.toAdd.val
  map_one' := by simp
  map_mul' n m := by
    rw [← pow_add, toAdd_mul]
    refine pow_eq_pow_of_modEq ?_ hT
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ 5

theorem powHom_apply {M : Type*} [Monoid M] (T : M) (hT : T ^ 5 = 1)
    (n : Multiplicative (ZMod 5)) : powHom T hT n = T ^ n.toAdd.val := rfl

theorem powHom_injective {M : Type*} [Group M] {T : M} (hT5 : T ^ 5 = 1)
    (hT : orderOf T = 5) : Function.Injective (powHom T hT5) := by
  intro n m hnm
  have hrel : powHom T hT5 (n * m⁻¹) = 1 := by
    rw [map_mul, hnm, map_inv, mul_inv_cancel]
  have hval : T ^ (n * m⁻¹).toAdd.val = 1 := by
    simpa [powHom_apply] using hrel
  exact mul_inv_eq_one.mp (zmod5_eq_one_of_pow_eq_one hT hval)

@[expose] def mulHom {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (f : M →* P) (g : N →* P) (hcomm : ∀ a b, f a * g b = g b * f a) : M × N →* P where
  toFun x := f x.1 * g x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    calc (f x.1 * f y.1) * (g x.2 * g y.2)
        = f x.1 * (f y.1 * g x.2) * g y.2 := by simp only [mul_assoc]
      _ = f x.1 * (g x.2 * f y.1) * g y.2 := by rw [hcomm y.1 x.2]
      _ = (f x.1 * g x.2) * (f y.1 * g y.2) := by simp only [mul_assoc]

theorem mulHom_apply {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (f : M →* P) (g : N →* P) (hcomm : ∀ a b, f a * g b = g b * f a) (x : M × N) :
    mulHom f g hcomm x = f x.1 * g x.2 := rfl

@[expose] noncomputable def pairRep {M : Type*} [Monoid M] (T0 T1 : M)
    (h0 : T0 ^ 5 = 1) (h1 : T1 ^ 5 = 1) (hcomm : Commute T0 T1) :
    Multiplicative (ZMod 5) × Multiplicative (ZMod 5) →* M :=
  mulHom (powHom T0 h0) (powHom T1 h1) (fun a b => by
    rw [powHom_apply, powHom_apply]
    exact (hcomm.pow_left a.toAdd.val).pow_right b.toAdd.val)

theorem pairRep_apply {M : Type*} [Monoid M] (T0 T1 : M)
    (h0 : T0 ^ 5 = 1) (h1 : T1 ^ 5 = 1) (hcomm : Commute T0 T1)
    (x : Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) :
    pairRep T0 T1 h0 h1 hcomm x = T0 ^ x.1.toAdd.val * T1 ^ x.2.toAdd.val := by
  simp [pairRep, mulHom_apply, powHom_apply]

theorem mulHom_pow_left_injective {M N P : Type*} [Group M] [Group N] [Group P]
    {φ : M →* P} {g : N →* P} (hcomm : ∀ a b, φ a * g b = g b * φ a)
    {b : M} (hb : orderOf b = 5) (hfb : (φ b) ^ 5 = 1)
    (hφ : ∀ u : P, (∀ a : M, Commute u (φ a)) → ∀ n : ℕ, φ (b ^ n) * u = 1 →
      b ^ n = 1)
    (hg : Function.Injective g) :
    Function.Injective
      (mulHom (powHom (φ b) hfb) g (fun a y => by
        simpa [powHom_apply, map_pow] using hcomm (b ^ a.toAdd.val) y)) := by
  intro x y hxy
  have hker : mulHom (powHom (φ b) hfb) g
      (fun a y => by simpa [powHom_apply, map_pow] using hcomm (b ^ a.toAdd.val) y)
      (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hrelExp : (φ b) ^ (x * y⁻¹).1.toAdd.val * g (x * y⁻¹).2 = 1 := by
    simpa [mulHom_apply, powHom_apply] using hker
  have hrel : φ (b ^ (x * y⁻¹).1.toAdd.val) * g (x * y⁻¹).2 = 1 := by
    rw [map_pow]
    exact hrelExp
  have hn : b ^ (x * y⁻¹).1.toAdd.val = 1 :=
    hφ (g (x * y⁻¹).2) (fun a => (hcomm a (x * y⁻¹).2).symm)
      (x * y⁻¹).1.toAdd.val hrel
  have hy : (x * y⁻¹).2 = 1 := by
    apply hg
    have hφk : (φ b) ^ (x * y⁻¹).1.toAdd.val = 1 := by
      rw [← map_pow, hn, map_one]
    rw [hφk, one_mul] at hrelExp
    simpa using hrelExp
  have hx : x * y⁻¹ = 1 := Prod.ext (zmod5_eq_one_of_pow_eq_one hb hn) hy
  exact mul_inv_eq_one.mp hx

theorem pow_factor_eq_one_nat {Γ P : Type*} [Group Γ] [Group P]
    {L' : Subgroup G} (φ : ↥L' →* P) (hL : IsAlt (Bar2 L') 5)
    (hφ : ∃ g : ↥L', φ g ≠ 1)
    (hker : ∀ g : ↥L', g ∈ CFSG.pCore 2 ↥L' → φ g = 1)
    {b : ↥L'} (hb : orderOf b = 5) {u : P}
    (hcomm : ∀ g : ↥L', Commute u (φ g)) {n : ℕ}
    (hrel : φ (b ^ n) * u = 1) : b ^ n = 1 := by
  have hcen := centerless_range49 (φ := φ) hL hker hφ
  have hbn : φ (b ^ n) = u⁻¹ := mul_eq_one_iff_eq_inv.mp hrel
  have hcentral : ∀ g : ↥L', φ (b ^ n) * φ g = φ g * φ (b ^ n) := by
    intro g
    rw [hbn]
    exact (hcomm g).inv_left
  have hpc : b ^ n ∈ CFSG.pCore 2 ↥L' := hcen.1 (b ^ n) (hcen.2 (b ^ n) hcentral)
  exact eq_one_of_mem_pCore_pow_five hpc
    (by rw [← pow_mul, Nat.mul_comm, pow_mul, pow_five_eq_one_of_orderOf hb, one_pow])

theorem ne_one_of_faithful {M P : Type*} [Group M] [Group P] {φ : M →* P} {b : M}
    (hb : orderOf b = 5)
    (hφ : ∀ u : P, (∀ a : M, Commute u (φ a)) → ∀ n : ℕ, φ (b ^ n) * u = 1 →
      b ^ n = 1) : φ b ≠ 1 := by
  intro h
  have h1 : b ^ 1 = 1 := hφ 1 (fun a => Commute.one_left _) 1 (by simpa using h)
  have hb1 : b = 1 := by simpa using h1
  rw [hb1, orderOf_one] at hb
  norm_num at hb

theorem order_five_of_faithful {M P : Type*} [Group M] [Group P] {φ : M →* P} {b : M}
    (hb : orderOf b = 5)
    (hφ : ∀ u : P, (∀ a : M, Commute u (φ a)) → ∀ n : ℕ, φ (b ^ n) * u = 1 →
      b ^ n = 1) :
    orderOf (φ b) = 5 ∧ (φ b) ^ 5 = 1 := by
  have hne : φ b ≠ 1 := ne_one_of_faithful hb hφ
  have hT : orderOf (φ b) = 5 := orderOf_map_eq_five φ hb hne
  exact ⟨hT, pow_five_eq_one_of_orderOf hT⟩

theorem pairRep_injective_of_actions {M N P : Type*} [Group M] [Group N] [Group P]
    (φ : M →* P) (ψ : N →* P) {b : M} {b' : N}
    (hb : orderOf b = 5) (hfb : (φ b) ^ 5 = 1)
    (hfb' : (ψ b') ^ 5 = 1) (hT' : orderOf (ψ b') = 5)
    (hφ : ∀ u : P, (∀ a : M, Commute u (φ a)) → ∀ n : ℕ, φ (b ^ n) * u = 1 →
      b ^ n = 1)
    (hcomm : ∀ a b, φ a * ψ b = ψ b * φ a) :
    Function.Injective (pairRep (φ b) (ψ b') hfb hfb' (hcomm b b')) := by
  have hcommPow : ∀ a : M, ∀ c : Multiplicative (ZMod 5),
      φ a * (powHom (ψ b') hfb') c = (powHom (ψ b') hfb') c * φ a := by
    intro a c
    rw [powHom_apply]
    have hψ : (ψ b') ^ c.toAdd.val = ψ (b' ^ c.toAdd.val) := (map_pow ψ b' c.toAdd.val).symm
    rw [hψ]
    exact hcomm a (b' ^ c.toAdd.val)
  have hinj := mulHom_pow_left_injective (φ := φ) (g := powHom (ψ b') hfb')
    hcommPow hb hfb hφ (powHom_injective hfb' hT')
  intro x y hxy
  exact hinj (by simpa [pairRep, mulHom_apply] using hxy)

theorem zmod5_pow_five (n : Multiplicative (ZMod 5)) : n ^ 5 = 1 := by
  have := pow_card_eq_one' (G := Multiplicative (ZMod 5)) (x := n)
  simpa [Nat.card_zmod] using this

abbrev TwoFive : Type := Multiplicative (ZMod 5) × Multiplicative (ZMod 5)

abbrev ThreeFive : Type := Multiplicative (ZMod 5) × TwoFive

theorem twoFive_card : Nat.card TwoFive = 5 ^ 2 := by
  simp [TwoFive, Nat.card_prod, Nat.card_zmod]

theorem twoFive_pow_five : ∀ b : TwoFive, b ^ 5 = 1 := by
  rintro ⟨m, k⟩
  rw [Prod.pow_def, zmod5_pow_five, zmod5_pow_five]
  rfl

theorem threeFive_card : Nat.card ThreeFive = 5 ^ 3 := by
  simp [ThreeFive, TwoFive, Nat.card_prod, Nat.card_zmod, pow_succ]

theorem threeFive_pow_five : ∀ b : ThreeFive, b ^ 5 = 1 := by
  rintro ⟨m, k, l⟩
  rw [Prod.pow_def, Prod.pow_def, zmod5_pow_five, zmod5_pow_five, zmod5_pow_five]
  rfl

theorem finrank_bound_of_units {B W : Type} [Group B] [Finite B] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (k : ℕ)
    (ρ : B →* (Module.End (ZMod 2) W)ˣ) (hpow : ∀ b : B, b ^ 5 = 1)
    (hcomm : ∀ a b : B, a * b = b * a) (hcard : Nat.card B = 5 ^ k)
    (hinj : Function.Injective ρ) : 4 * k ≤ Module.finrank (ZMod 2) W := by
  let ρ' : Representation (ZMod 2) B W := (Units.coeHom _).comp ρ
  have hinj' : Function.Injective ρ' := by
    show Function.Injective ((Units.coeHom _).comp ρ)
    exact Units.val_injective.comp hinj
  exact five_finrank_bound k ρ' hpow hcomm hcard hinj'

theorem twoFive_finrank_bound {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : TwoFive →* (Module.End (ZMod 2) W)ˣ) (hinj : Function.Injective ρ) :
    8 ≤ Module.finrank (ZMod 2) W := by
  have h := finrank_bound_of_units 2 ρ twoFive_pow_five (fun a b => mul_comm a b)
    twoFive_card hinj
  norm_num at h
  exact h

theorem threeFive_finrank_bound {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : ThreeFive →* (Module.End (ZMod 2) W)ˣ) (hinj : Function.Injective ρ) :
    12 ≤ Module.finrank (ZMod 2) W := by
  have h := finrank_bound_of_units 3 ρ threeFive_pow_five (fun a b => mul_comm a b)
    threeFive_card hinj
  norm_num at h
  exact h

theorem triple_faithful {M P : Type*} [Group M] [Group P]
    (φ : M →* P) {b : M} (hb : orderOf b = 5) (hb5 : (φ b) ^ 5 = 1)
    {T1 T2 : P} (h15 : T1 ^ 5 = 1) (h25 : T2 ^ 5 = 1) (hcommT : Commute T1 T2)
    (hφ : ∀ u : P, (∀ a : M, Commute u (φ a)) → ∀ n : ℕ, φ (b ^ n) * u = 1 →
      b ^ n = 1)
    (h01 : ∀ a : M, Commute (φ a) T1) (h02 : ∀ a : M, Commute (φ a) T2)
    (hPairInj : Function.Injective (pairRep T1 T2 h15 h25 hcommT)) :
    ∃ R : ThreeFive →* P, Function.Injective R := by
  let g := pairRep T1 T2 h15 h25 hcommT
  have hcommR : ∀ a : M, ∀ y : TwoFive, φ a * g y = g y * φ a := by
    intro a y
    rw [show g y = T1 ^ y.1.toAdd.val * T2 ^ y.2.toAdd.val from pairRep_apply _ _ _ _ _ y]
    exact ((h01 a).pow_right y.1.toAdd.val).mul_right
      ((h02 a).pow_right y.2.toAdd.val) |>.eq
  have hPowComm : ∀ a : Multiplicative (ZMod 5), ∀ y : TwoFive,
      (powHom (φ b) hb5) a * g y = g y * (powHom (φ b) hb5) a := by
    intro a y
    rw [powHom_apply]
    have hT : (φ b) ^ a.toAdd.val = φ (b ^ a.toAdd.val) :=
      (map_pow φ b a.toAdd.val).symm
    rw [hT]
    exact hcommR (b ^ a.toAdd.val) y
  refine ⟨mulHom (powHom (φ b) hb5) g hPowComm, ?_⟩
  simpa [ThreeFive, TwoFive, mulHom_apply] using
    (mulHom_pow_left_injective (φ := φ) (g := g) hcommR hb hb5 hφ hPairInj)

noncomputable def restrictUnit {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Submodule K V} (T : (Module.End K V)ˣ)
    (hW : ∀ w : V, w ∈ W → (T : Module.End K V) w ∈ W) : (Module.End K W)ˣ := by
  classical
  let f : Module.End K W := (T : Module.End K V).restrict hW
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply Subtype.ext
    have hTker : LinearMap.ker (T : Module.End K V) = ⊥ :=
      (LinearMap.isUnit_iff_ker_eq_bot (f := (T : Module.End K V))).mp ⟨T, rfl⟩
    apply LinearMap.ker_eq_bot.mp hTker
    have hxy' := congrArg Subtype.val hxy
    simpa [f, LinearMap.restrict_apply] using hxy'
  exact (LinearMap.isUnit_iff_ker_eq_bot (f := f)).mpr hker |>.unit

noncomputable def restrictActionOf {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Submodule K V} {M : Type*} [Monoid M]
    (φ : M →* (Module.End K V)ˣ)
    (hW : ∀ g : M, ∀ w : V, w ∈ W → (φ g : Module.End K V) w ∈ W) :
    M →* (Module.End K W)ˣ where
  toFun g := restrictUnit (φ g) (hW g)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [restrictUnit, LinearMap.restrict_apply]
  map_mul' := by
    intro a b
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [restrictUnit, LinearMap.restrict_apply, map_mul, Module.End.mul_apply]

section Context

variable {H X L Q I : Subgroup G} {x : G} {A : Subgroup G} {a n : G} {N M : Subgroup G}

namespace Ctx49

variable (c : Ctx49 H X L Q I x A a n N M)
variable [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]

@[expose] noncomputable def actionUnitsOn (i : ℕ) :
    ↥(Lc L x i) →* (Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)))ˣ :=
  (chiefRep (p := 2) c.chief.2.1 c.chief.2.2.1).comp (Subgroup.inclusion (c.Lc_H i))

theorem actionUnitsOn_apply (i : ℕ) (g : ↥(Lc L x i)) :
    (actionUnitsOn c i g : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N))) =
      op49 c.chief ⟨(g : G), c.Lc_H i g.2⟩ := rfl

theorem actionUnitsOn_eq_one_of_mem_Q (i : ℕ) (g : ↥(Lc L x i))
    (hg : (g : G) ∈ Q) : actionUnitsOn c i g = 1 := by
  have h : chiefRep (p := 2) c.chief.2.1 c.chief.2.2.1
      (Subgroup.inclusion (c.Lc_H i) g) = 1 := by
    rw [chiefRep_eq_one_iff]
    intro w hw
    have := (Subgroup.commutator_le.mp (chief_q_trivial49 c.setup c.chief c.NQ)) w hw (g : G) hg
    simpa using this
  simpa [actionUnitsOn] using h

theorem actionUnitsOn_pCore (i : ℕ) (g : ↥(Lc L x i))
    (hg : g ∈ CFSG.pCore 2 ↥(Lc L x i)) : actionUnitsOn c i g = 1 := by
  have hgQ : (g : G) ∈ Q := by
    have hmem : g ∈ (Lc L x i ⊓ Q).subgroupOf (Lc L x i) := by
      rw [c.Lc_pCore i]; exact hg
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  exact actionUnitsOn_eq_one_of_mem_Q c i g hgQ

theorem actionUnitsOn_comm {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j)
    (gi : ↥(Lc L x i)) (gj : ↥(Lc L x j)) :
    Commute (actionUnitsOn c i gi) (actionUnitsOn c j gj) := by
  apply Units.ext
  simp only [Units.val_mul]
  have h := c.op_comm hi hj hij (g := Subgroup.inclusion (c.Lc_H i) gi)
    (g' := Subgroup.inclusion (c.Lc_H j) gj) gi.2 gj.2
  simpa [actionUnitsOn, op49] using h

theorem opA_zero_ne_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {A0 A1 A2 X Xi S Si : Module.End (ZMod 2) V} (hW : Wt49 A0 A1 A2 X Xi S Si) :
    A0 ≠ 1 := by
  intro h0
  have h1 : A1 = 1 := by rw [← hW.rot0, h0, mul_one]; exact hW.XiX
  have h2 : A2 = 1 := by rw [← hW.rot1, h1, mul_one]; exact hW.XiX
  exact hW.ne_one (by simp [h0, h1, h2])

theorem opA_ne_one (i : ℕ) (hi : i < 3) : c.opA i ≠ 1 := by
  interval_cases i
  · exact opA_zero_ne_one c.wt
  · exact opA_zero_ne_one c.wt.rotate
  · exact opA_zero_ne_one c.wt.rotate.rotate

@[expose] def aiL (i : ℕ) : ↥(Lc L x i) :=
  ⟨(c.ai i : G), c.ai_mem i⟩

theorem actionUnitsOn_aiL (i : ℕ) :
    actionUnitsOn c i (c.aiL i) = c.opA i := by
  rw [actionUnitsOn_apply]
  rfl

theorem actionUnitsOn_nontrivial (i : ℕ) (hi : i < 3) :
    ∃ g : ↥(Lc L x i), actionUnitsOn c i g ≠ 1 := by
  refine ⟨c.aiL i, ?_⟩
  intro h
  apply c.opA_ne_one i hi
  have h' : (actionUnitsOn c i (c.aiL i) :
      Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N))) = 1 := by
    rw [h]; rfl
  simpa [actionUnitsOn_aiL c i] using h'

theorem actionUnitsOn_faithful (i : ℕ) (hi : i < 3) {b : ↥(Lc L x i)}
    (hb : orderOf b = 5) :
    ∀ u : (Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)))ˣ,
      (∀ a : ↥(Lc L x i), Commute u (actionUnitsOn c i a)) →
      ∀ n : ℕ, actionUnitsOn c i (b ^ n) * u = 1 → b ^ n = 1 := by
  intro u hu n hrel
  exact pow_factor_eq_one_nat (L' := Lc L x i) (Γ := ↥(Lc L x i))
    (P := (Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)))ˣ)
    (φ := actionUnitsOn c i) (c.Lc_alt i) (actionUnitsOn_nontrivial c i hi)
    (actionUnitsOn_pCore c i) hb hu hrel

noncomputable abbrev fixedSpace : Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  LinearMap.range (e2 (c.opA 0))

theorem fixedSpace_invariant {i : ℕ} (hi : i < 3) (h0 : i ≠ 0)
    (g : ↥(Lc L x i)) :
    ∀ w ∈ fixedSpace c, (actionUnitsOn c i g : Module.End (ZMod 2)
      (Additive (N ⧸ M.subgroupOf N))) w ∈ fixedSpace c := by
  intro w hw
  have hcomm : (actionUnitsOn c i g : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N))) *
      c.opA 0 = c.opA 0 * (actionUnitsOn c i g : Module.End (ZMod 2)
        (Additive (N ⧸ M.subgroupOf N))) := by
    change op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) * op49 c.chief (c.ai 0) =
      op49 c.chief (c.ai 0) * op49 c.chief (Subgroup.inclusion (c.Lc_H i) g)
    exact c.op_comm hi (by norm_num) h0 (g := Subgroup.inclusion (c.Lc_H i) g)
      (g' := c.ai 0) g.2 (c.ai_mem 0)
  exact range_e2_invariant_of_comm _ _ hcomm w hw

noncomputable def fixedAction {i : ℕ} (hi : i < 3) (h0 : i ≠ 0) :
    ↥(Lc L x i) →* (Module.End (ZMod 2) ↥(fixedSpace c))ˣ :=
  restrictActionOf (actionUnitsOn c i) (fun g w hw => fixedSpace_invariant c hi h0 g w hw)

theorem fixedAction_apply {i : ℕ} (hi : i < 3) (h0 : i ≠ 0)
    (g : ↥(Lc L x i)) (w : ↥(fixedSpace c)) :
    ((fixedAction c hi h0 g : Module.End (ZMod 2) ↥(fixedSpace c)) w :
        Additive (N ⧸ M.subgroupOf N)) =
      (actionUnitsOn c i g : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N))) w := by
  simp [fixedAction, restrictActionOf, restrictUnit, LinearMap.restrict_apply]

theorem fixedAction_pCore {i : ℕ} (hi : i < 3) (h0 : i ≠ 0)
    (g : ↥(Lc L x i)) (hg : g ∈ CFSG.pCore 2 ↥(Lc L x i)) :
    fixedAction c hi h0 g = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  rw [fixedAction_apply c hi h0 g w]
  have h := actionUnitsOn_pCore c i g hg
  rw [h]
  rfl

theorem fixedAction_comm {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j)
    (h0i : i ≠ 0) (h0j : j ≠ 0) (g : ↥(Lc L x i)) (g' : ↥(Lc L x j)) :
    Commute (fixedAction c hi h0i g) (fixedAction c hj h0j g') := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have hcomm : (actionUnitsOn c i g : Module.End (ZMod 2)
        (Additive (N ⧸ M.subgroupOf N))) *
      (actionUnitsOn c j g' : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N))) =
      (actionUnitsOn c j g' : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N))) *
      (actionUnitsOn c i g : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N))) := by
    change op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) *
      op49 c.chief (Subgroup.inclusion (c.Lc_H j) g') =
      op49 c.chief (Subgroup.inclusion (c.Lc_H j) g') *
      op49 c.chief (Subgroup.inclusion (c.Lc_H i) g)
    exact c.op_comm hi hj hij g.2 g'.2
  have hw := congrArg (fun f : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) =>
    f (w : Additive (N ⧸ M.subgroupOf N))) hcomm
  rw [Module.End.mul_apply, Module.End.mul_apply] at hw
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [fixedAction_apply c hi h0i g
      (((fixedAction c hj h0j g') : Module.End (ZMod 2) ↥(fixedSpace c)) w),
    fixedAction_apply c hj h0j g' w]
  rw [fixedAction_apply c hj h0j g'
      (((fixedAction c hi h0i g) : Module.End (ZMod 2) ↥(fixedSpace c)) w),
    fixedAction_apply c hi h0i g w]
  exact hw

theorem fixedAction_nontrivial {i : ℕ} (hi : i < 3) (h0 : i ≠ 0)
    (h : ∃ w ∈ fixedSpace c, c.opA i w ≠ w) :
    ∃ g : ↥(Lc L x i), fixedAction c hi h0 g ≠ 1 := by
  obtain ⟨w, hw, hwne⟩ := h
  refine ⟨c.aiL i, ?_⟩
  intro h1
  apply hwne
  have h2 : ((fixedAction c hi h0 (c.aiL i) :
      Module.End (ZMod 2) ↥(fixedSpace c)) ⟨w, hw⟩ :
        Additive (N ⧸ M.subgroupOf N)) = w := by
    have h3 : ((fixedAction c hi h0 (c.aiL i) :
        Module.End (ZMod 2) ↥(fixedSpace c)) ⟨w, hw⟩) = ⟨w, hw⟩ := by
      rw [h1]; rfl
    exact congrArg (fun x : ↥(fixedSpace c) => (x : Additive (N ⧸ M.subgroupOf N))) h3
  rw [fixedAction_apply c hi h0 (c.aiL i) ⟨w, hw⟩] at h2
  rw [actionUnitsOn_aiL c i] at h2
  exact h2

theorem fixedAction_faithful {i : ℕ} (hi : i < 3) (h0 : i ≠ 0)
    (h : ∃ w ∈ fixedSpace c, c.opA i w ≠ w) {b : ↥(Lc L x i)}
    (hb : orderOf b = 5) :
    ∀ u : (Module.End (ZMod 2) ↥(fixedSpace c))ˣ,
      (∀ a : ↥(Lc L x i), Commute u (fixedAction c hi h0 a)) →
      ∀ n : ℕ, fixedAction c hi h0 (b ^ n) * u = 1 → b ^ n = 1 := by
  intro u hu n hrel
  exact pow_factor_eq_one_nat (L' := Lc L x i) (Γ := ↥(Lc L x i))
    (P := (Module.End (ZMod 2) ↥(fixedSpace c))ˣ) (φ := fixedAction c hi h0)
    (c.Lc_alt i) (fixedAction_nontrivial c hi h0 h) (fixedAction_pCore c hi h0) hb hu hrel

theorem five_rank_two
    (h1 : ∃ w ∈ LinearMap.range (e2 (c.opA 0)), c.opA 1 w ≠ w)
    (h2 : ∃ w ∈ LinearMap.range (e2 (c.opA 0)), c.opA 2 w ≠ w) :
    8 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (c.opA 0))) := by
  classical
  obtain ⟨b1, hb1⟩ := exists_order_five_of_isAlt (c.Lc_alt 1)
  obtain ⟨b2, hb2⟩ := exists_order_five_of_isAlt (c.Lc_alt 2)
  let φ1 := fixedAction c (i := 1) (by norm_num) (by norm_num)
  let φ2 := fixedAction c (i := 2) (by norm_num) (by norm_num)
  have hφ1 : ∀ u : (Module.End (ZMod 2) ↥(fixedSpace c))ˣ,
      (∀ a : ↥(Lc L x 1), Commute u (φ1 a)) →
      ∀ n : ℕ, φ1 (b1 ^ n) * u = 1 → b1 ^ n = 1 :=
    fixedAction_faithful c (i := 1) (by norm_num) (by norm_num) h1 hb1
  have hφ2 : ∀ u : (Module.End (ZMod 2) ↥(fixedSpace c))ˣ,
      (∀ a : ↥(Lc L x 2), Commute u (φ2 a)) →
      ∀ n : ℕ, φ2 (b2 ^ n) * u = 1 → b2 ^ n = 1 :=
    fixedAction_faithful c (i := 2) (by norm_num) (by norm_num) h2 hb2
  obtain ⟨hT1, h15⟩ := order_five_of_faithful hb1 hφ1
  obtain ⟨hT2, h25⟩ := order_five_of_faithful hb2 hφ2
  have hcommFull : ∀ a : ↥(Lc L x 1), ∀ b : ↥(Lc L x 2),
      φ1 a * φ2 b = φ2 b * φ1 a := by
    intro a b
    exact (fixedAction_comm c (i := 1) (j := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) a b).eq
  let T1 := φ1 b1
  let T2 := φ2 b2
  have hcommT : Commute T1 T2 := hcommFull b1 b2
  have hPairInj : Function.Injective (pairRep T1 T2 h15 h25 hcommT) := by
    simpa [T1, T2] using
      pairRep_injective_of_actions φ1 φ2 hb1 h15 h25 hT2 hφ1 hcommFull
  exact twoFive_finrank_bound (pairRep T1 T2 h15 h25 hcommT) hPairInj

include c in
theorem twelve_le : 12 ≤ Module.finrank (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) := by
  classical
  obtain ⟨b0, hb0⟩ := exists_order_five_of_isAlt (c.Lc_alt 0)
  obtain ⟨b1, hb1⟩ := exists_order_five_of_isAlt (c.Lc_alt 1)
  obtain ⟨b2, hb2⟩ := exists_order_five_of_isAlt (c.Lc_alt 2)
  have hφ0 := actionUnitsOn_faithful c 0 (by norm_num) hb0
  have hφ1 := actionUnitsOn_faithful c 1 (by norm_num) hb1
  have hφ2 := actionUnitsOn_faithful c 2 (by norm_num) hb2
  obtain ⟨hT0, h05⟩ := order_five_of_faithful hb0 hφ0
  obtain ⟨hT1, h15⟩ := order_five_of_faithful hb1 hφ1
  obtain ⟨hT2, h25⟩ := order_five_of_faithful hb2 hφ2
  have hcomm12 : ∀ a : ↥(Lc L x 1), ∀ b : ↥(Lc L x 2),
      actionUnitsOn c 1 a * actionUnitsOn c 2 b =
        actionUnitsOn c 2 b * actionUnitsOn c 1 a := by
    intro a b
    exact (actionUnitsOn_comm c (by norm_num) (by norm_num) (by norm_num) a b).eq
  let T1 := actionUnitsOn c 1 b1
  let T2 := actionUnitsOn c 2 b2
  have hcommT : Commute T1 T2 := hcomm12 b1 b2
  have hPairInj : Function.Injective (pairRep T1 T2 h15 h25 hcommT) := by
    simpa [T1, T2] using pairRep_injective_of_actions (actionUnitsOn c 1)
      (actionUnitsOn c 2) hb1 h15 h25 hT2 hφ1 hcomm12
  have h01 : ∀ a : ↥(Lc L x 0), Commute (actionUnitsOn c 0 a) T1 := by
    intro a
    simpa [T1] using actionUnitsOn_comm c (i := 0) (j := 1) (by norm_num)
      (by norm_num) (by norm_num) a b1
  have h02 : ∀ a : ↥(Lc L x 0), Commute (actionUnitsOn c 0 a) T2 := by
    intro a
    simpa [T2] using actionUnitsOn_comm c (i := 0) (j := 2) (by norm_num)
      (by norm_num) (by norm_num) a b2
  obtain ⟨R, hRInj⟩ := triple_faithful (φ := actionUnitsOn c 0) hb0 h05 h15 h25
    hcommT hφ0 h01 h02 hPairInj
  exact threeFive_finrank_bound R hRInj

end Ctx49

end Context

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
