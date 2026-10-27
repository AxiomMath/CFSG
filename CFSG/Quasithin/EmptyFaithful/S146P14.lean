module

public import CFSG.Quasithin.EmptyFaithful.S146P4
public import CFSG.Quasithin.EmptyFaithful.S146P8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement IsMulCommutative

section Abstract

variable {Γ : Type*} [Group Γ]

theorem comm_inf_fixed_P14 [Finite Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U X Q : Subgroup Γ}
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU2 : ∀ x ∈ U, x ^ 2 = 1)
    (hXU : ∀ g ∈ X, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hQU : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ = u)
    (hXnQ : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hXQ : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ Q) :
    ∀ x ∈ ⁅U, X⁆, (∀ g ∈ X, g * x * g⁻¹ = x) → x = 1 := by
  classical
  obtain ⟨P, hPX, hPodd, hPQ⟩ := exists_pComplement_P7 hp hp2 hXnQ hXQ
  let _ : Fintype P := Fintype.ofFinite P
  have _ : IsMulCommutative U := ⟨⟨fun x y => Subtype.ext (hUc x x.2 y y.2)⟩⟩
  have hconj : ∀ b ∈ P, ∀ k ∈ U, b * k * b⁻¹ ∈ U := fun b hb k hk => hXU b (hPX hb) k hk
  let f : P → U → U := fun b k => ⟨(b : Γ) * k * (b : Γ)⁻¹, hconj b b.2 k k.2⟩
  have hfmul : ∀ b k₁ k₂, f b (k₁ * k₂) = f b k₁ * f b k₂ := fun b k₁ k₂ =>
    Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)
  let σ : U →* U := MonoidHom.mk' (fun k => ∏ b : P, f b k) fun k₁ k₂ => by
    show ∏ b, f b (k₁ * k₂) = (∏ b, f b k₁) * ∏ b, f b k₂
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => hfmul b k₁ k₂
  have hσ : ∀ k, σ k = ∏ b : P, f b k := fun k => rfl
  have hfcoe : ∀ b k, ((f b k : U) : Γ) = (b : Γ) * k * (b : Γ)⁻¹ := fun b k => rfl
  have hff : ∀ a b k, f a (f b k) = f (a * b) k := fun a b k =>
    Subtype.ext (by simp only [hfcoe, Subgroup.coe_mul, mul_inv_rev]; group)
  have hσconj : ∀ (a : P) (k : U), σ (f a k) = σ k := by
    intro a k
    rw [hσ, hσ]
    exact Fintype.prod_equiv (Equiv.mulRight a) _ _ fun b => by simp only [Equiv.coe_mulRight, hff]
  have hodd2 : ∀ x : U, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hU2 x x.2)
  have hpow : ∀ x : U, x ^ Fintype.card P = x := by
    intro x
    obtain ⟨m, hm⟩ := hPodd
    rw [← Nat.card_eq_fintype_card, hm, pow_succ, pow_mul, hodd2, one_pow, one_mul]
  have hσid : ∀ x : U, (∀ a : P, f a x = x) → σ x = x := by
    intro x hx
    rw [hσ]
    simp only [hx, Finset.prod_const, Finset.card_univ]
    exact hpow x
  have hker : ⁅U, X⁆ ≤ σ.ker.map U.subtype := by
    refine Subgroup.commutator_le.mpr fun u hu g hg => ?_
    obtain ⟨a, ha, q, hq, rfl⟩ := hPQ g hg
    have hgu : (a * q) * u * (a * q)⁻¹ ∈ U := hXU _ hg u hu
    refine ⟨(⟨u, hu⟩ : U) * (⟨(a * q) * u * (a * q)⁻¹, hgu⟩ : U)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
      have e : (⟨(a * q) * u * (a * q)⁻¹, hgu⟩ : U) = f ⟨a, ha⟩ ⟨u, hu⟩ := by
        apply Subtype.ext
        show (a * q) * u * (a * q)⁻¹ = a * u * a⁻¹
        calc (a * q) * u * (a * q)⁻¹ = a * (q * u * q⁻¹) * a⁻¹ := by group
          _ = a * u * a⁻¹ := by rw [hQU q hq u hu]
      rw [e, hσconj]
    · show u * ((a * q) * u * (a * q)⁻¹)⁻¹ = ⁅u, a * q⁆
      rw [commutatorElement_def]
      group
  intro x hxE hxX
  obtain ⟨y, hy, rfl⟩ := hker hxE
  have hyfix : ∀ a : P, f a y = y := fun a => Subtype.ext (hxX a (hPX a.2))
  have h1 : σ y = y := hσid y hyfix
  have h2 : σ y = 1 := MonoidHom.mem_ker.mp hy
  rw [h2] at h1
  rw [← h1]
  rfl

end Abstract

section Quotient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_normalizes_P14 {U X : Subgroup G} (hXU : ∀ g ∈ X, ∀ u ∈ U, g * u * g⁻¹ ∈ U) :
    ⁅U, X⁆ ≤ U := by
  refine Subgroup.commutator_le.mpr fun u hu g hg => ?_
  have e : ⁅u, g⁆ = u * (g * u⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact U.mul_mem hu (hXU g hg u⁻¹ (U.inv_mem hu))

theorem comm_inf_fixed_mod_central_P14 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₁ Z U X Q : Subgroup G}
    (hZ : ∀ x ∈ G₁, ∀ b ∈ Z, x * b = b * x)
    (hUG : U ≤ G₁) (hXG : X ≤ G₁)
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU2 : ∀ x ∈ U, x ^ 2 = 1)
    (hXU : ∀ g ∈ X, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hQU : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ Z)
    (hXnQ : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hXQ : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ Q) :
    ∀ k ∈ ⁅U, X⁆, (∀ g ∈ X, g * k * g⁻¹ * k⁻¹ ∈ Z) → k ∈ Z := by
  classical
  have hZn : (Z.subgroupOf G₁).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h1 : (g : G) * n = n * g := hZ g g.2 n hn
      have : ((g * n * g⁻¹ : G₁) : G) = n := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [h1]
        group
      rw [this]
      exact hn⟩
  let π : G₁ →* G₁ ⧸ Z.subgroupOf G₁ := QuotientGroup.mk' _
  let img : Subgroup G → Subgroup (G₁ ⧸ Z.subgroupOf G₁) := fun S => (S.subgroupOf G₁).map π
  have mem_img : ∀ (S : Subgroup G) (y : G₁ ⧸ Z.subgroupOf G₁),
      y ∈ img S ↔ ∃ x : G₁, (x : G) ∈ S ∧ π x = y := by
    intro S y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hπ1 : ∀ x : G₁, π x = 1 ↔ (x : G) ∈ Z := fun x =>
    (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
  have hkey := comm_inf_fixed_P14 (Γ := G₁ ⧸ Z.subgroupOf G₁) hp hp2 (U := img U) (X := img X)
    (Q := img Q)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img U a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img U b).mp hb
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (hUc x hx y hy)))
    (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := (mem_img U a).mp ha
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hU2 x hx)
      rw [this, map_one])
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img X a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img U b).mp hb
      refine (mem_img U _).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
      simpa using hXU x hx y hy)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img Q a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img U b).mp hb
      have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := (hπ1 _).mpr (by simpa using hQU x hx y hy)
      have h2 : π x * π y * (π x)⁻¹ * (π y)⁻¹ = 1 := by simpa [map_mul, map_inv] using h1
      exact mul_inv_eq_one.mp h2)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img X a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img Q b).mp hb
      refine (mem_img Q _).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
      simpa using hXnQ x hx y hy)
    (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := (mem_img X a).mp ha
      obtain ⟨k, hk⟩ := hXQ x hx
      exact ⟨k, (mem_img Q _).mpr ⟨x ^ p ^ k, by simpa using hk, by simp⟩⟩)
  intro k hkE hk
  have hkG : k ∈ G₁ := by
    have hle : ⁅U, X⁆ ≤ G₁ := (commutator_le_of_normalizes_P14 hXU).trans hUG
    exact hle hkE
  let k₁ : G₁ := ⟨k, hkG⟩
  have hkE' : k₁ ∈ ⁅U.subgroupOf G₁, X.subgroupOf G₁⁆ := by
    have h1 : ⁅U, X⁆ = (⁅U.subgroupOf G₁, X.subgroupOf G₁⁆).map G₁.subtype := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hUG, inf_of_le_left hXG]
    rw [h1] at hkE
    obtain ⟨k₂, hk₂, hk₂k⟩ := Subgroup.mem_map.mp hkE
    have : k₂ = k₁ := Subtype.ext hk₂k
    rwa [this] at hk₂
  have hπk : π k₁ ∈ ⁅img U, img X⁆ := by
    have := Subgroup.mem_map_of_mem π hkE'
    rwa [Subgroup.map_commutator] at this
  have hfix : ∀ g ∈ img X, g * π k₁ * g⁻¹ = π k₁ := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := (mem_img X g).mp hg
    have h1 : π (x * k₁ * x⁻¹ * k₁⁻¹) = 1 := (hπ1 _).mpr (by simpa [k₁] using hk x hx)
    have h2 : π x * π k₁ * (π x)⁻¹ * (π k₁)⁻¹ = 1 := by simpa [map_mul, map_inv] using h1
    exact mul_inv_eq_one.mp h2
  have h1 : π k₁ = 1 := hkey (π k₁) hπk hfix
  simpa [k₁] using (hπ1 k₁).mp h1

end Quotient

section Dihedral

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.orderOf_dvd_of_odd_P14 (hp : p.Prime)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H₁) (hodd : Odd (orderOf x)) :
    orderOf x ∣ p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  let x' : ↥H₁ := ⟨x, hx⟩
  let y : DihedralGroup p := e (QuotientGroup.mk x')
  have hox : orderOf x' = orderOf x := (Subgroup.orderOf_coe x').symm
  have hyx : orderOf y ∣ orderOf x := by
    have h1 : orderOf y ∣ orderOf (QuotientGroup.mk x' : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) :=
      orderOf_map_dvd e.toMonoidHom _
    have h2 : orderOf (QuotientGroup.mk x' : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) ∣ orderOf x' :=
      orderOf_map_dvd (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁)) x'
    exact h1.trans (h2.trans hox.dvd)
  have hyodd : Odd (orderOf y) := hodd.of_dvd_nat hyx
  have hyp : orderOf y ∣ p := by
    cases hy : y with
    | r i =>
      rw [DihedralGroup.orderOf_r]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left p i.val)
    | sr i =>
      rw [hy, DihedralGroup.orderOf_sr] at hyodd
      exact absurd hyodd (by decide)
  set m := orderOf y with hm
  have hm1 : y ^ m = 1 := pow_orderOf_eq_one y
  have hxm : x' ^ m ∈ (pCoreOf 2 H).subgroupOf H₁ := by
    have h1 : e (QuotientGroup.mk (x' ^ m)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow]
      exact hm1
    have h2 : (QuotientGroup.mk (x' ^ m) : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) = 1 :=
      e.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hxm' : x ^ m ∈ pCoreOf 2 H := by
    have := Subgroup.mem_subgroupOf.mp hxm
    simpa using this
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  obtain ⟨k, hk⟩ := hQ2 ⟨x ^ m, hxm'⟩
  have hk' : (x ^ m) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd1 : orderOf (x ^ m) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd2 : orderOf (x ^ m) ∣ orderOf x := orderOf_pow_dvd m
  have hodd2 : Odd (orderOf (x ^ m)) := hodd.of_dvd_nat hd2
  have hcop : Nat.Coprime (orderOf (x ^ m)) (2 ^ k) := (Odd.coprime_two_right hodd2).pow_right k
  have hone : orderOf (x ^ m) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
  have hxm1 : x ^ m = 1 := orderOf_eq_one_iff.mp hone
  exact (orderOf_dvd_of_pow_eq_one hxm1).trans hyp

theorem IsDecP.exists_order_p_P14 (hp : p.Prime) (hp2 : p ≠ 2) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∃ x ∈ oTwoUpper H₁, orderOf x = p := by
  obtain ⟨z, hzH, hzQ, hzodd⟩ := h.exists_odd_notin hp hp2
  have hdvd := h.orderOf_dvd_of_odd_P14 hp hzH hzodd
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exfalso
    apply hzQ
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    exact (pCoreOf 2 H).one_mem
  · exact ⟨z, mem_oTwoUpper_of_odd hzH hzodd, h1⟩

omit [Finite G] in
theorem IsDecP.pow_mem_of_mem_oTwoUpper_P14 (hp : p.Prime) (h : IsDecP T M H p H₀ H₁ H₂ t) {x : G}
    (hx : x ∈ oTwoUpper H₁) : x ^ p ∈ pCoreOf 2 H := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  let φ : ↥H₁ →* DihedralGroup p :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁))
  have hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H := by
    intro y
    show e (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have key : ∃ hxH : x ∈ H₁, ∃ i : ZMod p, φ ⟨x, hxH⟩ = DihedralGroup.r i := by
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyH, hyodd⟩ := hy
      refine ⟨hyH, ?_⟩
      cases hφ : φ ⟨y, hyH⟩ with
      | r i => exact ⟨i, rfl⟩
      | sr i =>
        exfalso
        have hdvd : orderOf (φ ⟨y, hyH⟩) ∣ orderOf y := by
          have := orderOf_map_dvd φ (⟨y, hyH⟩ : ↥H₁)
          rwa [← Subgroup.orderOf_coe] at this
        rw [hφ, DihedralGroup.orderOf_sr] at hdvd
        have := hyodd.of_dvd_nat hdvd
        exact absurd this (by decide)
    | one =>
      refine ⟨H₁.one_mem, 0, ?_⟩
      have : (⟨1, H₁.one_mem⟩ : ↥H₁) = 1 := rfl
      rw [this, map_one]
      exact DihedralGroup.r_zero.symm
    | mul y z _ _ ihy ihz =>
      obtain ⟨hyH, i, hi⟩ := ihy
      obtain ⟨hzH, j, hj⟩ := ihz
      refine ⟨H₁.mul_mem hyH hzH, i + j, ?_⟩
      have : (⟨y * z, H₁.mul_mem hyH hzH⟩ : ↥H₁) = ⟨y, hyH⟩ * ⟨z, hzH⟩ := rfl
      rw [this, map_mul, hi, hj, DihedralGroup.r_mul_r]
    | inv y _ ih =>
      obtain ⟨hyH, i, hi⟩ := ih
      refine ⟨H₁.inv_mem hyH, -i, ?_⟩
      have : (⟨y⁻¹, H₁.inv_mem hyH⟩ : ↥H₁) = (⟨y, hyH⟩ : ↥H₁)⁻¹ := rfl
      rw [this, map_inv, hi, DihedralGroup.inv_r]
  obtain ⟨hxH, i, hi⟩ := key
  have hpow : φ (⟨x, hxH⟩ ^ p) = 1 := by
    rw [map_pow, hi]
    have h1 : orderOf (DihedralGroup.r i : DihedralGroup p) ∣ p := by
      rw [DihedralGroup.orderOf_r]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left p i.val)
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have := (hker _).mp hpow
  simpa using this

end Dihedral

section Generation

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.le_sup_oTwoUpper_P14 (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₁ ≤ oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁) := by
  obtain ⟨x₀, hx₀X, hx₀ord⟩ := h.exists_order_p_P14 hred.prime hred.odd
  obtain ⟨-, hQS, hidx⟩ := h.isSylowTwoOf_inf_H₁ S hred
  have hW : oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁) ≤ H₁ := sup_le (oTwoUpper_le H₁) inf_le_right
  have hcardS : Nat.card ↥((T ⊓ H₀) ⊓ H₁) = 2 * Nat.card (pCoreOf 2 H) := by
    have hmul := Subgroup.relIndex_mul_card (pCoreOf 2 H) ((T ⊓ H₀) ⊓ H₁)
    rw [inf_eq_left.mpr hQS, hidx] at hmul
    exact hmul.symm
  have hcardH₁ : Nat.card H₁ = 2 * p * Nat.card (pCoreOf 2 H) := h.card_H₁_gen hred.prime.ne_zero
  have hpW : p ∣ Nat.card ↥(oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁)) := by
    have := Subgroup.orderOf_dvd_natCard (oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁))
      (Subgroup.mem_sup_left hx₀X)
    rwa [hx₀ord] at this
  have hSW : Nat.card ↥((T ⊓ H₀) ⊓ H₁) ∣ Nat.card ↥(oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁)) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hcop : Nat.Coprime p (Nat.card ↥((T ⊓ H₀) ⊓ H₁)) := by
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
    rw [hcardS, hk]
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hred.prime Nat.prime_two).mpr hred.odd
    have : (2 : ℕ) * 2 ^ k = 2 ^ (k + 1) := by ring
    rw [this]
    exact h2.pow_right _
  have hdiv := hcop.mul_dvd_of_dvd_of_dvd hpW hSW
  have hle : Nat.card H₁ ≤ Nat.card ↥(oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁)) := by
    have hpos : 0 < Nat.card ↥(oTwoUpper H₁ ⊔ ((T ⊓ H₀) ⊓ H₁)) := Nat.card_pos
    have := Nat.le_of_dvd hpos hdiv
    calc Nat.card H₁ = p * Nat.card ↥((T ⊓ H₀) ⊓ H₁) := by rw [hcardH₁, hcardS]; ring
      _ ≤ _ := this
  have heq := Subgroup.eq_of_le_of_card_ge hW hle
  exact le_of_eq heq.symm

end Generation

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_commutator_P14 {U X : Subgroup G} {g : G}
    (hU : g ∈ Subgroup.normalizer (U : Set G)) (hX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((⁅U, X⁆ : Subgroup G) : Set G) := by
  have h1 : conjSub g ⁅U, X⁆ = ⁅U, X⁆ := by
    rw [show conjSub g ⁅U, X⁆ = ⁅conjSub g U, conjSub g X⁆ from Subgroup.map_commutator _ _ _,
      conjSub_eq_of_mem_normalizer hU, conjSub_eq_of_mem_normalizer hX]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h1

theorem input14617Mod_proved : Input14617Mod := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t hdec u hu huZ
  by_contra hcon
  push Not at hcon
  have hdecP : IsDecP T M H p H₀ H₁ H₂ t := hdec.toIsDecP hred
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₀H : H₀ ≤ H := hdec.le
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUG : conjClosure (VZ T M) H ≤ mcOf T := fun x hx => S.mem_mcOf_of_mem_conjClosure hH hx
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H := hZV.trans hVU
  have hZc : ∀ x ∈ mcOf T, ∀ b ∈ quasithinOmegaOneCenter T, x * b = b * x :=
    fun x hx b hb => S146T.comm_Z hx hb
  have hNZ : ∀ x ∈ mcOf T, x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    fun x hx => by rw [S.normalizer_Z]; exact hx
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  have hQU := pCoreOf_fixes_U_mod_Z_P8 S hred
  have hUc : ∀ x ∈ conjClosure (VZ T M) H, ∀ y ∈ conjClosure (VZ T M) H, x * y = y * x :=
    fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hU2 : ∀ x ∈ conjClosure (VZ T M) H, x ^ 2 = 1 := fun x hx => isElemAbelian_pow_eq_one hUab hx
  have hXH₁ : oTwoUpper H₁ ≤ H₁ := oTwoUpper_le H₁
  have hXG : oTwoUpper H₁ ≤ mcOf T := hXH₁.trans (hH₁H.trans hHG)
  have hXU : ∀ g ∈ oTwoUpper H₁, ∀ w ∈ conjClosure (VZ T M) H,
      g * w * g⁻¹ ∈ conjClosure (VZ T M) H := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHU (hH₁H (hXH₁ hg))) w).mp hw
  have hXnQ : ∀ g ∈ oTwoUpper H₁, ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ ∈ pCoreOf 2 H :=
    fun g hg q hq => hQn g (hH₁H (hXH₁ hg)) q hq
  have hXQ : ∀ x ∈ oTwoUpper H₁, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H := fun x hx =>
    ⟨1, by simpa using hdecP.pow_mem_of_mem_oTwoUpper_P14 hred.prime hx⟩
  have hS₁H₁ : ((T ⊓ H₀) ⊓ H₁) ≤ H₁ := inf_le_right
  have hS₁T : ((T ⊓ H₀) ⊓ H₁) ≤ T := inf_le_left.trans inf_le_left
  have hS₁G : ((T ⊓ H₀) ⊓ H₁) ≤ mcOf T := (hS₁T.trans hTH).trans hHG
  have hS₁U : ∀ τ ∈ (T ⊓ H₀) ⊓ H₁, ∀ w ∈ conjClosure (VZ T M) H,
      τ * w * τ⁻¹ ∈ conjClosure (VZ T M) H := fun τ hτ w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHU (hTH (hS₁T hτ))) w).mp hw
  have hS₁X : ∀ τ ∈ (T ⊓ H₀) ⊓ H₁, ∀ g ∈ oTwoUpper H₁, τ * g * τ⁻¹ ∈ oTwoUpper H₁ :=
    fun τ hτ g hg => conj_mem_oTwoUpper (Subgroup.le_normalizer (hS₁H₁ hτ)) hg
  have hZc2 : Nat.card (quasithinOmegaOneCenter T) = 2 := S.card_Z
  have hVc4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hrel : (quasithinOmegaOneCenter T).relIndex (VZ T M) = 2 := by
    have e := Subgroup.relIndex_mul_card (H := quasithinOmegaOneCenter T) (K := VZ T M)
    rw [inf_eq_left.mpr hZV, hZc2, hVc4] at e
    omega
  have hne : ¬ VZ T M ≤ quasithinOmegaOneCenter T := fun hle => by
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨v, hvV, hvZ⟩ := Set.not_subset.mp fun hs => hne (SetLike.coe_subset_coe.mp hs)
  obtain ⟨kv, hkvE, cv, hcvU, hcv, hvkc⟩ := decomp_mod_central_P7 (G₁ := mcOf T)
    (Z := quasithinOmegaOneCenter T) (U := conjClosure (VZ T M) H) (X := oTwoUpper H₁)
    (Q := pCoreOf 2 H) (T := (T ⊓ H₀) ⊓ H₁) hred.prime hred.odd hZc hUG hXG hS₁G hUc hU2 hXU
    hS₁U hS₁X hQU hXnQ hXQ (hVU hvV)
    (fun τ hτ => T_fixes_V_mod_Z_P8 S τ (hS₁T hτ) v hvV)
  have hH₁le := hdecP.le_sup_oTwoUpper_P14 S hred
  have hcvC : cv ∈ centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ := by
    refine ⟨hcvU, hNZ cv (hUG hcvU), fun y hy => ?_⟩
    have h1 := (quasithinOmegaOneCenter T).inv_mem (hcv y (hH₁le hy))
    have e : (y * cv * y⁻¹ * cv⁻¹)⁻¹ = cv * y * cv⁻¹ * y⁻¹ := by group
    rwa [e] at h1
  have hKU : ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ≤ conjClosure (VZ T M) H :=
    commutator_le_of_normalizes_P14 hXU
  have hZC : quasithinOmegaOneCenter T ≤
      centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ := by
    intro z hz
    refine ⟨hZU hz, hNZ z (hUG (hZU hz)), fun y hy => ?_⟩
    have hyG : y ∈ mcOf T := (hH₁H.trans hHG) hy
    have e : z * y * z⁻¹ * y⁻¹ = 1 := by
      rw [(hZc y hyG z hz).symm]
      group
    rw [e]
    exact (quasithinOmegaOneCenter T).one_mem
  set L : Subgroup G := ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔
    centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ with hLdef
  have hZL : quasithinOmegaOneCenter T ≤ L := hZC.trans le_sup_right
  have hvL : v ∈ L := by
    have hz : v * (kv * cv)⁻¹ ∈ L := hZL hvkc
    have hk : kv ∈ L := Subgroup.mem_sup_left hkvE
    have hc : cv ∈ L := Subgroup.mem_sup_right hcvC
    have e : v = (v * (kv * cv)⁻¹) * kv * cv := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hz hk) hc
  have hH₀X : ∀ h ∈ H₀, h ∈ Subgroup.normalizer (oTwoUpper H₁ : Set G) := fun h hh =>
    normalizer_le_normalizer_oTwoUpper_P (hdecP.H₀_le_normalizer_H₁ hh)
  have hH₀U : ∀ h ∈ H₀, h ∈ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := fun h hh =>
    hHU (hH₀H hh)
  have hH₀N : ∀ h ∈ H₀, h ∈ Subgroup.normalizer (L : Set G) := by
    intro h hh
    refine mem_normalizer_sup_P (mem_normalizer_commutator_P14 (hH₀U h hh) (hH₀X h hh)) ?_
    exact le_normalizer_centralizerMod (H := H₀) (fun x hx => hNZ x (hH₀H hx |> hHG))
      (fun x hx => hH₀U x hx) (fun x hx => hdecP.H₀_le_normalizer_H₁ hx) hh
  have hconjv : ∀ h ∈ H, h * v * h⁻¹ ∈ L := by
    intro h hh
    have hTN : T ≤ Subgroup.normalizer (H₀ : Set G) := fun x hx => hdecP.normal (hTH hx)
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right T H₀ hTN
    have hhinv : h⁻¹ ∈ (↑(T ⊔ H₀) : Set G) := by
      rw [sup_comm, ← hdecP.eq]
      exact H.inv_mem hh
    rw [hmul] at hhinv
    obtain ⟨τ, hτ, h₀, hh₀, hτh₀⟩ := Set.mem_mul.mp hhinv
    have hhe : h = h₀⁻¹ * τ⁻¹ := by
      have : h = (h⁻¹)⁻¹ := by simp
      rw [this, ← hτh₀]
      group
    have hzv : τ⁻¹ * v * τ⁻¹⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T :=
      T_fixes_V_mod_Z_P8 S τ⁻¹ (T.inv_mem hτ) v hvV
    set z := τ⁻¹ * v * τ⁻¹⁻¹ * v⁻¹ with hz
    have hτv : τ⁻¹ * v * τ⁻¹⁻¹ = z * v := by rw [hz]; group
    have hH₀' : h₀⁻¹ ∈ H₀ := H₀.inv_mem hh₀
    have hconjL : h₀⁻¹ * v * h₀⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hH₀N h₀⁻¹ hH₀') v).mp hvL
    have hzcomm : h₀⁻¹ * z = z * h₀⁻¹ := hZc _ (hH₀H hH₀' |> hHG) z hzv
    have e : h * v * h⁻¹ = z * (h₀⁻¹ * v * h₀⁻¹⁻¹) := by
      calc h * v * h⁻¹ = h₀⁻¹ * (τ⁻¹ * v * τ⁻¹⁻¹) * h₀⁻¹⁻¹ := by rw [hhe]; group
        _ = h₀⁻¹ * (z * v) * h₀⁻¹⁻¹ := by rw [hτv]
        _ = (h₀⁻¹ * z) * v * h₀⁻¹⁻¹ := by group
        _ = (z * h₀⁻¹) * v * h₀⁻¹⁻¹ := by rw [hzcomm]
        _ = z * (h₀⁻¹ * v * h₀⁻¹⁻¹) := by group
    rw [e]
    exact L.mul_mem (hZL hzv) hconjL
  have hUL : conjClosure (VZ T M) H ≤ L := by
    refine conjClosure_le fun h hh y hy => ?_
    by_cases hyZ : y ∈ quasithinOmegaOneCenter T
    · have e : h * y * h⁻¹ = y := by
        calc h * y * h⁻¹ = (y * h) * h⁻¹ := by rw [hZc h (hHG hh) y hyZ]
          _ = y := by group
      rw [e]
      exact hZL hyZ
    · have hyv : y * v⁻¹ ∈ quasithinOmegaOneCenter T :=
        mul_inv_mem_of_relIndex_two hrel hy hvV hyZ hvZ
      have hzc : h * (y * v⁻¹) * h⁻¹ = y * v⁻¹ := by
        calc h * (y * v⁻¹) * h⁻¹ = ((y * v⁻¹) * h) * h⁻¹ := by rw [hZc h (hHG hh) _ hyv]
          _ = y * v⁻¹ := by group
      have e : h * y * h⁻¹ = (y * v⁻¹) * (h * v * h⁻¹) := by
        calc h * y * h⁻¹ = (h * (y * v⁻¹) * h⁻¹) * (h * v * h⁻¹) := by group
          _ = (y * v⁻¹) * (h * v * h⁻¹) := by rw [hzc]
      rw [e]
      exact L.mul_mem (hZL hyv) (hconjv h hh)
  have hcomm : ⁅conjClosure (VZ T M) H, H₁⁆ ≤
      ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔ quasithinOmegaOneCenter T := by
    refine Subgroup.commutator_le.mpr fun w hw y hy => ?_
    have hnorm : ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ≤ Subgroup.normalizer
        ((centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ : Subgroup G) :
          Set G) := by
      refine S146A.le_normalizer_of_forall_conj_mem fun k hk c hc => ?_
      have hkU := hKU hk
      have hcU : c ∈ conjClosure (VZ T M) H := hc.1
      have e : k * c * k⁻¹ = c := by
        calc k * c * k⁻¹ = (c * k) * k⁻¹ := by rw [hUc k hkU c hcU]
          _ = c := by group
      rw [e]
      exact hc
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right
      ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆
      (centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁) hnorm
    have hwL : w ∈ (↑L : Set G) := hUL hw
    rw [hLdef, hmul] at hwL
    obtain ⟨k, hk, c, hc, hkc⟩ := Set.mem_mul.mp hwL
    have hyH : y ∈ H := hH₁H hy
    have hczy : c * y * c⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T := hc.2.2 y hy
    have hkyk : y * k⁻¹ * y⁻¹ ∈ ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ :=
      (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator_P14 (hHU hyH) (le_normalizer_oTwoUpper H₁ hy)) k⁻¹).mp
        (Subgroup.inv_mem _ hk)
    have e : ⁅w, y⁆ = k * (c * y * c⁻¹ * y⁻¹) * (y * k⁻¹ * y⁻¹) := by
      rw [← hkc, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right hczy)) (Subgroup.mem_sup_left hkyk)
  have hu' : u ∈ ⁅conjClosure (VZ T M) H, H₁⁆ ⊔ quasithinOmegaOneCenter T := hu
  have hule : u ∈ ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔ quasithinOmegaOneCenter T :=
    (sup_le hcomm le_sup_right) hu'
  have hnormZ : ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    fun k hk => hNZ k (hUG (hKU hk))
  have hmulZ := Subgroup.coe_mul_of_left_le_normalizer_right
    ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ (quasithinOmegaOneCenter T) hnormZ
  have hule' : u ∈ (↑(⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔ quasithinOmegaOneCenter T) :
      Set G) := hule
  rw [hmulZ] at hule'
  obtain ⟨k, hk, z, hz, hkz⟩ := Set.mem_mul.mp hule'
  have hfix : ∀ g ∈ oTwoUpper H₁, g * k * g⁻¹ * k⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro g hg
    have h1 := hcon g hg
    have hgz : Commute g z := hZc g (hXG hg) z hz
    have hgz' : z * g⁻¹ = g⁻¹ * z := hgz.inv_left.symm.eq
    have e : g * u * g⁻¹ * u⁻¹ = g * k * g⁻¹ * k⁻¹ := by
      rw [← hkz]
      calc g * (k * z) * g⁻¹ * (k * z)⁻¹ = g * k * (z * g⁻¹) * z⁻¹ * k⁻¹ := by group
        _ = g * k * (g⁻¹ * z) * z⁻¹ * k⁻¹ := by rw [hgz']
        _ = g * k * g⁻¹ * k⁻¹ := by group
    rw [e] at h1
    exact h1
  have hkZ : k ∈ quasithinOmegaOneCenter T :=
    comm_inf_fixed_mod_central_P14 hred.prime hred.odd (G₁ := mcOf T)
      (Z := quasithinOmegaOneCenter T) (U := conjClosure (VZ T M) H) (X := oTwoUpper H₁)
      (Q := pCoreOf 2 H) hZc hUG hXG hUc hU2 hXU hQU hXnQ hXQ k hk hfix
  apply huZ
  rw [← hkz]
  exact (quasithinOmegaOneCenter T).mul_mem hkZ hz

end Main

end CFSG.Quasithin
