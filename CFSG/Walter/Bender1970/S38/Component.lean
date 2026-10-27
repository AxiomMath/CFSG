module

public import CFSG.Walter.Bender1970.S38.Types
public import CFSG.Walter.Bender1970.S2.Components
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

section CentralQuotient

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem eq_one_of_mem_center_of_pow (hZ : Odd (Nat.card (Subgroup.center M))) {x : M}
    (hx : x ∈ Subgroup.center M) {m : ℕ} (hxm : x ^ 2 ^ m = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : Subgroup.center M) ∣ 2 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hxm)
  have h2 : orderOf (⟨x, hx⟩ : Subgroup.center M) ∣ Nat.card (Subgroup.center M) :=
    orderOf_dvd_natCard _
  have h3 : Nat.Coprime (2 ^ m) (Nat.card (Subgroup.center M)) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hZ)
  have h4 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  have h5 : (⟨x, hx⟩ : Subgroup.center M) = 1 := orderOf_eq_one_iff.mp h4
  exact congrArg Subtype.val h5

theorem exists_pow_eq_one_of_isPGroup {P : Subgroup M} (hP : IsPGroup 2 P) :
    ∃ k : ℕ, ∀ x ∈ P, x ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  refine ⟨k, fun x hx => ?_⟩
  have h := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
  rw [hk] at h
  simpa using congrArg Subtype.val h

variable (hZ : Odd (Nat.card (Subgroup.center M)))
include hZ

theorem eq_of_mk_eq_of_isPGroup {P : Subgroup M} (hP : IsPGroup 2 P) {x y : M} (hx : x ∈ P)
    (hy : y ∈ P) (h : (x : M ⧸ Subgroup.center M) = y) : x = y := by
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hP
  have h1 : x⁻¹ * y ∈ Subgroup.center M := QuotientGroup.eq.mp h
  have h2 := eq_one_of_mem_center_of_pow hZ h1 (hk _ (P.mul_mem (P.inv_mem hx) hy))
  rw [inv_mul_eq_one] at h2
  exact h2

theorem conj_mem_of_mk_mem {P : Subgroup M} (hP : IsPGroup 2 P) {n : M}
    (hn : ∀ v ∈ P, ((n * v * n⁻¹ : M) : M ⧸ Subgroup.center M) ∈
      P.map (QuotientGroup.mk' (Subgroup.center M))) {v : M} (hv : v ∈ P) : n * v * n⁻¹ ∈ P := by
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hP
  obtain ⟨v', hv', hv'eq⟩ := hn v hv
  set z := v'⁻¹ * (n * v * n⁻¹) with hz
  have hzZ : z ∈ Subgroup.center M := QuotientGroup.eq.mp hv'eq
  have hcomm : Commute v'⁻¹ (n * v * n⁻¹) := by
    have h1 : n * v * n⁻¹ = v' * z := by rw [hz, mul_inv_cancel_left]
    rw [h1]
    exact (Commute.inv_left (Commute.refl v')).mul_right
      ((Subgroup.mem_center_iff.mp hzZ v'⁻¹))
  have hzk : z ^ 2 ^ k = 1 := by
    rw [hz, hcomm.mul_pow, inv_pow, hk v' hv', inv_one, one_mul, conj_pow, hk v hv,
      mul_one, mul_inv_cancel]
  have hz1 := eq_one_of_mem_center_of_pow hZ hzZ hzk
  rw [hz, inv_mul_eq_one] at hz1
  rw [← hz1]
  exact hv'

end CentralQuotient

section Component

variable {G : Type} [Group G] [Finite G] {H K : Subgroup G}

theorem component_sylow_le_normalizer (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) : (T : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
  intro s hs
  have hK' := fstar_isComponentOf_subgroupOf_top hK
  have hsT : (⟨s, hTH hs⟩ : H) ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hs
  have h1 := sylow_le_normalizer_of_isComponentOf' hHA.1 (T.subtype hTH) hK' hsT
  rw [← Subgroup.subgroupOf_normalizer_eq hK.1, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem component_exists_inner (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) {s : G} (hs : s ∈ (T : Subgroup G)) :
    ∃ ℓ ∈ (T : Subgroup G) ⊓ K, ∀ x ∈ K, s * x * s⁻¹ = ℓ * x * ℓ⁻¹ := by
  have hsT : (⟨s, hTH hs⟩ : H) ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hs
  obtain ⟨ℓ, ⟨hℓT, hℓK⟩, hℓ⟩ :=
    exists_inner_mem_sylow_inf hHA.1 (T.subtype hTH) (fstar_isComponentOf_subgroupOf_top hK) hsT
  have hℓT' : (ℓ : G) ∈ (T : Subgroup G) := hℓT
  refine ⟨ℓ, ⟨hℓT', hℓK⟩, fun x hx => ?_⟩
  exact congrArg Subtype.val (hℓ ⟨x, hK.1 hx⟩ hx)

theorem component_exists_sylow (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := exists_sylow_map_eq_inf_of_isSubnormal (T.subtype hTH) hK.2.1
  let e : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hK.1
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  refine ⟨P'.mapSurjective he, ?_⟩
  rw [Sylow.coe_mapSurjective]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hy' : (y : H) ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H) ⊓ K.subgroupOf H := by
      rw [← hP']
      exact ⟨y, hy, rfl⟩
    rw [Sylow.coe_subtype] at hy'
    exact ⟨hy'.1, hy'.2⟩
  · rintro ⟨hxT, hxK⟩
    have hx' : (⟨x, hK.1 hxK⟩ : H) ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H) ⊓
        K.subgroupOf H := by
      rw [Sylow.coe_subtype]
      exact ⟨hxT, hxK⟩
    rw [← hP'] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    refine ⟨e y, ⟨y, hy, rfl⟩, ?_⟩
    have := congrArg Subtype.val hyx
    exact this

theorem component_odd_center (hHA : IsAStar H) (hK : IsComponentOf K H) :
    Odd (Nat.card (Subgroup.center K)) := by
  have hab : HasAbelianSylowTwo K :=
    (hHA.1.subgroup (K.subgroupOf H)).of_surjective (f := (Subgroup.subgroupOfEquivOfLe hK.1))
      (Subgroup.subgroupOfEquivOfLe hK.1).surjective
  exact odd_card_center_of_isQuasisimple hK.2.2 hab

theorem component_bender38Type
    (hHA : IsAStar H) (hK : IsComponentOf K H) :
    Bender38Type (K ⧸ Subgroup.center K) := by
  have h := hHA.isTypeL2_or_isTypeJR (fstar_isComponentOf_subgroupOf_top hK)
  have e := subgroupOfQuotientCenterEquiv hK.1
  have h' : IsTypeL2 (K ⧸ Subgroup.center K) ∨ IsTypeJR (K ⧸ Subgroup.center K) := by
    rcases h with h | h
    · exact Or.inl (h.of_mulEquiv e)
    · exact Or.inr (h.of_mulEquiv e)
  exact bender38Type_of_isTypeL2_or_isTypeJR (IsQuasisimple.exists_mul_ne_mul hK.2.2) h'

end Component

section Facts

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem' {S : Subgroup G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  have hS : S.map (MulAut.conj g).toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← hS] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  have : x = y := by
    have := congrArg (fun z => g⁻¹ * z * g) hyx
    simpa [mul_assoc] using this.symm
  rw [this]
  exact hy

structure Bender38Component (K Q : Subgroup G) : Prop where
  le : Q ≤ K
  odd_center : Odd (Nat.card (Subgroup.center K))
  sq_eq_one : ∀ v ∈ Q, v ^ 2 = 1
  four_le_card : 4 ≤ Nat.card Q
  card_eq : Nat.card Q = 2 ^ (Nat.card K).factorization 2
  isConj : ∀ u ∈ K, ∀ v ∈ K, orderOf u = 2 → orderOf v = 2 → ∃ k ∈ K, k * u * k⁻¹ = v
  trans : ∀ u ∈ Q, u ≠ 1 → ∀ v ∈ Q, v ≠ 1 →
    ∃ n ∈ K, (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) ∧ n * u * n⁻¹ = v
  even : 8 < Nat.card Q → ∃ d ∈ K, (∀ x ∈ Q, d * x * d⁻¹ ∈ Q) ∧
    (∀ n ∈ K, (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) →
      ∃ m : ℕ, ∀ v ∈ Q, n * v * n⁻¹ = d ^ m * v * (d ^ m)⁻¹) ∧
    (∀ n ∈ K, (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) → ∀ u ∈ Q, u ≠ 1 → n * u * n⁻¹ = u →
      ∀ v ∈ Q, n * v * n⁻¹ = v)
  psl : Nat.card Q = 4 → ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
    Nonempty (K ⧸ Subgroup.center K ≃* PSL(2, GaloisField p f))

variable {H K : Subgroup G}

theorem bender38Component
    (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTab : IsMulCommutative (T : Subgroup G)) :
    Bender38Component K ((T : Subgroup G) ⊓ K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (T : Subgroup G) ⊓ K with hQ
  obtain ⟨P, hP⟩ := component_exists_sylow hK T hTH
  have hZ := component_odd_center hHA hK
  have hBT := component_bender38Type hHA hK
  set ψ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  set Pb : Sylow 2 (K ⧸ Subgroup.center K) := P.mapSurjective hψs with hPb
  have hPb' : (Pb : Subgroup (K ⧸ Subgroup.center K)) = (P : Subgroup K).map ψ :=
    Sylow.coe_mapSurjective _ _
  have hPp : IsPGroup 2 (P : Subgroup K) := P.isPGroup'
  have hmemQ : ∀ x : K, (x : G) ∈ Q ↔ x ∈ (P : Subgroup K) := by
    intro x
    rw [hQ, ← hP]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hinj : ∀ x ∈ (P : Subgroup K), ∀ y ∈ (P : Subgroup K), ψ x = ψ y → x = y :=
    fun x hx y hy h => eq_of_mk_eq_of_isPGroup hZ hPp hx hy h
  have hcardQ : Nat.card Q = Nat.card (P : Subgroup K) := by
    rw [hQ, ← hP, Subgroup.card_map_of_injective K.subtype_injective]
  have hcardPb : Nat.card (Pb : Subgroup (K ⧸ Subgroup.center K)) = Nat.card (P : Subgroup K) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun x : (P : Subgroup K) =>
      (⟨ψ x, hPb' ▸ ⟨x, x.2, rfl⟩⟩ : (Pb : Subgroup (K ⧸ Subgroup.center K))))
      ⟨fun x y h => Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val h)), fun z => ?_⟩)).symm
    have hz : (z : K ⧸ Subgroup.center K) ∈ (P : Subgroup K).map ψ := hPb' ▸ z.2
    obtain ⟨x, hx, hxz⟩ := hz
    exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  have hψP : ∀ x ∈ (P : Subgroup K), ψ x ∈ (Pb : Subgroup (K ⧸ Subgroup.center K)) :=
    fun x hx => hPb' ▸ ⟨x, hx, rfl⟩
  have hPb_mem : ∀ z ∈ (Pb : Subgroup (K ⧸ Subgroup.center K)), ∃ x ∈ (P : Subgroup K),
      ψ x = z := fun z hz => by
    rw [hPb'] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  have hsq : ∀ v ∈ Q, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hPp
    have hvK : v ∈ K := hv.2
    have hvP := (hmemQ ⟨v, hvK⟩).mp hv
    have h1 := (hBT.sylow Pb).1 _ (hψP _ hvP)
    rw [← map_pow] at h1
    have h2 : (⟨v, hvK⟩ : K) ^ 2 ∈ Subgroup.center K := by
      rwa [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h3 := eq_one_of_mem_center_of_pow hZ h2 (hk _ ((P : Subgroup K).pow_mem hvP 2))
    simpa using congrArg Subtype.val h3
  have hconj : ∀ u ∈ K, ∀ v ∈ K, orderOf u = 2 → orderOf v = 2 → ∃ k ∈ K, k * u * k⁻¹ = v := by
    intro u hu v hv hu2 hv2
    have hord : ∀ x : K, orderOf (x : G) = 2 → orderOf (ψ x) = 2 := by
      intro x hx2
      rw [Subgroup.orderOf_coe] at hx2
      have h1 : ψ x ^ 2 = 1 := by rw [← map_pow, ← hx2, pow_orderOf_eq_one, map_one]
      refine orderOf_eq_prime h1 fun h => ?_
      have h2 : x ∈ Subgroup.center K := by
        rwa [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      have h3 := eq_one_of_mem_center_of_pow hZ h2 (m := 1) (by
        rw [pow_one, ← hx2, pow_orderOf_eq_one])
      rw [h3, orderOf_one] at hx2
      omega
    obtain ⟨c, hc⟩ := isConj_iff.mp (hBT.isConj _ _ (hord ⟨u, hu⟩ hu2) (hord ⟨v, hv⟩ hv2))
    obtain ⟨c', rfl⟩ := hψs c
    refine ⟨c', c'.2, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul] at hc
    set w : K := c' * ⟨u, hu⟩ * c'⁻¹ with hw
    have hz : w⁻¹ * ⟨v, hv⟩ ∈ Subgroup.center K := QuotientGroup.eq.mp hc
    have hw2 : w ^ 2 = 1 := by
      rw [hw, conj_pow]
      have : (⟨u, hu⟩ : K) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, ← hu2, pow_orderOf_eq_one]; rfl)
      rw [this, mul_one, mul_inv_cancel]
    have hv2' : (⟨v, hv⟩ : K) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hv2, pow_orderOf_eq_one]; rfl)
    have hcomm : Commute w⁻¹ ⟨v, hv⟩ := by
      have h1 : (⟨v, hv⟩ : K) = w * (w⁻¹ * ⟨v, hv⟩) := by rw [mul_inv_cancel_left]
      rw [h1]
      exact (Commute.inv_left (Commute.refl w)).mul_right
        (Subgroup.mem_center_iff.mp hz w⁻¹)
    have hz2 : (w⁻¹ * ⟨v, hv⟩) ^ 2 ^ 1 = 1 := by
      rw [pow_one, hcomm.mul_pow, inv_pow, hw2, inv_one, one_mul, hv2']
    have hz1 := eq_one_of_mem_center_of_pow hZ hz hz2
    rw [inv_mul_eq_one] at hz1
    exact congrArg Subtype.val hz1
  have hPab : IsMulCommutative (P : Subgroup K) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : ((a : K) : G) ∈ (T : Subgroup G) := ((hmemQ a).mpr a.2).1
    have hb : ((b : K) : G) ∈ (T : Subgroup G) := ((hmemQ b).mpr b.2).1
    have := congrArg Subtype.val (hTab.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    exact Subtype.ext (Subtype.ext this)
  have htrans : ∀ u ∈ Q, u ≠ 1 → ∀ v ∈ Q, v ≠ 1 →
      ∃ n ∈ K, (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) ∧ n * u * n⁻¹ = v := by
    intro u hu hu1 v hv hv1
    have hu2 : orderOf u = 2 := orderOf_eq_prime (hsq u hu) hu1
    have hv2 : orderOf v = 2 := orderOf_eq_prime (hsq v hv) hv1
    obtain ⟨c, hcK, hc⟩ := hconj u hu.2 v hv.2 hu2 hv2
    set u' : K := ⟨u, hu.2⟩
    set v' : K := ⟨v, hv.2⟩
    set c' : K := ⟨c, hcK⟩
    have hu'P : u' ∈ (P : Subgroup K) := (hmemQ u').mp hu
    have hv'P : v' ∈ (P : Subgroup K) := (hmemQ v').mp hv
    have hcv : c'⁻¹⁻¹ * u' * c'⁻¹ = v' := Subtype.ext (by simpa using hc)
    obtain ⟨n, hn, hneq⟩ := Sylow.conj_eq_normalizer_conj_of_mem P u' c'⁻¹ hu'P (hcv ▸ hv'P)
    rw [hcv] at hneq
    refine ⟨((n⁻¹ : K) : G), (n⁻¹ : K).2, fun x hx => ?_, ?_⟩
    · have hxP := (hmemQ ⟨x, hx.2⟩).mp hx
      have h1 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer ((P : Subgroup K) : Set K)).inv_mem hn) _).mp hxP
      exact (hmemQ _).mpr h1
    · have := congrArg Subtype.val hneq
      simpa using this.symm
  have hconjP : ∀ n : K, ψ n ∈ Subgroup.normalizer
      ((Pb : Subgroup (K ⧸ Subgroup.center K)) : Set (K ⧸ Subgroup.center K)) →
      ∀ x ∈ (P : Subgroup K), n * x * n⁻¹ ∈ (P : Subgroup K) := by
    intro n hn x hx
    refine conj_mem_of_mk_mem hZ hPp (fun v hv => ?_) hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hn (ψ v)).mp (hψP v hv)
    rw [← hPb']
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnormPb : ∀ n : K, (∀ x ∈ (P : Subgroup K), n * x * n⁻¹ ∈ (P : Subgroup K)) →
      ψ n ∈ Subgroup.normalizer
        ((Pb : Subgroup (K ⧸ Subgroup.center K)) : Set (K ⧸ Subgroup.center K)) := by
    intro n hn
    refine mem_normalizer_of_conj_mem' fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := hPb_mem z hz
    rw [← map_inv, ← map_mul, ← map_mul]
    exact hψP _ (hn x hx)
  have hnormQ : ∀ (n : G) (hnK : n ∈ K), (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) →
      ∀ x ∈ (P : Subgroup K), (⟨n, hnK⟩ : K) * x * (⟨n, hnK⟩ : K)⁻¹ ∈ (P : Subgroup K) :=
    fun n hnK hnQ x hx => (hmemQ _).mp (hnQ _ ((hmemQ x).mpr hx))
  have heven : 8 < Nat.card Q → ∃ d ∈ K, (∀ x ∈ Q, d * x * d⁻¹ ∈ Q) ∧
      (∀ n ∈ K, (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) →
        ∃ m : ℕ, ∀ v ∈ Q, n * v * n⁻¹ = d ^ m * v * (d ^ m)⁻¹) ∧
      (∀ n ∈ K, (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) → ∀ u ∈ Q, u ≠ 1 → n * u * n⁻¹ = u →
        ∀ v ∈ Q, n * v * n⁻¹ = v) := by
    intro h8
    have h8' : 8 < Nat.card (Pb : Subgroup (K ⧸ Subgroup.center K)) := by
      rwa [hcardPb, ← hcardQ]
    obtain ⟨db, hdb, hcyc, hfree⟩ := hBT.normalizer Pb h8'
    obtain ⟨d, rfl⟩ := hψs db
    have hdP := hconjP d hdb
    have hdN : d ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
      mem_normalizer_of_conj_mem' hdP
    refine ⟨(d : G), d.2, fun x hx => (hmemQ _).mpr (hdP _ ((hmemQ ⟨x, hx.2⟩).mp hx)),
      fun n hnK hnQ => ?_, fun n hnK hnQ u hu hu1 hnu v hv => ?_⟩
    · obtain ⟨m, hm⟩ := hcyc _ (hnormPb _ (hnormQ n hnK hnQ))
      refine ⟨m, fun v hv => ?_⟩
      have hv'P := (hmemQ ⟨v, hv.2⟩).mp hv
      have h1 := hm _ (hψP _ hv'P)
      rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at h1
      have hdm : d ^ m * ⟨v, hv.2⟩ * (d ^ m)⁻¹ ∈ (P : Subgroup K) :=
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer ((P : Subgroup K) : Set K)).pow_mem hdN m) _).mp hv'P
      have h2 := hinj _ (hnormQ n hnK hnQ _ hv'P) _ hdm h1
      have := congrArg Subtype.val h2
      simpa using this
    · have hu'P := (hmemQ ⟨u, hu.2⟩).mp hu
      have hv'P := (hmemQ ⟨v, hv.2⟩).mp hv
      have hψu1 : ψ ⟨u, hu.2⟩ ≠ 1 := by
        intro h
        apply hu1
        have := hinj _ hu'P 1 (P : Subgroup K).one_mem (by rw [h, map_one])
        exact congrArg Subtype.val this
      have hfix : ψ ⟨n, hnK⟩ * ψ ⟨u, hu.2⟩ * (ψ ⟨n, hnK⟩)⁻¹ = ψ ⟨u, hu.2⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hnu
      have h1 := hfree _ (hnormPb _ (hnormQ n hnK hnQ)) _ (hψP _ hu'P) hψu1 hfix _ (hψP _ hv'P)
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      have h2 := hinj _ (hnormQ n hnK hnQ _ hv'P) _ hv'P h1
      exact congrArg Subtype.val h2
  refine ⟨inf_le_right, hZ, hsq, ?_, ?_, hconj, htrans, heven, fun h4 => ?_⟩
  · rw [hcardQ, ← hcardPb]
    exact (hBT.sylow Pb).2
  · rw [hcardQ]
    exact Sylow.card_eq_multiplicity P
  · exact hBT.psl Pb (by rw [hcardPb, ← hcardQ, h4])

end Facts

end CFSG.Walter
