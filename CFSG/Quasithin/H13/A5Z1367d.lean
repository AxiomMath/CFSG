module

public import CFSG.Quasithin.H13.A5X1367n

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

theorem le_of_isPGroup_of_le_normalizer {G : Type} [Group G] [Finite G] {T H X : Subgroup G}
    (hT : IsSylowTwoOf T H) (hX : IsPGroup 2 X) (hXH : X ≤ H)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) : X ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXT : IsPGroup 2 ↥(X ⊔ T) := hX.to_sup_of_normal_left' hT.2.1 hTX
  exact le_sup_left.trans ((A4.isSylowTwoOf_iff_maximal.mp hT).2.2 (X ⊔ T) (sup_le hXH hT.1) hXT
    le_sup_right)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem Lv_le_normalizer_V : S.Lv ≤ Subgroup.normalizer (V : Set G) := fun _ hx =>
  S.frame.L_le (oTwoRes_le _ hx).1

@[expose] noncomputable def LvQ : Subgroup G :=
  S.Lv ⊓ (S.frame.ρ.ker.map (Subgroup.normalizer (V : Set G)).subtype)

theorem LvQ_le_Lv : S.LvQ ≤ S.Lv := inf_le_left

theorem mem_LvQ {x : G} : x ∈ S.LvQ ↔ ∃ h : x ∈ Subgroup.normalizer (V : Set G),
    x ∈ S.Lv ∧ S.frame.ρ ⟨x, h⟩ = 1 := by
  constructor
  · rintro ⟨hx, ⟨y, hy, rfl⟩⟩
    exact ⟨y.2, hx, hy⟩
  · rintro ⟨h, hx, hρ⟩
    exact ⟨hx, ⟨⟨x, h⟩, hρ, rfl⟩⟩

theorem isPGroup_LvQ : IsPGroup 2 S.LvQ := by
  rintro ⟨x, hx⟩
  obtain ⟨h, hxL, hρ⟩ := S.mem_LvQ.1 hx
  obtain ⟨k, hk⟩ := S.two_pow_of_Lv_of_rho ⟨x, h⟩ hxL hρ
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem Tv_le_normalizer_LvQ : S.Tv ≤ Subgroup.normalizer (S.LvQ : Set G) := by
  have key : ∀ t ∈ S.Tv, ∀ x ∈ S.LvQ, t * x * t⁻¹ ∈ S.LvQ := by
    intro t ht x hx
    obtain ⟨h, hxL, hρ⟩ := S.mem_LvQ.1 hx
    have htV : t ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le (Subgroup.mem_inf.mp ht).1
    have hm : t * x * t⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ htV h) (Subgroup.inv_mem _ htV)
    refine S.mem_LvQ.2 ⟨hm, (Subgroup.mem_normalizer_iff.mp (S.Tv_le_normalizer_Lv ht) x).mp hxL,
      ?_⟩
    have e : (⟨t * x * t⁻¹, hm⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨t, htV⟩ * ⟨x, h⟩ * (⟨t, htV⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hρ, mul_one, mul_inv_cancel]
  intro t ht
  refine B6.mem_normalizer_of_forall_mem (key t ht) fun x hx => ?_
  have := key t⁻¹ (S.Tv.inv_mem ht) x hx
  rwa [inv_inv] at this

theorem Lv_le_normalizer_LvQ : S.Lv ≤ Subgroup.normalizer (S.LvQ : Set G) := by
  have key : ∀ l ∈ S.Lv, ∀ x ∈ S.LvQ, l * x * l⁻¹ ∈ S.LvQ := by
    intro l hl x hx
    obtain ⟨h, hxL, hρ⟩ := S.mem_LvQ.1 hx
    have hlV := S.Lv_le_normalizer_V hl
    have hm : l * x * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hlV h) (Subgroup.inv_mem _ hlV)
    refine S.mem_LvQ.2 ⟨hm, S.Lv.mul_mem (S.Lv.mul_mem hl hxL) (S.Lv.inv_mem hl), ?_⟩
    have e : (⟨l * x * l⁻¹, hm⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨l, hlV⟩ * ⟨x, h⟩ * (⟨l, hlV⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hρ, mul_one, mul_inv_cancel]
  intro l hl
  refine B6.mem_normalizer_of_forall_mem (key l hl) fun x hx => ?_
  have := key l⁻¹ (S.Lv.inv_mem hl) x hx
  rwa [inv_inv] at this

theorem autOn_LvQ_le_TvS (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) : autOn S.LvQ S.Uv ≤ autOn S.Tv S.Uv := by
  have hsyl := S.isSylowTwoOf_TvS h1222 h517
  have hQU : S.LvQ ≤ Subgroup.normalizer (S.Uv : Set G) :=
    (S.LvQ_le_Lv.trans S.Lv_le_Gv).trans S.Gv_le_normalizer_Uv
  have hQ2 : IsPGroup 2 (autOn S.LvQ S.Uv) := by
    have := S.isPGroup_LvQ
    have h1 : IsPGroup 2 ↥(S.LvQ.subgroupOf (Subgroup.normalizer (S.Uv : Set G))) :=
      this.of_equiv (Subgroup.subgroupOfEquivOfLe hQU).symm
    exact h1.map _
  exact le_of_isPGroup_of_le_normalizer hsyl hQ2
    (S.autOn_le_GvS (S.LvQ_le_Lv.trans S.Lv_le_Gv))
    (autOn_le_normalizer_autOn S.Tv_le_normalizer_LvQ)

theorem relIndex_LvQ_le : S.LvQ.relIndex S.Lv ≤ 3 := by
  let ψ : ↥S.Lv →* Equiv.Perm (Fin 5) :=
    S.frame.ρ.comp (Subgroup.inclusion S.Lv_le_normalizer_V)
  have hker : S.LvQ.subgroupOf S.Lv = ψ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, S.mem_LvQ]
    constructor
    · rintro ⟨h, -, hρ⟩
      exact hρ
    · intro hρ
      exact ⟨S.Lv_le_normalizer_V x.2, x.2, hρ⟩
  have hrange : ψ.range ≤ Subgroup.zpowers c234 := by
    rintro _ ⟨x, rfl⟩
    rcases S.rho_Lv_cases ⟨x, S.Lv_le_normalizer_V x.2⟩ x.2 with h | h | h
    · show S.frame.ρ ⟨x, _⟩ ∈ _
      rw [h]
      exact Subgroup.one_mem _
    · show S.frame.ρ ⟨x, _⟩ ∈ _
      rw [h]
      exact Subgroup.mem_zpowers _
    · show S.frame.ρ ⟨x, _⟩ ∈ _
      rw [h]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have h3 : Nat.card (Subgroup.zpowers c234) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  show (S.LvQ.subgroupOf S.Lv).index ≤ 3
  rw [hker, Subgroup.index_ker]
  exact h3 ▸ Subgroup.card_le_of_le hrange

theorem card_LvS_le (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) :
    Nat.card ↥(autOn S.Lv S.Uv) ≤ 3 * Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) := by
  have hLU : S.Lv ≤ Subgroup.normalizer (S.Uv : Set G) := S.Lv_le_Gv.trans S.Gv_le_normalizer_Uv
  set φ := InternalSec.autOnHom hLU with hφ
  have hsφ : Function.Surjective φ := InternalSec.autOnHom_surjective hLU
  set Q : Subgroup ↥S.Lv := S.LvQ.subgroupOf S.Lv with hQ
  have hidx : (Q.map φ).index ≤ 3 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (Subgroup.index_map_dvd Q hsφ)).trans S.relIndex_LvQ_le
  have hQS : ((Q.map φ).map (autOn S.Lv S.Uv).subtype) ≤ autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(φ x).2, S.autOn_LvQ_le_TvS h1222 h517 ?_⟩
    refine Setup.mem_autOn_iff.2 ⟨⟨x, hLU x.2⟩, Subgroup.mem_subgroupOf.mp hx, ?_⟩
    rfl
  have h1 := Subgroup.card_mul_index (Q.map φ)
  have h2 : Nat.card ↥(Q.map φ) ≤ Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) := by
    have e := Nat.card_congr ((Q.map φ).equivMapOfInjective _
      (autOn S.Lv S.Uv).subtype_injective).toEquiv
    rw [e]
    exact Subgroup.card_le_of_le hQS
  calc Nat.card ↥(autOn S.Lv S.Uv) = Nat.card ↥(Q.map φ) * (Q.map φ).index := h1.symm
    _ ≤ Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) * 3 := Nat.mul_le_mul h2 hidx
    _ = 3 * Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) := mul_comm _ _

theorem exists_LvS_order_three :
    ∃ l ∈ autOn S.Lv S.Uv, orderOf l = 3 := by
  obtain ⟨l₀, hl₀Lv, hl₀odd, hl₀σ⟩ := S.exists_Lv_c234_odd
  have hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G) :=
    S.Gv_le_normalizer_Uv (S.Lv_le_Gv hl₀Lv)
  refine ⟨conjAct S.Uv ⟨l₀, hl₀N⟩, Setup.mem_autOn_iff.2 ⟨⟨l₀, hl₀N⟩, hl₀Lv, rfl⟩, ?_⟩
  have hl₀3 : (l₀ : G) ^ 3 = 1 := by
    have hρ3 : S.frame.ρ (l₀ ^ 3) = 1 := by
      rw [map_pow]
      rcases hl₀σ with h | h <;> rw [h]
      · decide
      · decide
    have hmem : ((l₀ ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.Lv := by
      rw [Subgroup.coe_pow]
      exact S.Lv.pow_mem hl₀Lv 3
    obtain ⟨k, hk⟩ := S.two_pow_of_Lv_of_rho _ hmem hρ3
    rw [Subgroup.coe_pow, ← pow_mul] at hk
    have h1 : orderOf (l₀ : G) ∣ 3 * 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : (orderOf (l₀ : G)).Coprime (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hl₀odd)
    have h3 : orderOf (l₀ : G) ∣ 3 := h2.dvd_of_dvd_mul_right h1
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨l₀, hl₀N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hl₀3)
    rw [this, map_one]
  · intro h1
    have hv := S.vU_eq_mul_conjAct l₀ hl₀σ hl₀N
    rw [h1, inv_one] at hv
    have hz3 : S.vU = S.zU := by
      rw [hv]
      have hUe : S.zU * S.zU = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, ← pow_two]
        exact S.z_sq)
      calc S.zU * (1 : MulAut ↥S.Uv) S.zU * S.zU = S.zU * S.zU * S.zU := rfl
        _ = S.zU := by rw [hUe, one_mul]
    have hvz' : (S.vU : G) = (S.zU : G) := congrArg Subtype.val hz3
    have hvz : S.v12 = S.z := hvz'
    exact S.v12_not_mem_V1 (hvz ▸ Subgroup.mem_zpowers _)

end Setting

end CFSG.Quasithin.H13.A5
