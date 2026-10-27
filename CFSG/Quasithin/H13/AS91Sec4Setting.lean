module

public import CFSG.Quasithin.H13.AS91Sec4Defs
public import CFSG.Quasithin.H13.AS91Sec4Module
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G] {z : G}

theorem HypJ4.hext (h : HypJ4 G z) :
    timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({z} : Set G))) := by
  rw [← Bridge.generalizedFitting_eq_timmesfeldFStar, ← h.core.1]
  exact (Bridge.timmesfeldIsExtraspecial_iff _).mpr h.core.2.1

@[expose] noncomputable def HypJ4.setting (h : HypJ4 G z) : Setting G :=
  Setting.ofFStar z h.orderOf_z h.hext

@[simp] theorem HypJ4.setting_z (h : HypJ4 G z) : h.setting.z = z := rfl

theorem HypJ4.setting_M (h : HypJ4 G z) : h.setting.M = H z := rfl

theorem HypJ4.setting_Q (h : HypJ4 G z) :
    h.setting.Q = CFSG.pCore 2 (centralizer ({z} : Set G)) := by
  change timmesfeldFStar _ = _
  rw [← Bridge.generalizedFitting_eq_timmesfeldFStar, h.core.1]

theorem HypJ4.setting_QG (h : HypJ4 G z) : h.setting.QG = Q z := by
  change h.setting.Q.map h.setting.M.subtype = _
  rw [h.setting_Q]
  rfl

theorem HypJ4.setting_width (h : HypJ4 G z) : h.setting.width = 6 := by
  apply Setting.width_eq
  rw [h.setting_Q]
  exact h.core.2.2.1

@[expose] noncomputable def HypJ4.quotEquivMbar (h : HypJ4 G z) :
    (centralizer ({z} : Set G) ⧸ CFSG.pCore 2 (centralizer ({z} : Set G))) ≃* h.setting.Mbar :=
  (@QuotientGroup.quotientMulEquivOfEq _ _ _ _ CFSG.pCore_normal h.setting.normal
    h.setting_Q.symm).trans h.setting.quotientEquivMbar

theorem HypJ4.autTriple_Mbar (h : HypJ4 G z) : J4.IsAutTripleM22 h.setting.Mbar :=
  h.autTriple.of_mulEquiv h.quotEquivMbar

theorem isQuasisimple_of_quot_M22 {X : Type} [Group X]
    (hP : Group.IsPerfect X) (e : X ⧸ center X ≃* CFSG.Blueprint.NativeSporadic.M22) :
    CFSG.IsQuasisimple X := by
  obtain ⟨-, hnt, hsimp⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  have : Nontrivial CFSG.Blueprint.NativeSporadic.M22 := hnt
  have hS : IsSimpleGroup (X ⧸ center X) := e.isSimpleGroup
  refine ⟨hP, hS, ?_⟩
  by_contra hc
  push Not at hc
  have hPQ : Group.IsPerfect (X ⧸ center X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center X))
  have hcomm : commutator (X ⧸ center X) = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hc a b, mul_inv_cancel_right, mul_inv_cancel]
  rw [hPQ.commutator_eq_top] at hcomm
  have : Nontrivial (X ⧸ center X) := e.toEquiv.nontrivial
  exact top_ne_bot hcomm

@[expose] noncomputable def cMbar (S : Setting G) (θ : S.O) : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (S.Mbar ⊓ centralizer ({θ} : Set S.O)).map S.O.subtype

theorem mem_cMbar {S : Setting G} {θ : S.O} {g : S.Qt ≃ₗ[ZMod 2] S.Qt} :
    g ∈ cMbar S θ ↔ ∃ m : S.O, m ∈ S.Mbar ∧ m * θ = θ * m ∧ (m : S.Qt ≃ₗ[ZMod 2] S.Qt) = g := by
  constructor
  · rintro ⟨m, ⟨hmM, hmc⟩, rfl⟩
    exact ⟨m, hmM, mem_centralizer_singleton_iff.mp hmc, rfl⟩
  · rintro ⟨m, hmM, hmc, rfl⟩
    exact ⟨m, ⟨hmM, mem_centralizer_singleton_iff.mpr hmc⟩, rfl⟩

theorem exists_gen_of_isAutTripleM22 {X : Type} [Group X]
    [Finite X] (hX : J4.IsAutTripleM22 X) :
    ∃ ζ : X, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ (∀ m : X, m * ζ * m⁻¹ ∈ zpowers ζ) ∧
      IsHat ↥(centralizer ({ζ} : Set X)) (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      (∃ τ : X, τ * ζ ≠ ζ * τ) ∧ Nat.card X = 2661120 := by
  obtain ⟨Z, hZn, hZ3, hidx, hperf, hcen, -, ψ, -, hψs, hψk, -⟩ := hX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Z).mp (isCyclic_of_prime_card hZ3)
  have hord : orderOf ζ = 3 := by rw [← Nat.card_zpowers, hζ, hZ3]
  have hζZ : ζ ∈ Z := hζ ▸ mem_zpowers ζ
  have hC : centralizer (Z : Set X) = centralizer ({ζ} : Set X) := by
    rw [← hζ, zpowers_eq_closure, centralizer_closure]
  have hZC : Z ≤ centralizer (Z : Set X) := fun x hx => by
    have : x ∈ (center ↥(centralizer (Z : Set X))).map (centralizer (Z : Set X)).subtype := by
      rw [hcen]; exact hx
    exact map_subtype_le _ this
  have hcenC : center ↥(centralizer (Z : Set X)) = ψ.ker := by
    apply Subgroup.map_injective (centralizer (Z : Set X)).subtype_injective
    rw [hψk, map_subgroupOf_eq_of_le hZC]
    exact hcen
  have eC : ↥(centralizer (Z : Set X)) ⧸ center ↥(centralizer (Z : Set X)) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier .M22 :=
    (QuotientGroup.quotientMulEquivOfEq hcenC).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hcard3 : Nat.card (center ↥(centralizer (Z : Set X))) = 3 := by
    have h1 := Subgroup.card_map_of_injective (K := center ↥(centralizer (Z : Set X)))
      (centralizer (Z : Set X)).subtype_injective
    rw [hcen, hZ3] at h1
    exact h1.symm
  have hHat : IsHat ↥(centralizer (Z : Set X)) (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    ⟨isQuasisimple_of_quot_M22 hperf eC, hcard3, ⟨eC⟩⟩
  refine ⟨ζ, hord ▸ pow_orderOf_eq_one ζ, fun h1 => by rw [h1, orderOf_one] at hord; omega,
    fun m => hζ ▸ hZn.conj_mem ζ hζZ m, isHat_of_mulEquiv (MulEquiv.subgroupCongr hC) hHat, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have htop : centralizer (Z : Set X) = ⊤ := by
      rw [hC, eq_top_iff]
      intro τ _
      exact mem_centralizer_singleton_iff.mpr (hall τ)
    rw [htop, Subgroup.index_top] at hidx
    omega
  · have hC1 : Nat.card ↥(centralizer (Z : Set X)) = 3 * 443520 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(centralizer (Z : Set X))),
        Nat.card_congr eC.toEquiv, hcard3]
      change Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 * 3 = _
      rw [CFSG.Sporadic.Mathieu.card_M22]
    have h2 := Subgroup.card_mul_index (centralizer (Z : Set X))
    rw [hC1, hidx] at h2
    omega

theorem exists_gen_of_isAutTripleM22_sub {O : Type} [Group O]
    (M : Subgroup O) [Finite M] (hM : J4.IsAutTripleM22 ↥M) :
    ∃ θ : O, θ ∈ M ∧ θ ^ 3 = 1 ∧ θ ≠ 1 ∧ (∀ m ∈ M, m * θ * m⁻¹ ∈ zpowers θ) ∧
      IsHat ↥(M ⊓ centralizer ({θ} : Set O)) (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      (∃ τ ∈ M, τ * θ ≠ θ * τ) ∧ Nat.card M = 2661120 := by
  obtain ⟨ζ, hζ3, hζ1, hζn, hζH, ⟨τ, hτ⟩, hcard⟩ := exists_gen_of_isAutTripleM22 hM
  refine ⟨ζ, ζ.2, by rw [← Subgroup.coe_pow, hζ3, Subgroup.coe_one],
    fun h1 => hζ1 (Subtype.ext h1), fun m hm => ?_, ?_,
    ⟨τ, τ.2, fun h => hτ (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h))⟩,
    hcard⟩
  · obtain ⟨k, hk⟩ := hζn ⟨m, hm⟩
    refine ⟨k, ?_⟩
    show (ζ : O) ^ k = m * ζ * m⁻¹
    rw [← Subgroup.coe_zpow]
    exact congrArg Subtype.val hk
  · have hmap : (centralizer ({ζ} : Set ↥M)).map M.subtype =
        M ⊓ centralizer ({(ζ : O)} : Set O) := by
      ext m
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
      · rintro ⟨hm, hmc⟩
        exact ⟨⟨m, hm⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hmc)), rfl⟩
    exact isHat_of_mulEquiv (((centralizer ({ζ} : Set ↥M)).equivMapOfInjective _
      M.subtype_injective).trans (MulEquiv.subgroupCongr hmap)) hζH

theorem HypJ4.exists_center_gen (h : HypJ4 G z) :
    ∃ θ : h.setting.O, θ ∈ h.setting.Mbar ∧ θ ^ 3 = 1 ∧ θ ≠ 1 ∧
      (∀ m ∈ h.setting.Mbar, m * θ * m⁻¹ ∈ zpowers θ) ∧
      IsHat ↥(cMbar h.setting θ) (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      (∃ τ ∈ h.setting.Mbar, τ * θ ≠ θ * τ) ∧ Nat.card h.setting.Mbar = 2661120 := by
  haveI : Finite ↥h.setting.Mbar := Bridge.finite_Mbar h.setting
  obtain ⟨θ, hθM, hθ3, hθ1, hθn, hθH, hτ, hcard⟩ :=
    exists_gen_of_isAutTripleM22_sub _ h.autTriple_Mbar
  exact ⟨θ, hθM, hθ3, hθ1, hθn,
    isHat_of_mulEquiv (Subgroup.equivMapOfInjective _ _ h.setting.O.subtype_injective) hθH, hτ,
    hcard⟩

end CFSG.Quasithin.H13.AS91
