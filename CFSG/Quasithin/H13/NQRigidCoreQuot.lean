module

public import CFSG.Quasithin.H13.NQTermNoncyclicAction
public import CFSG.Quasithin.SteinbergBTQuasisimpleSQTKCenter
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.NQRigidFitting4

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj frattiniQuotConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

section Witness

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_frattini_subgroupOf {X K : Subgroup G} (hXK : X ≤ K) :
    Nat.card ((X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ⧸
        frattini (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K))) =
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  Nat.card_congr (QuotientGroup.congr _ _ (coreQuotEquivSubgroupOf hXK)
    (map_frattini_mulEquiv (coreQuotEquivSubgroupOf hXK))).toEquiv

omit [Finite G] in
theorem isPGroup_coreQuot_subgroupOf {p : ℕ} {X K : Subgroup G} (hXK : X ≤ K)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) :
    IsPGroup p (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) :=
  hXA.of_equiv (coreQuotEquivSubgroupOf hXK).symm

theorem isPGroup_of_exponent {p : ℕ} {X : Type*} [Group X] (hexp : Monoid.exponent X = p) :
    IsPGroup p X := fun w => ⟨1, by rw [pow_one, ← hexp]; exact Monoid.pow_exponent_eq_one w⟩

@[expose] noncomputable def coreQuotEquivOfLe {X K : Subgroup G} (hXK : X ≤ K) :
    (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ≃* (X ⧸ CFSG.pCore 2 X) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXK) (CFSG.pCore_map_iso 2 _)

@[expose] noncomputable def frattiniEquivSubgroupOf {X K : Subgroup G} (hXK : X ≤ K) :
    ((X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ⧸
        frattini (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K))) ≃*
      ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  QuotientGroup.congr _ _ (coreQuotEquivOfLe hXK)
    (map_frattini_mulEquiv (coreQuotEquivOfLe hXK))

omit [Finite G] in
theorem frattiniEquivSubgroupOf_mk {X K : Subgroup G} (hXK : X ≤ K) (x : X.subgroupOf K) :
    frattiniEquivSubgroupOf hXK (((x : X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) :
      (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ⧸
        frattini (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)))) =
      (((subgroupOfEquivOfLe hXK x : X) : X ⧸ CFSG.pCore 2 X) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  rfl

omit [Finite G] in
theorem frattiniQuotConj_mk_mk {L : Type*} [Group L] {X : Subgroup L} [X.Normal] (l : L)
    (x : X) :
    frattiniQuotConj X l (((x : X ⧸ CFSG.pCore 2 X) :
      (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) =
      (((MulAut.conjNormal l x : X) : X ⧸ CFSG.pCore 2 X) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  rfl

omit [Finite G] in
theorem normalizerFrattiniConj_mk_mk {X : Subgroup G} (h : normalizer (X : Set G)) (y : X) :
    normalizerFrattiniConj X h (((y : X ⧸ CFSG.pCore 2 X) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) =
      (((X.normalizerMonoidHom h y : X) : X ⧸ CFSG.pCore 2 X) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  rfl

omit [Finite G] in
theorem subgroupOfEquivOfLe_conjNormal {X L : Subgroup G} (hXL : X ≤ L)
    [(X.subgroupOf L).Normal] (h : normalizer (X : Set G)) (hhL : (h : G) ∈ L)
    (x : X.subgroupOf L) :
    subgroupOfEquivOfLe hXL (MulAut.conjNormal (⟨h, hhL⟩ : L) x) =
      X.normalizerMonoidHom h (subgroupOfEquivOfLe hXL x) := by
  apply Subtype.ext
  rfl

theorem frattiniQuotConj_irreducible_of {X L : Subgroup G} (hXL : X ≤ L)
    [(X.subgroupOf L).Normal] (hirr : IsFrattiniIrreducible X L) :
    ∀ U : Subgroup ((X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) ⧸
        frattini (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L))),
      (∀ l : L, ∀ u ∈ U, frattiniQuotConj (X.subgroupOf L) l u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  set eW := frattiniEquivSubgroupOf hXL with heW
  have hcompat : ∀ (h : normalizer (X : Set G)) (hhL : (h : G) ∈ L)
      (w : (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) ⧸
        frattini (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L))),
      eW (frattiniQuotConj (X.subgroupOf L) ⟨h, hhL⟩ w) = normalizerFrattiniConj X h (eW w) := by
    intro h hhL w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [heW, frattiniQuotConj_mk_mk, frattiniEquivSubgroupOf_mk hXL (MulAut.conjNormal _ x),
      frattiniEquivSubgroupOf_mk hXL x, normalizerFrattiniConj_mk_mk,
      subgroupOfEquivOfLe_conjNormal]
  rcases hirr (U.map eW.toMonoidHom) (by
    rintro h hhL _ ⟨u, hu, rfl⟩
    exact ⟨_, hU ⟨h, hhL⟩ u hu, hcompat h hhL u⟩) with h0 | ht
  · left
    rw [eq_bot_iff]
    intro y hy
    have h1 : eW y ∈ U.map eW.toMonoidHom := ⟨y, hy, rfl⟩
    rw [h0, mem_bot] at h1
    rw [mem_bot]
    exact eW.injective (h1.trans (map_one eW).symm)
  · right
    rw [eq_top_iff]
    intro y _
    have h1 : eW y ∈ U.map eW.toMonoidHom := ht ▸ mem_top _
    obtain ⟨y', hy', hyy⟩ := h1
    have : y' = y := eW.injective hyy
    rwa [← this]

end Witness

noncomputable abbrev coreCenterQuot (K : Type*) [Group K] :
    K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
  (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))

theorem coreCenterQuot_surjective (K : Type*) [Group K] :
    Function.Surjective (coreCenterQuot K) := fun z => by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center (K ⧸ CFSG.pCore 2 K)) z
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) j
  exact ⟨k, rfl⟩

theorem not_dvd_card_ker_coreCenterQuot {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ¬ p ∣ Nat.card (coreCenterQuot K).ker := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (coreCenterQuot K).ker) p hdvd
  have hxo : orderOf (x : K) = p := by rw [Subgroup.orderOf_coe, hx]
  have hx1 : QuotientGroup.mk' (CFSG.pCore 2 K) (x : K) ∈ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.eq_one_iff _).mp x.2
  have hx2 : QuotientGroup.mk' (CFSG.pCore 2 K) (x : K) = 1 :=
    NQTerm.eq_one_of_orderOf_dvd_prime_pow (k := 1) hp hZ hx1
      ((orderOf_map_dvd _ _).trans (by rw [hxo, pow_one]))
  have hx3 : (x : K) ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff _).mp hx2
  have h4 : ¬ p ∣ Nat.card (CFSG.pCore 2 K) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).exists_card_eq
    rw [hm]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have h5 : (x : K) = 1 :=
    NQTerm.eq_one_of_orderOf_dvd_prime_pow (k := 1) hp h4 hx3 (by rw [hxo, pow_one])
  rw [h5, orderOf_one] at hxo
  exact hp.one_lt.ne hxo

theorem pCore_le_center_of_quasisimple {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) : CFSG.pCore 2 K ≤ center K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK CFSG.pCore_normal with h | h
  · exfalso
    apply CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hK
    have h2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
    have : IsPGroup 2 K := by
      intro g
      have hg : g ∈ CFSG.pCore 2 K := h ▸ mem_top g
      obtain ⟨n, hn⟩ := h2 ⟨g, hg⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    have : Group.IsNilpotent K := this.isNilpotent
    infer_instance
  · exact h

theorem ker_coreCenterQuot_of_quasisimple {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) : (coreCenterQuot K).ker = center K := by
  have : Group.IsPerfect K := hK.1
  have hA := pCore_le_center_of_quasisimple hK
  have hc := SteinbergBT.center_quotient_eq_map_center (CFSG.pCore 2 K) hA
  ext k
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  rw [hc]
  constructor
  · rintro ⟨z, hz, hzk⟩
    rw [QuotientGroup.mk'_apply] at hzk
    have h1 : z⁻¹ * k ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp hzk
    have h2 : k = z * (z⁻¹ * k) := by group
    rw [h2]
    exact mul_mem hz (hA h1)
  · intro hk
    exact ⟨k, hk, rfl⟩

@[expose] noncomputable def centerQuotEquivOfQuasisimple {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) :
    (K ⧸ center K) ≃* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_coreCenterQuot_of_quasisimple hK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (coreCenterQuot_surjective K))

theorem card_eq_two_pow_mul_prime_pow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) : ∃ a b : ℕ, Nat.card X = 2 ^ a * p ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)).exists_card_eq
  obtain ⟨b, hb⟩ := hXA.exists_card_eq
  refine ⟨a, b, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 X), hb, ha, mul_comm]

end CFSG.Quasithin.H13.NQRigid
