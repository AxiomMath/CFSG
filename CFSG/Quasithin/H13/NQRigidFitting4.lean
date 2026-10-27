module

public import CFSG.Quasithin.H13.NQRigidFitting3
public import CFSG.Quasithin.H13.NQRigidBridge

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open scoped IsMulCommutative

section Irreducible

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem isFrattiniIrreducible_inf_centralizer_of_ne_one
    (h : QTNQ T L M)
    (hmod : QTNQExplicitModule L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXL : X ≤ L) (hXchar : (X.subgroupOf L).Characteristic)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {u : G} (hu : u ∈ qtnqU L M) : IsFrattiniIrreducible X (L ⊓ centralizer {u}) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hLN : L ≤ normalizer (X : Set G) := by
    refine le_normalizer.trans ?_
    exact NQSetup.normalizer_le_normalizer_of_characteristic hXL hXchar
  have hpow : ∀ w : X ⧸ CFSG.pCore 2 X, w ^ p = 1 := fun w => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one w
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := fun w => ⟨1, by rw [pow_one, hpow]⟩
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXp⟩
  have : IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    CFSG.isElementaryAbelian_quotient_frattini
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  set β := (normalizerFrattiniConj X).comp (inclusion hLN) with hβ
  have hβ1 : β ≠ 1 := by
    obtain ⟨l, hl, hl1⟩ := hLW
    intro hb
    apply hl1
    have h2 := DFunLike.congr_fun hb ⟨l, hl⟩
    have h3 : inclusion hLN ⟨(l : G), hl⟩ = l := Subtype.ext rfl
    rw [MonoidHom.comp_apply, h3] at h2
    exact h2
  set α := (NQSetup.mulAutLinear p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))).comp β
    with hα
  have hα1 : α ≠ 1 := by
    intro h1
    apply hβ1
    ext l w
    have h2 := LinearEquiv.congr_fun (DFunLike.congr_fun h1 l) (Additive.ofMul w)
    exact congrArg Additive.toMul h2
  have hfin := NQSetup.finrank_additive_eq_two hW
  obtain ⟨B, hBH, hBnc, hBcop⟩ := exists_noncyclic_coprime_of_explicitModule h hmod hu hp hp5
  intro Y hY
  set U' : Submodule (ZMod p) (Additive ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) :=
    AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup Y) with hU'
  have hmemU' : ∀ x, x ∈ U' ↔ Additive.toMul x ∈ Y := fun _ => Iff.rfl
  rcases NQSetup.nq_noncyclic_coprime_projective_irreducibility hp5 hLC hfin α hα1
      ((centralizer ({u} : Set G)).subgroupOf L) ⟨B, hBH, hBnc, hBcop⟩ U' (by
        intro l hl x hx
        rw [hmemU'] at hx ⊢
        exact hY ⟨l, hLN l.2⟩ (mem_inf.mpr ⟨l.2, hl⟩) _ hx) with h0 | ht
  · left
    rw [eq_bot_iff]
    intro y hy
    have h1 : Additive.ofMul y ∈ U' := (hmemU' _).mpr hy
    rw [h0, Submodule.mem_bot] at h1
    exact (mem_bot).mpr (Additive.ofMul.injective h1)
  · right
    rw [eq_top_iff]
    intro y _
    have h1 : Additive.ofMul y ∈ U' := by rw [ht]; exact Submodule.mem_top
    exact (hmemU' _).mp h1

end Irreducible

section Transport

variable {G : Type} [Group G] [Finite G]

noncomputable def coreQuotEquivSubgroupOf {X K : Subgroup G} (hXK : X ≤ K) :
    (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ≃* (X ⧸ CFSG.pCore 2 X) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXK) (CFSG.pCore_map_iso 2 _)

theorem subgroupOf_transport {p : ℕ} {X A K : Subgroup G} (hXK : X ≤ K) (hAK : A ≤ K)
    (hX2 : NoPQuotient 2 X) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hp1 : 1 < p)
    (hirr : IsFrattiniIrreducible X A) :
    NoPQuotient 2 (X.subgroupOf K) ∧
      Monoid.exponent (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) = p ∧
      CFSG.pRank p (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) = 2 ∧
      IsFrattiniIrreducible (X.subgroupOf K) (A.subgroupOf K) := by
  classical
  set e := subgroupOfEquivOfLe hXK with he
  set eQ := coreQuotEquivSubgroupOf hXK with heQ
  refine ⟨NoPQuotient.of_surjective e.symm.toMonoidHom e.symm.surjective hX2,
    by rw [Monoid.exponent_eq_of_mulEquiv eQ, hexp], by rw [pRank_congr hp1 eQ, hrk], ?_⟩
  set eW : ((X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ⧸
      frattini (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K))) ≃*
      ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    QuotientGroup.congr _ _ eQ (map_frattini_mulEquiv eQ) with heW
  intro Y hY
  have hN : ∀ (h : normalizer (X : Set G)) (hhA : (h : G) ∈ A),
      (⟨h, hAK hhA⟩ : K) ∈ normalizer ((X.subgroupOf K : Subgroup K) : Set K) := by
    intro h hhA
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp h.2 y
  have hcompat : ∀ (h : normalizer (X : Set G)) (hhA : (h : G) ∈ A)
      (w : (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ⧸
        frattini (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K))),
      eW (normalizerFrattiniConj (X.subgroupOf K) ⟨⟨h, hAK hhA⟩, hN h hhA⟩ w) =
        normalizerFrattiniConj X h (eW w) := by
    intro h hhA w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rfl
  rcases hirr (Y.map eW.toMonoidHom) (by
    rintro h hhA _ ⟨y, hy, rfl⟩
    refine ⟨_, hY ⟨⟨h, hAK hhA⟩, hN h hhA⟩ hhA y hy, ?_⟩
    exact hcompat h hhA y) with h0 | ht
  · left
    rw [eq_bot_iff]
    intro y hy
    have h1 : eW y ∈ Y.map eW.toMonoidHom := ⟨y, hy, rfl⟩
    rw [h0, mem_bot] at h1
    rw [mem_bot]
    exact eW.injective (h1.trans (map_one eW).symm)
  · right
    rw [eq_top_iff]
    intro y _
    have h1 : eW y ∈ Y.map eW.toMonoidHom := ht ▸ mem_top _
    obtain ⟨y', hy', hyy⟩ := h1
    have : y' = y := eW.injective hyy
    rwa [← this]

end Transport

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem isStronglyQuasithin_centralizer (h : QTNQ T L M) {v : G} (hv : v ∈ qtnqU L M)
    (hv1 : v ≠ 1) : CFSG.IsStronglyQuasithin (centralizer ({v} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer ({v} : Set G) with hK
  have hvK : v ∈ K := mem_centralizer_singleton_iff.mpr rfl
  have hv2 : v ^ 2 = 1 := by
    have := qtnqU_isElementaryAbelian h
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
  set Z : Subgroup K := zpowers ⟨v, hvK⟩ with hZ
  have hZn : Z.Normal := by
    refine ⟨fun a ha k => ?_⟩
    have hc : k * ⟨v, hvK⟩ * k⁻¹ = ⟨v, hvK⟩ := by
      apply Subtype.ext
      have h1 := mem_centralizer_singleton_iff.mp k.2
      change (k : G) * v * (k : G)⁻¹ = v
      rw [h1, mul_inv_cancel_right]
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← conj_zpow, hc]
    exact zpow_mem (mem_zpowers _) n
  have hZ2 : IsPGroup 2 Z := isPGroup_two_of_card_dvd (k := 1) (by
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_dvd_of_pow_eq_one ?_
    exact Subtype.ext hv2)
  have hle := SteinbergCC.le_pCore_of_normal_of_isPGroup hZn hZ2
  refine QuasithinUnique.isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank h.qtke.2.2 ?_
  unfold pCoreOf
  intro hbot
  apply hv1
  have h1 : v ∈ (CFSG.pCore 2 K).map K.subtype := ⟨⟨v, hvK⟩, hle (mem_zpowers _), rfl⟩
  rw [hbot, mem_bot] at h1
  exact h1

theorem explicit_module_selected_witness_Fitting_containment
    (h : QTNQ T L M)
    (hmod : QTNQExplicitModule L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXL : X ≤ L) (hXchar : (X.subgroupOf L).Characteristic)
    (hXRad : X ≤ (CFSG.solvableRadical L).map L.subtype) (hNX : normalizer (X : Set G) = M)
    (hX2 : NoPQuotient 2 X) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) :
    (∀ v ∈ qtnqU L M, IsFrattiniIrreducible X (M ⊓ centralizer {v})) ∧
    ∀ v ∈ qtnqU L M, v ≠ 1 →
      (∃ S : Sylow 2 (centralizer ({v} : Set G)), (S : Subgroup (centralizer ({v} : Set G))) ≤
        (M ⊓ centralizer {v}).subgroupOf (centralizer {v})) →
      (CFSG.fittingSubgroup (centralizer ({v} : Set G) ⧸
          CFSG.pCore 2 (centralizer ({v} : Set G)))).comap
          (QuotientGroup.mk' (CFSG.pCore 2 (centralizer ({v} : Set G)))) ≤
        (M ⊓ centralizer {v}).subgroupOf (centralizer {v}) ∧
      (¬ centralizer {v} ≤ M →
        ⁅(X.subgroupOf (centralizer {v})).map
            (QuotientGroup.mk' (CFSG.pCore 2 (centralizer ({v} : Set G)))),
          CFSG.fittingSubgroup (centralizer ({v} : Set G) ⧸
            CFSG.pCore 2 (centralizer ({v} : Set G)))⁆ = ⊥ ∧
        IsCyclic (CFSG.pCore p (centralizer ({v} : Set G) ⧸
          CFSG.pCore 2 (centralizer ({v} : Set G))))) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hirr : ∀ v ∈ qtnqU L M, IsFrattiniIrreducible X (M ⊓ centralizer {v}) := fun v hv =>
    (isFrattiniIrreducible_inf_centralizer_of_ne_one h hmod hp hp5 hXL hXchar hexp hW hLW
      hv).mono (inf_le_inf_right _ h.l_le)
  refine ⟨hirr, fun v hv hv1 hS => ?_⟩
  set K := centralizer ({v} : Set G) with hK
  have hXM : X ≤ M := hXL.trans h.l_le
  have hXK : X ≤ K := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    obtain ⟨l, hl, rfl⟩ := hXRad hx
    exact NQSetup.radical_commute_qtnqVc h hl (NQSetup.qtnqU_le_qtnqVc h hv)
  have hAK : M ⊓ K ≤ K := inf_le_right
  obtain ⟨hX2', hexp', hrk', hirr'⟩ :=
    subgroupOf_transport hXK hAK hX2 hexp hrk hp.one_lt (hirr v hv)
  have hSQT := isStronglyQuasithin_centralizer h hv hv1
  have hXA' : X.subgroupOf K ≤ (M ⊓ K).subgroupOf K := fun x hx =>
    mem_subgroupOf.mpr (mem_inf.mpr ⟨hXM (mem_subgroupOf.mp hx), hXK (mem_subgroupOf.mp hx)⟩)
  have hNX' : normalizer ((X.subgroupOf K : Subgroup K) : Set K) = (M ⊓ K).subgroupOf K := by
    rw [← subgroupOf_normalizer_eq hXK, hNX]
    ext k
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun hk => ⟨hk, k.2⟩, fun hk => hk.1⟩
  have hXn' : ((X.subgroupOf K).subgroupOf ((M ⊓ K).subgroupOf K)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXA').mpr hNX'.ge
  obtain ⟨-, hB, -, hpart⟩ := Sylow_containing_normalizer_lifts_quotient_Fitting_control
    (fun r hr hr2 => hSQT r hr hr2) hp hp2 hXA' hXn' hS hX2' hexp' hrk' hirr'
  refine ⟨hNX' ▸ hB, fun hKM => ?_⟩
  have hlt : (M ⊓ K).subgroupOf K < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hKM ?_
    intro k hk
    have : (⟨k, hk⟩ : K) ∈ (M ⊓ K).subgroupOf K := htop ▸ mem_top _
    exact (mem_inf.mp this).1
  obtain ⟨-, hcomm, hcyc⟩ := hpart hNX' hlt
  exact ⟨hcomm, hcyc⟩

end CFSG.Quasithin.H13.NQRigid
