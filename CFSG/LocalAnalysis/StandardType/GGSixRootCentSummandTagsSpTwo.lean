module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL

public section

namespace CFSG.StandardType

namespace RCSTSp2

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot OTwoGen RootCentSp RCSTSp
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem quot_equiv_of_disjoint {Q L : Subgroup G} (hLQ : L ≤ normalizer (Q : Set G))
    (hdisj : Disjoint Q L) [(Q.subgroupOf (Q ⊔ L)).Normal] :
    Nonempty (↥(Q ⊔ L) ⧸ Q.subgroupOf (Q ⊔ L) ≃* L) := by
  have hLN : L ≤ Q ⊔ L := le_sup_right
  set f : ↥L →* ↥(Q ⊔ L) ⧸ Q.subgroupOf (Q ⊔ L) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hLN) with hf
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hx' : x ∈ L ⊔ Q := by rwa [sup_comm] at hx
    obtain ⟨l, hl, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hLQ hx'
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hq
  have hfi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨l, hl⟩ h1
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext ((Subgroup.disjoint_def.mp hdisj) h1 hl)
  exact ⟨(MulEquiv.ofBijective f ⟨hfi, hfs⟩).symm⟩

theorem card_sup_of_disjoint [Finite G] {Q L : Subgroup G} (hLQ : L ≤ normalizer (Q : Set G))
    (hdisj : Disjoint Q L) : Nat.card ↥(Q ⊔ L) = Nat.card L * Nat.card Q := by
  have hQN : Q ≤ Q ⊔ L := le_sup_left
  have hQn : (Q.subgroupOf (Q ⊔ L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQN]
    exact sup_le Subgroup.le_normalizer hLQ
  obtain ⟨e⟩ := quot_equiv_of_disjoint hLQ hdisj
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (Q ⊔ L)),
    Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]

theorem comm_mem_iff {X Q : Subgroup G} [(Q.subgroupOf X).Normal] {a b : G} (ha : a ∈ X)
    (hb : b ∈ X) :
    a * b * a⁻¹ * b⁻¹ ∈ Q ↔
      QuotientGroup.mk' (Q.subgroupOf X) ⟨a, ha⟩ * QuotientGroup.mk' (Q.subgroupOf X) ⟨b, hb⟩ =
        QuotientGroup.mk' (Q.subgroupOf X) ⟨b, hb⟩ *
          QuotientGroup.mk' (Q.subgroupOf X) ⟨a, ha⟩ := by
  have e : a * b * a⁻¹ * b⁻¹ ∈ Q ↔ QuotientGroup.mk' (Q.subgroupOf X)
      (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥X)⁻¹ * (⟨b, hb⟩ : ↥X)⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  constructor
  · intro h
    calc _ = (QuotientGroup.mk' (Q.subgroupOf X) ⟨a, ha⟩ *
          QuotientGroup.mk' (Q.subgroupOf X) ⟨b, hb⟩ *
          (QuotientGroup.mk' (Q.subgroupOf X) ⟨a, ha⟩)⁻¹ *
          (QuotientGroup.mk' (Q.subgroupOf X) ⟨b, hb⟩)⁻¹) *
          (QuotientGroup.mk' (Q.subgroupOf X) ⟨b, hb⟩ *
            QuotientGroup.mk' (Q.subgroupOf X) ⟨a, ha⟩) := by group
      _ = _ := by rw [h, one_mul]
  · intro h
    rw [h]
    group

theorem exists_sThree_piece [Finite G] {V R₀ Q : Subgroup G} (hQR : Q ≤ R₀) (hR₀V : R₀ ≤ V)
    (hVR : V ≤ normalizer (R₀ : Set G)) (hQ2 : IsPGroup 2 Q) (hVQ : V ≤ normalizer (Q : Set G))
    [hn : (Q.subgroupOf R₀).Normal] (e : ↥R₀ ⧸ Q.subgroupOf R₀ ≃* Equiv.Perm (Fin 3)) :
    ∃ S, GGRCSLayerSThree V S R₀ Q ∧ ∀ y ∈ R₀, y ^ 3 = 1 → y ∈ S := by
  set f : ↥R₀ →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf R₀))
    with hf
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : f.ker = Q.subgroupOf R₀ := by
    ext x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set S := ((alternatingGroup (Fin 3)).comap f).map R₀.subtype with hS
  refine ⟨S, ⟨Subgroup.map_subtype_le _, hR₀V, hVR, ?_, hQ2, hVQ, ?_, ?_⟩, fun y hy hy3 => ?_⟩
  · intro q hq
    refine ⟨⟨q, hQR hq⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have : f ⟨q, hQR hq⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hfker]
      exact hq
    rw [this]
    exact one_mem _
  · have h1 : Nat.card S = Nat.card ((alternatingGroup (Fin 3)).comap f) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ R₀.subtype_injective).symm.toEquiv
    rw [h1, ggRCSS_card_comap_of_surjective f hfs, ggRCSS_card_alternating_three, hfker]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv
  · intro _
    exact ⟨(QuotientGroup.quotientMulEquivOfEq rfl).trans e⟩
  · refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
    refine ggRCSS_sign_of_pow_three _ ?_
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥R₀) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]

end Helpers

section Structure

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

theorem disjoint_wRadical_levi :
    Disjoint (wRadical F (1 : Fin (n + 3)) 2)
      ((shortBlock F (one_ne_two_fin (n := n))).range ⊔ spCompl12 F n) :=
  (disjoint_wRadical_range_leviHom one_ne_two_fin (a := (0 : F)) one_ne_zero).mono_right
    (sup_le (range_shortBlock_le_range_leviHom one_ne_zero)
      (spCompl12_le_range_leviHom one_ne_zero))

omit [CharP F 2] in
theorem disjoint_shortBlock_spCompl12 :
    Disjoint (shortBlock F (one_ne_two_fin (n := n))).range (spCompl12 F n) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨A, rfl⟩ ht
  have ht' : shortBlock F one_ne_two_fin A ∈
      suppGroup {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t}ᶜ := by
    have : {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t}ᶜ = {t | OffPQ 1 2 t} := by
      ext t
      simp
    rw [this, ← spCompl12_eq_suppGroup]
    exact ht
  exact eq_one_of_isSupp_of_isSupp_compl (shortBlock_mem_suppGroup (n := n) A) ht'

theorem eq_one_of_commute_spCompl12 {t : StatedSp (n + 3) F} (ht : t ∈ spCompl12 F n)
    (h : ∀ t' ∈ spCompl12 F n, t * t' = t' * t) : t = 1 := by
  set e := spCompl12Equiv F n
  have hc : e.symm ⟨t, ht⟩ ∈ center (StatedSp (n + 1) F) := by
    rw [mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (h _ (e g).2).symm
  rw [center_statedSp_eq_bot, mem_bot] at hc
  have := congrArg (fun x => ((e x : spCompl12 F n) : StatedSp (n + 3) F)) hc
  simpa using this

end Structure

section Layer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem disjoint_map_of_injective {U : Type*} [Group U] {ψ : U →* G} (hψ : Function.Injective ψ)
    {A B : Subgroup U} (h : Disjoint A B) : Disjoint (A.map ψ) (B.map ψ) := by
  rw [Subgroup.disjoint_def] at h ⊢
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have : b = a := hψ hab
  rw [h ha (this ▸ hb), map_one]

theorem layer_short_two_three (hK : Nat.card F = 2) (hn : 2 ≤ n)
    (ψ : StatedSp (n + 3) F →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) {r : G}
    (hr : ψ.range ⊓ centralizer {r} =
      ψ.range ⊓ centralizer {ψ (twoCentralElt (n + 3) 1 2 (0 : F) 1)}) :
    GGRCSLayer 3 ψ.range M r := by
  have h12 := one_ne_two_fin (n := n)
  have : Finite (StatedSp (n + 3) F) := by
    have : Finite (GL (Fin (n + 3) ⊕ Fin (n + 3)) F) := inferInstance
    exact Subtype.finite
  obtain ⟨hC, hSQ, hTQ, hST⟩ := centralizer_a2_facts (F := F) (n := n)
  set QW := wRadical F (1 : Fin (n + 3)) 2 with hQW
  set S := (shortBlock F h12).range with hS
  set T := spCompl12 F n with hT
  set X := ggRCSX ψ.range r with hXdef
  have hXU : X = (QW ⊔ (S ⊔ T)).map ψ := by
    change ggOTwoPrime (ψ.range ⊓ centralizer {r}) = _
    rw [hr]
    change ggRCSX ψ.range (ψ (twoCentralElt (n + 3) 1 2 0 1)) = _
    rw [ggRCSX_eq_map_centralizer ψ hψ (centralizer_twoCentralElt_le_ggOTwoPrime h12), hC]
  set V := M ⊓ centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  set Q := QW.map ψ with hQdef
  set Sψ := S.map ψ with hSψ
  set Tψ := T.map ψ with hTψ
  have hX : X = Q ⊔ (Sψ ⊔ Tψ) := by rw [hXU, Subgroup.map_sup, Subgroup.map_sup]
  set D := CFSG.Quasithin.perfectCore X with hDdef
  have hD : D = Q ⊔ Tψ := by
    rw [hDdef, hXU, ← CFSG.Quasithin.map_perfectCore, ← hC,
      perfectCore_centralizer_twoCentralElt_two hK hn (Or.inl rfl), Subgroup.map_sup]
  have hVD : V ≤ normalizer (D : Set G) :=
    hVX.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
  have hDX : D ≤ X := CFSG.Quasithin.perfectCore_le _
  have hQ2 : IsPGroup 2 Q := (isPGroup_wRadical h12).map ψ
  have hSψQ : Sψ ≤ normalizer (Q : Set G) := ggRCST_map_le_normalizer ψ hSQ
  have hTψQ : Tψ ≤ normalizer (Q : Set G) := ggRCST_map_le_normalizer ψ hTQ
  have hSψT : Sψ ≤ centralizer (Tψ : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hST hs)) t ht]
  have hTψS : Tψ ≤ centralizer (Sψ : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro s hs
    exact ((mem_centralizer_iff.mp (hSψT hs)) t ht).symm
  have hdQL : Disjoint Q (Sψ ⊔ Tψ) := by
    rw [hSψ, hTψ, ← Subgroup.map_sup]
    exact disjoint_map_of_injective hψ disjoint_wRadical_levi
  have hdST : Disjoint Sψ Tψ := disjoint_map_of_injective hψ disjoint_shortBlock_spCompl12
  have hLQ : Sψ ⊔ Tψ ≤ normalizer (Q : Set G) := sup_le hSψQ hTψQ
  have hTq : CFSG.IsQuasisimple Tψ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((spCompl12Equiv F n).trans (T.equivMapOfInjective ψ hψ))
      (CFSG.LieType.Universal.Symplectic.isQuasisimple (n + 1) F (by omega)
        (Or.inr (Or.inr ⟨hK, by omega⟩)))
  have hTcen : ∀ t ∈ Tψ, (∀ t' ∈ Tψ, t * t' = t' * t) → t = 1 := by
    rintro _ ⟨t, ht, rfl⟩ h
    rw [eq_one_of_commute_spCompl12 ht fun t' ht' => hψ (by
      rw [map_mul, map_mul]
      exact h _ ⟨t', ht', rfl⟩), map_one]
  have h3T : 3 ∣ Nat.card Tψ := by
    have h6 : Nat.card (longRootSp2 F (n + 3) 0) = 6 := by
      rw [longRootSp2, Nat.card_congr (MonoidHom.ofInjective (longBlock_injective 0)).symm.toEquiv,
        CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK]
      norm_num
    have h1 : Nat.card (longRootSp2 F (n + 3) 0) ∣ Nat.card T :=
      Subgroup.card_dvd_of_le (longRootSp2_le_spCompl12 n)
    rw [h6] at h1
    rw [hTψ, Nat.card_congr (T.equivMapOfInjective ψ hψ).symm.toEquiv]
    exact dvd_trans (by norm_num) h1
  have hQD : CFSG.Assembly.pCoreOf 2 D = Q := by
    rw [hD]
    refine ggRCST_pCoreOf_eq rfl hQ2 hTψQ ?_
    intro N hNT hN2 hTN
    have hNn : (N.subgroupOf Tψ).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNT]
      exact hTN
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hTq hNn with h | h
    · exfalso
      have h2 : IsPGroup 2 ↥Tψ := fun x => by
        have hx : x ∈ N.subgroupOf Tψ := h ▸ Subgroup.mem_top x
        obtain ⟨k, hk⟩ := hN2 ⟨x, hx⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      have : Nontrivial ↥Tψ := CFSG.LocalCores.isQuasisimple_nontrivial hTq
      have : Group.IsPerfect ↥Tψ := hTq.1
      exact Group.IsPerfect.not_isNilpotent _ h2.isNilpotent
    · rw [eq_bot_iff]
      intro x hx
      have hxT := hNT hx
      have hxc := h (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hxT⟩ : ↥Tψ) ∈ N.subgroupOf Tψ)
      rw [Subgroup.mem_bot]
      refine hTcen x hxT fun t' ht' => ?_
      exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxc) ⟨t', ht'⟩)).symm
  have hVQ : V ≤ normalizer (Q : Set G) := by
    rw [← hQD]
    exact hVD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D)
  have hQX : Q ≤ X := by rw [hX]; exact le_sup_left
  have hSX : Sψ ≤ X := by rw [hX]; exact le_sup_left.trans le_sup_right
  have hTX : Tψ ≤ X := by rw [hX]; exact le_sup_right.trans le_sup_right
  have hXQ : X ≤ normalizer (Q : Set G) := by rw [hX]; exact sup_le le_normalizer hLQ
  have hQn : (Q.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
    exact hXQ
  have hdQT : Disjoint Q Tψ := hdQL.mono_right le_sup_right
  have hSTN : Sψ ≤ normalizer (Tψ : Set G) := fun g hg => centralizer_le_normalizer _ (hSψT hg)
  have hdec : ∀ x ∈ X, ∃ s ∈ Sψ, ∃ t ∈ Tψ, ∃ q ∈ Q, x = s * t * q := by
    intro x hx
    rw [hX, sup_comm] at hx
    obtain ⟨l, hl, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hLQ hx
    obtain ⟨s', hs', t, ht, rfl⟩ := ggRCST_exists_of_mem_sup hSTN hl
    exact ⟨s', hs', t, ht, q, hq, rfl⟩
  set φ := QuotientGroup.mk' (Q.subgroupOf X) with hφ
  have hφq : ∀ q (hq : q ∈ Q), φ ⟨q, hQX hq⟩ = 1 := fun q hq => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq
  have hφST : ∀ s (hs : s ∈ Sψ) t (ht : t ∈ Tψ),
      φ ⟨s, hSX hs⟩ * φ ⟨t, hTX ht⟩ = φ ⟨t, hTX ht⟩ * φ ⟨s, hSX hs⟩ := by
    intro s hs t ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (show s * t = t * s from (mem_centralizer_iff.mp (hTψS ht)) s hs)
  have hR₀ : ∀ x, x ∈ Q ⊔ Sψ ↔ x ∈ X ∧ ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ Q := by
    intro x
    constructor
    · intro hx
      have hxX : x ∈ X := sup_le hQX hSX hx
      refine ⟨hxX, fun d hd => ?_⟩
      have hdX := hDX hd
      rw [comm_mem_iff hxX hdX]
      rw [sup_comm] at hx
      obtain ⟨s, hs, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hSψQ hx
      rw [hD] at hd
      have hd' : d ∈ Tψ ⊔ Q := by rwa [sup_comm] at hd
      obtain ⟨t, ht, q', hq', rfl⟩ := ggRCST_exists_of_mem_sup hTψQ hd'
      have e1 : (⟨s * q, hxX⟩ : ↥X) = ⟨s, hSX hs⟩ * ⟨q, hQX hq⟩ := rfl
      have e2 : (⟨t * q', hdX⟩ : ↥X) = ⟨t, hTX ht⟩ * ⟨q', hQX hq'⟩ := rfl
      rw [e1, e2, map_mul, map_mul, hφq q hq, hφq q' hq', mul_one, mul_one]
      exact hφST s hs t ht
    · rintro ⟨hxX, hxD⟩
      obtain ⟨s, hs, t, ht, q, hq, rfl⟩ := hdec _ hxX
      have ht1 : t = 1 := by
        refine hTcen t ht fun t' ht' => ?_
        have h1 := hxD t' (by rw [hD]; exact Subgroup.mem_sup_right ht')
        rw [comm_mem_iff hxX (hTX ht')] at h1
        have e1 : (⟨s * t * q, hxX⟩ : ↥X) = ⟨s, hSX hs⟩ * ⟨t, hTX ht⟩ * ⟨q, hQX hq⟩ := rfl
        rw [e1, map_mul, map_mul, hφq q hq, mul_one] at h1
        have hc := hφST s hs t' ht'
        have h2 : φ ⟨t, hTX ht⟩ * φ ⟨t', hTX ht'⟩ = φ ⟨t', hTX ht'⟩ * φ ⟨t, hTX ht⟩ := by
          apply mul_left_cancel (a := φ ⟨s, hSX hs⟩)
          calc φ ⟨s, hSX hs⟩ * (φ ⟨t, hTX ht⟩ * φ ⟨t', hTX ht'⟩)
              = φ ⟨s, hSX hs⟩ * φ ⟨t, hTX ht⟩ * φ ⟨t', hTX ht'⟩ := (mul_assoc _ _ _).symm
            _ = φ ⟨t', hTX ht'⟩ * (φ ⟨s, hSX hs⟩ * φ ⟨t, hTX ht⟩) := h1
            _ = (φ ⟨t', hTX ht'⟩ * φ ⟨s, hSX hs⟩) * φ ⟨t, hTX ht⟩ := (mul_assoc _ _ _).symm
            _ = (φ ⟨s, hSX hs⟩ * φ ⟨t', hTX ht'⟩) * φ ⟨t, hTX ht⟩ := by rw [hc]
            _ = φ ⟨s, hSX hs⟩ * (φ ⟨t', hTX ht'⟩ * φ ⟨t, hTX ht⟩) := mul_assoc _ _ _
        have h3 := (comm_mem_iff (Q := Q) (hTX ht) (hTX ht')).mpr h2
        have h4 : t * t' * t⁻¹ * t'⁻¹ ∈ Tψ :=
          Tψ.mul_mem (Tψ.mul_mem (Tψ.mul_mem ht ht') (Tψ.inv_mem ht)) (Tψ.inv_mem ht')
        have h5 := (Subgroup.disjoint_def.mp hdQT) h3 h4
        calc t * t' = (t * t' * t⁻¹ * t'⁻¹) * (t' * t) := by group
          _ = t' * t := by rw [h5, one_mul]
      rw [ht1, mul_one]
      exact mul_mem (mem_sup_right hs) (mem_sup_left hq)
  have hVR : V ≤ normalizer ((Q ⊔ Sψ : Subgroup G) : Set G) := by
    have key : ∀ v ∈ V, ∀ x ∈ Q ⊔ Sψ, v * x * v⁻¹ ∈ Q ⊔ Sψ := by
      intro v hv x hx
      rw [hR₀] at hx ⊢
      refine ⟨(mem_normalizer_iff.mp (hVX hv) x).mp hx.1, fun d hd => ?_⟩
      have hd' : v⁻¹ * d * v⁻¹⁻¹ ∈ D := (mem_normalizer_iff.mp (hVD (V.inv_mem hv)) d).mp hd
      rw [inv_inv] at hd'
      have h2 := (mem_normalizer_iff.mp (hVQ hv) _).mp (hx.2 _ hd')
      convert h2 using 1
      group
    intro v hv
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key v hv x, fun h => ?_⟩
    have := key v⁻¹ (V.inv_mem hv) _ h
    rwa [inv_inv, show v⁻¹ * (v * x * v⁻¹) * v = x by group] at this
  have hR₀V : Q ⊔ Sψ ≤ V := (sup_le hQX hSX).trans hXV
  have hQR : Q ≤ Q ⊔ Sψ := le_sup_left
  have hQnR : (Q.subgroupOf (Q ⊔ Sψ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQR]
    exact sup_le le_normalizer hSψQ
  obtain ⟨eS⟩ := quot_equiv_of_disjoint hSψQ (hdQL.mono_right le_sup_left)
  obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := F) hK
  have e : ↥(Q ⊔ Sψ) ⧸ Q.subgroupOf (Q ⊔ Sψ) ≃* Equiv.Perm (Fin 3) :=
    ((eS.trans (S.equivMapOfInjective ψ hψ).symm).trans
      (MonoidHom.ofInjective (shortBlock_injective h12)).symm).trans e3
  obtain ⟨Sp, hSp, hSpcov⟩ := exists_sThree_piece hQR hR₀V hVR hQ2 hVQ e
  have hDpiece : GGRCSLayerPiece 3 V D := by
    refine Or.inl ⟨Q, hDX.trans hXV, ggIsSubnormal_of_normal (hDX.trans hXV)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hDX.trans hXV)).mpr hVD),
      CFSG.Quasithin.perfectCore_perfect _, ?_, by rw [hD]; exact le_sup_left, hQ2, hVQ, ?_⟩
    · exact dvd_trans h3T (Subgroup.card_dvd_of_le (by rw [hD]; exact le_sup_right))
    · intro _
      exact ggRCST_isQuasisimple_quot Nat.prime_three (by norm_num) hTψQ
        (by rw [hD]; exact le_sup_right) hD.le hQ2 inf_le_right hTq h3T
  refine ⟨{D, Sp}, ?_, fun y hy hy3 => ?_⟩
  · rintro P (rfl | rfl)
    · exact hDpiece
    · exact Or.inr ⟨rfl, Q ⊔ Sψ, Q, hSp⟩
  · obtain ⟨s, hs, t, ht, q, hq, rfl⟩ := hdec y hy
    have hs3 : s ^ 3 = 1 := by
      have h1 : φ ⟨s * t * q, hy⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨s * t * q, hy⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
        rw [this, map_one]
      have e1 : (⟨s * t * q, hy⟩ : ↥X) = ⟨s, hSX hs⟩ * ⟨t, hTX ht⟩ * ⟨q, hQX hq⟩ := rfl
      rw [e1, map_mul, map_mul, hφq q hq, mul_one, (Commute.mul_pow (hφST s hs t ht) 3),
        ← map_pow, ← map_pow, ← map_mul] at h1
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      have h2 : s ^ 3 * t ^ 3 ∈ Q := by simpa using h1
      have h3 : s ^ 3 * t ^ 3 ∈ Sψ ⊔ Tψ :=
        mul_mem (mem_sup_left (pow_mem hs 3)) (mem_sup_right (pow_mem ht 3))
      have h4 := (Subgroup.disjoint_def.mp hdQL) h2 h3
      have h5 : s ^ 3 = (t ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h4
      have h6 : s ^ 3 ∈ Tψ := h5 ▸ Tψ.inv_mem (pow_mem ht 3)
      exact (Subgroup.disjoint_def.mp hdST) (pow_mem hs 3) h6
    have hsSp : s ∈ Sp := hSpcov s (mem_sup_right hs) hs3
    have htqD : t * q ∈ D := by
      rw [hD]
      exact mul_mem (mem_sup_right ht) (mem_sup_left hq)
    have hle₁ : Sp ≤ sSup ({D, Sp} : Set (Subgroup G)) := le_sSup (by simp)
    have hle₂ : D ≤ sSup ({D, Sp} : Set (Subgroup G)) := le_sSup (by simp)
    rw [mul_assoc]
    exact mul_mem (hle₁ hsSp) (hle₂ htqD)

theorem layer_short_two_three_gen (hK : Nat.card F = 2) (hn : 2 ≤ n)
    (ψ : StatedSp (n + 3) F →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) {r : G}
    {h : StatedSp (n + 3) F} {i j : Fin (n + 3)} (hij : i ≠ j)
    (hr : ψ.range ⊓ centralizer {r} =
      ψ.range ⊓ centralizer {ψ (h * twoCentralElt (n + 3) i j (0 : F) 1 * h⁻¹)}) :
    GGRCSLayer 3 ψ.range M r := by
  obtain ⟨g, hg⟩ := exists_conj_one_two (F := F) hij
  have hrange : (ψ.comp (MulAut.conj (h * g)).toMonoidHom).range = ψ.range :=
    range_comp_conj ψ (h * g)
  have h1 : ψ (h * twoCentralElt (n + 3) i j (0 : F) 1 * h⁻¹) =
      (ψ.comp (MulAut.conj (h * g)).toMonoidHom) (twoCentralElt (n + 3) 1 2 0 1) := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
    congr 1
    group
  have key := layer_short_two_three hK hn (ψ.comp (MulAut.conj (h * g)).toMonoidHom)
    (comp_conj_injective hψ _) (M := M) (by rw [hrange]; exact hG₀M) (by rw [hrange]; exact hM)
    (r := r) (by rw [hrange, ← h1]; exact hr)
  rwa [hrange] at key

end Layer

end RCSTSp2

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGSpSixEightRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (ψ : StatedSp n (GaloisField 2 1) →* G),
    (n = 3 ∨ n = 4) → Function.Injective ψ → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
      ¬ GGTwoLocalRankFour 3 (Subgroup.normalizer (ψ.range : Set G))

theorem ggRootCentLayerSpShortTwoThreeInput_of_rank (hrank : GGSpSixEightRankInput) :
    GGRootCentLayerSpShortTwoThreeInput := by
  intro G _ _ n ψ hn hψ hC h4 r _ hsh
  by_cases hn5 : 5 ≤ n
  · obtain ⟨h, i, j, hij, hrc⟩ := hsh
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 one_ne_zero, pow_one]
    exact RCSTSp2.layer_short_two_three_gen hK (by omega) ψ hψ Subgroup.le_normalizer le_rfl hij
      hrc
  · exact absurd h4 (hrank G n ψ (by omega) hψ hC)

theorem ggRootCentLayerTag_PSp_of_rank (hrank : GGSpSixEightRankInput) :
    GGRootCentLayerTag .PSp :=
  ggRootCentLayerTag_PSp_of_three (ggRootCentLayerSpShortTwoThreeInput_of_rank hrank)

end Tag

end CFSG.StandardType
