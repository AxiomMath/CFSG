module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.FFModules (fixSub mem_fixSub)

variable {G : Type} [Group G] [Finite G]

theorem uc22br_gt_conj_mem {M V : Subgroup G} (hV : M ≤ normalizer (V : Set G)) {m v : G}
    (hm : m ∈ M) (hv : v ∈ V) : m * v * m⁻¹ ∈ V :=
  (mem_normalizer_iff.1 (hV hm) v).1 hv

theorem uc22br_gt_centralizesMod_bot_iff (V : Subgroup G) (m : G) :
    CentralizesMod ⊥ V m ↔ m ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 : m * v * m⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.1 (h v hv)
    have h3 : m * v * m⁻¹ = v := mul_inv_eq_one.1 h1
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  · intro h v hv
    rw [Subgroup.mem_bot, ← h v hv]
    group

theorem uc22br_gt_mk_eq_one_iff {M V : Subgroup G} (hV : M ≤ normalizer (V : Set G)) (m : ↥M) :
    (QuotientGroup.mk m : MBar M V) = 1 ↔ (m : G) ∈ centralizer (V : Set G) := by
  haveI := kerAct_normal M V hV
  rw [QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self, kerAct, Subgroup.mem_subgroupOf]

theorem uc22br_gt_orderOf_mk_eq_two_iff {M V : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (m : ↥M) :
    orderOf (QuotientGroup.mk m : MBar M V) = 2 ↔
      ¬ CentralizesMod ⊥ V (m : G) ∧ CentralizesMod ⊥ V ((m : G) * m) := by
  have h1 : CentralizesMod ⊥ V (m : G) ↔ (QuotientGroup.mk m : MBar M V) = 1 := by
    rw [uc22br_gt_centralizesMod_bot_iff, uc22br_gt_mk_eq_one_iff hV]
  have h2 : CentralizesMod ⊥ V ((m : G) * m) ↔ (QuotientGroup.mk m : MBar M V) ^ 2 = 1 := by
    rw [uc22br_gt_centralizesMod_bot_iff, ← QuotientGroup.mk_pow, uc22br_gt_mk_eq_one_iff hV]
    simp [pow_two]
  rw [orderOf_eq_prime_iff, h1, h2]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨b, a⟩
  · rintro ⟨a, b⟩
    exact ⟨b, a⟩

theorem uc22br_gt_even_iff_exists_involution (M V : Subgroup G) :
    Even (Nat.card (MBar M V)) ↔ ∃ t : MBar M V, orderOf t = 2 := by
  constructor
  · intro h
    exact exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 h)
  · rintro ⟨t, ht⟩
    have h := _root_.orderOf_dvd_natCard t
    rw [ht] at h
    exact even_iff_two_dvd.2 h

theorem uc22br_gt_mem_fixSub_zpowers {K : Type} [Group K] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) K W) (t : K) (w : W) :
    w ∈ fixSub ρ (zpowers t) ↔ ρ t w = w := by
  refine ⟨fun h => mem_fixSub.1 h t (mem_zpowers t), fun h => mem_fixSub.2 fun a ha => ?_⟩
  let S : Subgroup K :=
    { carrier := {g | ρ g w = w}
      mul_mem' := fun {g h} hg hh => by
        change ρ (g * h) w = w
        rw [map_mul, Module.End.mul_apply, hh, hg]
      one_mem' := by change ρ 1 w = w; rw [map_one, Module.End.one_apply]
      inv_mem' := fun {g} hg => by
        change ρ g⁻¹ w = w
        conv_lhs => rw [← hg]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact (zpowers_le.2 (show t ∈ S from h)) ha

theorem uc22br_gt_conj_iff (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod)
    (hc : ConjModule M V e ρ) (m : ↥M) (v : ↥V) :
    (m : G) * v * (m : G)⁻¹ = v ↔
      ρ (QuotientGroup.mk m) (Multiplicative.toAdd (e v)) = Multiplicative.toAdd (e v) := by
  have hmem : (m : G) * v * (m : G)⁻¹ ∈ V := uc22br_gt_conj_mem hV m.2 v.2
  have h1 := hc m v ⟨(m : G) * v * (m : G)⁻¹, hmem⟩ rfl
  constructor
  · intro h
    have h2 : (⟨(m : G) * v * (m : G)⁻¹, hmem⟩ : ↥V) = v := Subtype.ext h
    rw [h2] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  · intro h
    rw [h] at h1
    have h2 : (⟨(m : G) * v * (m : G)⁻¹, hmem⟩ : ↥V) = v := e.injective h1
    exact congrArg Subtype.val h2

theorem uc22br_gt_card_centMod (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod)
    (hc : ConjModule M V e ρ) (m : ↥M) :
    Nat.card (centMod ⊥ V (m : G)) =
      Nat.card (fixSub ρ (zpowers (QuotientGroup.mk m : MBar M V))) := by
  let ψ : Vmod → G := fun w => ((e.symm (Multiplicative.ofAdd w) : ↥V) : G)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 : e.symm (Multiplicative.ofAdd a) = e.symm (Multiplicative.ofAdd b) := Subtype.ext hab
    exact Multiplicative.ofAdd.injective (e.symm.injective h1)
  have hmemC : ∀ g : G, g ∈ centMod ⊥ V (m : G) ↔ g ∈ V ∧ (m : G) * g * (m : G)⁻¹ = g := by
    intro g
    simp only [centMod, Set.mem_setOf_eq, Subgroup.mem_bot, mul_inv_eq_one]
  have himg : ψ '' (fixSub ρ (zpowers (QuotientGroup.mk m : MBar M V)) : Set Vmod) =
      centMod ⊥ V (m : G) := by
    ext g
    rw [hmemC g]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : ρ (QuotientGroup.mk m) w = w := (uc22br_gt_mem_fixSub_zpowers ρ _ w).1 hw
      set v : ↥V := e.symm (Multiplicative.ofAdd w) with hv
      have hev : Multiplicative.toAdd (e v) = w := by simp [hv]
      refine ⟨v.2, (uc22br_gt_conj_iff M V hV e ρ hc m v).2 ?_⟩
      rw [hev]
      exact hw'
    · rintro ⟨hgV, hg⟩
      refine ⟨Multiplicative.toAdd (e ⟨g, hgV⟩), ?_, ?_⟩
      · rw [SetLike.mem_coe, uc22br_gt_mem_fixSub_zpowers]
        exact (uc22br_gt_conj_iff M V hV e ρ hc m ⟨g, hgV⟩).1 hg
      · simp [ψ]
  calc Nat.card (centMod ⊥ V (m : G))
      = Nat.card (ψ '' (fixSub ρ (zpowers (QuotientGroup.mk m : MBar M V)) : Set Vmod)) := by
        rw [himg]
    _ = Nat.card (fixSub ρ (zpowers (QuotientGroup.mk m : MBar M V)) : Set Vmod) :=
        Nat.card_image_of_injective hψ _
    _ = _ := rfl

theorem uc22br_gt_card_V (V : Subgroup G) {Vmod : Type} [AddCommGroup Vmod]
    [Module (ZMod 2) Vmod] [Finite Vmod] (e : ↥V ≃* Multiplicative Vmod) :
    Nat.card ↥V = 2 ^ Module.finrank (ZMod 2) Vmod := by
  rw [Nat.card_congr e.toEquiv, ← CFSG.RankThree.FFModules.card_eq_two_pow_finrank']
  exact Nat.card_congr Multiplicative.toAdd

theorem uc22br_gt_card_cond (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod)
    (hc : ConjModule M V e ρ) (m : ↥M) (n : ℕ) :
    2 ^ (n + 1) * Nat.card (centMod ⊥ V (m : G)) ≤ Nat.card ↥V ↔
      n < Module.finrank (ZMod 2)
        (Vmod ⧸ fixSub ρ (zpowers (QuotientGroup.mk m : MBar M V))) := by
  have hq := Submodule.finrank_quotient_add_finrank
    (fixSub ρ (zpowers (QuotientGroup.mk m : MBar M V)))
  rw [uc22br_gt_card_centMod M V hV e ρ hc m, CFSG.RankThree.FFModules.card_eq_two_pow_finrank,
    uc22br_gt_card_V V e, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
  omega

theorem mbarGT_bot_iff_lt_mGV (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    (hel : CFSG.Open.IsElemAbelian 2 V)
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod)
    (hc : ConjModule M V e ρ) (n : ℕ) :
    MBarGT M ⊥ V n ↔ n < F05.mGV ρ := by
  clear hel
  have hA : (∀ m ∈ M, ¬ CentralizesMod ⊥ V m → CentralizesMod ⊥ V (m * m) →
        2 ^ (n + 1) * Nat.card (centMod ⊥ V m) ≤ Nat.card V) ↔
      ∀ t : MBar M V, orderOf t = 2 →
        n < Module.finrank (ZMod 2) (Vmod ⧸ fixSub ρ (zpowers t)) := by
    constructor
    · intro h t ht
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective t
      obtain ⟨h1, h2⟩ := (uc22br_gt_orderOf_mk_eq_two_iff hV m).1 ht
      exact (uc22br_gt_card_cond M V hV e ρ hc m n).1 (h m m.2 h1 h2)
    · intro h m hm h1 h2
      exact (uc22br_gt_card_cond M V hV e ρ hc ⟨m, hm⟩ n).2
        (h _ ((uc22br_gt_orderOf_mk_eq_two_iff hV ⟨m, hm⟩).2 ⟨h1, h2⟩))
  unfold MBarGT F05.mGV
  by_cases hev : Even (Nat.card (MBar M V))
  · rw [if_pos hev]
    obtain ⟨t0, ht0⟩ := (uc22br_gt_even_iff_exists_involution M V).1 hev
    have hS : {k | ∃ t : MBar M V, orderOf t = 2 ∧
        k = Module.finrank (ZMod 2) (Vmod ⧸ fixSub ρ (zpowers t))}.Nonempty :=
      ⟨_, t0, ht0, rfl⟩
    have hlt : n < sInf {k | ∃ t : MBar M V, orderOf t = 2 ∧
        k = Module.finrank (ZMod 2) (Vmod ⧸ fixSub ρ (zpowers t))} ↔
        ∀ t : MBar M V, orderOf t = 2 →
          n < Module.finrank (ZMod 2) (Vmod ⧸ fixSub ρ (zpowers t)) := by
      constructor
      · intro h t ht
        exact lt_of_lt_of_le h (Nat.sInf_le ⟨t, ht, rfl⟩)
      · intro h
        obtain ⟨t, ht, hk⟩ := Nat.sInf_mem hS
        rw [hk]
        exact h t ht
    refine (and_iff_left_of_imp fun _ hall => ?_).trans (hA.trans hlt.symm)
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective t0
    obtain ⟨h1, h2⟩ := (uc22br_gt_orderOf_mk_eq_two_iff hV m).1 ht0
    exact absurd (hall m m.2 h2) h1
  · rw [if_neg hev]
    have hno : ∀ t : MBar M V, orderOf t ≠ 2 := fun t ht =>
      hev ((uc22br_gt_even_iff_exists_involution M V).2 ⟨t, ht⟩)
    have hall : ∀ m ∈ M, CentralizesMod ⊥ V (m * m) → CentralizesMod ⊥ V m := by
      intro m hm h
      by_contra h'
      exact hno _ ((uc22br_gt_orderOf_mk_eq_two_iff hV ⟨m, hm⟩).2 ⟨h', h⟩)
    have hfin : 2 ^ (n + 1) * Nat.card (⊥ : Subgroup G) ≤ Nat.card ↥V ↔
        n < Module.finrank (ZMod 2) Vmod := by
      rw [Subgroup.card_bot, mul_one, uc22br_gt_card_V V e,
        Nat.pow_le_pow_iff_right (by norm_num)]
      omega
    constructor
    · rintro ⟨-, h2⟩
      exact hfin.1 (h2 hall)
    · intro h
      refine ⟨fun m hm h1 h2 => ?_, fun _ => hfin.2 h⟩
      exact absurd ((uc22br_gt_orderOf_mk_eq_two_iff hV ⟨m, hm⟩).2 ⟨h1, h2⟩) (hno _)

end CFSG.LocalAnalysis.UniquenessCase.UC22
