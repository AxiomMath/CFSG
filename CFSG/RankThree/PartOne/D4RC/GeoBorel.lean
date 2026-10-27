module

public import CFSG.RankThree.PartOne.D4RC.Dichotomy
public import CFSG.LieType.HighestRoot.GenModels

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.Timmesfeld.ARS
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

noncomputable abbrev lineN (σ : K →+* K) : Subgroup (twistedGroup σ) :=
  Xh σ ⊔ twistedRootGroup σ (rt 3)

noncomputable abbrev lineB (σ : K →+* K) : Subgroup (twistedGroup σ) :=
  Xh σ ⊔ twistedRootGroup σ (rt 0)

theorem rcg_conjSub_sup {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    conjSub (A ⊔ B) g = conjSub A g ⊔ conjSub B g :=
  Subgroup.map_sup _ _ _

theorem rcg_commuting_self {t : ℕ} (ht : t < 12) :
    Commuting (twistedRootGroup σ (rt t)) (twistedRootGroup σ (rt t)) := fun _ ha _ hb =>
  Subtype.ext_iff.2 (commute_of_mem_twistedRootSubgroupD4 σ (isRoot_rt ht)
    (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb)).eq

theorem rcg_Uhat_conj_lineN [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {u : twistedGroup σ}
    (hu : (u : adjointGroup d4 K) ∈ Uhat σ) {g : twistedGroup σ} (hg : g ∈ lineN σ) :
    u * g * u⁻¹ ∈ lineN σ := by
  have hc : ∀ a ∈ Xh σ, ∀ b ∈ twistedRootGroup σ (rt 3), Commute a b :=
    fun a ha b hb => rcg_commuting_pos hσ (t := 3) (Or.inr rfl) a ha b hb
  obtain ⟨a, ha, b, hb, rfl⟩ := rcg_exists_mul_of_mem_sup hc hg
  obtain ⟨c, hc0, -, -, hcu⟩ := exists_ordT hσ hu
  obtain ⟨d, hdσ, hbd⟩ := (rcg_mem_XNg hσ b).1 hb
  have hw : σ (c 0 * d) = c 0 * d := by rw [map_mul, hc0, hdσ]
  have hwmem : xHg hσ (c 0 * d) hw ∈ Xh σ := xHg_mem hσ _ hw
  have hbw : u * b * u⁻¹ = b * xHg hσ (c 0 * d) hw := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcu, hbd]
    exact conj_xN σ c d
  have hau : u * a * u⁻¹ = a := (rcg_commute_Uhat_Xh hσ hu ha).mul_inv_cancel
  have e : u * (a * b) * u⁻¹ = (a * xHg hσ (c 0 * d) hw) * b := by
    rw [show u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) by group, hau, hbw, mul_assoc,
      ← (hc _ hwmem b hb).eq]
  rw [e]
  exact Subgroup.mul_mem_sup ((Xh σ).mul_mem ha hwmem) hb

theorem rcg_posUnipotent_le_normalizer_lineN [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    posUnipotent (twistedDatum σ) ≤ Subgroup.normalizer (lineN σ : Set (twistedGroup σ)) := by
  refine le_normalizer_of_conjSub_le fun u hu => ?_
  have hu' : (u : adjointGroup d4 K) ∈ Uhat σ := by
    rw [posUnipotent_twisted] at hu
    exact Subgroup.mem_subgroupOf.1 hu
  rintro _ ⟨g, hg, rfl⟩
  exact rcg_Uhat_conj_lineN hσ hu' hg

theorem rcg_borel_le_normalizer_lineN [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    borel (twistedDatum σ) (hHat σ) ≤ Subgroup.normalizer (lineN σ : Set (twistedGroup σ)) := by
  refine sup_le ?_ (rcg_posUnipotent_le_normalizer_lineN hσ)
  intro t ht
  have h7 := conjSub_of_mem_normalizer (Tt_normalizes σ (isRoot_rt (by norm_num : 7 < 12)) ht)
  have h3 := conjSub_of_mem_normalizer (Tt_normalizes σ (isRoot_rt (by norm_num : 3 < 12)) ht)
  exact conjSub_eq_self_iff.1 (by rw [rcg_conjSub_sup, h7, h3])

theorem rcg_conj_nHat_lines [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    conjSub (Xh σ) (nHat σ (ng 1)) = Xh σ ∧
      conjSub (lineN σ) (nHat σ (ng 1)) = lineB σ ∧
      conjSub (lineB σ) (nHat σ (ng 1)) = lineN σ := by
  obtain ⟨r10, r13, -, -, -, r17⟩ := rcg_refl_facts
  have hE := rcg_conj_nHat hσ (ng 1) (by norm_num) r17
  have h3 := rcg_conj_nHat hσ (ng 1) (by norm_num) r13
  have h0 := rcg_conj_nHat hσ (ng 1) (by norm_num) r10
  refine ⟨hE, ?_, ?_⟩
  · rw [rcg_conjSub_sup, hE, h3]
  · rw [rcg_conjSub_sup, hE, h0]

theorem rcg_lineN_ne_lineB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) : lineN σ ≠ lineB σ := by
  intro h
  have hX0 : twistedRootGroup σ (rt 0) ≤ lineN σ := h ▸ le_sup_right
  have h13 : Commuting (Xh σ) (twistedRootGroup σ (rt 3)) :=
    rcg_commuting_pos hσ (t := 3) (Or.inr rfl)
  have hab : Commuting (lineN σ) (lineN σ) :=
    Commuting.sup_left (Commuting.sup_right (rcg_commuting_self (σ := σ) (by norm_num)) h13)
      (Commuting.sup_right h13.symm (rcg_commuting_self (σ := σ) (by norm_num)))
  have hc : Commuting (twistedRootGroup σ (rt 0)) (twistedRootGroup σ (rt 3)) :=
    hab.mono hX0 le_sup_right
  have hbot := commuting_iff_commutator_eq_bot.1 hc
  rw [rcg_commutator_Xp0_Xp3 hσ] at hbot
  exact rcg_ne_bot hσ (rcg_Xh_mem (σ := σ)) hbot

theorem rcg_ht_rt1 : 0 < ht (rt 1) := by decide +kernel

theorem rcg_stab_le_borel [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {g : twistedGroup σ}
    (hE : conjSub (Xh σ) g = Xh σ) (hV : conjSub (lineN σ) g = lineN σ) :
    g ∈ borel (twistedDatum σ) (hHat σ) := by
  have h1 : xHg hσ 1 (map_one σ) ∈ Xh σ := xHg_mem hσ 1 (map_one σ)
  have h2 : g * xHg hσ 1 (map_one σ) * g⁻¹ ∈ conjSub (Xh σ) g := ⟨_, h1, rfl⟩
  rw [hE] at h2
  have h4 : (g : adjointGroup d4 K) * xH 1 * (g : adjointGroup d4 K)⁻¹ ∈ Upt σ := by
    have h3 : ((g * xHg hσ 1 (map_one σ) * g⁻¹ : twistedGroup σ) : adjointGroup d4 K) ∈
        twistedRootSubgroupD4 σ (rt 7) := h2
    exact Subgroup.mem_sup_left h3
  rcases bruhat_stab_h_tw hσ one_ne_zero (map_one σ) h4 with hB | ⟨b, hb, u, hu, rfl⟩
  · exact hB
  · exfalso
    have hr1 : rt 1 ∈ (twistedDatum σ).roots := by
      rw [twistedDatum_roots]
      exact isRoot_rt (by norm_num)
    have hub : u ∈ borel (twistedDatum σ) (hHat σ) :=
      posUnipotent_le_borel (rootGroup_le_posUnipotent hr1 rcg_ht_rt1 hu)
    have e1 : conjSub (lineN σ) b = lineN σ :=
      conjSub_of_mem_normalizer (rcg_borel_le_normalizer_lineN hσ hb)
    have e2 : conjSub (lineN σ) u = lineN σ :=
      conjSub_of_mem_normalizer (rcg_borel_le_normalizer_lineN hσ hub)
    rw [conjSub_mul, conjSub_mul, e2] at hV
    have e3 : conjSub (lineN σ) (nHat σ (ng 1)) = lineN σ := by
      have h5 := congrArg (fun X => conjSub X b⁻¹) hV
      simp only [conjSub_conjSub_inv'] at h5
      rw [h5]
      exact conjSub_of_mem_normalizer (Subgroup.inv_mem _ (rcg_borel_le_normalizer_lineN hσ hb))
    exact rcg_lineN_ne_lineB hσ ((rcg_conj_nHat_lines hσ).2.1.symm.trans e3).symm

theorem rcg_units_pow_card {F : Type} [Field F] [Finite F] (u : Fˣ) :
    u ^ (Nat.card F - 1) = 1 := by
  have : Fintype F := Fintype.ofFinite F
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Nat.card_eq_fintype_card, Units.val_one]
  exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero

theorem rcg_torus_pow_eq_one {m : ℕ} (hm : ∀ u : Kˣ, u ^ m = 1) {z : adjointGroup d4 K}
    (hz : z ∈ ⨆ a : Fin d4.rank, CFSG.LieType.Steinberg.Adjoint.torus (τ := d4) K a) :
    z ^ m = 1 := by
  have key : z ∈ (⨆ a : Fin d4.rank, CFSG.LieType.Steinberg.Adjoint.torus (τ := d4) K a) ∧
      z ^ m = 1 := by
    refine Subgroup.iSup_induction _ (C := fun z => z ∈ (⨆ a : Fin d4.rank,
      CFSG.LieType.Steinberg.Adjoint.torus (τ := d4) K a) ∧ z ^ m = 1) hz
      (fun a x hx => ?_) ⟨Subgroup.one_mem _, one_pow m⟩ ?_
    · obtain ⟨u, rfl⟩ := hx
      refine ⟨Subgroup.mem_iSup_of_mem a ⟨u, rfl⟩, ?_⟩
      rw [← map_pow, hm u, map_one]
    · rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
      refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
      rw [(commute_of_mem_iSup_torus hx hy).mul_pow, hxm, hym, one_mul]
  exact key.2

theorem rcg_torusHat_pow_eq_one {m : ℕ} (hm : ∀ u : Kˣ, u ^ m = 1) {t : twistedGroup σ}
    (ht : t ∈ ⨆ i, hHat σ i) : t ^ m = 1 := by
  have h1 : (t : adjointGroup d4 K) ∈
      ⨆ a : Fin d4.rank, CFSG.LieType.Steinberg.Adjoint.torus (τ := d4) K a := by
    refine Subgroup.iSup_induction _ (C := fun t : twistedGroup σ => (t : adjointGroup d4 K) ∈
      ⨆ a : Fin d4.rank, CFSG.LieType.Steinberg.Adjoint.torus (τ := d4) K a) ht
      (fun i x hx => ?_) (Subgroup.one_mem _) (fun x y hx hy => ?_)
    · rw [hHat, Subgroup.mem_subgroupOf] at hx
      exact hHatE_le_iSup_torus σ i hx
    · rw [Subgroup.coe_mul]
      exact Subgroup.mul_mem _ hx hy
  exact Subtype.ext (by rw [Subgroup.coe_pow, rcg_torus_pow_eq_one hm h1]; rfl)

theorem rcg_no_order_borel [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {m : ℕ}
    (hm : ∀ u : Kˣ, u ^ m = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : Nat.Coprime p m)
    {y : twistedGroup σ} (hy : y ∈ borel (twistedDatum σ) (hHat σ)) : orderOf y ≠ p := by
  intro hord
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  have hN2 : IsPGroup 2 (posUnipotent (twistedDatum σ)) :=
    isPGroup_iSup_pos hext fun γ hγ => CFSG.LieType.HighestRoot.isPGroup_twistedD4_rootGroup σ hσ
      (isRoot_of_mem_twistedDatum_roots σ hγ)
  have hy' : y ∈ (borel (twistedDatum σ) (hHat σ) : Set (twistedGroup σ)) := hy
  rw [coe_borel hct, Set.mem_mul] at hy'
  obtain ⟨t, ht, u, hu, rfl⟩ := hy'
  have hTn : ∀ v ∈ posUnipotent (twistedDatum σ), t⁻¹ * v * t ∈ posUnipotent (twistedDatum σ) := by
    intro v hv
    have hn : t⁻¹ ∈ Subgroup.normalizer (posUnipotent (twistedDatum σ) : Set (twistedGroup σ)) :=
      Subgroup.inv_mem _ (borel_le_normalizer_posUnipotent hct (iSup_le_borel ht))
    have := (Subgroup.mem_normalizer_iff.1 hn v).1 hv
    rwa [inv_inv] at this
  have hpow : ∀ k : ℕ, ∃ v ∈ posUnipotent (twistedDatum σ), (t * u) ^ k = t ^ k * v := by
    intro k
    induction k with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, hk⟩ := ih
      refine ⟨t⁻¹ * v * t * u, Subgroup.mul_mem _ (hTn v hv) hu, ?_⟩
      rw [pow_succ, hk, pow_succ]
      group
  obtain ⟨v, hv, hvm⟩ := hpow m
  rw [rcg_torusHat_pow_eq_one hm ht, one_mul] at hvm
  have hord' : orderOf ((t * u) ^ m) = p := by
    rw [Nat.Coprime.orderOf_pow (by rwa [hord]), hord]
  rw [hvm] at hord'
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hN2 ⟨v, hv⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hp.one_lt.ne' (hord'.symm.trans hk)
  have h2p : 2 ∣ p := by
    rw [← hord', hk]
    exact dvd_pow_self 2 hk0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p).symm

end CFSG.RankThree.PartOne.D4RC
