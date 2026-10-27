module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedClass
public import CFSG.LargeExtraspecial.AS35YTPSLMaps

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour
import CFSG.RankThree.GF2n.Stroth78.Sec3Three
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.LargeExtraspecial.A2ModPointMapsTvCore
public import CFSG.RankThree.GF2n.Stroth78.Sec3LbarBound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LargeExtraspecial.A2Mod (IsPointMaps tv transvectionSet exists_isPointMaps)
open CFSG.ClassicalGroups.SpecialLinear.TvMod (tvCore tvCoreGen subset_tvCore commutator_tvCore
  mulVec_eq_of_mem_tvCore contra_eq_of_mem_tvCore)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem conj_mem_Lbar_of_mem_CHbar (S : Setting z E F) (a : G) {y ℓ : Hbar z}
    (hy : y ∈ CHbar S a) (hℓ : ℓ ∈ Lbar S a) : y * ℓ * y⁻¹ ∈ Lbar S a := by
  obtain ⟨c, hcC, rfl⟩ := (mem_CHbar_iff S a y).mp hy
  rw [← map_L0_eq_Lbar S a] at hℓ ⊢
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hℓ
  refine Subgroup.mem_map.mpr ⟨c * l * c⁻¹, ?_, ?_⟩
  · obtain ⟨hlQ, hlH⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl)
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hcC hlQ
    · exact (H z).mul_mem ((H z).mul_mem c.2 hlH) ((H z).inv_mem c.2)
  · simp [QuotientGroup.mk'_apply]

section Hub


theorem not_lieModel_psl_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4) {m : ℕ} (hm : 5 ≤ m) :
    ¬ CFSG.Blueprint.LieModel ↥(Xsub S a) .PSL m 2 1 := by
  intro hL
  classical
  have : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hXn : (Xsub S a).Normal := Xsub_normal S a
  obtain ⟨n, Ψ, hn, hb, hD, hA⟩ :=
    CFSG.LargeExtraspecial.AS35YT.exists_bijective_sl_of_lieModel_psl
      (rootClass_Xsub S h h217 h34) (a2Action_Xsub S a) hm hL
  obtain ⟨P, Pd, hP⟩ := exists_isPointMaps hA hn
  set Ψ' : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* Hbar z := (Xsub S a).subtype.comp Ψ
    with hΨ'
  have hP' : IsPointMaps ((rhoGL S).comp Ψ') (qS S) P Pd := hP
  have hΨ'inj : Function.Injective Ψ' := (Xsub S a).subtype_injective.comp hb.1
  have hrange : Ψ'.range = Xsub S a := by
    rw [hΨ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hb.2, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨α, hαR, hα1⟩ : ∃ α ∈ Rbar S a, α ≠ 1 := by
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
    exact ⟨r, r.2, fun h1 => hr1 (Subtype.ext h1)⟩
  have hαE : α ∈ Eset S a := Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hαR hα1)
  obtain ⟨τ₀, hτ₀⟩ := hb.2 ⟨α, subset_Xsub S a hαE⟩
  obtain ⟨v₀, φ₀, hv₀, hφ₀, h₀, rfl⟩ :=
    CFSG.LargeExtraspecial.A2Mod.mem_transvectionSet.mp ((hD τ₀).mpr (by rw [hτ₀]; exact hαE))
  have hΨτ : Ψ' (tv v₀ φ₀) = α := congrArg Subtype.val hτ₀
  have haV : aVec S h.mem_Q ∈ Submodule.span (ZMod 2) {P v₀, Pd φ₀} := by
    rw [← hP'.commSpace_tv v₀ φ₀ hv₀ hφ₀ h₀]
    have := aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hαR hα1
    rw [← hΨτ] at this
    exact this
  have hYfix : ∀ g ∈ tvCore v₀ φ₀, rhoLin S (Ψ' g) (aVec S h.mem_Q) = aVec S h.mem_Q := by
    intro g hg
    have h1 : rhoLin S (Ψ' g) (P v₀) = P v₀ := by
      have := hP'.map_mulVec g v₀
      rw [mulVec_eq_of_mem_tvCore hg] at this
      exact this.symm
    have h2 : rhoLin S (Ψ' g) (Pd φ₀) = Pd φ₀ := by
      have := hP'.map_contra g φ₀
      rw [contra_eq_of_mem_tvCore hg] at this
      exact this.symm
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp haV
    rw [← hst, map_add, map_smul, map_smul, h1, h2]
  have hYperf : ⁅(tvCore v₀ φ₀).map Ψ', (tvCore v₀ φ₀).map Ψ'⁆ = (tvCore v₀ φ₀).map Ψ' := by
    rw [← Subgroup.map_commutator, commutator_tvCore hn]
  have hYC : (tvCore v₀ φ₀).map Ψ' ≤ CHbar S a := by
    refine le_CHbar_of_perfect S h.mem_Q hYperf (fun y hy => ?_) (fun y hy u => ?_)
    · obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
      exact hYfix g hg
    · obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hy
      exact rhoZ_eq_self_of_mem_Xsub_of_card_ZQ_eq_four S h h217 h34 hZ _ (Ψ g).2 u
  have hL2 : ∀ ℓ ∈ Lbar S a, ℓ * ℓ = 1 := fun ℓ hℓ => by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hℓ
  have hτL : Ψ' (tv v₀ φ₀) ∈ Lbar S a := by
    rw [hΨτ]
    exact Rbar_le_Lbar S a hαR
  have hLX : ∀ ℓ ∈ Lbar S a, ∀ g, ∃ g', ℓ * Ψ' g * ℓ⁻¹ = Ψ' g' := by
    intro ℓ _ g
    have hmem : ℓ * Ψ' g * ℓ⁻¹ ∈ Ψ'.range := by
      rw [hrange]
      exact hXn.conj_mem _ (Ψ g).2 ℓ
    obtain ⟨g', hg'⟩ := hmem
    exact ⟨g', hg'.symm⟩
  have hLY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ ℓ ∈ Lbar S a, Ψ' y * ℓ * (Ψ' y)⁻¹ ∈ Lbar S a :=
    fun y hy ℓ hℓ => conj_mem_Lbar_of_mem_CHbar S a
      (hYC (Subgroup.mem_map_of_mem Ψ' (subset_tvCore v₀ φ₀ hy))) hℓ
  obtain ⟨hLle, hcardLX⟩ :=
    hP'.le_sup_centralizer_of_tvCore hn hΨ'inj hv₀ hφ₀ h₀ hL2 hτL hLX hLY
  rw [hrange] at hLle hcardLX
  set C : Subgroup (Hbar z) := Subgroup.centralizer (Xsub S a : Set (Hbar z)) with hC
  have hrel : (Xsub S a).relIndex (Lbar S a) ∣ Nat.card C := by
    have hle : Lbar S a ⊔ Xsub S a ≤ C ⊔ Xsub S a :=
      sup_le (hLle.trans (le_of_eq (sup_comm _ _))) le_sup_right
    have h1 := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : Xsub S a ≤ Lbar S a ⊔ Xsub S a) hle
    rw [Subgroup.relIndex_sup_right, Subgroup.relIndex_sup_right] at h1
    exact (Dvd.intro _ h1).trans (Subgroup.relIndex_dvd_card _ _)
  have hp : IsPGroup 2 ↥(Lbar S a) := fun x =>
    ⟨1, Subtype.ext (by simpa using sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hr2 : (Xsub S a).relIndex (Lbar S a) ≤ 2 := by
    have h6 : (Xsub S a).relIndex (Lbar S a) ∣ 6 :=
      hrel.trans (card_centralizer_Xsub_dvd_six S h h217)
    have h3 : ¬ 3 ∣ (Xsub S a).relIndex (Lbar S a) := fun h3 => by
      have h32 : 3 ∣ 2 ^ k := hk ▸ h3.trans (Subgroup.relIndex_dvd_card _ _)
      have := Nat.prime_three.dvd_of_dvd_pow h32
      omega
    have hpos : 0 < (Xsub S a).relIndex (Lbar S a) := Nat.pos_of_dvd_of_pos h6 (by norm_num)
    have hle6 : (Xsub S a).relIndex (Lbar S a) ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    generalize (Xsub S a).relIndex (Lbar S a) = r at h6 h3 hpos hle6 ⊢
    interval_cases r <;> omega
  have hdim := hP'.finrank_commSpaceOf_top
  have hdimQ := finrank_QbarOf_eq_two_mul S h.card_F
  have hnw : n ≤ w := by
    have := Submodule.finrank_le (CFSG.LargeExtraspecial.A2Mod.commSpaceOf
      ((rhoGL S).comp Ψ') ⊤)
    omega
  have hlt : (Xsub S a).relIndex (Lbar S a) * 2 ^ (n - 1) < 2 ^ w := by
    rcases hnw.lt_or_eq with hlt | heq
    · calc (Xsub S a).relIndex (Lbar S a) * 2 ^ (n - 1) ≤ 2 * 2 ^ (n - 1) :=
            Nat.mul_le_mul_right _ hr2
        _ = 2 ^ n := by rw [← pow_succ']; congr 1; omega
        _ < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) hlt
    ·
      have htop : CFSG.LargeExtraspecial.A2Mod.commSpaceOf ((rhoGL S).comp Ψ') ⊤ = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by omega)
      have hCbot : C = ⊥ := by
        rw [eq_bot_iff]
        intro c hc
        rw [Subgroup.mem_bot]
        have hcomm : ∀ g, Commute (rhoGL S c) (((rhoGL S).comp Ψ') g) := fun g =>
          (show Commute c (Ψ' g) from
            (Subgroup.mem_centralizer_iff.mp hc _ (Ψ g).2).symm).map (rhoGL S)
        have hfix : ∀ x, rhoGL S c x = x := fun x =>
          hP'.apply_eq_self_of_mem_commSpaceOf_top (by omega) hcomm
            (by rw [htop]; exact Submodule.mem_top)
        have h1 : rhoGL S c = rhoGL S 1 := by
          rw [map_one]
          exact LinearEquiv.ext fun x => by rw [hfix x]; rfl
        exact rhoGL_injective S h1
      have hr1 : (Xsub S a).relIndex (Lbar S a) = 1 := by
        rw [hCbot, Subgroup.card_bot] at hrel
        exact Nat.dvd_one.mp hrel
      rw [hr1, one_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcard : Nat.card ↥(Lbar S a) ≤ (Xsub S a).relIndex (Lbar S a) * 2 ^ (n - 1) := by
    rw [← Subgroup.relIndex_mul_card (Xsub S a) (Lbar S a), inf_comm]
    exact Nat.mul_le_mul_left _ hcardLX
  exact absurd (h.two_pow_le_card_Lbar.trans hcard) (not_le.mpr hlt)

end Hub

end CFSG.RankThree.GF2n.Stroth78
