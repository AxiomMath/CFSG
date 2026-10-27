module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeventeenKHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Lift
public import CFSG.Goldschmidt.Steps.Sec82PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_Omega6Minus_smallComm : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n s : ℕ),
    2 ≤ n → 1 ≤ s → s ≤ 2 → IsOmegaMinus ↥H 6 n →
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 n) H ⊤ ⊥ s →
        p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
          ∀ t : MulAut W, t ∈ Subgroup.normalizer (H : Set (MulAut W)) →
            (∃ k : ℕ, orderOf t = 2 ^ k) →
              Nat.card W < 2 ^ (2 * n * s) * Nat.card (fixV (Subgroup.zpowers t)) →
                ∀ z : W, z ≠ 1 → z ∈ commSub ⊤ (Subgroup.zpowers t) →
                  ∃ E : Subgroup (MulAut W), E ≤ H ∧ IsPGroup p E ∧ ¬ IsCyclic E ∧
                    ∀ e ∈ E, e z = z

@[expose] def K_Omega4Plus_smallComm : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n : ℕ),
    2 ≤ n → IsOmegaPlus ↥H 4 n → NatOmegaPlus H ⊤ ⊥ 4 n →
      p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
        ∀ t : MulAut W, t ∈ Subgroup.normalizer (H : Set (MulAut W)) →
          (∃ k : ℕ, orderOf t = 2 ^ k) →
            Nat.card W < 2 ^ (2 * n) * Nat.card (fixV (Subgroup.zpowers t)) →
              ∀ z : W, z ≠ 1 → z ∈ commSub ⊤ (Subgroup.zpowers t) →
                ∃ P : Subgroup (MulAut W), P ≤ H ∧ Group.IsPerfect P ∧ p ∣ Nat.card P ∧
                  ∀ e ∈ P, e z = z

@[expose] def K_OmegaFourPlusNormalizer_pRank : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H Y : Subgroup (MulAut W)) (p n : ℕ),
    2 ≤ n → IsOmegaPlus ↥H 4 n → NatOmegaPlus H ⊤ ⊥ 4 n → p.Prime → p ≠ 2 →
      (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] → H ≤ Y →
        Y ≤ Subgroup.normalizer (H : Set (MulAut W)) →
          UC22.F10.OpRes p Y = Y → CFSG.Open.pRank p Y ≤ 2

theorem opRes_mbar_eq (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h638 : UC6.R6_38 D) :
    UC22.F10.OpRes p (Mbar D.M V₀ V h.hyp125.isElemAbelian) =
      Mbar D.M V₀ V h.hyp125.isElemAbelian := by
  classical
  have hp : p.Prime := h.p_prime
  let H := Mbar D.M V₀ V h.hyp125.isElemAbelian
  have hM : UC22.F10.OpRes p D.M = D.M :=
    h638 p hp h.p_ne_two (Or.inl h.hp)
  have htop : CFSG.GH74.GLS.oResidual p ↥D.M = ⊤ := by
    apply Subgroup.map_injective D.M.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype,
      ← UC6.opRes_eq_map_oResidual_uc6 hp D.M, hM]
  have hle : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  let f : ↥D.M →* ↥H :=
    MonoidHom.codRestrict
      ((actTil V₀ V h.hyp125.isElemAbelian).comp (Subgroup.inclusion hle)) H
      (fun m => actTil_mem_barSub V₀ V h.hyp125.isElemAbelian m.2 (hle m.2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, hg, hgy⟩ :=
      (mem_barSub V₀ V h.hyp125.isElemAbelian D.M
        (y : MulAut (Vtil V₀ V h.hyp125.isElemAbelian))).1 y.2
    refine ⟨⟨(g : G), hg⟩, ?_⟩
    apply Subtype.ext
    change actTil V₀ V h.hyp125.isElemAbelian
      (Subgroup.inclusion hle ⟨(g : G), hg⟩) =
        (y : MulAut (Vtil V₀ V h.hyp125.isElemAbelian))
    rw [show Subgroup.inclusion hle ⟨(g : G), hg⟩ = g from Subtype.ext rfl]
    exact hgy
  have hmap := CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual f hf hp
  rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.mpr hf] at hmap
  have hmap' : CFSG.GH74.GLS.oResidual p ↥H = ⊤ := hmap.symm
  rw [UC6.opRes_eq_map_oResidual_uc6 hp H, hmap', Subgroup.map_top,
    Subgroup.range_subtype]

theorem mbar_le_normalizer_conjClosure {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) :
    Mbar D.M V₀ V h.hyp125.isElemAbelian ≤
      Subgroup.normalizer (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) :
        Set (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (barSub_mono V₀ V h.hyp125.isElemAbelian h.X_le_M)).1
    (barSub_subgroupOf_mbar_normal h.hyp125.isElemAbelian h.X_le_M
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L))

theorem card_Vtil_lt_mul_card_fixV {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (g : stabTil V₀ V) {d : ℕ} (hd : 0 < d)
    (h : Nat.card V < 2 ^ d * Nat.card (centMod V₀ V (g : G))) :
    Nat.card (Vtil V₀ V hV) <
      2 ^ d * Nat.card (fixV (Subgroup.zpowers (actTil V₀ V hV g))) := by
  let W := Vtil V₀ V hV
  let S : Subgroup W := fixV (Subgroup.zpowers (actTil V₀ V hV g))
  have hW2 : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hnot : ¬ (2 ^ ((d - 1) + 1) * Nat.card (centMod V₀ V (g : G)) ≤ Nat.card V) := by
    rw [Nat.sub_add_cancel hd]
    exact not_le.2 h
  have hrk : rkIdx S ≤ d - 1 := by
    by_contra hlt
    exact hnot ((centMod_card_iff V₀ V hV g (d - 1)).2 (not_le.1 hlt))
  have hidx : S.index = 2 ^ rkIdx S := B1.index_eq_two_pow hW2 S
  have hidxle : S.index ≤ 2 ^ (d - 1) := by
    rw [hidx]
    exact Nat.pow_le_pow_right (by norm_num) hrk
  have hcard : Nat.card S * S.index = Nat.card W := Subgroup.card_mul_index S
  have hSpow : 0 < Nat.card S := Nat.card_pos
  have hlt : 2 ^ (d - 1) < 2 ^ d :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc Nat.card W = Nat.card S * S.index := hcard.symm
    _ ≤ Nat.card S * 2 ^ (d - 1) := Nat.mul_le_mul_left _ hidxle
    _ < 2 ^ d * Nat.card S := by
        rw [mul_comm (Nat.card S) (2 ^ (d - 1))]
        exact Nat.mul_lt_mul_of_pos_right hlt hSpow

theorem tilOf_mem_commSub {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (ht : t ∈ stabTil V₀ V) {z : G} (hz : z ∈ commElt V t) (hzV : z ∈ V) :
    tilOf V₀ V hV z hzV ∈
      commSub (⊤ : Subgroup (Vtil V₀ V hV))
        (Subgroup.zpowers (actTil V₀ V hV ⟨t, ht⟩)) := by
  classical
  let W := Vtil V₀ V hV
  let τ : MulAut W := actTil V₀ V hV ⟨t, ht⟩
  let σ : MulAut (IntMod V hV) := actStab V₀ V hV ⟨t, ht⟩
  let P : Subgroup (IntMod V hV) :=
    (commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)).comap (mkTil V₀ V hV)
  have htN : t ∈ Subgroup.normalizer (V : Set G) := stabTil_le_normalizer V₀ V ht
  have hleV : commElt V t ≤ V := by
    rw [commElt, Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    have htw : t⁻¹ * w * t ∈ V := (Subgroup.mem_normalizer_iff''.1 htN w).1 hw
    have hgen : w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * w * t) := by group
    rw [hgen]
    exact V.mul_mem (V.inv_mem hw) htw
  have hσ : ∀ w : IntMod V hV, mkTil V₀ V hV (σ⁻¹ w) = τ⁻¹ (mkTil V₀ V hV w) := by
    intro w
    rw [show σ⁻¹ = actStab V₀ V hV ⟨t, ht⟩⁻¹ from (map_inv (actStab V₀ V hV) ⟨t, ht⟩).symm]
    calc mkTil V₀ V hV (actStab V₀ V hV ⟨t, ht⟩⁻¹ w)
        = actTil V₀ V hV ⟨t, ht⟩⁻¹ (mkTil V₀ V hV w) :=
          (actTil_mk V₀ V hV ⟨t, ht⟩⁻¹ w).symm
      _ = τ⁻¹ (mkTil V₀ V hV w) := by rw [map_inv (actTil V₀ V hV) ⟨t, ht⟩]
  have hgen : ∀ w : IntMod V hV, w⁻¹ * σ⁻¹ w ∈ P := by
    intro w
    refine Subgroup.mem_comap.2 ?_
    have hmap : mkTil V₀ V hV (w⁻¹ * σ⁻¹ w) =
        (mkTil V₀ V hV w)⁻¹ * τ⁻¹ (mkTil V₀ V hV w) := by
      rw [map_mul, map_inv, hσ]
    rw [hmap, mul_comm]
    exact Subgroup.subset_closure ⟨τ⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers τ),
      mkTil V₀ V hV w, Subgroup.mem_top _, rfl⟩
  have hσw : ∀ (w : G) (hw : w ∈ V),
      σ⁻¹ (IntMod.mk hV ⟨w, hw⟩) =
        IntMod.mk hV ⟨t⁻¹ * w * t, (Subgroup.mem_normalizer_iff''.1 htN w).1 hw⟩ := by
    intro w hw
    refine Subtype.ext ?_
    change (σ⁻¹ (IntMod.mk hV ⟨w, hw⟩)).val = t⁻¹ * w * t
    rw [show σ⁻¹ = actStab V₀ V hV ⟨t, ht⟩⁻¹ from (map_inv (actStab V₀ V hV) ⟨t, ht⟩).symm]
    rw [actStab_apply_val]
    simp only [Subgroup.coe_inv, inv_inv, IntMod.mk, IntMod.val]
  have hmem : ∀ (x : G) (hx : x ∈ commElt V t),
      IntMod.mk hV ⟨x, hleV hx⟩ ∈ P := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        have hval : IntMod.mk hV ⟨w⁻¹ * t⁻¹ * w * t,
            hleV (Subgroup.subset_closure ⟨w, hw, rfl⟩)⟩ =
            (IntMod.mk hV ⟨w, hw⟩)⁻¹ * σ⁻¹ (IntMod.mk hV ⟨w, hw⟩) := by
          rw [hσw w hw]
          refine Subtype.ext ?_
          change w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * w * t)
          group
        rw [hval]
        exact hgen (IntMod.mk hV ⟨w, hw⟩)
    | one =>
        have h1 : IntMod.mk hV ⟨1, hleV (Subgroup.one_mem _)⟩ = (1 : IntMod V hV) :=
          Subtype.ext rfl
        rw [h1]
        exact P.one_mem
    | mul a b ha hb iha ihb =>
        have hv : IntMod.mk hV ⟨a * b, hleV (Subgroup.mul_mem _ ha hb)⟩ =
            IntMod.mk hV ⟨a, hleV ha⟩ * IntMod.mk hV ⟨b, hleV hb⟩ :=
          Subtype.ext rfl
        rw [hv]
        exact P.mul_mem iha ihb
    | inv a ha iha =>
        have hv : IntMod.mk hV ⟨a⁻¹, hleV (Subgroup.inv_mem _ ha)⟩ =
            (IntMod.mk hV ⟨a, hleV ha⟩)⁻¹ :=
          Subtype.ext rfl
        rw [hv]
        exact P.inv_mem iha
  exact hmem z hz

theorem exists_noncyclic_pSubgroup_of_three_le_pRank (D : Data G) {p : ℕ} (hp : p.Prime)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M) :
    ∃ Q : Subgroup G, Q ≤ D.M ∧ IsPGroup p Q ∧ ¬ IsCyclic Q := by
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt D.M
  refine ⟨E, hEM, hE.isPGroup, ?_⟩
  refine CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank hp ?_
  have hle : CFSG.Open.pRank p D.M ≤ CFSG.Open.pRank p E :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hEcard
  omega

theorem le_centralizer_of_mem_V₀ {M V₀ : Subgroup G} (_hV₀ : IsElemAbelian 2 V₀)
    (hcard : Nat.card V₀ ≤ 2) (hM : M ≤ Subgroup.normalizer (V₀ : Set G))
    {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) :
    M ≤ Subgroup.centralizer ({z} : Set G) := by
  haveI : Nontrivial ↥V₀ := ⟨⟨z, hz⟩, 1, fun e => hz1 (congrArg Subtype.val e)⟩
  have h2 : Nat.card V₀ = 2 := le_antisymm hcard Finite.one_lt_card
  exact hM.trans ((CFSG.Quasithin.normalizer_eq_centralizer_of_card_eq_two h2).le.trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hz)))

section Certified


theorem gap_18_17_one (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) :
    Gap_18_17_one D V₀ V p L h := by
  intro h1 t htM ht2 hnc hsmall z hz hz1
  exfalso
  obtain ⟨f, hSUn, hNat⟩ := h1
  let W := Vtil V₀ V h.hyp125.isElemAbelian
  let H : Subgroup (MulAut W) :=
    barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)
  have hV := h.hyp125.isElemAbelian
  have hU4 : IsU4 ↥H f := isU4_of_isSUn_four hSUn
  obtain ⟨-, hnof, hf1, -⟩ := isU4_barSub_cong h h1742 hU4
  have hf2 : 2 ≤ f := by omega
  have hnormH : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (H : Set (MulAut W)) :=
    mbar_le_normalizer_conjClosure h
  let tbar : MulAut W := actTil V₀ V hV t
  have htbarN : tbar ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
    hnormH (actTil_mem_barSub V₀ V hV htM t.2)
  have htbar2 : ∃ k : ℕ, orderOf tbar = 2 ^ k := by
    obtain ⟨k, hk⟩ := ht2
    have hdvd : orderOf tbar ∣ 2 ^ k := by
      have h1 : orderOf tbar ∣ orderOf t := orderOf_map_dvd (actTil V₀ V hV) t
      have h2 : orderOf t = 2 ^ k := (Subgroup.orderOf_coe t).symm.trans hk
      exact h2 ▸ h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  have htbar1 : tbar ≠ 1 := by
    intro h1'
    apply hnc
    exact (actTil_eq_one_iff V₀ V hV t).1 h1'
  have hK' := k_K_SU4_minComm_holds H f hf2 hSUn hNat tbar htbarN htbar2 htbar1
  rw [hnof] at hsmall
  have hlt := card_Vtil_lt_mul_card_fixV hV t (d := 2 * f) (by omega) hsmall
  change Nat.card (Vtil V₀ V hV) <
    2 ^ (2 * f) * Nat.card (fixV (Subgroup.zpowers tbar)) at hlt
  exact (not_le_of_gt hlt) hK'

theorem gap_18_17_two (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D) (hK : K_Omega6Minus_smallComm)
    (h1742 : S17.R17_42At D V₀ V) :
    Gap_18_17_two D V₀ V p L h := by
  intro s h2 t htM ht2 hnc hsmall z hz hz1
  have hV := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  have hzV : z ∈ V := commElt_le_V_of_mem_M D h.hyp125 htM hz
  by_cases hz0 : z ∈ V₀
  · obtain ⟨Q, hQM, hQp, hQc⟩ :=
      exists_noncyclic_pSubgroup_of_three_le_pRank D h.p_prime (hSg.three_le p h.hp)
    refine ⟨Q, le_inf hQM (hQM.trans ?_), hQp, hQc⟩
    exact le_centralizer_of_mem_V₀ hP.elemAbelian₀
      ((mSub_le_one_iff hP.elemAbelian₀).1 h.small) hP.le_normalizer₀ hz0 hz1
  · obtain ⟨hsl, hsr, f, hO, hSum⟩ := h2
    have hU4 : IsU4 ↥(barSub V₀ V hV (UC22.conjClosure D.M L)) f :=
      isU4_of_isOmegaMinus hO
    obtain ⟨-, hnof, hf1, hcong⟩ := isU4_barSub_cong h h1742 hU4
    have hf2 : 2 ≤ f := by omega
    let W := Vtil V₀ V hV
    let H : Subgroup (MulAut W) :=
      barSub V₀ V hV (UC22.conjClosure D.M L)
    have hX : UC22.conjClosure D.M L ≤ D.M := h.X_le_M
    have hHle : H ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hX
    have hnormH : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (H : Set (MulAut W)) :=
      mbar_le_normalizer_conjClosure h
    let tbar : MulAut W := actTil V₀ V hV t
    have htbarN : tbar ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
      hnormH (actTil_mem_barSub V₀ V hV htM t.2)
    have htbar2 : ∃ k : ℕ, orderOf tbar = 2 ^ k := by
      obtain ⟨k, hk⟩ := ht2
      have hdvd : orderOf tbar ∣ 2 ^ k := by
        have h1 : orderOf tbar ∣ orderOf t := orderOf_map_dvd (actTil V₀ V hV) t
        have h2 : orderOf t = 2 ^ k := (Subgroup.orderOf_coe t).symm.trans hk
        exact h2 ▸ h1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact ⟨j, hj⟩
    rw [hnof] at hsmall
    have hlt := card_Vtil_lt_mul_card_fixV hV t (d := 2 * f * s)
      (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)) hsmall
    change Nat.card (Vtil V₀ V hV) <
      2 ^ (2 * f * s) * Nat.card (fixV (Subgroup.zpowers tbar)) at hlt
    have hzmem : tilOf V₀ V hV z hzV ∈ commSub (⊤ : Subgroup W)
        (Subgroup.zpowers tbar) := tilOf_mem_commSub hV t.2 hz hzV
    obtain ⟨E, hEH, hEp, hEc, hEz⟩ :=
      hK H p f s hf2 hsl hsr hO hSum h.p_prime hcong tbar htbarN htbar2 hlt
        (tilOf V₀ V hV z hzV) (by
          intro h0
          apply hz0
          have h0'' : mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩) = 1 := by
            simpa only [tilOf] using h0
          have h0q : (QuotientGroup.mk (IntMod.mk hV ⟨z, hzV⟩) : Vtil V₀ V hV) = 1 := by
            simpa [mkTil] using h0''
          have h0' : IntMod.mk hV ⟨z, hzV⟩ ∈ modNull V₀ V hV :=
            (QuotientGroup.eq_one_iff _).1 h0q
          exact (mem_modNull V₀ V hV _).1 h0') hzmem
    have hEM : E ≤ Mbar D.M V₀ V hV := hEH.trans hHle
    have hEfix : ∀ x ∈ E, x (mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩)) =
        mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩) := by
      intro x hx
      simpa [tilOf] using hEz x hx
    have hV0lt : Nat.card V₀ < p := by
      have hle : Nat.card V₀ ≤ 2 := (mSub_le_one_iff hP.elemAbelian₀).1 h.small
      have hp2 : p ≠ 2 := h.p_ne_two
      have := h.p_prime.two_le
      omega
    exact C163.exists_noncyclic_le_centralizer hV h.p_prime hV0lt hzV hEM hEp hEc hEfix

theorem gap_18_17_three (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D)
    (hK : K_Omega4Plus_smallComm) (hKp : K_OmegaFourPlusNormalizer_pRank)
    (h638 : UC6.R6_38 D) (h1742 : S17.R17_42At D V₀ V) :
    P18_13_3 D V₀ V p L h → ∀ (t : stabTil V₀ V), (t : G) ∈ D.M →
      (∃ k : ℕ, orderOf (t : G) = 2 ^ k) → ¬ CentralizesMod V₀ V (t : G) →
      Nat.card V < 2 ^ (2 * S17.nOf L) * Nat.card (centMod V₀ V (t : G)) →
      ∀ z ∈ commElt V (t : G), z ≠ 1 →
        ∃ Q : Subgroup G,
          Q ≤ D.M ⊓ Subgroup.centralizer ({z} : Set G) ∧ IsPGroup p Q ∧ ¬ IsCyclic Q := by
  intro h3 t htM ht2 hnc hsmall z hz hz1
  have hV := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  have hzV : z ∈ V := commElt_le_V_of_mem_M D h.hyp125 htM hz
  by_cases hz0 : z ∈ V₀
  · obtain ⟨Q, hQM, hQp, hQc⟩ :=
      exists_noncyclic_pSubgroup_of_three_le_pRank D h.p_prime (hSg.three_le p h.hp)
    refine ⟨Q, le_inf hQM (hQM.trans ?_), hQp, hQc⟩
    exact le_centralizer_of_mem_V₀ hP.elemAbelian₀
      ((mSub_le_one_iff hP.elemAbelian₀).1 h.small) hP.le_normalizer₀ hz0 hz1
  · obtain ⟨f, hO, hNat⟩ := h3
    obtain ⟨-, hnof, hf2, hcong⟩ := isOmegaPlus_barSub_cong h h1742 hO
    let W := Vtil V₀ V hV
    let H : Subgroup (MulAut W) :=
      barSub V₀ V hV (UC22.conjClosure D.M L)
    have hX : UC22.conjClosure D.M L ≤ D.M := h.X_le_M
    have hHle : H ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hX
    have hnormH : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (H : Set (MulAut W)) :=
      mbar_le_normalizer_conjClosure h
    let tbar : MulAut W := actTil V₀ V hV t
    have htbarN : tbar ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
      hnormH (actTil_mem_barSub V₀ V hV htM t.2)
    have htbar2 : ∃ k : ℕ, orderOf tbar = 2 ^ k := by
      obtain ⟨k, hk⟩ := ht2
      have hdvd : orderOf tbar ∣ 2 ^ k := by
        have h1 : orderOf tbar ∣ orderOf t := orderOf_map_dvd (actTil V₀ V hV) t
        have h2 : orderOf t = 2 ^ k := (Subgroup.orderOf_coe t).symm.trans hk
        exact h2 ▸ h1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact ⟨j, hj⟩
    rw [hnof] at hsmall
    have hlt := card_Vtil_lt_mul_card_fixV hV t (d := 2 * f) (by omega) hsmall
    change Nat.card (Vtil V₀ V hV) <
      2 ^ (2 * f) * Nat.card (fixV (Subgroup.zpowers tbar)) at hlt
    have hzmem : tilOf V₀ V hV z hzV ∈ commSub (⊤ : Subgroup W)
        (Subgroup.zpowers tbar) := tilOf_mem_commSub hV t.2 hz hzV
    have hzmod1 : tilOf V₀ V hV z hzV ≠ 1 := by
      intro h0
      apply hz0
      have h0'' : mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩) = 1 := by
        simpa only [tilOf] using h0
      have h0q : (QuotientGroup.mk (IntMod.mk hV ⟨z, hzV⟩) : Vtil V₀ V hV) = 1 := by
        simpa [mkTil] using h0''
      have h0' : IntMod.mk hV ⟨z, hzV⟩ ∈ modNull V₀ V hV :=
        (QuotientGroup.eq_one_iff _).1 h0q
      exact (mem_modNull V₀ V hV _).1 h0'
    obtain ⟨P, hPH, hPperf, hPdvd, hPz⟩ :=
      hK H p f hf2 hO hNat h.p_prime hcong tbar htbarN htbar2 hlt
        (tilOf V₀ V hV z hzV) hzmod1 hzmem
    have hPM : P ≤ Mbar D.M V₀ V hV := hPH.trans hHle
    have hPfix : P ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩)) := by
      refine le_inf hPM ?_
      intro x hx
      rw [MulAction.mem_stabilizer_iff]
      simpa [tilOf] using hPz x hx
    have hMbar_le : CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 2 :=
      hKp H (Mbar D.M V₀ V hV) p f hf2 hO hNat h.p_prime h.p_ne_two hcong hHle hnormH
        (opRes_mbar_eq D h h638)
    have hpker : p ∣ Nat.card (F11.CTilde D.M V₀ V) := by
      by_contra hnd
      have hle := pRank_le_pRank_mbar_of_not_dvd hV hP h.p_prime hnd
      have h3le := hSg.three_le p h.hp
      omega
    have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
      rcases h.hyp125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
      · exact Or.inl h0
      · exact Or.inr h0
    have h4 : Nat.card V₀ ≤ 4 := by
      have := (mSub_le_one_iff hP.elemAbelian₀).1 h.small
      omega
    exact exists_noncyclic_cent_of_perfect_bar D h.p_prime h.p_ne_two hV hP hcase h4
      (IntMod.mk hV ⟨z, hzV⟩) hz0 hPfix hPperf hPdvd hpker

theorem eighteen_seventeen_one_of_K (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_17_1At D V₀ V p L h :=
  eighteen_seventeen_one D V₀ V p L h h61 (gap_18_17_one D V₀ V p L h h1742)

theorem eighteen_seventeen_two_of_K (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (hK : K_Omega6Minus_smallComm)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_17_2At D V₀ V p L h :=
  eighteen_seventeen_two D V₀ V p L h h61
    (gap_18_17_two D V₀ V p L h hSg hK h1742)

theorem eighteen_seventeen_three_of_K (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (hK : K_Omega4Plus_smallComm)
    (hKp : K_OmegaFourPlusNormalizer_pRank) (h638 : UC6.R6_38 D)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_17_3At D V₀ V p L h := by
  intro h3
  refine le_deltaN_of_centralizer_commElt D h.hyp125 (mSub V) (2 * S17.nOf L) ?_
  intro t htM ht2 hnc hsmall z hz hz1
  have hzV : z ∈ V := commElt_le_V_of_mem_M D h.hyp125 htM hz
  exact centralizer_le_of_gap D h61 h.hyp125 h.hp hzV hz1
    (gap_18_17_three D V₀ V p L h hSg hK hKp h638 h1742 h3 t htM ht2 hnc hsmall z hz hz1)

theorem eighteen_seventeen_of_K (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D)
    (hK2 : K_Omega6Minus_smallComm) (hK3 : K_Omega4Plus_smallComm)
    (hKp : K_OmegaFourPlusNormalizer_pRank) (h638 : UC6.R6_38 D)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_17At D V₀ V p L h :=
  ⟨eighteen_seventeen_one_of_K D V₀ V p L h h61 h1742,
    eighteen_seventeen_two_of_K D V₀ V p L h h61 hSg hK2 h1742,
    eighteen_seventeen_three_of_K D V₀ V p L h h61 hSg hK3 hKp h638 h1742⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
