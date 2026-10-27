module

public import CFSG.Quasithin.Background.C1PackS15205E
public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

variable {G : Type} [Group G] [Finite G]

@[expose] def Y1of (T M₁ Yh : Subgroup G) : Subgroup G :=
  Yh ⊔ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G))

@[expose] def Y2of (T Mc M₁ Yh : Subgroup G) : Subgroup G :=
  oTwoUpper (conjClosure (pCoreOf 2 (Mc ⊓ M₁)) (Y1of T M₁ Yh ⊔ T))

section Facts

variable {T Mc M M₁ Yh : Subgroup G}

omit [Finite G] in
theorem autOn_eq_bot_of_le_centralizer {X V : Subgroup G} (h : X ≤ Subgroup.centralizer (V : Set G)) :
    autOn X V = ⊥ :=
  CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer h

theorem Ctr5.hyp1 (c : Ctr5 T Mc M M₁) : Hyp14117 T Mc M₁ Mc (VZ T M₁) where
  inM := c.inM₁
  twoReduced := (isTwoReducedIn_VZ c.qtfe c.inM₁).1
  ne_bot := VZ_ne_bot c.qtfe.omegaOneCenter_ne_bot
  inM₁ := ⟨c.qtfe.mc_max, c.qtfe.t_le_mc⟩
  ne := c.ne_c.symm
  cases := Or.inr rfl

omit [Finite G] in
theorem M₁_le_normalizer_C₁ (T M₁ : Subgroup G) :
    M₁ ≤ Subgroup.normalizer ((M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, A4.mem_normalizer_centralizer (le_normalizer_VZ T M₁ hg)⟩

omit [Finite G] in
theorem Yd5.Y1_le (hY : Yd5 T Mc M M₁ Yh) : Y1of T M₁ Yh ≤ M₁ :=
  sup_le (hY.le_H.trans inf_le_left) inf_le_left

theorem Ctr5.M₁_le_normalizer_Y1 (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    M₁ ≤ Subgroup.normalizer (Y1of T M₁ Yh : Set G) := by
  intro g hg
  obtain ⟨h, hh, k, hk, rfl⟩ := c.exists_mul g hg
  have h1 : h ∈ Subgroup.normalizer (Y1of T M₁ Yh : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hY.H_norm hh, M₁_le_normalizer_C₁ T M₁ hh.1⟩
  have h2 : k ∈ Subgroup.normalizer (Y1of T M₁ Yh : Set G) :=
    Subgroup.le_normalizer ((le_sup_right : _ ≤ Y1of T M₁ Yh) hk)
  exact (Subgroup.normalizer _).mul_mem h1 h2

theorem Ctr5.T_le_normalizer_Y1 (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    T ≤ Subgroup.normalizer (Y1of T M₁ Yh : Set G) := c.T_le_M₁.trans (c.M₁_le_normalizer_Y1 hY)

omit [Finite G] in
theorem Yd5.autOn_Y1 (hY : Yd5 T Mc M M₁ Yh) :
    autOn (Y1of T M₁ Yh) (VZ T M₁) = autOn Yh (VZ T M₁) := by
  have hN : M₁ ≤ Subgroup.normalizer (VZ T M₁ : Set G) := le_normalizer_VZ T M₁
  unfold Y1of
  rw [autOn_sup (hY.le_H.trans (inf_le_left.trans hN)) (inf_le_left.trans hN),
    autOn_eq_bot_of_le_centralizer (inf_le_right : M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) ≤ _),
    sup_bot_eq]

omit [Finite G] in
theorem Yd5.card_Y1 (hY : Yd5 T Mc M M₁ Yh) :
    Nat.card (autOn (Y1of T M₁ Yh) (VZ T M₁)) = 3 := by
  rw [hY.autOn_Y1]; exact hY.card

theorem Ctr5.R1_le_T (c : Ctr5 T Mc M M₁) : pCoreOf 2 (Mc ⊓ M₁) ≤ T :=
  c.hyp1.pCoreOf_le_sylow c.qtfe

theorem Ctr5.T_le_normalizer_R1 (c : Ctr5 T Mc M M₁) :
    T ≤ Subgroup.normalizer (pCoreOf 2 (Mc ⊓ M₁) : Set G) :=
  (le_inf c.qtfe.t_le_mc c.T_le_M₁).trans (le_normalizer_pCoreOf 2 (Mc ⊓ M₁))

omit [Finite G] in
theorem inf_le_normalizer_R1 (Mc M₁ : Subgroup G) :
    M₁ ⊓ Mc ≤ Subgroup.normalizer (pCoreOf 2 (Mc ⊓ M₁) : Set G) := by
  rw [inf_comm]; exact le_normalizer_pCoreOf 2 (Mc ⊓ M₁)

theorem Ctr5.Rhat_ne_bot (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁) :
    autOn (pCoreOf 2 (Mc ⊓ M₁)) (VZ T M₁) ≠ ⊥ :=
  lemma_14_1_17_one h113 c.qtfe c.hyp1

theorem Ctr5.Yhat_comm (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    ⁅autOn (Y1of T M₁ Yh) (VZ T M₁), autOn (pCoreOf 2 (Mc ⊓ M₁)) (VZ T M₁)⁆ =
      autOn (Y1of T M₁ Yh) (VZ T M₁) := by
  classical
  have hN₁ : M₁ ≤ Subgroup.normalizer (VZ T M₁ : Set G) := le_normalizer_VZ T M₁
  have hR1M₁ : pCoreOf 2 (Mc ⊓ M₁) ≤ M₁ := c.R1_le_T.trans c.T_le_M₁
  have hY1M₁ : Y1of T M₁ Yh ≤ M₁ := hY.Y1_le
  have hcomm_eq := autOn_commutator (hY1M₁.trans hN₁) (hR1M₁.trans hN₁)
  have hcommle : ⁅Y1of T M₁ Yh, pCoreOf 2 (Mc ⊓ M₁)⁆ ≤ Y1of T M₁ Yh := by
    refine Subgroup.commutator_le.mpr fun y hy r hr => ?_
    have h1 : r * y⁻¹ * r⁻¹ ∈ Y1of T M₁ Yh :=
      (Subgroup.mem_normalizer_iff.mp (c.T_le_normalizer_Y1 hY (c.R1_le_T hr)) y⁻¹).mp
        ((Y1of T M₁ Yh).inv_mem hy)
    rw [commutatorElement_def]
    have : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
    rw [this]
    exact (Y1of T M₁ Yh).mul_mem hy h1
  have hle : ⁅autOn (Y1of T M₁ Yh) (VZ T M₁), autOn (pCoreOf 2 (Mc ⊓ M₁)) (VZ T M₁)⁆ ≤
      autOn (Y1of T M₁ Yh) (VZ T M₁) := by
    rw [← hcomm_eq]
    exact A4.autOn_mono hcommle
  refine le_antisymm hle ?_
  by_contra hne
  have hdvd : Nat.card ↥⁅autOn (Y1of T M₁ Yh) (VZ T M₁), autOn (pCoreOf 2 (Mc ⊓ M₁)) (VZ T M₁)⁆ ∣ 3 :=
    hY.card_Y1 ▸ Subgroup.card_dvd_of_le hle
  have hbot : ⁅autOn (Y1of T M₁ Yh) (VZ T M₁), autOn (pCoreOf 2 (Mc ⊓ M₁)) (VZ T M₁)⁆ = ⊥ := by
    have h1 : Nat.card ↥⁅autOn (Y1of T M₁ Yh) (VZ T M₁),
        autOn (pCoreOf 2 (Mc ⊓ M₁)) (VZ T M₁)⁆ ≠ 3 := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hY.card_Y1, h])).symm.le
    have h2 := ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_right h1
    exact Subgroup.card_eq_one.mp h2
  rw [← hcomm_eq] at hbot
  have hcent : ⁅Y1of T M₁ Yh, pCoreOf 2 (Mc ⊓ M₁)⁆ ≤ Subgroup.centralizer (VZ T M₁ : Set G) :=
    le_centralizer_of_autOn_eq_bot (hcommle.trans (hY1M₁.trans hN₁)) hbot
  have hRC : ∀ y ∈ Y1of T M₁ Yh, ∀ r ∈ pCoreOf 2 (Mc ⊓ M₁),
      ⁅y, r⁆ ∈ M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) := fun y hy r hr =>
    ⟨hY1M₁ (hcommle (Subgroup.commutator_mem_commutator hy hr)),
      hcent (Subgroup.commutator_mem_commutator hy hr)⟩
  set C₁ : Subgroup G := M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) with hC₁
  have hDN : M₁ ≤ Subgroup.normalizer ((C₁ ⊔ pCoreOf 2 (Mc ⊓ M₁) : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨y, hy, a, ha, rfl⟩ := hY.fac m hm
    have hy1 : y ∈ Y1of T M₁ Yh := (le_sup_left : Yh ≤ Y1of T M₁ Yh) hy
    have hyM₁ : y ∈ M₁ := (hY.le_H hy).1
    have hyN : y ∈ Subgroup.normalizer ((C₁ ⊔ pCoreOf 2 (Mc ⊓ M₁) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨conj_mem_sup_of_commutator (fun x hx =>
        (Subgroup.mem_normalizer_iff.mp (M₁_le_normalizer_C₁ T M₁ hyM₁) x).mp hx)
        (fun b hb => hRC y hy1 b hb) z, fun hz => ?_⟩
      have := conj_mem_sup_of_commutator (c := y⁻¹) (fun x hx =>
        (Subgroup.mem_normalizer_iff.mp (M₁_le_normalizer_C₁ T M₁ (M₁.inv_mem hyM₁)) x).mp hx)
        (fun b hb => hRC y⁻¹ ((Y1of T M₁ Yh).inv_mem hy1) b hb) _ hz
      simpa [mul_assoc] using this
    have haN : a ∈ Subgroup.normalizer ((C₁ ⊔ pCoreOf 2 (Mc ⊓ M₁) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨M₁_le_normalizer_C₁ T M₁ ha.1, inf_le_normalizer_R1 Mc M₁ ha⟩
    exact (Subgroup.normalizer _).mul_mem hyN haN
  have hR1N : pCoreOf 2 (Mc ⊓ M₁) ≤ Subgroup.normalizer (C₁ : Set G) := hR1M₁.trans
    (M₁_le_normalizer_C₁ T M₁)
  have hD2 : ∀ d ∈ C₁ ⊔ pCoreOf 2 (Mc ⊓ M₁), ∃ k : ℕ,
      d ^ 2 ^ k ∈ Subgroup.centralizer (VZ T M₁ : Set G) := fun d hd => by
    obtain ⟨k, hk⟩ := C1Pack153.exists_pow_mem_of_mem_sup_two (pCoreOf_isPGroup 2 _) hR1N hd
    exact ⟨k, hk.2⟩
  have hDC := (isTwoReducedIn_VZ c.qtfe c.inM₁).1.2.2.2 (C₁ ⊔ pCoreOf 2 (Mc ⊓ M₁))
    (sup_le inf_le_left hR1M₁) hDN hD2
  exact c.Rhat_ne_bot h113 (autOn_eq_bot_of_le_centralizer (le_sup_right.trans hDC))

theorem Ctr5.Y2_autOn (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    autOn (Y2of T Mc M₁ Yh) (VZ T M₁) = autOn Yh (VZ T M₁) := by
  have h := lemma_14_1_17_two c.qtfe c.hyp1 hY.Y1_le (c.T_le_normalizer_Y1 hY)
    (by rw [hY.card_Y1]; exact ⟨1, rfl⟩)
  unfold Y2of
  rw [h, c.Yhat_comm h113 hY, hY.autOn_Y1]

theorem Ctr5.C1_R1_comm (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    ⁅M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G), pCoreOf 2 (Mc ⊓ M₁)⁆ ≤ pCoreOf 2 M₁ := by
  have hR1M₁ : pCoreOf 2 (Mc ⊓ M₁) ≤ M₁ := c.R1_le_T.trans c.T_le_M₁
  have h3 := (lemma_14_1_17_three c.qtfe c.hyp1 hY.Y1_le).1
  have h4 : ⁅imageOTwoQuot M₁ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)),
      imageOTwoQuot M₁ (pCoreOf 2 (Mc ⊓ M₁))⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono le_rfl le_sup_right).trans h3.le)
  rw [← S152Y.imageOTwoQuot_commutator (inf_le_left : M₁ ⊓ _ ≤ M₁) hR1M₁] at h4
  intro x hx
  have hcM₁ : ⁅M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G), pCoreOf 2 (Mc ⊓ M₁)⁆ ≤ M₁ :=
    Subgroup.commutator_le.mpr fun g hg r hr => by
      rw [commutatorElement_def]
      exact M₁.mul_mem (M₁.mul_mem (M₁.mul_mem hg.1 (hR1M₁ hr)) (M₁.inv_mem hg.1))
        (M₁.inv_mem (hR1M₁ hr))
  have hxM₁ : x ∈ M₁ := hcM₁ hx
  have h5 : (QuotientGroup.mk ⟨x, hxM₁⟩ : OTwoQuot M₁) ∈ imageOTwoQuot M₁
      ⁅M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G), pCoreOf 2 (Mc ⊓ M₁)⁆ :=
    mem_imageOTwoQuot_iff.mpr ⟨x, hxM₁, hx, rfl⟩
  rw [h4, Subgroup.mem_bot] at h5
  exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hxM₁⟩).mp h5

theorem Ctr5.Y2_normal (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    M₁ ≤ Subgroup.normalizer (Y2of T Mc M₁ Yh : Set G) := by
  set R₁ := pCoreOf 2 (Mc ⊓ M₁) with hR₁
  set Y₁ := Y1of T M₁ Yh with hY₁
  have hTN := c.T_le_normalizer_Y1 hY
  have hmul : ((Y₁ ⊔ T : Subgroup G) : Set G) = (Y₁ : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y₁ T hTN
  have hW : M₁ ≤ Subgroup.normalizer (conjClosure R₁ (Y₁ ⊔ T) : Set G) := by
    refine le_normalizer_of_conj' fun m hm x hx => ?_
    have hle : conjClosure R₁ (Y₁ ⊔ T) ≤
        (conjClosure R₁ (Y₁ ⊔ T)).comap (MulAut.conj m).toMonoidHom := by
      refine conjClosure_le fun g hg z hz => ?_
      show m * (g * z * g⁻¹) * m⁻¹ ∈ conjClosure R₁ (Y₁ ⊔ T)
      obtain ⟨y, hy, a, ha, rfl⟩ := hY.fac m hm
      have hg' : g ∈ (Y₁ : Set G) * (T : Set G) := by rw [← hmul]; exact hg
      obtain ⟨y₁, hy₁, t, ht, rfl⟩ := Set.mem_mul.mp hg'
      have e : y * a * (y₁ * t * z * (y₁ * t)⁻¹) * (y * a)⁻¹ =
          (y * (a * y₁ * a⁻¹)) * (a * (t * z * t⁻¹) * a⁻¹) * (y * (a * y₁ * a⁻¹))⁻¹ := by group
      rw [e]
      have hy1 : y ∈ Y₁ := (le_sup_left : Yh ≤ Y1of T M₁ Yh) hy
      have hay : a * y₁ * a⁻¹ ∈ Y₁ :=
        (Subgroup.mem_normalizer_iff.mp (c.M₁_le_normalizer_Y1 hY ha.1) y₁).mp hy₁
      have htz : t * z * t⁻¹ ∈ R₁ :=
        (Subgroup.mem_normalizer_iff.mp (c.T_le_normalizer_R1 ht) z).mp hz
      have hatz : a * (t * z * t⁻¹) * a⁻¹ ∈ R₁ :=
        (Subgroup.mem_normalizer_iff.mp (inf_le_normalizer_R1 Mc M₁ ha) _).mp htz
      exact mem_conjClosure (Subgroup.mem_sup_left (Y₁.mul_mem hy1 hay)) hatz
    exact hle hx
  unfold Y2of
  exact fun g hg => normalizer_le_normalizer_oTwoUpper _ (hW hg)

theorem Ctr5.Y2_le_comm (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    Y2of T Mc M₁ Yh ≤ ⁅Y1of T M₁ Yh, pCoreOf 2 (Mc ⊓ M₁)⁆ := by
  have hconj : conjClosure (pCoreOf 2 (Mc ⊓ M₁)) (Y1of T M₁ Yh ⊔ T) =
      ⁅Y1of T M₁ Yh, pCoreOf 2 (Mc ⊓ M₁)⁆ ⊔ pCoreOf 2 (Mc ⊓ M₁) :=
    conjClosure_sup_eq_commutator_sup (c.T_le_normalizer_Y1 hY) c.T_le_normalizer_R1
  unfold Y2of
  rw [hconj]
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  exact C1Pack153.exists_pow_mem_of_mem_sup_two (pCoreOf_isPGroup 2 _)
    (le_normalizer_commutator_of_le ((c.R1_le_T).trans (c.T_le_normalizer_Y1 hY))
      Subgroup.le_normalizer) hx

theorem Ctr5.comm_le (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    ⁅Y1of T M₁ Yh, pCoreOf 2 (Mc ⊓ M₁)⁆ ≤ Yh ⊔ pCoreOf 2 M₁ := by
  refine Subgroup.commutator_le.mpr fun x hx r hr => ?_
  have hx' : x ∈ ((Yh ⊔ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Yh _
    (fun y hy => M₁_le_normalizer_C₁ T M₁ (hY.le_H hy).1)] at hx'
  obtain ⟨y, hy, k, hk, rfl⟩ := Set.mem_mul.mp hx'
  have hkr : ⁅k, r⁆ ∈ pCoreOf 2 M₁ := c.C1_R1_comm hY (Subgroup.commutator_mem_commutator hk hr)
  have hyM₁ : y ∈ M₁ := (hY.le_H hy).1
  have h1 : y * ⁅k, r⁆ * y⁻¹ ∈ pCoreOf 2 M₁ :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M₁ hyM₁) _).mp hkr
  have hrN : r ∈ Subgroup.normalizer (Yh : Set G) := hY.H_norm (c.T_le_H (c.R1_le_T hr))
  have h2 : ⁅y, r⁆ ∈ Yh := by
    have : r * y⁻¹ * r⁻¹ ∈ Yh := (Subgroup.mem_normalizer_iff.mp hrN y⁻¹).mp (Yh.inv_mem hy)
    rw [commutatorElement_def]
    have e : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
    rw [e]
    exact Yh.mul_mem hy this
  have e : ⁅y * k, r⁆ = (y * ⁅k, r⁆ * y⁻¹) * ⁅y, r⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Yh ⊔ pCoreOf 2 M₁).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)

theorem Ctr5.pCoreOf_M₁_le_T (c : Ctr5 T Mc M M₁) : pCoreOf 2 M₁ ≤ T :=
  pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le151 c.qtfe.sylow c.T_le_M₁)

theorem Ctr5.Y2_le_H (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    Y2of T Mc M₁ Yh ≤ M₁ ⊓ M :=
  (c.Y2_le_comm hY).trans ((c.comm_le hY).trans (sup_le hY.le_H (c.pCoreOf_M₁_le_T.trans c.T_le_H)))

theorem Ctr5.false_of_Y2_normal (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁)
    (hY : Yd5 T Mc M M₁ Yh) (hN : M ≤ Subgroup.normalizer (Y2of T Mc M₁ Yh : Set G)) : False := by
  have hY2M₁ : Y2of T Mc M₁ Yh ≤ M₁ := (c.Y2_le_H hY).trans inf_le_left
  have hY2ne : Y2of T Mc M₁ Yh ≠ ⊥ := by
    intro h
    have h1 := c.Y2_autOn h113 hY
    rw [h] at h1
    have : Nat.card (autOn (⊥ : Subgroup G) (VZ T M₁)) = 3 := by
      rw [h1]; exact hY.card
    have h2 : autOn (⊥ : Subgroup G) (VZ T M₁) = ⊥ := autOn_eq_bot_of_le_centralizer bot_le
    rw [h2, Subgroup.card_bot] at this
    omega
  have hY2O : oTwoUpper (Y2of T Mc M₁ Yh) = Y2of T Mc M₁ Yh := by
    unfold Y2of; exact C1Pack153.oTwoUpper_idem' _
  have hCT : CharTwo M₁ := by
    obtain ⟨S, hS⟩ := c.qtfe.exists_sylow
    exact c.qtfe.qtke.2.1 M₁ c.inM₁.1.1 ⟨S, hS ▸ c.T_le_M₁⟩
  have hne := C1Pack153.pCoreOf_ne_bot_of_normal hCT hY2M₁ (c.Y2_normal hY) hY2ne hY2O
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (Y2of T Mc M₁ Yh) : Set G)) :=
    ⟨pCoreOf 2 (Y2of T Mc M₁ Yh), hne, pCoreOf_isPGroup 2 _, rfl⟩
  have hYL := normalizer_le_normalizer_pCoreOf (r := 2) (Y2of T Mc M₁ Yh)
  have hL : Subgroup.normalizer (pCoreOf 2 (Y2of T Mc M₁ Yh) : Set G) = M₁ :=
    c.inM₁.1.2 _ hloc ((c.Y2_normal hY).trans hYL)
  have hML : M ≤ M₁ := fun x hx => hL ▸ hYL (hN hx)
  exact c.ne (c.std.hs.mf.1.1.1.2 M₁ c.inM₁.1.1 hML)

end Facts

end C1Pack5

end CFSG.Quasithin
