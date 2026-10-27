module

public import CFSG.Quasithin.MS93.S32FF
public import CFSG.Quasithin.Background.C124Dict
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.B5Irr

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S32

section ToG

variable [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem toG_top : C124.toG hV ⊤ = V := by
  ext g
  rw [C124.mem_toG]
  constructor
  · rintro ⟨w, -, rfl⟩
    exact w.val_mem
  · intro hg
    exact ⟨IntMod.mk hV ⟨g, hg⟩, Subgroup.mem_top _, rfl⟩

theorem toG_fixV {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    C124.toG hV (fixV (autI hV K)) = V ⊓ Subgroup.centralizer (K : Set G) := by
  ext g
  rw [C124.mem_toG]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.val_mem, (mem_fixV_autI hV hK w).mp hw⟩
  · rintro ⟨hgV, hgC⟩
    exact ⟨IntMod.mk hV ⟨g, hgV⟩, (mem_fixV_autI hV hK _).mpr hgC, rfl⟩

end ToG

section Fixed

variable {V : Type} [CommGroup V]

theorem fixV_eq_fixed (X : Subgroup (MulAut V)) : fixV X = XMod.fixed ↥X ⊤ := by
  ext v
  constructor
  · intro hv
    exact ⟨Subgroup.mem_top _, fun a => hv a a.2⟩
  · intro hv x hx
    exact hv.2 ⟨x, hx⟩

theorem fixV_ne_bot_of_isPGroup [Finite V] (hV : ∀ v : V, v ^ 2 = 1) [Nontrivial V]
    {P : Subgroup (MulAut V)} (hP : IsPGroup 2 ↥P) : fixV P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints V
  have hfix : Nat.card (MulAction.fixedPoints ↥P V) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one]; exact hV v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card V % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

end Fixed

end S32

open S32

section Hyps

variable [Finite G] {M T L W : Subgroup G}

namespace IsSecW

variable (hs : IsSecW M L W) (h : PUHyp M T L)
include hs h

omit h [Finite G] in
theorem ne_bot : W ≠ ⊥ := by
  rintro rfl
  apply hs.not_le
  rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.mpr (fun x hx => by
    simp only [Set.mem_singleton_iff] at hx
    simp [hx])]
  exact le_top

theorem nontrivial : Nontrivial (IntMod W (hs.isElemAbelian h)) := by
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hs.ne_bot
  refine ⟨⟨IntMod.mk _ w, 1, fun he => hw1 ?_⟩⟩
  exact Subtype.ext (congrArg IntMod.val he)

theorem ffHyp (hSQ : SQTKQuot)
    (hirr : XMod.IsIrrSec ↥(autI (hs.isElemAbelian h) L)
      (⊥ : Subgroup (IntMod W (hs.isElemAbelian h))) ⊤)
    (hFF : IsFFModule (autI (hs.isElemAbelian h) M)) :
    FFHyp (autI (hs.isElemAbelian h) M) (autI (hs.isElemAbelian h) L) := by
  set hW := hs.isElemAbelian h
  have : Nontrivial (IntMod W hW) := hs.nontrivial h
  refine ⟨hs.autI_L_le h, hs.autI_le_normalizer h, hs.quasisimple h, hs.sqtk h hSQ,
    hs.rankTwo h, hs.cent h, hs.two h, ?_, ?_, hFF⟩
  · obtain ⟨T₀, hT₀⟩ := B5.exists_isSylowTwoOf (autI hW L)
    refine ⟨T₀, hT₀, ?_⟩
    have hne : fixV T₀ ≠ ⊥ := fixV_ne_bot_of_isPGroup IntMod.sq_eq_one hT₀.2.1
    have hinv : XMod.IsInv ↥(autI hW L)
        (G6.submoduleClosure (autI hW M) (fixV T₀) : Subgroup (IntMod W hW)) :=
      fun a w hw => submoduleClosure_inv (hs.autI_L_le h a.2) hw
    rcases hirr.2 _ hinv bot_le le_top with hb | ht
    · exact absurd (eq_bot_iff.mpr ((le_submoduleClosure _ _).trans hb.le)) hne
    · exact ht
  · rw [eq_bot_iff]
    intro v hv
    have hvK : v ∈ fixV (autI hW L) := fun x hx => hv x (hs.autI_L_le h hx)
    have hirr1 := hirr.1
    by_contra hv1
    have hfix : XMod.IsInv ↥(autI hW L) (fixV (autI hW L)) := fun a w hw x hx => by
      show x ((a : MulAut (IntMod W hW)) w) = (a : MulAut (IntMod W hW)) w
      rw [hw a a.2, hw x hx]
    rcases hirr.2 _ hfix bot_le le_top with hb | ht
    · exact hv1 (by rw [hb] at hvK; exact hvK)
    ·
      apply hs.not_le
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hmem : IntMod.mk hW ⟨w, hw⟩ ∈ fixV (autI hW L) := by rw [ht]; exact Subgroup.mem_top _
      have h1 := hmem _ (convI_mem_autI hW hl (hs.L_le_normalizer h hl))
      have h2 := congrArg IntMod.val h1
      rw [convI_apply_val] at h2
      symm
      calc l * w = (l * w * l⁻¹) * l := by group
        _ = w * l := by rw [show l * w * l⁻¹ = w from h2]

theorem ms15Hyp (hSQ : SQTKQuot) (hcomm : commV (autI (hs.isElemAbelian h) L) = ⊤)
    (hfix : fixV (autI (hs.isElemAbelian h) L) ≠ ⊥)
    (hirr : XMod.IsIrrSec ↥(autI (hs.isElemAbelian h) L) (fixV (autI (hs.isElemAbelian h) L)) ⊤)
    (hFF : IsFFModule (autI (hs.isElemAbelian h) M)) :
    MS15Hyp (autI (hs.isElemAbelian h) M) (autI (hs.isElemAbelian h) L) := by
  obtain ⟨A, hAX, hA1, hA2, hcard⟩ := hFF
  refine ⟨hs.autI_L_le h, hs.autI_le_normalizer h, hs.quasisimple h, hs.sqtk h hSQ,
    hs.rankTwo h, hs.cent h, hs.two h, hcomm, hfix, hirr, A, hAX, hA1, hA2, ?_⟩
  refine hcard.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le fun v hv a ha => ?_))
  rw [hv a ha, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem b51 (h51 : AsB51) (hSQ : SQTKQuot) (hFF : IsFFModule (autI (hs.isElemAbelian h) M)) :
    B51Conclusion (ffJ (autI (hs.isElemAbelian h) M)) (autI (hs.isElemAbelian h) L) :=
  h51 _ IntMod.sq_eq_one _ _ (hs.b51Hyp h hSQ hFF)

end IsSecW

end Hyps

namespace S32

section UCases

variable [Finite G] {M T L : Subgroup G}

@[expose] def NoSL45 : Prop :=
  ∀ (P : Type) [Group P], IsRankTwoLie2Derived (P ⧸ Subgroup.center P) → ∀ d : ℕ,
    (d = 4 ∨ d = 5) → (↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) ≃* P) → False

theorem isSecW_Uq (h : PUHyp M T L) : IsSecW M L (Uq M T L) :=
  ⟨h.Uq_le_Xq, le_normalizer_Uq h.le_normalizer, h.not_le_centralizer_of_Uq_le le_rfl⟩

theorem isSecW_Xq (h : PUHyp M T L) : IsSecW M L (Xq M) :=
  ⟨le_rfl, le_normalizer_Xq M, h.not_le_centralizer_of_Uq_le h.Uq_le_Xq⟩

theorem commV_autI_Uq (h : PUHyp M T L) :
    commV (autI h.isElemAbelian_Uq L) = ⊤ := by
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := (isSecW_Uq h).L_le_normalizer h
  rw [← C124.toG_inj h.isElemAbelian_Uq, C124.toG_commV h.isElemAbelian_Uq hLU, toG_top,
    Subgroup.commutator_comm, h.Uq_comm]

theorem toG_fixV_Uq (h : PUHyp M T L) :
    C124.toG h.isElemAbelian_Uq (fixV (autI h.isElemAbelian_Uq L)) = Uq M T L ⊓ Zq M L := by
  rw [toG_fixV _ ((isSecW_Uq h).L_le_normalizer h), h.Uq_inf_Zq]

theorem u_cases (h : PUHyp M T L) (h51 : AsB51) (h14 : MS14AS) (h15 : MS15AS)
    (hSQ : SQTKQuot) (h45 : NoSL45) :
    (XMod.IsIrrSec ↥(autI h.isElemAbelian_Uq L) (fixV (autI h.isElemAbelian_Uq L)) ⊤ ∧
      ((fixV (autI h.isElemAbelian_Uq L) = ⊥ ∧
          FFConclusion (autI h.isElemAbelian_Uq M) (autI h.isElemAbelian_Uq L)) ∨
        (fixV (autI h.isElemAbelian_Uq L) ≠ ⊥ ∧
          MS15Conclusion (autI h.isElemAbelian_Uq M) (autI h.isElemAbelian_Uq L)))) ∨
    B51Case1ii (ffJ (autI h.isElemAbelian_Uq M)) (autI h.isElemAbelian_Uq L) := by
  have hs := (isSecW_Uq h)
  have hcomm := (commV_autI_Uq h)
  have hFF := h.isFFModule_of_le_Z0q hs (Uq_le_Z0q h.L_le)
  obtain ⟨⟨-, hcases⟩, -, -, -, -, -⟩ := hs.b51 h h51 hSQ hFF
  rcases hcases with hi | hii | ⟨n, -, hm, π, U₁, U₂, -, h1, -⟩ | ⟨-, n, hn, k, hk1, hkn, I, π, -,
      -, -, hreal⟩
  · have hirr : XMod.IsIrrSec ↥(autI h.isElemAbelian_Uq L)
        (fixV (autI h.isElemAbelian_Uq L)) ⊤ := by
      have := hi.1.2.2.2
      rwa [hcomm, ← fixV_eq_fixed] at this
    by_cases hC : fixV (autI h.isElemAbelian_Uq L) = ⊥
    · rw [hC] at hirr
      refine Or.inl ⟨hC ▸ hirr, Or.inl ⟨hC, h14 _ IntMod.sq_eq_one _ _ ?_⟩⟩
      exact hs.ffHyp h hSQ hirr hFF
    · exact Or.inl ⟨hirr, Or.inr ⟨hC, h15 _ IntMod.sq_eq_one _ _
        (hs.ms15Hyp h hSQ hcomm hC hirr hFF)⟩⟩
  · exact Or.inr hii
  · exact (h45 _ (hs.rankTwo h) _ hm (FFC.equivOfRealizes (FFModel.nat_faithful _) h1)).elim
  · exact (h45 _ (hs.rankTwo h) _ hn
      (FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩))).elim

end UCases

end S32

end CFSG.Quasithin.MS93
