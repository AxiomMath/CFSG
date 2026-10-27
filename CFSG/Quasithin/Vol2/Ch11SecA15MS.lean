module

public import CFSG.Quasithin.Vol2.Ch11SecA11Setup
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

omit [Finite G] in
theorem lOf_sup_le_normalizer_ROf :
    LOf L V₁ ⊔ T ≤ Subgroup.normalizer (ROf T L V₁ : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem isPGroup_ROf : IsPGroup 2 (ROf T L V₁) :=
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem ROf_le_T (h : Hyp11 G T L I n) : ROf T L V₁ ≤ T :=
  CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)

theorem ROf_le_normalizer_L (h : Hyp11 G T L I n) :
    ROf T L V₁ ≤ Subgroup.normalizer (L : Set G) :=
  (ROf_le_T h).trans h.normal

theorem pCoreOf_le_ROf (h : Hyp11 G T L I n) : pCoreOf 2 L ≤ ROf T L V₁ := by
  have hLT : pCoreOf 2 L ≤ T :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h)).trans inf_le_left
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hLT.trans le_sup_right)
    (sup_le ?_ ?_) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  · exact ((perfectCore_le _).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  · exact h.normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

theorem T_le_normalizer_lOf_sup_ROf (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) :
    T ≤ Subgroup.normalizer ((LOf L V₁ ⊔ ROf T L V₁ : Subgroup G) : Set G) :=
  (le_inf (T_le_normalizer_lOf h.normal (IsVi.le_normalizer hU))
    (le_sup_right.trans lOf_sup_le_normalizer_ROf)).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem pCoreOf_lOf_sup_ROf (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) :
    pCoreOf 2 (LOf L V₁ ⊔ ROf T L V₁) = ROf T L V₁ := by
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ (sup_le ?_ ?_)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le le_sup_left
        ((ROf_le_T h).trans le_sup_right))
    · exact le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    · exact (T_le_normalizer_lOf_sup_ROf h hU).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le (le_sup_left.trans lOf_sup_le_normalizer_ROf) Subgroup.le_normalizer) isPGroup_ROf

theorem coe_msG0 (h : Hyp11 G T L I n) :
    ((L ⊔ ROf T L V₁ : Subgroup G) : Set G) = (L : Set G) * (ROf T L V₁ : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (ROf_le_normalizer_L h)

theorem msG0_le_normalizer (h : Hyp11 G T L I n) :
    L ⊔ T ≤ Subgroup.normalizer ((L ⊔ ROf T L V₁ : Subgroup G) : Set G) := by
  refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
  exact (le_inf h.normal (le_sup_right.trans lOf_sup_le_normalizer_ROf)).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem charTwo_LT (h : Hyp11 G T L I n) : QuasithinUnique.CharTwo (L ⊔ T) := by
  refine charTwo_of_inH h.fsu.qtke.2.1 (h.fsu.sylow.1.toSylow h.fsu.sylow.2)
    ⟨le_sup_right, fun h0 => fsuV_ne_bot h (eq_bot_iff.mpr ?_)⟩
  rw [← h0]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((fsuV_le_T h).trans le_sup_right)
    (sup_le (L_le_normalizer_fsuV h) (T_le_normalizer_fsuV T I)) (isPGroup_fsuV h)

theorem charTwo_msG0 (h : Hyp11 G T L I n) :
    QuasithinUnique.CharTwo (L ⊔ ROf T L V₁) := by
  have hle : L ⊔ ROf T L V₁ ≤ L ⊔ T := sup_le_sup_left (ROf_le_T h) L
  have hn : ((L ⊔ ROf T L V₁).subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (msG0_le_normalizer h)
  exact QuasithinUnique.CharTwo.of_isSubnormal (charTwo_LT h) hle hn.isSubnormal

theorem L_mem_cComp_msG0 (h : Hyp11 G T L I n) : L ∈ cComp (L ⊔ ROf T L V₁) := by
  have hLM := mem_cComp_of_le h le_rfl (sup_le Subgroup.le_normalizer h.normal)
  have hn : (L.subgroupOf (L ⊔ ROf T L V₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (ROf_le_normalizer_L h))
  exact mem_cComp_of_quasisimple (ne_bot_of_mem_cComp hLM) (perfect_of_mem_cComp hLM)
    h.fsu.quasisimple (IsSubnormal.step le_sup_left hn (IsSubnormal.refl _))

theorem isSylowTwoOf_inf_msG0 (h : Hyp11 G T L I n) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ (L ⊔ ROf T L V₁)) (L ⊔ ROf T L V₁) :=
  B6.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)
    (sup_le_sup_left (ROf_le_T h) L) (msG0_le_normalizer h)

theorem inf_msG0_le (h : Hyp11 G T L I n) :
    T ⊓ (L ⊔ ROf T L V₁) ≤ (T ⊓ L) ⊔ ROf T L V₁ := by
  intro x ⟨hxT, hxG⟩
  have hx : x ∈ ((L ⊔ ROf T L V₁ : Subgroup G) : Set G) := hxG
  rw [coe_msG0 h] at hx
  obtain ⟨l, hl, r, hr, rfl⟩ := hx
  have hlT : l ∈ T := by
    have := T.mul_mem hxT (T.inv_mem (ROf_le_T h hr))
    simpa using this
  exact Subgroup.mul_mem_sup ⟨hlT, hl⟩ hr

theorem ms3_of_not_le (h331 : Stmt3_3_1) (h : Hyp11 G T L I n)
    (hN : ¬ Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∀ C : Subgroup G, C ≤ ROf T L V₁ → C ≠ ⊥ → (C.subgroupOf (ROf T L V₁)).Characteristic →
      ¬ L ⊔ ROf T L V₁ ≤ Subgroup.normalizer (C : Set G) := by
  intro C hCR hC hchar hG
  have hRC : Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf (ROf T L V₁))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at this
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    (le_sup_right.trans lOf_sup_le_normalizer_ROf).trans hRC
  exact hN (hRC.trans (normalizer_le_of_isPGroup h331 h (isPGroup_ROf.to_le hCR) hC
    (sup_le (le_sup_left.trans hG) hTC)))

end CFSG.Quasithin.Vol2.Ch11.SecA
