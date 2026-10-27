module

public import CFSG.Quasithin.EmptyFaithful.S152ZFMain
public import CFSG.Quasithin.Recognition.F112J2Ctx

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F204

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem hyp111_plus (hH : Hyp111 K1 L2 S) (hinf : S ⊓ L2 ≤ twistFree K1 S) :
    Hyp111 K1 L2 (twistFree K1 S) := by
  set S0 := twistFree K1 S with hS0
  have hS1 : S ≤ Subgroup.normalizer (K1 : Set G) := hH.h1.normalizes
  have hS2 : S ≤ Subgroup.normalizer (L2 : Set G) := hH.h2.normalizes
  have hle : S0 ≤ S := twistFree_le hS1 hH.h1.pgroup hH.h1.sylow
  have hinfK : S0 ⊓ K1 = S ⊓ K1 := twistFree_inf_L2 hS1 hH.h1.pgroup hH.h1.sylow
  have hinfL : S0 ⊓ L2 = S ⊓ L2 :=
    le_antisymm (inf_le_inf_right L2 hle) (le_inf hinf inf_le_right)
  have hBK : borelOf K1 S0 = borelOf K1 S := by
    unfold borelOf
    rw [hinfK]
  have hBL : borelOf L2 S0 = borelOf L2 S := by
    unfold borelOf
    rw [hinfL]
  have hSN : S ≤ Subgroup.normalizer (S0 : Set G) := le_normalizer_twistFree hS1
  have hSB1 : S ≤ Subgroup.normalizer ((borelOf K1 S : Subgroup G) : Set G) :=
    F1.le_normalizer_borelOf hS1
  have hSB2 : S ≤ Subgroup.normalizer ((borelOf L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_borelOf hS2
  refine ⟨⟨inferInstance, hH.h1.pgroup.to_le hle, hle.trans hS1, ?_, hH.h1.listed, ?_, ?_⟩,
    ⟨inferInstance, hH.h1.pgroup.to_le hle, hle.trans hS2, ?_, hH.h2.listed, ?_, ?_⟩, ?_⟩
  · rw [hinfK]
    exact hH.h1.sylow
  · rw [hBL]
    exact hH.h1.borel_le
  · rw [hBL]
    have hHK : K1 ⊔ S0 ⊔ borelOf L2 S ≤ K1 ⊔ S ⊔ borelOf L2 S :=
      sup_le_sup_right (sup_le_sup_left hle K1) _
    refine CharTwo.of_normal hH.h1.charTwo hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr ?_)
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
    · intro x hx
      refine Subgroup.inf_normalizer_le_normalizer_sup (K1 ⊔ S0) (borelOf L2 S) ⟨?_, hSB2 hx⟩
      exact Subgroup.inf_normalizer_le_normalizer_sup K1 S0 ⟨hS1 hx, hSN hx⟩
    · exact le_sup_right.trans Subgroup.le_normalizer
  · rw [hinfL]
    exact hH.h2.sylow
  · rw [hBK]
    exact hH.h2.borel_le
  · rw [hBK]
    have hHK : L2 ⊔ S0 ⊔ borelOf K1 S ≤ L2 ⊔ S ⊔ borelOf K1 S :=
      sup_le_sup_right (sup_le_sup_left hle L2) _
    refine CharTwo.of_normal hH.h2.charTwo hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr ?_)
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
    · intro x hx
      refine Subgroup.inf_normalizer_le_normalizer_sup (L2 ⊔ S0) (borelOf K1 S) ⟨?_, hSB1 hx⟩
      exact Subgroup.inf_normalizer_le_normalizer_sup L2 S0 ⟨hS2 hx, hSN hx⟩
    · exact le_sup_right.trans Subgroup.le_normalizer
  · have hG0' : K1 ⊔ L2 ⊔ S0 ≤ K1 ⊔ L2 ⊔ S := sup_le_sup_left hle _
    have hnorm : K1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer ((K1 ⊔ L2 ⊔ S0 : Subgroup G) : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
      · exact (le_sup_right.trans le_sup_left).trans Subgroup.le_normalizer
      · intro x hx
        refine Subgroup.inf_normalizer_le_normalizer_sup (K1 ⊔ L2) S0 ⟨?_, hSN hx⟩
        exact Subgroup.inf_normalizer_le_normalizer_sup K1 L2 ⟨hS1 hx, hS2 hx⟩
    have hsub : pCoreOf 2 (K1 ⊔ L2 ⊔ S0) ≤ pCoreOf 2 (K1 ⊔ L2 ⊔ S) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hG0')
        (hnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    rw [hH.o2] at hsub
    exact le_bot_iff.mp hsub

theorem pCoreOf_le_pCoreOf_plus (hS1 : S ≤ Subgroup.normalizer (K1 : Set G)) (hS : IsPGroup 2 S)
    (hsyl : IsSylowTwoOf (S ⊓ K1) K1) :
    pCoreOf 2 (K1 ⊔ S) ≤ pCoreOf 2 (K1 ⊔ twistFree K1 S) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((le_sup_right : pCoreOf 2 (K1 ⊔ S) ≤ twistFree K1 S).trans le_sup_right) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact (sup_le_sup_left (twistFree_le hS1 hS hsyl) K1).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K1 ⊔ S))

theorem twistFree_le_sup_pCoreOf (hS1 : S ≤ Subgroup.normalizer (K1 : Set G)) (hS : IsPGroup 2 S)
    (hsyl : IsSylowTwoOf (S ⊓ K1) K1) :
    twistFree K1 S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ twistFree K1 S) :=
  sup_le (inf_le_right.trans le_sup_left)
    ((pCoreOf_le_pCoreOf_plus hS1 hS hsyl).trans le_sup_right)

theorem r1Setting_plus_of_inf (h : R1SettingLegacyBare K1 L2 S Zs) (hinf : S ⊓ L2 ≤ twistFree K1 S) :
    R1SettingLegacyBare K1 L2 (twistFree K1 S) Zs := by
  have hS1 : S ≤ Subgroup.normalizer (K1 : Set G) := h.hyp.h1.normalizes
  have hle : twistFree K1 S ≤ S := twistFree_le hS1 h.hyp.h1.pgroup h.hyp.h1.sylow
  have hinfL : twistFree K1 S ⊓ L2 = S ⊓ L2 :=
    le_antisymm (inf_le_inf_right L2 hle) (le_inf hinf inf_le_right)
  have hBL : borelOf L2 (twistFree K1 S) = borelOf L2 S := by
    unfold borelOf
    rw [hinfL]
  have hB2S : borelOf L2 S ≤ Subgroup.normalizer (S : Set G) :=
    le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp h.hnorm)
  have hB2K : borelOf L2 S ≤ Subgroup.normalizer (K1 : Set G) := h.hyp.h1.borel_le
  have hB2P : borelOf L2 S ≤ Subgroup.normalizer ((K1 ⊔ S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hB2K hB2S
  have hB2SK : borelOf L2 S ≤ Subgroup.normalizer ((S ⊓ K1 : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hB2S hb, hB2K hb⟩
  have hB2Q : borelOf L2 S ≤ Subgroup.normalizer ((pCoreOf 2 (K1 ⊔ S) : Subgroup G) : Set G) :=
    hB2P.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K1 ⊔ S))
  have hB2S0 : borelOf L2 S ≤ Subgroup.normalizer ((twistFree K1 S : Subgroup G) : Set G) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hB2SK hb, hB2Q hb⟩
  exact
    { hyp := hyp111_plus h.hyp hinf
      qt := F204.isQuasithinSub_mono (sup_le_sup_left hle _) h.qt
      hnorm := by
        rw [hBL]
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
          (sup_le Subgroup.le_normalizer hB2S0)
      cComp_mem := cComp_mem_of_le h.cComp_mem le_sup_left (sup_le_sup_left hle K1)
      s3 := h.s3
      solv := by
        have := h.solv
        exact Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (sup_le_sup_left hle L2)) (Subgroup.inclusion_injective _)
      card_Z := h.card_Z
      Z_le := h.Z_le
      Z_cent := h.Z_cent
      Z_not_norm := h.Z_not_norm
      Z_cent_S := h.Z_cent_S.trans (Subgroup.centralizer_le hle)
      K1_cent_Z := h.K1_cent_Z
      V_le := h.V_le.trans (pCoreOf_le_pCoreOf_plus hS1 h.hyp.h1.pgroup h.hyp.h1.sylow)
      V_card := h.V_card }

theorem le_normalizer_V (h : R1SettingLegacyBare K1 L2 S Zs) :
    S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) := by
  have hc := F112J2.conjClosure_sup_S h.hyp.h2.normalizes (F112J2.S_le_centralizer_Z h)
  have := le_normalizer_conjClosure Zs (L2 ⊔ S)
  rw [hc] at this
  exact le_sup_right.trans this

theorem vBeta_plus_eq (h : R1SettingLegacyBare K1 L2 S Zs) :
    vBeta K1 L2 (twistFree K1 S) Zs = vBeta K1 L2 S Zs := by
  have hS1 : S ≤ Subgroup.normalizer (K1 : Set G) := h.hyp.h1.normalizes
  have hle : twistFree K1 S ≤ S := twistFree_le hS1 h.hyp.h1.pgroup h.hyp.h1.sylow
  have hSV := le_normalizer_V h
  refine le_antisymm (conjClosure_mono le_rfl (sup_le_sup_left hle K1)) ?_
  refine conjClosure_le fun g hg v hv => ?_
  have hSN : S ≤ Subgroup.normalizer ((K1 ⊔ twistFree K1 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hS1 (le_normalizer_twistFree hS1)
  have hg' : g ∈ (K1 ⊔ twistFree K1 S) ⊔ S :=
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right : K1 ⊔ S ≤ (K1 ⊔ twistFree K1 S) ⊔ S) hg
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSN).mp hg'
  have hbv : b * v * b⁻¹ ∈ conjClosure Zs L2 := (Subgroup.mem_normalizer_iff.mp (hSV hb) v).mp hv
  have hmem := mem_conjClosure ha hbv
  have e : a * b * v * (a * b)⁻¹ = a * (b * v * b⁻¹) * a⁻¹ := by group
  rw [e]
  exact hmem

end CFSG.Quasithin.SzVB
