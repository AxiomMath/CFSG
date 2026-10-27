module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.Open

private theorem cp_baseChange_mem {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    (Ω : Type) [Field Ω] [Algebra (GaloisField 2 (2 * f)) Ω]
    [IsAlgClosure (GaloisField 2 (2 * f)) Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    (c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
    baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ TwistedDiag.Rgrp Ω Fr := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : GaloisField 2 (2 * f), frobQ 2 f c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  have hle : TwistedDiag.Cgrp (GaloisField 2 (2 * f)) (frobQ 2 f) Ω ≤
      TwistedDiag.Rgrp Ω Fr :=
    (TwistedDiag.cgrp_facts hf (GaloisField 2 (2 * f)) hK (frobQ 2 f) hσ h3 Ω Fr hFr).2.1
  apply hle
  change baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
      (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
    (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
      (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω))
  exact Subgroup.mem_map.2 ⟨c, c.2, rfl⟩

theorem exists_rgrpAut_baseChange {f : ℕ} (hf : 1 ≤ f) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ f) :
    ∃ Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      Function.Injective Φ ∧ Φ.range = LayerSixE.twInndiagAut f ∧
      ∀ (c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
        (hc : baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
          (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ TwistedDiag.Rgrp Ω Fr),
        Φ ⟨baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω) (c : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * f))), hc⟩ = MulAut.conj c := by
  classical
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : GaloisField 2 (2 * f), frobQEquiv hf c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  refine ⟨rgrpConjAut hf hK (frobQEquiv hf) hσ Fr hFr,
    rgrpConjAut_injective hf hK (frobQEquiv hf) hσ Fr hFr, ?_, ?_⟩
  · refine Eq.trans (rgrpConjAut_range (L := Ω) hf hK (frobQEquiv hf) hσ Fr hFr) ?_
    rw [LayerSixE.twInndiagAut]
    exact (inn_sup_compatParamAut_eq_range_twConj (K := GaloisField 2 (2 * f))
      (σ := frobQEquiv hf)).symm
  · intro c hc
    have hcΓ : (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf) :=
      RecipeExcLang.graphFixedRootGroup_le_twInndiag (frobQEquiv hf) c.2
    set e := twInndiagEquivRgrp hf hK (frobQEquiv hf) hσ Fr hFr with he
    have h1 : e ⟨c, hcΓ⟩ = ⟨baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hc⟩ := Subtype.ext rfl
    have hval : rgrpConjAut hf hK (frobQEquiv hf) hσ Fr hFr
        ⟨baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
          (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hc⟩ = MulAut.conj c := by
      rw [← h1, rgrpConjAut_apply_baseChange]
      exact RecipeExcLang.twConj_of_mem_C0 (frobQEquiv hf) c
    exact hval

theorem comap_map_conj_eq_map_baseChange {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    (Ω : Type) [Field Ω] [Algebra (GaloisField 2 (2 * f)) Ω]
    [IsAlgClosure (GaloisField 2 (2 * f)) Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    (Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hΦinj : Function.Injective Φ)
    (hΦc : ∀ (c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (hc : baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ TwistedDiag.Rgrp Ω Fr),
      Φ ⟨baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω) (c : ModGL TwistTag.E6.tag
        (GaloisField 2 (2 * f))), hc⟩ = MulAut.conj c)
    (Xh : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
    ((Xh.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f)))).comap Φ).map (TwistedDiag.Rgrp Ω Fr).subtype =
      Xh.map ((baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)).comp
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    obtain ⟨c, hcX, hcz⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hz)
    have hbase := cp_baseChange_mem hf h3 Ω Fr hFr c
    have h1 : Φ ⟨baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
          (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hbase⟩ = Φ z := by
      rw [hΦc c hbase]
      exact hcz
    have h2v : baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
          (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) = (z : ModGL Tag.E6 Ω) :=
      congrArg Subtype.val (hΦinj h1)
    have hy' : y = baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
          (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := hzy.symm.trans h2v.symm
    rw [hy']
    exact Subgroup.mem_map.2 ⟨c, hcX, rfl⟩
  · intro hy
    obtain ⟨c, hcX, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨⟨baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
      (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))),
      cp_baseChange_mem hf h3 Ω Fr hFr c⟩, ?_, rfl⟩
    refine Subgroup.mem_comap.2 ?_
    rw [hΦc c (cp_baseChange_mem hf h3 Ω Fr hFr c)]
    exact Subgroup.mem_map.2 ⟨c, hcX, rfl⟩

end CFSG.StandardType.NoOffTwE6Three
