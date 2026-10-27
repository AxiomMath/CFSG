module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6FiveLang
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6InnerForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Open

namespace ExcFrames

local instance fiveAutFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance fiveAutNeZero : NeZero (5 : ℕ) := ⟨by norm_num⟩

section FiveAut


private theorem units_map_entrywiseHom_frameDiag_of_fixes {L : Type} [Field L] {ζ : Lˣ}
    (hζ : ζ ^ 5 = 1) {δL : L ≃+* L}
    (hδLζ : Units.map (δL : L →+* L).toMonoidHom ζ = ζ) (s : Fin 6 → ZMod 5) :
    Units.map (entrywiseHom (δL : L →+* L)) (frameDiag (τ := Tag.E6) ζ hζ s) =
      frameDiag (τ := Tag.E6) ζ hζ s := by
  rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]
  simp only [frameDiag, CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  rw [TableBExc.E6Three.zetaVec_apply, map_pow, hδLζ]

private theorem canonicalRep_conj_frameDiag_six {L : Type} [Field L] {ζ : Lˣ}
    (hζ : ζ ^ 5 = 1) (w : WeylGroup TwistTag.E6.tag) (s : Fin 6 → ZMod 5) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹ =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (TableBExc.torusAct TwistTag.E6.tag 5 w s) :=
  canonicalRep_conj_frameDiag (τ := TwistTag.E6.tag) ζ hζ w s

theorem fiveLangFrame_aut {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    (ζK : (GaloisField 2 (2 * f))ˣ) (hζKord : orderOf ζK = 5)
    (hζ : (Units.map (algebraMap (GaloisField 2 (2 * f))
      (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) ^ 5 = 1)
    (g₀ : ModGL Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))))
    (hg₀C : g₀ ∈ adjointGroup Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))))
    (ι₀ : Multiplicative (Fin 6 → ZMod 5) →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hι₀ : Function.Injective ι₀)
    (hbase : ∀ s : Fin 6 → ZMod 5,
      baseChangeGL (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f))))
        (((ι₀ (Multiplicative.ofAdd s)) : _) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        g₀ * frameDiag (τ := Tag.E6)
          (Units.map (algebraMap (GaloisField 2 (2 * f))
            (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * g₀⁻¹) :
    ∀ β : MulAut ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)),
      β ^ 5 = 1 → (∀ b ∈ ι₀.range, β b ∈ ι₀.range) →
        ∃ w : WeylGroup .E6, ∀ s : Fin 6 → ZMod 5,
          β (ι₀ (Multiplicative.ofAdd s)) =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 w s)) := by
  intro β hβ5 hstab
  have hζK5 : ζK ^ 5 = 1 := by rw [← hζKord, pow_orderOf_eq_one]
  have hζK5' : ((ζK : GaloisField 2 (2 * f))) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζK5, Units.val_one]
  have h3 : ¬ 3 ∣ 2 ^ f + 1 := not_three_dvd_two_pow_add_one_of_five_dvd hf h5
  obtain ⟨x, δ, hδ5, hβx⟩ := exists_inner_normalForm_twistedE6 hf h3 β hβ5
  have hδζK : δ (ζK : GaloisField 2 (2 * f)) = (ζK : GaloisField 2 (2 * f)) :=
    OrdPRest.ringAut_fix_of_pow_eq_one Nat.prime_five hδ5 hζK5'
  let δL : AlgebraicClosure (GaloisField 2 (2 * f)) ≃+*
      AlgebraicClosure (GaloisField 2 (2 * f)) :=
    IsAlgClosure.equivOfEquiv _ _ δ
  have hδL : ∀ c : GaloisField 2 (2 * f),
      δL (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f))) c) =
      algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f))) (δ c) :=
    fun c => IsAlgClosure.equivOfEquiv_algebraMap _ _ δ c
  have hδLζ : Units.map (δL : AlgebraicClosure (GaloisField 2 (2 * f)) →+*
      AlgebraicClosure (GaloisField 2 (2 * f))).toMonoidHom
      (Units.map (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) =
      Units.map (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK := by
    refine Units.ext ?_
    change δL (algebraMap (GaloisField 2 (2 * f))
      (AlgebraicClosure (GaloisField 2 (2 * f))) (ζK : GaloisField 2 (2 * f))) =
      algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f))) (ζK : GaloisField 2 (2 * f))
    rw [hδL, hδζK]
  let g : ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))) := g₀
  have hgC : g ∈ adjointGroup TwistTag.E6.tag
      (AlgebraicClosure (GaloisField 2 (2 * f))) := hg₀C
  have hbaseT : ∀ s : Fin 6 → ZMod 5,
      baseChangeGL (τ := TwistTag.E6.tag) (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f))))
        (((ι₀ (Multiplicative.ofAdd s)) : _) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        g * frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap (GaloisField 2 (2 * f))
            (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * g⁻¹ :=
    fun s => hbase s
  have hfixFrame : ∀ s : Fin 6 → ZMod 5,
      Units.map (entrywiseHom (δL : AlgebraicClosure (GaloisField 2 (2 * f)) →+*
        AlgebraicClosure (GaloisField 2 (2 * f)))) (frameDiag (τ := TwistTag.E6.tag)
        (Units.map (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s) =
      frameDiag (τ := TwistTag.E6.tag)
        (Units.map (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s :=
    fun s => units_map_entrywiseHom_frameDiag_of_fixes hζ hδLζ s
  let xK : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)) :=
    (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
  let xL : ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))) :=
    baseChangeGL (τ := TwistTag.E6.tag) (algebraMap (GaloisField 2 (2 * f))
      (AlgebraicClosure (GaloisField 2 (2 * f)))) xK
  let δg : ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))) :=
    Units.map (entrywiseHom δL.toRingHom) g
  let y : ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))) :=
    g⁻¹ * xL * δg
  have hxK_adj : xK ∈ adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f)) :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
      (graphFixedRootGroup_le TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) x.2)
  have hxL_adj : xL ∈ adjointGroup TwistTag.E6.tag
      (AlgebraicClosure (GaloisField 2 (2 * f))) :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup
      (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))) hxK_adj
  have hδg_adj : δg ∈ adjointGroup TwistTag.E6.tag
      (AlgebraicClosure (GaloisField 2 (2 * f))) :=
    CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup
      δL.toRingHom hgC
  have hyC : y ∈ adjointGroup TwistTag.E6.tag
      (AlgebraicClosure (GaloisField 2 (2 * f))) :=
    mul_mem (mul_mem (inv_mem hgC) hxL_adj) hδg_adj
  have hbaseβ : ∀ s : Fin 6 → ZMod 5,
      baseChangeGL (τ := TwistTag.E6.tag) (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f))))
          (((β (ι₀ (Multiplicative.ofAdd s)) : _) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) =
        g * (y * frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap (GaloisField 2 (2 * f))
            (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * y⁻¹) *
          g⁻¹ := by
    intro s
    have h1 := congrArg (baseChangeGL (τ := TwistTag.E6.tag)
      (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))))
      (hβx (ι₀ (Multiplicative.ofAdd s)))
    rw [map_mul, map_mul, map_inv] at h1
    rw [CFSG.RankThree.Chevalley.SteinbergBN.baseChangeGL_entrywise_comm δ δL hδL,
      hbaseT s, map_mul, map_mul, map_inv, hfixFrame s] at h1
    rw [h1]
    change xL * (δg * frameDiag (τ := TwistTag.E6.tag)
        (Units.map (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * δg⁻¹) *
        xL⁻¹ =
      g * (y * frameDiag (τ := TwistTag.E6.tag)
        (Units.map (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * y⁻¹) * g⁻¹
    rw [show y = g⁻¹ * xL * δg from rfl]
    group
  have himage : ∀ s : Fin 6 → ZMod 5, ∃ t : Fin 6 → ZMod 5,
      y * frameDiag (τ := TwistTag.E6.tag)
        (Units.map (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * y⁻¹ =
        frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap (GaloisField 2 (2 * f))
            (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ t := by
    intro s
    obtain ⟨t, ht⟩ := hstab _ ⟨Multiplicative.ofAdd s, rfl⟩
    refine ⟨Multiplicative.toAdd t, ?_⟩
    have h1 : baseChangeGL (τ := TwistTag.E6.tag) (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f))))
        (((β (ι₀ (Multiplicative.ofAdd s)) : _) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) =
        g * frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap (GaloisField 2 (2 * f))
            (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ
          (Multiplicative.toAdd t) * g⁻¹ := by
      rw [← ht]
      exact hbaseT (Multiplicative.toAdd t)
    rw [hbaseβ s] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hVD : ∀ z ∈ Set.range (frameDiag (τ := TwistTag.E6.tag)
      (Units.map (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ),
      ∃ a : Fin TwistTag.E6.tag.rank →
        (AlgebraicClosure (GaloisField 2 (2 * f)))ˣ,
        z = rootDiagUnit TwistTag.E6.tag a := by
    rintro z ⟨s, rfl⟩
    exact ⟨TableBExc.E6Three.zetaVec _ hζ (frameCoord TwistTag.E6.tag 5 s), rfl⟩
  have hgV : ∀ z ∈ Set.range (frameDiag (τ := TwistTag.E6.tag)
      (Units.map (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ),
      y * z * y⁻¹ ∈ Set.range (frameDiag (τ := TwistTag.E6.tag)
        (Units.map (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ) := by
    rintro z ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := himage s
    exact ⟨t, ht.symm⟩
  obtain ⟨w, hw⟩ :=
    NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := TwistTag.E6.tag) (k := AlgebraicClosure (GaloisField 2 (2 * f))) hVD hyC hgV
  refine ⟨w, fun s => ?_⟩
  apply Subtype.ext
  apply CFSG.LieType.Chevalley.baseChangeGL_injective (τ := TwistTag.E6.tag)
    (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
  rw [hbaseβ s]
  have h1 := hw (frameDiag (τ := TwistTag.E6.tag)
    (Units.map (algebraMap (GaloisField 2 (2 * f))
      (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s) ⟨s, rfl⟩
  rw [h1, canonicalRep_conj_frameDiag_six]
  exact (hbaseT (TableBExc.torusAct .E6 5 w s)).symm

theorem exists_fiveLangFrame_aut {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    ∃ (ζK : (GaloisField 2 (2 * f))ˣ)
      (hζ : (Units.map (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) ^ 5 = 1)
      (g₀ : ModGL Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))))
      (T : Subgroup ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (ι₀ : Multiplicative (Fin 6 → ZMod 5) →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      orderOf ζK = 5 ∧
      g₀ ∈ adjointGroup Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))) ∧
      Function.Injective ι₀ ∧
      (∀ s : Fin 6 → ZMod 5,
        baseChangeGL (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f))))
          (((ι₀ (Multiplicative.ofAdd s)) : _) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        g₀ * frameDiag (τ := Tag.E6)
          (Units.map (algebraMap (GaloisField 2 (2 * f))
            (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * g₀⁻¹) ∧
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
      ι₀.range ≤ T ∧
      (∀ t ∈ T, t ^ 5 = 1 → t ∈ ι₀.range) ∧
      Nat.card T = (2 ^ f + 1) ^ 6 ∧
      (∀ c : ↥(graphFixedRootGroup TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f)),
        (∀ x ∈ ι₀.range, c * x = x * c) → c ∈ T) ∧
      ∀ β : MulAut ↥(graphFixedRootGroup TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f)),
        β ^ 5 = 1 → (∀ b ∈ ι₀.range, β b ∈ ι₀.range) →
          ∃ w : WeylGroup .E6, ∀ s : Fin 6 → ZMod 5,
            β (ι₀ (Multiplicative.ofAdd s)) =
              ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 w s)) := by
  obtain ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hι₀, hbase, hTcomm, hrangeT, htors, hcardT,
    hcent⟩ := exists_fiveLangFrame hf h5
  exact ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hι₀, hbase, hTcomm, hrangeT, htors, hcardT, hcent,
    fiveLangFrame_aut hf h5 ζK hζKord hζ g₀ hg₀C ι₀ hι₀ hbase⟩

end FiveAut

end ExcFrames

end CFSG.StandardType
