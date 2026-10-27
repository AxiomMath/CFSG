module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4Defs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6NonsplitThree
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeNormalizer
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeTorus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
import CFSG.RankThree.PartOne.K133H.F4Weyl
import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient
import CFSG.LieType.Chevalley.FoldedWeylIdentification

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

private theorem l04fHE2_ref
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    IsElemAbelian 3 (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range ∧
      Nat.card (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range = 3 ^ 4 := by
  have htop : IsElemAbelian 3
      (⊤ : Subgroup (Multiplicative (Fin Tag.F4.rank → ZMod 3))) := by
    refine ⟨inferInstance, fun x _ => ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨?_, ?_⟩
  · have h := CFSG.Open.IsElemAbelian.map htop
        (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ)
    rwa [Subgroup.map_top] at h
  · rw [← Subgroup.map_top (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ),
      Subgroup.card_map_of_injective
        (ExcFrames.twE6ThreeFrameHom_injective hf h3 hζo hζ),
      Subgroup.card_top, Nat.card_eq_fintype_card]
    change Fintype.card (Fin 4 → ZMod 3) = 3 ^ 4
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

private theorem l04fHE2_realize
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (wF4 : WeylGroup .F4) :
    ∃ x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      ∀ s : Fin Tag.F4.rank → ZMod 3,
        x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * x⁻¹ =
          ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ
            (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 3 wF4 s)) := by
  let wsub : ↥(relWeylTwist TwistTag.E6) := (foldedWeylEquiv TwistTag.E6).symm wF4
  let w : WeylGroup TwistTag.E6.tag := wsub.1
  have hw : w ∈ relWeylTwist TwistTag.E6 := wsub.2
  let n : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (GaloisField 2 (2 * f)) w
  have hn : n ∈ graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) :=
    canonicalRep_mem_graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) hw
  let x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ⟨n, graphFixedRootMonomial_le TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) hn⟩
  have hx : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := hn
  have hWeyl : graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
      ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩ = w :=
    graphFixedRootWeylHom_canonicalRep TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) hw
  have hfe : foldedWeylEquiv TwistTag.E6
      ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
          ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f)).le ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩, rfl⟩⟩ =
      wF4 := by
    have hsub : (⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
          ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f)).le ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩, rfl⟩⟩ :
        ↥(relWeylTwist TwistTag.E6)) = ⟨w, hw⟩ := by
      apply Subtype.ext
      exact hWeyl
    have hfold : foldedWeylEquiv TwistTag.E6 ⟨w, hw⟩ = wF4 := by
      have h2 : (⟨w, hw⟩ : ↥(relWeylTwist TwistTag.E6)) =
          (foldedWeylEquiv TwistTag.E6).symm wF4 := rfl
      rw [h2]
      exact MulEquiv.apply_symm_apply (foldedWeylEquiv TwistTag.E6) wF4
    rw [hsub, hfold]
  refine ⟨x, fun s => ?_⟩
  have hconj := ExcFrames.twE6ThreeFrameHom_conj hf h3 hζo hζ hx s
  rw [hfe] at hconj
  exact Subtype.ext hconj

private theorem l04fHE2_normalizes
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (_hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    {w : WeylGroup .F4}
    (hx : ∀ s : Fin Tag.F4.rank → ZMod 3,
      x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * x⁻¹ =
        ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ
          (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 3 w s))) :
    x ∈ Subgroup.normalizer
      ((ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range :
        Set ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
  classical
  let ι₀ := ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ
  let A₀ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ι₀.range
  have hmap_le : A₀.map (MulAut.conj x).toMonoidHom ≤ A₀ := by
    rintro b ⟨a, ha, rfl⟩
    obtain ⟨v, rfl⟩ := ha
    have hv : v = Multiplicative.ofAdd (Multiplicative.toAdd v) := (ofAdd_toAdd v).symm
    rw [hv]
    rw [show (MulAut.conj x).toMonoidHom
          (ι₀ (Multiplicative.ofAdd (Multiplicative.toAdd v))) =
        x * ι₀ (Multiplicative.ofAdd (Multiplicative.toAdd v)) * x⁻¹ from rfl,
      hx (Multiplicative.toAdd v)]
    exact ⟨_, rfl⟩
  have hcard : Nat.card (A₀.map (MulAut.conj x).toMonoidHom) = Nat.card A₀ :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hmap_eq : A₀.map (MulAut.conj x).toMonoidHom = A₀ :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcard])
  change x ∈ Subgroup.normalizer (A₀ : Set _)
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hmap_le (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hb)
  · intro hb
    have hb' : x * b * x⁻¹ ∈ A₀.map (MulAut.conj x).toMonoidHom := by
      rw [hmap_eq]
      exact hb
    obtain ⟨a, ha, hae⟩ := hb'
    have hab : (a : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) = b := by
      have h : x * (a : _) * x⁻¹ = x * b * x⁻¹ := hae
      have h' := congrArg (fun y => x⁻¹ * y * x) h
      simpa [mul_assoc] using h'
    rw [← hab]
    exact ha

private theorem l04fHE2_ref_automizer
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Nat.card (ggAutomizer ⊤ (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range) = 1152 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let V := Multiplicative (Fin Tag.F4.rank → ZMod 3)
  let ι₀ := ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ
  let A₀ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ι₀.range
  let e : V ≃* A₀ := MonoidHom.ofInjective
    (ExcFrames.twE6ThreeFrameHom_injective hf h3 hζo hζ)
  have he_apply : ∀ v : V,
      ((e v : A₀) : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) =
        ι₀ v := fun v => rfl
  have hTor_apply : ∀ (w : WeylGroup .F4) (s : Fin Tag.F4.rank → ZMod 3),
      ((e (ExcWeylOuter.torusMulAut Tag.F4 3 w (Multiplicative.ofAdd s)) : A₀) :
          ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 3 w s)) := by
    intro w s
    rw [he_apply, ExcWeylOuter.torusMulAut_apply]
  have hTorInj : Function.Injective (ExcWeylOuter.torusMulAut Tag.F4 3) :=
    ExcWeylOuter.torusMulAut_injective (τ := Tag.F4) (p := 3) (by norm_num)
  change Nat.card (ggAutomizer ⊤ A₀) = 1152
  have hkey : ggAutomizer ⊤ A₀ =
      (ExcWeylOuter.torusMulAut Tag.F4 3).range.map
        (MulAut.congr e).toMonoidHom := by
    apply le_antisymm
    · intro φ hφ
      rw [mem_ggAutomizer_iff] at hφ
      obtain ⟨g, -, hgN, hgφ⟩ := hφ
      have hxs : ∀ s, g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ ∈ ι₀.range := by
        intro s
        have hmem : ι₀ (Multiplicative.ofAdd s) ∈ A₀ := ⟨_, rfl⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp hgN (ι₀ (Multiplicative.ofAdd s))).mp hmem
        simpa [A₀] using h1
      have hxM :=
        ExcFrames.mem_graphFixedRootMonomial_of_normalizes_twE6ThreeFrame hf h3 hζo hζ hxs
      let wF4 : WeylGroup .F4 :=
        foldedWeylEquiv TwistTag.E6
          ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
            ⟨(g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩,
            (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
              (frobQ 2 f)).le
              ⟨⟨(g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩, rfl⟩⟩
      refine Subgroup.mem_map.mpr
        ⟨ExcWeylOuter.torusMulAut Tag.F4 3 wF4, ⟨wF4, rfl⟩, ?_⟩
      have hEq : (MulAut.congr e).toMonoidHom
          (ExcWeylOuter.torusMulAut Tag.F4 3 wF4) = φ := by
        refine MulEquiv.ext fun b => ?_
        obtain ⟨v, rfl⟩ := e.surjective b
        have hv : v = Multiplicative.ofAdd (Multiplicative.toAdd v) := (ofAdd_toAdd v).symm
        rw [hv]
        change MulAut.congr e (ExcWeylOuter.torusMulAut Tag.F4 3 wF4)
            (e (Multiplicative.ofAdd (Multiplicative.toAdd v))) =
          φ (e (Multiplicative.ofAdd (Multiplicative.toAdd v)))
        apply Subtype.ext
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        rw [hTor_apply wF4 (Multiplicative.toAdd v)]
        rw [hgφ (e (Multiplicative.ofAdd (Multiplicative.toAdd v)))]
        rw [he_apply (Multiplicative.ofAdd (Multiplicative.toAdd v))]
        exact (Subtype.ext
          (ExcFrames.twE6ThreeFrameHom_conj hf h3 hζo hζ hxM
            (Multiplicative.toAdd v))).symm
      exact hEq
    · intro ψ hψ
      rw [Subgroup.mem_map] at hψ
      obtain ⟨τ, hτ, hτeq⟩ := hψ
      rw [MonoidHom.mem_range] at hτ
      obtain ⟨wF4, rfl⟩ := hτ
      obtain ⟨x, hx⟩ := l04fHE2_realize hf h3 hζo hζ wF4
      have hxN := l04fHE2_normalizes hf h3 hζo hζ hx
      have hmem := ggConjAut_mem_ggAutomizer (H := ⊤) (Bs := A₀)
        (Subgroup.mem_top x) hxN
      rw [← hτeq]
      have hEq : ggConjAut A₀ hxN =
          (MulAut.congr e).toMonoidHom (ExcWeylOuter.torusMulAut Tag.F4 3 wF4) := by
        refine MulEquiv.ext fun b => ?_
        obtain ⟨v, rfl⟩ := e.surjective b
        have hv : v = Multiplicative.ofAdd (Multiplicative.toAdd v) := (ofAdd_toAdd v).symm
        rw [hv]
        change ggConjAut A₀ hxN (e (Multiplicative.ofAdd (Multiplicative.toAdd v))) =
          MulAut.congr e (ExcWeylOuter.torusMulAut Tag.F4 3 wF4)
            (e (Multiplicative.ofAdd (Multiplicative.toAdd v)))
        apply Subtype.ext
        rw [ggConjAut_apply]
        rw [show MulAut.congr e (ExcWeylOuter.torusMulAut Tag.F4 3 wF4)
              (e (Multiplicative.ofAdd (Multiplicative.toAdd v))) =
            e (ExcWeylOuter.torusMulAut Tag.F4 3 wF4
              (Multiplicative.ofAdd (Multiplicative.toAdd v))) from by
          simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]]
        rw [hTor_apply wF4 (Multiplicative.toAdd v)]
        rw [he_apply (Multiplicative.ofAdd (Multiplicative.toAdd v))]
        exact hx (Multiplicative.toAdd v)
      rw [← hEq]
      exact hmem
  rw [hkey]
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
  rw [Nat.card_congr (MonoidHom.ofInjective hTorInj).toEquiv.symm]
  exact CFSG.RankThree.PartOne.K133H.card_weylGroup_F4

private theorem l04fHE2_conj
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
    Nat.card (ggAutomizer ⊤
      ((ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range.map
        (MulAut.conj c).toMonoidHom)) = 1152 := by
  classical
  let ι₀ := ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ
  let A₀ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ι₀.range
  change Nat.card (ggAutomizer ⊤
    (A₀.map (MulAut.conj c).toMonoidHom)) = 1152
  have h := F4AutWeyl.ggAutomizer_map_eq (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective ⊤ A₀
    (rfl : A₀.map (MulAut.conj c).toMonoidHom = A₀.map (MulAut.conj c).toMonoidHom)
  have hmap_top : (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))).map (MulAut.conj c).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective
  rw [← hmap_top]
  rw [h]
  rw [Subgroup.card_map_of_injective (MulAut.congr _).injective]
  exact l04fHE2_ref_automizer hf h3 hζo hζ

theorem ggPumpTwExc_autOrderAt_twE6
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    KGA.GGF4AutOrderAt 3
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
  classical
  intro E hE hr
  have : Finite ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    Subtype.finite
  obtain ⟨E', hEE', hE'elem, hE'sc⟩ :=
    A6InsideSp.exists_elemAbelian_le_selfCentralizing (p := 3) Nat.prime_three hE
  have hE'card_ge : 3 ^ 4 ≤ Nat.card E' := hr.trans (Subgroup.card_le_of_le hEE')
  obtain ⟨ζ, hζ, -, hζo, -, -, -, -⟩ := ExcFrames.exists_threeFrame hf h3
  have hE'sc' : ∀ c ∈ Subgroup.centralizer (E' : Set _), c ^ 3 = 1 → c ∈ E' :=
    fun c hc hc3 => hE'sc c
      (fun y hy => ((Subgroup.mem_centralizer_iff.mp hc) y hy).symm) hc3
  obtain ⟨c, hc⟩ :=
    ExcFrames.twistedE6ThreeSCReference_holds hf h3 hζo hζ hE'elem hE'card_ge hE'sc'
  have hcardA₀ : Nat.card (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range = 3 ^ 4 :=
    (l04fHE2_ref hf h3 hζo hζ).2
  have hcardE' : Nat.card E' = 3 ^ 4 := by
    rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hcardA₀
  have hcardE : Nat.card E = 3 ^ 4 :=
    le_antisymm (hcardE' ▸ Subgroup.card_le_of_le hEE') hr
  have hEEq : E = E' :=
    Subgroup.eq_of_le_of_card_ge hEE' (by rw [hcardE', hcardE])
  refine ⟨hcardE, ?_⟩
  rw [hEEq, hc]
  exact l04fHE2_conj hf h3 hζo hζ c

end CFSG.StandardType

end
