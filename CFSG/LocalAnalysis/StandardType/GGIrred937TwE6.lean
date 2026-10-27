module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred
public import CFSG.LocalAnalysis.StandardType.GGIrred937Lattice
public import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6Transport

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

section TwE6

theorem exists_normalizer_realization_twE6
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (i : Fin Tag.F4.rank) :
    ∃ x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      ∀ s : Fin Tag.F4.rank → ZMod 3,
        x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * x⁻¹ =
          ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ
            (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 3 (simple Tag.F4 i) s)) := by
  let wsub : ↥(relWeylTwist TwistTag.E6) :=
    (foldedWeylEquiv TwistTag.E6).symm (simple Tag.F4 i)
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
      simple Tag.F4 i := by
    have hsub : (⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
          ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f)).le ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩, rfl⟩⟩ :
        ↥(relWeylTwist TwistTag.E6)) = ⟨w, hw⟩ := by
      apply Subtype.ext
      exact hWeyl
    have hfold : foldedWeylEquiv TwistTag.E6 ⟨w, hw⟩ = simple Tag.F4 i := by
      have h2 : (⟨w, hw⟩ : ↥(relWeylTwist TwistTag.E6)) =
          (foldedWeylEquiv TwistTag.E6).symm (simple Tag.F4 i) := rfl
      rw [h2]
      exact MulEquiv.apply_symm_apply (foldedWeylEquiv TwistTag.E6) (simple Tag.F4 i)
    rw [hsub, hfold]
  refine ⟨x, fun s => ?_⟩
  have hconj := ExcFrames.twE6ThreeFrameHom_conj hf h3 hζo hζ hx s
  rw [hfe] at hconj
  exact Subtype.ext hconj

theorem ggSCWeylIrred_twE6Three_gf
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    GGSCWeylIrred 3 4
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
  intro E hE hr hr3 hsc
  obtain ⟨ζ, hζ, ι₀, hζo, hinj, happly, hmem, hlast⟩ := ExcFrames.exists_threeFrame hf h3
  have hsc' : ∀ c ∈ Subgroup.centralizer (E : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
      c ∈ E := by
    intro c hc hc3
    exact hsc c (fun e he => ((Subgroup.mem_centralizer_iff.mp hc) e he).symm) hc3
  obtain ⟨c, hc⟩ := ExcFrames.twistedE6ThreeSCReference_holds hf h3 hζo hζ hE hr hsc'
  rw [hc]
  apply ggWeylIrred_map (MulAut.conj c)
  let m : Fin Tag.F4.rank →
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    fun i => Classical.choose (exists_normalizer_realization_twE6 hf h3 hζo hζ i)
  have hm : ∀ (i : Fin Tag.F4.rank) (s : Fin Tag.F4.rank → ZMod 3),
      m i * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * (m i)⁻¹ =
        ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ
          (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 3 (simple Tag.F4 i) s)) :=
    fun i s => Classical.choose_spec (exists_normalizer_realization_twE6 hf h3 hζo hζ i) s
  exact ggWeylIrred_range_of_torusAct (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ)
    (ExcFrames.twE6ThreeFrameHom_injective hf h3 hζo hζ) m hm latticeIrred_F4

theorem ggNbrKGTwE6ThreeSubSCWeylIrred_holds :
    GGNbrKGTwE6ThreeSubSCWeylIrred := by
  intro K _ _ n hn hK h3
  have hchar : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * n))
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  set τ := FiniteField.ringEquivOfCardEq hcard with hτdef
  have hτ : ∀ c : GaloisField 2 (2 * n), τ (frobQ 2 n c) = σ (τ c) := fun c => by
    rw [frobQ_apply, hσ, map_pow]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (K := K) hn hK σ hσ
  obtain ⟨e₂⟩ := graphFixedRootGroup_mulEquiv_of_ringEquiv (K := GaloisField 2 (2 * n))
    (K' := K) τ (frobQ 2 n) σ (fun c => (hτ c).symm)
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := by
    intro h
    have hd : 3 ∣ 2 := by
      have h1 : 3 ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h h3
      have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
        have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rwa [h2] at h1
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hgf : GGSCWeylIrred 3 4
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n)) (frobQ 2 n)) :=
    ggSCWeylIrred_twE6Three_gf hn h3'
  have hKσ : GGSCWeylIrred 3 4 ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    ggSCWeylIrred_of_mulEquiv e₂.symm hgf
  exact ggSCWeylIrred_of_mulEquiv e hKσ

end TwE6

end Irred937

end CFSG.StandardType

end
