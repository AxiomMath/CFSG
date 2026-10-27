module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwoLocalToral
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma105
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)

section Toral

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.toral_twE6
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hf : 1 ≤ f) (hp : p = 3) (h3 : 3 ∣ 2 ^ f + 1) (hcard : 3 ^ 4 ≤ Nat.card B)
    (act : TwE6Act G₀ B hf) {R : Subgroup X} (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hRG : R ≤ G₀)
    (hBR : B ≤ Subgroup.normalizer (R : Set X)) :
    ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))), ∀ b : ↥B,
      g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam b : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))) := by
  subst hp
  let K := GaloisField 2 (2 * f)
  have hK : Nat.card K = (2 ^ f) ^ 2 := CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : K, frobQEquiv hf c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  have : CharP K 2 := CFSG.StandardType.TwE6FieldCore.charP_two_of_card_sq hK
  let A : Subgroup (ModGL TwistTag.E6.tag K) :=
    (act.lam.range).map (RecipeExcLang.twInndiagGroup K (frobQEquiv hf)).subtype
  have hAI : A ≤
      CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K (frobQEquiv hf) := by
    rintro x ⟨w, -, rfl⟩
    exact NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL (frobQEquiv hf) w.2
  have hA : IsElemAbelian 3 A := by
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥B) := by
      have hb := h.b_elem.subgroupOf B
      rwa [Subgroup.subgroupOf_self] at hb
    have hrange : IsElemAbelian 3 act.lam.range := by
      have hm := htop.map act.lam
      rwa [Subgroup.map_top] at hm
    exact hrange.map (RecipeExcLang.twInndiagGroup K (frobQEquiv hf)).subtype
  have hcardA : 3 ^ 4 ≤ Nat.card A := by
    have hcardAB : Nat.card A = Nat.card B := by
      change Nat.card ((act.lam.range).map
        (RecipeExcLang.twInndiagGroup K (frobQEquiv hf)).subtype) = Nat.card B
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      rw [← Subgroup.map_top act.lam, Subgroup.card_map_of_injective act.lam_inj]
      exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    rwa [hcardAB]
  have hU : TwE6RootKill.TwNormTwo K (frobQEquiv hf) A := by
    let Rq : Subgroup (↥G₀ ⧸ Subgroup.center ↥G₀) :=
      (R.subgroupOf G₀).map (QuotientGroup.mk' (Subgroup.center ↥G₀))
    have hV2 : IsPGroup 2 Rq :=
      (hR2.comap_subtype).map (QuotientGroup.mk' (Subgroup.center ↥G₀))
    have hV1 : Rq ≠ ⊥ := by
      intro hVbot
      have hRleC : R ≤ Subgroup.centralizer (G₀ : Set X) := by
        intro s hs
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hmem : QuotientGroup.mk' (Subgroup.center ↥G₀) (⟨s, hRG hs⟩ : ↥G₀) ∈ Rq :=
          Subgroup.mem_map.mpr ⟨⟨s, hRG hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
        rw [hVbot] at hmem
        have hsc : (⟨s, hRG hs⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ :=
          (QuotientGroup.eq_one_iff (⟨s, hRG hs⟩ : ↥G₀)).mp (Subgroup.mem_bot.mp hmem)
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hsc) (⟨y, hy⟩ : ↥G₀))
      exact hR1 (CFSG.LocalAnalysis.GLTheoremA.S10.eq_bot_of_le_odd hR2 h.cent_odd hRleC)
    refine CFSG.StandardType.TwE6Transport.twNormTwo_of_conj (frobQEquiv hf) act.θ.symm
      (V := Rq) hV1 hV2 ?_
    rintro x hx v hv
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hw
    obtain ⟨y, hy, rfl⟩ := hv
    have hyR : (y : X) ∈ R := Subgroup.mem_subgroupOf.mp hy
    have hybR : (b : X) * (y : X) * (b : X)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 (hBR b.2) (y : X)).1 hyR
    let y' : ↥G₀ := ⟨(b : X) * (y : X) * (b : X)⁻¹, hRG hybR⟩
    refine ⟨QuotientGroup.mk' (Subgroup.center ↥G₀) y', ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨y', Subgroup.mem_subgroupOf.mpr hybR, rfl⟩
    · simp only [QuotientGroup.mk'_apply, MulEquiv.symm_symm]
      exact (act.act b y y' rfl).symm
  obtain ⟨g, hg, hgT⟩ := CFSG.StandardType.TwE6RootKill.exists_conj_torus_of_twNormTwo
    (K₀ := K) (K := K) (n := f) CFSG.StandardType.ExcFramesHalf.bigElemAbelianToralBar_E6_three
    hK hσ h3 (algebraMap K (AlgebraicClosure K)) hAI hA hcardA hU
  refine ⟨g, hg, fun b => hgT _ ?_⟩
  exact Subgroup.mem_map.mpr ⟨act.lam b, MonoidHom.mem_range.mpr ⟨b, rfl⟩, rfl⟩

end Toral

end CFSG.StandardType.TableCRes

end
