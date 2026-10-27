module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcLangFrame

import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrame
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplitTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeFrame
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeDiag
import CFSG.LocalAnalysis.StandardType.GGTwE6D4RootFacts
import CFSG.RankThree.PartOne.KE6.EqpTorus
import CFSG.RankThree.Lattice.SteinbergBIE6EvenFixedRootData
import CFSG.CGT.T75N.L29Generic
import CFSG.CGT.Timmesfeld75.ListWCLin
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42STorus
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
open CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Lattice CFSG.CGT.T75N CFSG.CGT.Timmesfeld75 CFSG.StandardType.TwE6RootKill
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.ExcFrames CFSG.StandardType.ExcFrames.E6QPlusThree
  CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S CFSG.StandardType.KGL.TwLayer

noncomputable section


private theorem rho_eq_split_of_lang {K : Type} [Field K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {D : LangDatum Tag.E6 (AlgebraicClosure K)}
    {w : CFSG.LieType.Chevalley.WeylGroup Tag.E6}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hDΦ : D.Φ = Units.map (entrywiseHom Fr)) (hDq : D.q = Nat.card K)
    (hDn : D.n = CFSG.LieType.Chevalley.canonicalRep
      (CFSG.LieType.Chevalley.coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (hneg : ∀ u : Fin Tag.E6.rank → ℤ, w • u = -permLattice TwistTag.E6.perm u)
    (hpos : 0 < Nat.card K)
    {S : LangSetup Tag.E6 (AlgebraicClosure K) 5} (hSD : S.D = D) :
    ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -permLattice TwistTag.E6.perm γ := by
  intro γ hγ
  have hfrobD : FrobRootMap D S.ρ := by
    rw [← hSD]
    exact S.frob
  let D' : LangDatum Tag.E6 (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w D.g0_mem
      (by rw [← hDΦ, ← hDn]; exact D.lang)
  have hfrobD' : FrobRootMap D' S.ρ :=
    frobRootMap_congr_fields hDΦ.symm hDq.symm hDn.symm hfrobD
  have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.frobRootMap_ofFrobenius_apply
    (τ := Tag.E6) (L := AlgebraicClosure K) (Fr := Fr) (q := Nat.card K) hpos hFr D.g0_mem
    (hg0 := by rw [← hDΦ, ← hDn]; exact D.lang) hfrobD' hγ
  rw [h, hneg γ]

theorem e6SplitLangSetup_holds : E6SplitLangSetup := by
  intro K _ _ hK E hE hcard
  classical
  let Ω := AlgebraicClosure K
  have hcharK : CharP K 2 := charP_two_of_card_pow (m := 1) (by norm_num [hK])
  have hcharΩ : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have h3 : 3 ∣ Nat.card K + 1 := by norm_num [hK]
  obtain ⟨Fr, g0, ζ, hζ, F, hFr, hg0C, hg0Fr, hζo, hFrζ, hsurj, hbc⟩ :=
    CFSG.StandardType.ExcFrames.E6QPlusThree.exists_e6QPlusThreeFrame_with_coordinates
      (K := K) h3
  let Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := Units.map (entrywiseHom Fr)
  have hsteinberg : IsSteinbergEnd Tag.E6 Ω 2 Φ := by
    refine ⟨Fr, ?_, 1, Or.inl rfl, ?_⟩
    · intro c; simp [hFr, hK]
    · intro g; simp [Φ]
  let D : LangDatum Tag.E6 Ω :=
    { Φ := Φ
      q := 2
      n := eqpN Ω
      g0 := g0
      steinberg := hsteinberg
      n_weyl := ⟨e6W0, rfl⟩
      g0_mem := hg0C
      lang := hg0Fr }
  let ι₀ : adjointGroup Tag.E6 K →* ModGL Tag.E6 Ω :=
    (CFSG.LieType.Chevalley.baseChangeGL (algebraMap K Ω)).comp
      (adjointGroup Tag.E6 K).subtype
  have hι₀ : Function.Injective ι₀ :=
    (CFSG.LieType.Chevalley.baseChangeGL_injective (algebraMap K Ω)).comp
      (Subgroup.subtype_injective _)
  have hperf : commutator ↥(adjointGroup Tag.E6 K) = ⊤ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_E6_eq_top K
  have hd : LangDescent D 5 ι₀ :=
    langDescent_untw 3 (Or.inl ⟨rfl, rfl⟩) hFr D rfl Nat.prime_five (by norm_num) hperf
  have hfin : Finite D.model := hd.finite_model
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := hd.Γ_eq
  obtain ⟨S, ι, hSD, hιval, hιinj, hιrange, _huniform⟩ :=
    CFSG.StandardType.LangRat.exists_langSetup_of_toral_datum_uniform (τ := Tag.E6) (L := Ω)
      (ℓ := 2) (f := 1) Nat.prime_two le_rfl D (by norm_num) Nat.prime_five (by norm_num)
      (Or.inl le_rfl) hfin ι₀ hι₀ hΓ
  have hqS : S.D.q = 2 := by rw [hSD]
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_isAlgClosure K 1 (by rw [pow_one, hqS, hK])
  have hρS : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -permLattice TwistTag.E6.perm γ :=
    rho_eq_split_of_lang hFr rfl hK.symm rfl
      (fun u => e6W0_smul u) (by norm_num [hK]) hSD
  let A₀ : Subgroup (adjointGroup Tag.E6 K) := F.frame.range
  have htor : fullThreeTorus S = A₀.map ι := by
    have hι_frame : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
        ι (F.frame s) = e6ThreeDiag ζ hζ s := by
      intro s
      rw [hιval]
      dsimp only [ι₀, Ω, D]
      calc
        g0⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K))) ↑(F.frame s) * g0
            = g0⁻¹ * (g0 * (e6ThreeDiag ζ hζ) s * g0⁻¹) * g0 := by rw [hbc s]
        _ = (e6ThreeDiag ζ hζ) s := by group
    have hA₀map : A₀.map ι = (e6ThreeDiag ζ hζ).range := by
      dsimp only [A₀]
      refine le_antisymm ?_ ?_
      · rintro y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
        obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hx
        exact MonoidHom.mem_range.2 ⟨s, (hι_frame s).symm⟩
      · rintro y hy
        obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hy
        exact Subgroup.mem_map.2 ⟨F.frame s, MonoidHom.mem_range.2 ⟨s, rfl⟩, hι_frame s⟩
    rw [hA₀map]
    refine le_antisymm ?_ ?_
    · intro y hy
      have hyS : y ∈ S.D.torus := (mem_fullThreeTorus S).1 hy |>.1
      have hy3 : y ^ 3 = 1 := (mem_fullThreeTorus S).1 hy |>.2
      have hyD : y ∈ D.torus := by rwa [hSD] at hyS
      have hyTw : y ∈ CFSG.RankThree.PartOne.KE.twistedTorus (eqpN Ω) Fr := by
        simpa [D, LangDatum.torus, CFSG.RankThree.PartOne.KE.twistedTorus, Φ] using hyD
      obtain ⟨s, hs⟩ := exists_e6ThreeDiag_eq Fr hζo hζ hFrζ hyTw hy3
      exact ⟨s, hs⟩
    · rintro y ⟨s, rfl⟩
      have hmem : e6ThreeDiag ζ hζ s ∈ D.torus := by
        have h := e6ThreeDiag_mem_NFix Fr hζ hFrζ s
        dsimp only [D, LangDatum.torus, Φ]
        exact CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mem_twistedTorusOf_iff_negPhi.2 ⟨rootDiagUnit_mem_torusGroup _, (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mem_NFix.1 h).2⟩
      have hcube : (e6ThreeDiag ζ hζ s) ^ 3 = 1 := by
        change (e6ThreeDiag ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd s))) ^ 3 = 1
        rw [e6ThreeDiag_apply ζ hζ (Multiplicative.toAdd s)]
        rw [rootDiagUnit_pow]
        rw [← rootDiagUnit_one]
        congr 1
        funext i
        exact zetaVec_apply_pow_three hζ (twE6ThreeFrame (Multiplicative.toAdd s)) i
      exact (mem_fullThreeTorus S).2 ⟨by rwa [hSD], hcube⟩
  have h2 : (2 : K) = 0 := hcharK.cast_eq_zero
  have hA0elem : IsElemAbelian 3 A₀ := by
    refine ⟨isMulCommutative_range F.frame, ?_⟩
    rintro a ⟨s, rfl⟩
    change F.frame s ^ 3 = 1
    rw [← map_pow, show s ^ 3 = 1 from ?_, map_one]
    conv_lhs => rw [show s = Multiplicative.ofAdd (Multiplicative.toAdd s) from rfl]
    rw [← ofAdd_nsmul]
    congr 1
    ext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [ZMod.natCast_self]
    simp
  have hA0card : 3 ^ 4 ≤ Nat.card A₀ := by
    have hcard : Nat.card A₀ = 3 ^ 4 := by
      dsimp only [A₀]
      change Nat.card ↑(Set.range ⇑F.frame) = 3 ^ 4
      rw [Nat.card_range_of_injective F.frame_injective]
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
      rw [show Tag.F4.rank = 4 from rfl]
      norm_num
    rw [hcard]
  obtain ⟨c₁, hc₁⟩ :=
    CFSG.StandardType.E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE hcard
  obtain ⟨c₂, hc₂⟩ :=
    CFSG.StandardType.E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hA0elem hA0card
  let c : adjointGroup Tag.E6 K := c₂⁻¹ * c₁
  have hc : E.map (MulAut.conj c).toMonoidHom = A₀ := by
    have h1 : E.map (MulAut.conj c₁).toMonoidHom =
        A₀.map (MulAut.conj c₂).toMonoidHom := by
      rw [hc₁, hc₂]
    have h2 : E.map (MulAut.conj c).toMonoidHom =
        (E.map (MulAut.conj c₁).toMonoidHom).map
          (MulAut.conj c₂⁻¹).toMonoidHom := by
      rw [show c = c₂⁻¹ * c₁ from rfl]
      rw [Subgroup.map_map]
      congr 1
    rw [h2, h1]
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj c₂⁻¹).toMonoidHom.comp
        (MulAut.conj c₂).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun x => ?_
      show c₂⁻¹ * (c₂ * x * c₂⁻¹) * c₂⁻¹⁻¹ = x
      group
    rw [hcomp, Subgroup.map_id]
  let ι' : adjointGroup Tag.E6 K →* ModGL Tag.E6 Ω :=
    ι.comp (MulAut.conj c).toMonoidHom
  have hι'inj : Function.Injective ι' := hιinj.comp (MulAut.conj c).injective
  have hι'range : ι'.range = S.Γ := by
    dsimp only [ι']
    rw [MonoidHom.range_comp]
    rw [MonoidHom.range_eq_top.2 (MulAut.conj c).surjective]
    rw [Subgroup.map_top]
    exact hιrange
  have hfull : fullThreeTorus S = E.map ι' := by
    dsimp only [ι']
    rw [htor]
    rw [← hc]
    rw [Subgroup.map_map]
  exact ⟨S, ι', ⟨hqS, hAlg, hρS⟩, hι'inj, hι'range, hfull⟩

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
