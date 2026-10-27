module

public import CFSG.LocalAnalysis.StandardType.GGKD2LinearBlock1615
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
public import CFSG.RankThree.PartOne.FOC.PSLDecomp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
public import CFSG.LocalAnalysis.StandardType.GGKD2LinearLemmas1615

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.Open (StatedSL StatedProj)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma ltrcl_comp {P L' : Type} [Group P] [Group L'] [Finite L'] (ψ₀ : L' →* P)
    (hψ₀ : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    {u : MulAut P} {e : MulAut L'} (he : ∀ l : L', u (ψ₀ l) = ψ₀ (e l))
    {J : Subgroup L'} (hJ : IsComponentOf J (ggFixSub e)) {lab : LargeEvenLabel}
    (hlab : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) :
    IsComponentOf (J.map ψ₀) (ggFix u) ∧
      GGHasLabel lab (↥(J.map ψ₀) ⧸ Subgroup.center ↥(J.map ψ₀)) := by
  refine ⟨USixTwo.isComponentOf_map_fix hψ₀ hker he hJ, ?_⟩
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
  have hf : Function.Surjective (ψ₀.subgroupMap J) := ψ₀.subgroupMap_surjective J
  have hkerf : (ψ₀.subgroupMap J).ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hψx : ψ₀ (x : L') = 1 := congrArg Subtype.val hx
    have hxc : (x : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hψx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxc (y : L')
  obtain ⟨φ⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf (ψ₀.subgroupMap J) hf hkerf
  exact ggHasLabel_of_mulEquiv φ hlab

private lemma ltrcl_core_contradiction
    (lab : LargeEvenLabel) (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .A)
    {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (e : MulAut L') (J : Subgroup L') (a : MulAut L')
    (hsetup : GGRankOneSetup I ψ 3 e J 3 a) (hsplit : SplitLift lab R I ψ e) : False := by
  obtain ⟨-, -, -, -, -, hJ, -, hlab, hea, ⟨φa, hφaI, hφa⟩, haJ, hnot⟩ := hsetup
  simp only [LargeEvenInLambda2, htag] at hΛ
  obtain ⟨hn1, hr1, hr1n⟩ := hΛ
  rcases hsplit with ⟨-, K, fK, finK, hcard, M, hMN, hM3, θ, hθe, hθI⟩ | ⟨hA, -⟩
  swap
  · rw [htag] at hA
    cases hA
  letI : Field K := fK
  letI : Finite K := finK
  have h2 : (2 : K) = 0 := by
    have h0 : Nat.card K • (1 : K) = 0 := card_nsmul_eq_zero'
    rw [nsmul_one, hcard, Nat.cast_pow, Nat.cast_ofNat] at h0
    exact pow_eq_zero_iff (by omega) |>.mp h0
  set S := LargeEvenSLGroup (Fin (lab.rank + 1)) K with hS
  obtain ⟨β, hβ, hβa⟩ := hθI φa hφaI
  have hψ₀ : Function.Surjective (θ.toMonoidHom.comp ψ) := θ.surjective.comp hψ
  have hker₀ : (θ.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (map_eq_one_iff θ θ.injective).mp hx
  have hθe' : ∀ l : L', TableB.projConj S ⟨M, hMN⟩ ((θ.toMonoidHom.comp ψ) l) =
      (θ.toMonoidHom.comp ψ) (e l) := hθe
  have hβa' : ∀ l : L', β ((θ.toMonoidHom.comp ψ) l) = (θ.toMonoidHom.comp ψ) (a l) := by
    intro l
    show β (θ (ψ l)) = θ (ψ (a l))
    rw [hβa (ψ l), hφa l]
  obtain ⟨hJ₀, hlab₀⟩ := ltrcl_comp (θ.toMonoidHom.comp ψ) hψ₀ hker₀ hθe' hJ hlab
  obtain ⟨r, D, ee, hFld, hFin, hAlg, θH, i, -, hrange, he2, hWS, hJeq, ⟨φq⟩⟩ :=
    linearFixedComponentBlock h2 M hMN hM3 hJ₀
  letI : ∀ k, Field (D k) := hFld
  haveI : ∀ k, Finite (D k) := hFin
  letI : ∀ k, Algebra K (D k) := hAlg
  have h2D : (2 : D i) = 0 := by
    rw [← map_ofNat (algebraMap K (D i)) 2, h2, map_zero]
  obtain ⟨hk2, hD8⟩ := kd2Lin_numerology h2D he2 φq hlab₀
  obtain ⟨N, hNnorm, hN⟩ := kd2Lin_actor (θ.toMonoidHom.comp ψ) β hβ hβa'
  obtain ⟨ζ, hζ3, hNM⟩ := kd2Lin_zeta hcard (by omega) (fun h => hr1n (by omega))
    (θ.toMonoidHom.comp ψ) hψ₀ hea hMN hNnorm hM3 hθe' hN
  have hζ : ζ = 1 := kd2Lin_zeta_one (E := D i) hD8 hζ3
  have hNrange : N ∈ θH.range := by
    rw [hrange, Subgroup.mem_centralizer_singleton_iff]
    rw [hζ] at hNM
    simp only [map_one, one_mul] at hNM
    calc N * M = (N * M * N⁻¹) * N := by group
      _ = M * N := by rw [hNM]
  obtain ⟨s, hsW, hsconj⟩ := kd2Lin_inner θH i hk2 hD8 hNrange
  have hsS : s ∈ S := hWS hsW
  have ht : LargeEvenProjMk S ⟨s, hsS⟩ ∈ J.map (θ.toMonoidHom.comp ψ) := by
    rw [hJeq]
    exact Subgroup.mem_map.mpr ⟨⟨s, hsS⟩, hsW, rfl⟩
  refine hnot (kd2Lin_inner_of_conj (θ.toMonoidHom.comp ψ) hker₀
    (u := TableB.projConj S ⟨N, hNnorm⟩) hN ht ?_)
  intro x hx
  rw [hJeq] at hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have h3 := hsconj (g : GL (Fin (lab.rank + 1)) K) hg
  have h4 : S.normalizerMonoidHom ⟨N, hNnorm⟩ g = ⟨s, hsS⟩ * g * ⟨s, hsS⟩⁻¹ :=
    Subtype.ext h3
  show TableB.projConj S ⟨N, hNnorm⟩ (LargeEvenProjMk S g) =
    LargeEvenProjMk S ⟨s, hsS⟩ * LargeEvenProjMk S g * (LargeEvenProjMk S ⟨s, hsS⟩)⁻¹
  calc TableB.projConj S ⟨N, hNnorm⟩ (LargeEvenProjMk S g)
      = LargeEvenProjMk S (S.normalizerMonoidHom ⟨N, hNnorm⟩ g) :=
        TableB.projConj_mk S ⟨N, hNnorm⟩ g
    _ = LargeEvenProjMk S (⟨s, hsS⟩ * g * ⟨s, hsS⟩⁻¹) := by rw [h4]
    _ = _ := by rw [map_mul, map_mul, map_inv]

theorem splitLiftLinear_holds :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .A →
      LargeEvenLabelAll lab (fun R _ I _ =>
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
            GGRankOneSetup I ψ 3 e J 3 a → SplitLift lab R I ψ e → False) := by
  intro lab hΛ htag
  intro Q hraw
  simp only [CFSG.StandardType.LargeEvenRawDatum, htag] at hraw ⊢
  obtain ⟨K, fieldK, finiteK, hcard, hQ⟩ := hraw
  refine ⟨K, fieldK, finiteK, hcard, hQ, ?_⟩
  intro L' _ _ ψ hψ hker hperf e J a hsetup hsplit
  exact ltrcl_core_contradiction lab hΛ htag ψ hψ hker hperf e J a hsetup hsplit

end CFSG.StandardType.KD2Pieces1615

end
