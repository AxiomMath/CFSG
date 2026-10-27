module
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberE7RootCentralizer
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCyclicCore
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UData
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoLang
public import CFSG.LocalAnalysis.StandardType.GGLangRatCompC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTQuot
public import Certificates.Certificate8064
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoModel
public noncomputable section
namespace CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
variable {G : Type} [Group G] [Finite G]

theorem ggG0_ne_L_of_twistedE6_E7_join {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hE7 : ∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ)
    (hmark : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) :
    ggG0 p B x L D J ≠ L := by
  intro h0
  have hW : GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer L Bs) := by
    by_cases hp3 : p = 3
    · exact ggTwE6Bad_weylOfType hcfg.1
        (hmark.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, hp3, hp3 ▸ h.2⟩)
    · exact ggTwE6Row_weylOfType hcfg.1
        (hmark.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, h.2, hp3⟩)
  obtain ⟨w, -⟩ := hW
  have hA : ggAutomizerJoin L Bs 𝒦 = ggAutomizer L Bs := by
    apply le_antisymm
    · have hle := ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
      rw [← hJoin, h0] at hle
      exact hle
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
  obtain ⟨σ, hM⟩ := hE7
  have h7 : Nat.card (ggAutomizerJoin L Bs 𝒦) = 2903040 := by
    rw [← Nat.card_congr e.toEquiv, hM, card_coxeterGroup_reindex, card_coxeterE7_group]
  have h6 : Nat.card (ggAutomizer L Bs) = 51840 := by
    rw [← Nat.card_congr w.toEquiv, card_coxeterE6_group]
  rw [hA] at h7
  omega

theorem ne_one_of_E7_centralizer_of_twistedE6_join {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    {ι : Type} {N : CoxeterMatrix ι} (e : N.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hE7 : ∃ σ : Fin 7 ≃ ι, N = CoxeterMatrix.E₇.reindex σ)
    (hmark : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hrange : lambda.range = ggG0 p B x L D J)
    (y : e7Data_valid.minGroup K) (M : Subgroup (e7Data_valid.minGroup K))
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer {y}))
    (hmap : M.map lambda = L) : y ≠ 1 := by
  intro hy
  have hcent : Subgroup.centralizer ({y} : Set (e7Data_valid.minGroup K)) = ⊤ := by
    rw [hy]
    ext z
    simp only [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul, Subgroup.mem_top,
      ]
  rw [hcent] at hM
  have htop := ExcNonsplit.eq_top_of_isComponentOf_top
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 K) hM
  rw [htop, Subgroup.map_top, hrange] at hmap
  exact ggG0_ne_L_of_twistedE6_E7_join hcfg hJoin e hE7 hmark hmap

theorem exists_rational_component_of_native_E7_centralizer_of_langData
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (y : e7Data_valid.minGroup K) (hy1 : y ≠ 1)
    (M : Subgroup (e7Data_valid.minGroup K))
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer {y}))
    (S : LangSetup Tag.E7 (AlgebraicClosure K) 5)
    (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hT : rootDiagUnit .E7 a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (hinj : Function.Injective iota) (hrange : iota.range = S.Γ)
    (heq : iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K y) = rootDiagUnit .E7 a) :
    ∃ c : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) c) ∧
      M.map (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom) =
        rationalComponent S.ρ S.Γ (rootCharHom a) c := by
  let theta := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K
  have hy' : theta y ≠ 1 := by
    intro h
    exact hy1 (theta.injective (h.trans (map_one theta).symm))
  have hMC : CFSG.Assembly.IsComponentOf (M.map theta.toMonoidHom)
      (Subgroup.centralizer {theta y}) := by
    apply CFSG.Assembly.isComponentOf_iff_open.mpr
    exact CFSG.LocalAnalysis.GLTheoremA.HSubT.isComponentOf_image_centralizer
      theta.toMonoidHom theta.surjective (fun z hz => by
        have hz1 : z = 1 := theta.injective (hz.trans (map_one theta).symm)
        simpa only [hz1] using (Subgroup.center _).one_mem)
      (CFSG.Assembly.isComponentOf_iff_open.mp hM)
  have hpL : (p : AlgebraicClosure K) ≠ 0 := by
    intro h
    have hdiv : 2 ∣ p := (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdiv).symm
  obtain ⟨c, hquasi, hmap⟩ := LangRat.langRatComp_of_component S (Or.inl rfl) hp hpL
    iota hinj hrange heq hT hap hy' (CFSG.Assembly.isComponentOf_iff_open.mp hMC)
  rw [Subgroup.map_map] at hmap
  exact ⟨c, hquasi, hmap⟩

end CFSG.StandardType
