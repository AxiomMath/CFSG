module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6KeyHyps
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Key
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Induces
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRoot
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreE6Char
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F KGCentE6

theorem ggKGCentTagStmt_E6
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput) : GGKGCentTagStmt .E6 := by
  rintro G _ _ p B Bs x L D J 𝒦 hcfg - ⟨r, hr, hrefl⟩ X hX n f ψ hloc hstd t ht2 htN htD htJ
  have hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K := hloc.2.1.1
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny (k := GaloisField 2 f) hker
  have hπ := Isogeny.e6Isogeny_surjective (GaloisField 2 f)
  have hπker := CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := GaloisField 2 f)
  have hXψ : ψ.range = X := hloc.2.1.2.1
  have htN' : t ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hXψ]
    exact htN
  have hDBs : D ≤ Bs := hcfg.1.1.2.2.1.1.trans hcfg.1.1.2.1.1
  have hDN : D ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hXψ]
    exact hDBs.trans hloc.2.2.1.2.1
  have hD : CFSG.Open.IsElemAbelian p D := hcfg.1.1.2.2.1.2.1
  have := CentralExt.FieldFour.finite_minGroup' (K := GaloisField 2 f) Minuscule.e6Data_valid
  have hperf := CFSG.LieType.CurtisTits.isPerfect_e6 (GaloisField 2 f)
  obtain ⟨α, hα'⟩ := RootDetect.exists_homAut hπ hπker hperf.commutator_eq_top hker (inv_mem htN')
  have hα : LayerSixE.GGInduces (Isogeny.e6Isogeny (GaloisField 2 f)) ψ t α := fun y y' h =>
    (hα' y y' (by rwa [inv_inv])).symm
  obtain ⟨hf, hp, hp2, hpK, hF, hne, hcyc, hrank⟩ :=
    ggKGCent_keyHyps_E6 ha₀ hL hcfg hr hrefl hX hloc hstd rfl
  have h1 : α = 1 := by
    refine eq_one_of_commute_famKernel_E6 hf (GaloisField.card 2 f (by omega)) hp hp2 hpK hF hne
      (fun _ => hcyc) hrank ?_ ?_ ?_
    ·
      obtain ⟨m, hm⟩ := ht2
      refine ⟨m, ?_⟩
      have h2 := hα.pow hkπ htN' (2 ^ m)
      rw [hm] at h2
      exact h2.unique hπ (one_mem _) (LayerSixE.GGInduces.one hkπ)
    ·
      rintro a ⟨d, hd, had⟩
      have h2 := had.mul htN' hα
      rw [Subgroup.mem_centralizer_iff.1 htD d hd] at h2
      exact (hα.mul (hDN hd) had).unique hπ (mul_mem htN' (hDN hd)) h2
    ·
      intro β hβ
      have hβr : β ∈ (ggU .E6 n f).D.roots :=
        (Minuscule.e6Data_valid.mem_minDatum_roots Minuscule.isFiniteType_cartan_E6
          (GaloisField 2 f)).2 hβ.1
      have hβΦ : β ∈ ggKGCentRoots (ggU .E6 n f).D ψ D := by
        refine ⟨hβr, fun z hz => Subgroup.mem_comap.2 (Subgroup.mem_centralizer_iff.2
          fun d hd => ?_)⟩
        obtain ⟨a, -, had⟩ := JCoreE6.exists_induces_rootDiag_E6 (k := GaloisField 2 f) ψ hker
          (hDN hd) (hD.2 d hd) (hstd d (hDBs hd))
        exact commute_of_rootChar_eq_one_E6 had hβ.1 (hβ.2 a ⟨d, hd, had⟩)
          (hstd d (hDBs hd) β hβr) z hz
      have hJ := ggKGCent_rootGroup_le ha₀ hL hcfg hr hrefl hX hloc hstd hβΦ
      exact ggInduces_fix_rootSubgroup_E6 hα hβ.1 fun z hz =>
        (Subgroup.mem_centralizer_iff.1 htJ (ψ z) (hJ (Subgroup.mem_map_of_mem ψ hz))).symm
  subst h1
  have htC := ExcNonsplit.mem_centralizer_of_induces_one hπker.le
    (Group.isPerfect_def.1 (@Group.IsPerfect.range _ _ _ _ ψ hperf)) htN' hα
  intro g hg h _
  rw [← hXψ] at hg
  rw [← Subgroup.mem_centralizer_iff.1 htC g hg, mul_inv_cancel_right, mul_inv_cancel]
  exact Commute.one_left h

end CFSG.StandardType

end
