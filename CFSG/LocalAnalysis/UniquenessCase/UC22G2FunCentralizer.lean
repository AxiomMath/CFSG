module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofLongCent
import CFSG.ClassicalInvolution.AschTight.S19FAut
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunLowerBound
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ClassicalInvolution.Generic
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section Fund


theorem g2LongSL2_mem_fundamentalSubgroups (F : Type) [Field F] :
    g2LongSL2 F ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum F) := by
  have h := conjSub_range_g2Chart_mem (K := F) 1 g2ia
  rw [CFSG.ClassicalInvolution.Generic.conjSub_one] at h
  have he : (g2Chart F g2ia).range = g2LongSL2 F := by
    ext z
    rw [mem_g2LongSL2_iff, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext hA⟩
  rw [he] at h
  exact h

theorem g2ShortSL2_mem_fundamentalSubgroups (F : Type) [Field F] :
    g2ShortSL2 F ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum F) := by
  let w : adjointGroup .G2 F :=
    ⟨canonicalRep (coxeterSystem .G2) F wV, canonicalRep_mem_adjointGroup _ F wV⟩
  have h := conjSub_range_g2Chart_mem (K := F) w g2s
  have he : CFSG.ClassicalInvolution.Generic.conjSub w (g2Chart F g2s).range = g2ShortSL2 F := by
    ext z
    rw [mem_g2ShortSL2_iff, CFSG.ClassicalInvolution.Generic.mem_conjSub_iff, MonoidHom.mem_range,
      MonoidHom.mem_range]
    constructor
    · rintro ⟨A, hA⟩
      have hA' : simpleRootSL2 .G2 F g2s A =
          (canonicalRep (coxeterSystem .G2) F wV)⁻¹ * (z : ModGL .G2 F) *
            canonicalRep (coxeterSystem .G2) F wV := congrArg Subtype.val hA
      exact ⟨A, by rw [rhoV_apply, hA']; group⟩
    · rintro ⟨A, hA⟩
      refine ⟨A, Subtype.ext ?_⟩
      rw [rhoV_apply] at hA
      show simpleRootSL2 .G2 F g2s A =
        (canonicalRep (coxeterSystem .G2) F wV)⁻¹ * (z : ModGL .G2 F) *
          canonicalRep (coxeterSystem .G2) F wV
      rw [← hA]
      group
  rw [he] at h
  exact h

end Fund

section Cent


theorem g2_centralizer_funSet_le {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 n p f)
    (hX : CFSG.Blueprint.LieModel X .G2 n p f) (h6 : 6 ≤ p ^ f) (P : Sylow 2 X)
    {K₁ K₂ : Subgroup X} (h₁ : K₁ ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X))
    (h₂ : K₂ ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    centralizer (K₁ : Set X) ≤ K₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h6
  have hF6 : 6 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    exact h6
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .G2 n p f hp hp2 (by trivial) hadm X hX
  let A : Bool → Subgroup (modelUniv .G2 n p f hp).K :=
    fun b => cond b (g2LongSL2 (GaloisField p f)) (g2ShortSL2 (GaloisField p f))
  have hA : ∀ b, A b ∈ fundamentalSubgroups .G2 (modelUniv .G2 n p f hp).D := by
    intro b
    cases b
    · exact g2ShortSL2_mem_fundamentalSubgroups _
    · exact g2LongSL2_mem_fundamentalSubgroups _
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij a ha b hb
    cases i <;> cases j
    · exact absurd rfl hij
    · exact g2Short_commute_g2Long ha hb
    · exact (g2Short_commute_g2Long hb ha).symm
    · exact absurd rfl hij
  have hAfund : ∀ k, IsFundamentalOver (p ^ f) ((A k).map ψ) := fun k =>
    ⟨.G2, n, p, f, hp, hp2, rfl, by trivial, hadm, ψ, hψ, hker, A k, hA k, rfl⟩
  have hnorm : ∀ i j, (A j).map ψ ≤ Subgroup.normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb =>
          CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hAc i j hij) b hb a ha
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hAfund hnorm P
  let ψc : (modelUniv .G2 n p f hp).K →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (modelUniv .G2 n p f hp).K := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) :=
    fun k => by simpa only [ψc, Subgroup.map_map] using hc k
  have hLS : (A true).map ψc ≠ (A false).map ψc := by
    intro heq
    obtain ⟨e⟩ := nonempty_mulEquiv_g2LongSL2 (K := GaloisField p f)
    obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψc hkerC e.symm
    have hb' : ψc b ∈ (A false).map ψc := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem ψc hb
    obtain ⟨s, hs, hsb⟩ := Subgroup.mem_map.mp hb'
    apply hab
    rw [← hsb, ← map_mul, ← map_mul, hAc true false (by decide) a ha s hs]
  have hcard := ncard_funSet_eq_two_of_funTwoType hp hp2 hadm hX trivial P
  have hFun : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      {(A true).map ψc, (A false).map ψc} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_
      (Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num))).symm
    · intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl
      · exact hc' true
      · exact hc' false
    · rw [hcard, Set.ncard_pair hLS]
  have hstep : ∀ i : Bool,
      centralizer (((A i).map ψc : Subgroup X) : Set X) ≤ (A (!i)).map ψc := by
    intro i x hx
    obtain ⟨xt, rfl⟩ := hψc x
    have hcomm : Commutes (A i) (Subgroup.zpowers xt) := by
      apply commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψc hkerC (hA i)
      rw [MonoidHom.map_zpowers]
      intro u hu v hv
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hux : Commute u (ψc xt) := Subgroup.mem_centralizer_iff.mp hx u hu
      exact (hux.zpow_right z).eq
    have hxtC : xt ∈ centralizer ((A i : Subgroup _) : Set (modelUniv .G2 n p f hp).K) :=
      Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha xt (Subgroup.mem_zpowers xt)
    refine Subgroup.mem_map_of_mem ψc ?_
    cases i
    · exact mem_g2LongSL2_of_mem_centralizer (by omega) hxtC
    · exact mem_g2ShortSL2_of_mem_centralizer hF6 hxtC
  rw [hFun] at h₁ h₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact absurd rfl hne
  · exact hstep true
  · exact hstep false
  · exact absurd rfl hne

end Cent

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
