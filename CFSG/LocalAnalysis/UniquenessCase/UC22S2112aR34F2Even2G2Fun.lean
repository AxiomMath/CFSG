module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily
import CFSG.LocalAnalysis.UniquenessCase.UC22G2FunCentralizer
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo
import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunLowerBound
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.ClassicalInvolution.Generic

theorem uc22s2112r34_exists_sylow_mem_funSet {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop} {K : Subgroup X}
    (hK : 𝔉 ⊤ K) : ∃ P : Sylow 2 X, K ∈ F14.FunSet 𝔉 X (P : Subgroup X) := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  let Q' : Subgroup X := (Q : Subgroup K).map K.subtype
  have hQ' : IsPGroup 2 Q' := Q.isPGroup'.map _
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  have hQS : CFSG.ABGLocalTools.IsSylowOf 2 Q' K := ⟨Q, rfl⟩
  have hinf : (P : Subgroup X) ⊓ K = Q' :=
    hQS.eq_of_le (le_inf hP (Subgroup.map_subtype_le _)) inf_le_right
      (P.isPGroup'.to_le inf_le_left)
  refine ⟨P, ?_⟩
  change 𝔉 ⊤ K ∧ CFSG.ABGLocalTools.IsSylowOf 2 ((P : Subgroup X) ⊓ K) K
  rw [hinf]
  exact ⟨hK, hQS⟩

private theorem uc22s2112r34_g2fun_centralizer_map {A X : Type} [Group A] [Group X]
    (ψ : A ≃* X) (s : Set A) :
    centralizer (ψ '' s) = (centralizer s).map ψ.toMonoidHom := by
  refine le_antisymm ?_ (Subgroup.map_centralizer_le_centralizer_image s ψ.toMonoidHom)
  intro x hx
  rw [Subgroup.mem_map]
  refine ⟨ψ.symm x, ?_, ψ.apply_symm_apply x⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro a ha
  exact ψ.injective (by
    simpa only [map_mul, ψ.apply_symm_apply] using hx (ψ a) (Set.mem_image_of_mem ψ ha))

theorem uc22s2112r34_centralizer_commutator_centralizer_map {A X : Type} [Group A] [Group X]
    (ψ : A ≃* X) (y : A) :
    centralizer ((⁅centralizer ({ψ y} : Set X), centralizer ({ψ y} : Set X)⁆ : Subgroup X) :
        Set X) =
      (centralizer ((⁅centralizer ({y} : Set A), centralizer ({y} : Set A)⁆ : Subgroup A) :
        Set A)).map ψ.toMonoidHom := by
  have h1 : centralizer ({ψ y} : Set X) =
      (centralizer ({y} : Set A)).map ψ.toMonoidHom := by
    simpa only [Set.image_singleton] using
      uc22s2112r34_g2fun_centralizer_map ψ ({y} : Set A)
  have hcomm : ((⁅centralizer ({y} : Set A), centralizer ({y} : Set A)⁆ : Subgroup A)).map
      ψ.toMonoidHom = ⁅centralizer ({ψ y} : Set X), centralizer ({ψ y} : Set X)⁆ := by
    rw [Subgroup.map_commutator, h1]
  rw [← hcomm]
  exact uc22s2112r34_g2fun_centralizer_map ψ
    (((⁅centralizer ({y} : Set A), centralizer ({y} : Set A)⁆ : Subgroup A) : Set A))

section Cent


theorem uc22s2112r34_g2_funSet_eq_pair {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 n p f)
    (hX : LieModel X .G2 n p f) (P : Sylow 2 X) :
    ∃ ψ : adjointGroup .G2 (GaloisField p f) ≃* X,
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
        {(g2LongSL2 (GaloisField p f)).map ψ.toMonoidHom,
          (g2ShortSL2 (GaloisField p f)).map ψ.toMonoidHom} := by
  have hp : p.Prime := Fact.out
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
  have hZ : Subgroup.center (modelUniv .G2 n p f hp).K = ⊥ :=
    center_adjointGroup_eq_bot
  have hkerbot : ψc.ker = ⊥ := le_bot_iff.mp (hZ ▸ hkerC)
  have hinj : Function.Injective ψc := (MonoidHom.ker_eq_bot_iff ψc).mp hkerbot
  let e : (modelUniv .G2 n p f hp).K ≃* X := MulEquiv.ofBijective ψc ⟨hinj, hψc⟩
  refine ⟨e, ?_⟩
  rw [hFun]
  rfl

theorem uc22s2112r34_g2_exists_mulEquiv_fund {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 n p f)
    (hX : LieModel X .G2 n p f) {K : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) :
    ∃ ψ : adjointGroup .G2 (GaloisField p f) ≃* X,
      K = (g2LongSL2 (GaloisField p f)).map ψ.toMonoidHom ∨
        K = (g2ShortSL2 (GaloisField p f)).map ψ.toMonoidHom := by
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_mem_funSet
    (𝔉 := fundPred (p ^ f)) (K := K) hK
  obtain ⟨ψ, hψ⟩ := uc22s2112r34_g2_funSet_eq_pair hp2 hadm hX P
  rw [hψ] at hP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  exact ⟨ψ, hP⟩

end Cent

end CFSG.LocalAnalysis.UniquenessCase.UC22
