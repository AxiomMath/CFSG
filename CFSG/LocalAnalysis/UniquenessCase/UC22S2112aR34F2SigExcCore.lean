module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
import CFSG.LocalAnalysis.UniquenessCase.UC22G2FunCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2F1
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitHolds
import CFSG.Adapters.TauCetiExceptional.ReeCatalog
import CFSG.GroupTheory.PRankBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.CGT.Foote82.T66.Proof511Rows
import CFSG.GH74.Generic.BProg.B2.PumpupOutOrdersAux
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Swap
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2SwapRows
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2UniqSp
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSetSL2
import CFSG.LinearAlgebra.LinearGroups.PGLTwoPPart
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2G2Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationFrattini
import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ClassicalInvolution.Generic


theorem pow_eq_one_of_forall_funSet_of_modelFamily
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hX : CFSG.Blueprint.LieModel X t n p e)
    {ι : Type} (i₀ : ι) (A : ι → Subgroup (modelUniv t n p e hp.out).K)
    (hA : ∀ k, A k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (hAc : ∀ i j, i ≠ j → Commutes (A i) (A j)) {m : ℕ}
    (hm : ∀ y : (modelUniv t n p e hp.out).K, (∀ k, ∀ x ∈ A k, Commute x y) →
      y ^ m ∈ Subgroup.center (modelUniv t n p e hp.out).K)
    (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ m = 1 := by
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  have hAfund : ∀ k, IsFundamentalOver (p ^ e) ((A k).map ψ) := fun k =>
    ⟨t, n, p, e, hp.out, hp2, rfl, hfund, hadm, ψ, hψ, hker, A k, hA k, rfl⟩
  have hnorm : ∀ i j, (A j).map ψ ≤ Subgroup.normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb =>
          CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hAc i j hij) b hb a ha
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ e))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hAfund hnorm P
  let ψc : (modelUniv t n p e hp.out).K →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (modelUniv t n p e hp.out).K := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) :=
    fun k => by simpa only [ψc, Subgroup.map_map] using hc k
  have hZ : center X = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple
      (exists_noncommuting_of_isFundamentalOver (hc' i₀).1)
  obtain ⟨xt, hxt⟩ := hψc x
  have hcommK : ∀ k, ∀ y ∈ A k, Commute y xt := by
    intro k y hy
    have hk : Commutes (A k) (Subgroup.zpowers xt) := by
      apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC (hA k)
      rw [MonoidHom.map_zpowers, hxt]
      intro u hu v hv
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hux : Commute u x := Subgroup.mem_centralizer_iff.mp (hx _ (hc' k)) u hu
      exact (hux.zpow_right z).eq
    exact hk y hy xt (Subgroup.mem_zpowers xt)
  have hzX : ψc (xt ^ m) ∈ Subgroup.center X :=
    Subgroup.map_center_le_center hψc (Subgroup.mem_map_of_mem ψc (hm xt hcommK))
  rw [hZ] at hzX
  calc x ^ m = ψc (xt ^ m) := by rw [map_pow, hxt]
    _ = 1 := Subgroup.mem_bot.mp hzX

section PSp

open Matrix CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

theorem sq_eq_one_of_forall_commute_root_psp {F : Type} [Field F] {n : ℕ} {M : StatedSp n F}
    (hpos : ∀ k, Commute M (elt (RootSubgroupIndex.positiveLong k) (1 : F)))
    (hneg : ∀ k, Commute M (elt (RootSubgroupIndex.negativeLong k) (1 : F))) :
    M ^ 2 = 1 := by
  classical
  have hsingle : ∀ (a b : Fin n ⊕ Fin n), (Matrix.transvection a b (1 : F) * mat n F M =
      mat n F M * Matrix.transvection a b (1 : F)) →
      Commute (Matrix.single a b (1 : F)) (mat n F M) := by
    intro a b h
    have h' : (1 + Matrix.single a b (1 : F)) * mat n F M =
        mat n F M * (1 + Matrix.single a b (1 : F)) := by
      simpa [Matrix.transvection] using h
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h'
    exact add_left_cancel h'
  have hposS : ∀ k, Commute (Matrix.single (Sum.inl k) (Sum.inr k) (1 : F)) (mat n F M) := by
    intro k
    apply hsingle
    simpa [map_mul, mat_elt_positiveLong] using (congrArg (mat n F) (hpos k)).symm
  have hnegS : ∀ k, Commute (Matrix.single (Sum.inr k) (Sum.inl k) (1 : F)) (mat n F M) := by
    intro k
    apply hsingle
    simpa [map_mul, mat_elt_negativeLong] using (congrArg (mat n F) (hneg k)).symm
  have hdiag : (mat n F M).IsDiag := by
    intro i j hij
    rcases j with k | k
    · exact Matrix.col_eq_zero_of_commute_single (hposS k) hij
    · exact Matrix.col_eq_zero_of_commute_single (hnegS k) hij
  set d := (mat n F M).diag with hd
  have hMd : mat n F M = Matrix.diagonal d := hdiag.diagonal_diag.symm
  have heq : ∀ k, d (Sum.inl k) = d (Sum.inr k) := by
    intro k
    have h := congrFun (congrFun (hposS k).eq (Sum.inl k)) (Sum.inr k)
    rw [hMd, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa [Matrix.single_apply] using h.symm
  have hform : (mat n F M)ᵀ * fromBlocks 0 1 (-1) 0 * mat n F M = fromBlocks 0 1 (-1) 0 := by
    have hmem : ((M : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
        CFSG.Blueprint.EvenSource.matrixIsometry (CFSG.Blueprint.EvenSource.sourceSpJ n F) := by
      rw [← CFSG.Blueprint.EvenSource.statedSp_eq_matrixIsometry]
      exact M.2
    exact hmem
  have hprod : ∀ k, d (Sum.inl k) * d (Sum.inr k) = 1 := by
    intro k
    have h := congrFun (congrFun hform (Sum.inl k)) (Sum.inr k)
    rw [hMd, Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h
  have hsq : ∀ a, d a * d a = 1 := by
    intro a
    rcases a with k | k
    · rw [show d (Sum.inl k) * d (Sum.inl k) = d (Sum.inl k) * d (Sum.inr k) by rw [heq k]]
      exact hprod k
    · rw [show d (Sum.inr k) * d (Sum.inr k) = d (Sum.inl k) * d (Sum.inr k) by rw [heq k]]
      exact hprod k
  apply mat_injective
  rw [map_pow, map_one, hMd, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext a
  simpa [pow_two] using hsq a

theorem sq_eq_one_of_forall_funSet_psp
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p f) (hX : CFSG.Blueprint.LieModel X .PSp n p f)
    (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ 2 = 1 := by
  let F := GaloisField p f
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hadm.2.2.1
  have hmodel : ∀ k : Fin n, longRootSp2 F n k ∈
      fundamentalSubgroups .PSp (modelUniv .PSp n p f hp.out).D := fun k =>
    (CFSG.ClassicalInvolution.ModelFacts.fund_iff_isLongRootSp2 hadm h2 _).mpr
      ⟨longInv F n k, isLongRootSp2_standard k⟩
  refine pow_eq_one_of_forall_funSet_of_modelFamily (t := .PSp) hp2 (by trivial) hadm hX
    (⟨0, hn⟩ : Fin n)
    (fun k => longRootSp2 F n k) hmodel (fun i j hij a ha b hb => ?_) ?_ P hx
  · exact (commute_longRootSp2 hij ha hb).eq
  · intro y hy
    have hy' : y ^ 2 = 1 := sq_eq_one_of_forall_commute_root_psp (M := y)
      (fun k => (hy k _ ⟨sl2Upper 1, longBlock_sl2Upper k 1⟩).symm)
      (fun k => (hy k _ ⟨sl2Lower 1, longBlock_sl2Lower k 1⟩).symm)
    rw [hy']
    exact Subgroup.one_mem _

end PSp

section G2
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

theorem sq_eq_one_of_mem_center_sl2 {F : Type} [Field F] {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : A ^ 2 = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h : ((A ^ 2 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow, hr, map_one]
  exact Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm)

theorem sq_eq_one_of_commute_g2LongSL2_g2ShortSL2 {F : Type} [Field F] [Finite F]
    (hF5 : 5 ≤ Nat.card F) {y : adjointGroup .G2 F} (hyL : ∀ x ∈ g2LongSL2 F, Commute x y)
    (hyS : ∀ x ∈ g2ShortSL2 F, Commute x y) : y ^ 2 = 1 := by
  have hyC : y ∈ centralizer (g2ShortSL2 F : Set (adjointGroup .G2 F)) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => (hyS a ha).eq
  have hyM : y ∈ g2LongSL2 F := mem_g2LongSL2_of_mem_centralizer hF5 hyC
  have hcen : (⟨y, hyM⟩ : g2LongSL2 F) ∈ Subgroup.center (g2LongSL2 F) :=
    Subgroup.mem_center_iff.mpr fun z => Subtype.ext (hyL z z.2).eq
  obtain ⟨e⟩ := nonempty_mulEquiv_g2LongSL2 (K := F)
  have hcen' : e.symm ⟨y, hyM⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.map_center_le_center e.symm.surjective
      (Subgroup.mem_map_of_mem e.symm.toMonoidHom hcen)
  have h2 : (⟨y, hyM⟩ : g2LongSL2 F) ^ 2 = 1 := by
    apply e.symm.injective
    rw [map_pow, map_one]
    exact sq_eq_one_of_mem_center_sl2 hcen'
  simpa using congrArg Subtype.val h2

theorem sq_eq_one_of_forall_funSet_g2
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .G2 n p f) (hX : CFSG.Blueprint.LieModel X .G2 n p f)
    (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ 2 = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have hF5 : 5 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    exact h5
  refine pow_eq_one_of_forall_funSet_of_modelFamily (t := .G2) hp2 (by trivial) hadm hX true
    (fun b => cond b (g2LongSL2 (GaloisField p f)) (g2ShortSL2 (GaloisField p f)))
    (fun b => ?_) (fun i j hij a ha b hb => ?_) (fun y hy => ?_) P hx
  · cases b
    · exact g2ShortSL2_mem_fundamentalSubgroups _
    · exact g2LongSL2_mem_fundamentalSubgroups _
  · cases i <;> cases j
    · exact absurd rfl hij
    · exact g2Short_commute_g2Long ha hb
    · exact (g2Short_commute_g2Long hb ha).symm
    · exact absurd rfl hij
  · have hy2 : y ^ 2 = 1 := sq_eq_one_of_commute_g2LongSL2_g2ShortSL2 hF5 (hy true) (hy false)
    rw [hy2]
    exact Subgroup.one_mem _

end G2

section Ree

theorem sixteen_dvd_ordBC_two {q : ℕ} (hq : Odd q) : 16 ∣ ordBC 2 q := by
  have hm := CFSG.CGT.Foote82.Proof511.ordBC_two_mul q
  have hg : Nat.gcd 2 (q - 1) = 2 := Nat.gcd_eq_left (by obtain ⟨k, rfl⟩ := hq; omega)
  rw [hg] at hm
  obtain ⟨a, ha⟩ := CFSG.CGT.Foote82.Proof511.eight_dvd_sq_sub hq
  obtain ⟨b, hb⟩ := CFSG.CGT.Foote82.Proof511.sixteen_dvd_fourth_sub hq
  refine ⟨4 * (q ^ 4 * a * b), Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) ?_⟩
  rw [hm, ha, hb]
  ring

theorem uc22s2112r34_not_ree_of_exc {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : CFSG.Blueprint.LieModel X .PSp 2 p 1 ∨ CFSG.Blueprint.LieModel X .G2 0 p 1) (f : ℕ) :
    ¬ CFSG.Blueprint.LieModel X .twistedG2 0 3 f := by
  intro hR
  obtain ⟨k, -, hk⟩ := CFSG.GH74.card_of_lieModel_twistedG2 hR
  apply CFSG.GH74.Generic.BProg.B2.PumpupOutOrders.not_sixteen_dvd_ordRee k
  rw [← hk]
  have hpo : Odd p := hp.odd_of_ne_two hp2
  rcases hX with hX | hX
  · rw [CFSG.GH74.card_of_lieModel_PSp (by norm_num) hp2 hX, pow_one]
    exact sixteen_dvd_ordBC_two hpo
  · rw [CFSG.GH74.card_of_lieModel_G2 hp2 hX, pow_one]
    exact CFSG.GH74.Generic.BProg.B2.PumpupOutOrders.sixteen_dvd_ordG2 hpo

end Ree

section Pair


theorem uc22s2112r34_exc_pair_faithful {G : Type} [Group G] [Finite G] {D : Data G}
    {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .PSp 2 p 1 ∨
      CFSG.Blueprint.LieModel (BarInf L) .G2 0 p 1)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {b : G} (hb : b ∈ c.B0) (hb1 : b ≠ 1) {K₁ K₂ : Subgroup (BarInf L)}
    (h₁ : IsFundamentalOver (p ^ 1) K₁) (h₂ : IsFundamentalOver (p ^ 1) K₂) (hne : K₁ ≠ K₂)
    (hc : ⁅K₁, K₂⁆ = ⊥) (hfix : ∀ k ∈ K₁ ⊔ K₂, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hadmS : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨hp, le_refl 1, le_refl 2, fun h => hp2 (by simpa using congrArg Prod.snd h)⟩
  have hadmG : StatedLieAdmissible .G2 0 p 1 := ⟨hp, le_refl 1, rfl, by rw [pow_one]; omega⟩
  have hle₁ : K₁ ≤ centralizer (K₂ : Set (BarInf L)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hle₂ : K₂ ≤ centralizer (K₁ : Set (BarInf L)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hc)
  have hsq : ∀ z : BarInf L, z ∈ centralizer (K₁ : Set (BarInf L)) →
      z ∈ centralizer (K₂ : Set (BarInf L)) → z ^ 2 = 1 := by
    intro z hz₁ hz₂
    obtain ⟨P⟩ : Nonempty (Sylow 2 (BarInf L)) := inferInstance
    let A : Bool → Subgroup (BarInf L) := fun i => cond i K₁ K₂
    have hnorm : ∀ i j, A j ≤ normalizer (A i : Set (BarInf L)) := by
      intro i j
      cases i <;> cases j
      · exact Subgroup.le_normalizer
      · exact hle₁.trans (Subgroup.centralizer_le_normalizer _)
      · exact hle₂.trans (Subgroup.centralizer_le_normalizer _)
      · exact Subgroup.le_normalizer
    obtain ⟨g, hg⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ 1))
      (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h) A
      (fun i => by cases i <;> assumption) hnorm P
    have hncard :
        (F14.FunSet (fundPred (p ^ 1)) (BarInf L) (P : Subgroup (BarInf L))).ncard = 2 := by
      rcases hX with hXs | hXg
      · exact (kFunCount_holds (BarInf L) .PSp 2 p 1 hp hp2 hadmS hXs P).1 rfl
      · exact (kFunCount_holds (BarInf L) .G2 0 p 1 hp hp2 hadmG hXg P).1 trivial
    have hne' :
        (A true).map (MulAut.conj g).toMonoidHom ≠ (A false).map (MulAut.conj g).toMonoidHom :=
      fun h => hne (Subgroup.map_injective (MulAut.conj g).injective h)
    have hpair := Set.eq_of_subset_of_ncard_le
      (Set.insert_subset (hg true) (Set.singleton_subset_iff.mpr (hg false)))
      (by rw [hncard, Set.ncard_pair hne']) (Set.toFinite _)
    have key : ∀ i, g * z * g⁻¹ ∈
        centralizer (((A i).map (MulAut.conj g).toMonoidHom : Subgroup (BarInf L)) :
          Set (BarInf L)) := by
      intro i
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k₀, hk₀, rfl⟩
      have hzk : k₀ * z = z * k₀ := by
        cases i
        · exact Subgroup.mem_centralizer_iff.mp hz₂ k₀ hk₀
        · exact Subgroup.mem_centralizer_iff.mp hz₁ k₀ hk₀
      show g * k₀ * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * k₀ * g⁻¹)
      calc g * k₀ * g⁻¹ * (g * z * g⁻¹) = g * (k₀ * z) * g⁻¹ := by group
        _ = g * (z * k₀) * g⁻¹ := by rw [hzk]
        _ = g * z * g⁻¹ * (g * k₀ * g⁻¹) := by group
    have hall : ∀ K ∈ F14.FunSet (fundPred (p ^ 1)) (BarInf L) (P : Subgroup (BarInf L)),
        g * z * g⁻¹ ∈ centralizer (K : Set (BarInf L)) := by
      intro K hK
      rw [← hpair, Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl
      · exact key true
      · exact key false
    have hz2 : (g * z * g⁻¹) ^ 2 = 1 := by
      rcases hX with hXs | hXg
      · exact sq_eq_one_of_forall_funSet_psp hp2 hadmS hXs P hall
      · exact sq_eq_one_of_forall_funSet_g2 hp2 (by rw [pow_one]; exact hp5) hadmG hXg P hall
    rw [conj_pow] at hz2
    simpa [mul_inv_eq_one] using hz2
  have hθodd : Odd (orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩)) := by
    have hdvd : orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) ∣ orderOf b := by
      have h := orderOf_map_dvd (inducedBarInfAutHom L) (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G)))
      simpa [Subgroup.orderOf_mk] using h
    exact Odd.of_dvd_nat (ch214_odd_card c.hpi) (hdvd.trans (Subgroup.orderOf_dvd_natCard c.B0 hb))
  have hθ1 : inducedBarInfAutHom L ⟨b, hBN hb⟩ = 1 := by
    set θ := inducedBarInfAutHom L ⟨b, hBN hb⟩ with hθ
    by_contra hne1
    have hord1 : orderOf θ ≠ 1 := fun h => hne1 (orderOf_eq_one_iff.mp h)
    obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hord1
    have hβord : orderOf (θ ^ (orderOf θ / s)) = s :=
      orderOf_pow_orderOf_div (orderOf_pos θ).ne' hsdvd
    have hsodd : Odd s := Odd.of_dvd_nat hθodd hsdvd
    have hpow : ∀ m : ℕ, ∀ k ∈ K₁ ⊔ K₂, (θ ^ m) k = k := by
      intro m k hk
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, MulAut.mul_apply, hfix k hk, ih]
    have hinn : θ ^ (orderOf θ / s) ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
      rcases hX with hXs | hXg
      · refine uc22s2112r34_inner_of_odd_f1 hp hp2 hXs (Or.inr ⟨rfl, le_refl 2⟩) ?_
          (by rw [hβord]; exact hsodd)
        intro r hr hr2 hdvd
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          (hdvd.trans (Nat.gcd_dvd_left 2 (p ^ 1 - 1))))
      · exact uc22s2112r34_inner_of_squarefree_f1_exc hadmG hXg (Or.inr (Or.inr (Or.inl rfl)))
          (by rw [hβord]; exact hsodd) (by rw [hβord]; exact hs.squarefree)
          (fun h => absurd h (by decide))
    obtain ⟨y, hy⟩ := hinn
    have hyk : ∀ k ∈ K₁ ⊔ K₂, k * y = y * k := by
      intro k hk
      have h1 : y * k * y⁻¹ = k := by
        rw [← MulAut.conj_apply, hy]
        exact hpow _ k hk
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    have hy2 := hsq y
      (Subgroup.mem_centralizer_iff.mpr fun k hk => hyk k (Subgroup.mem_sup_left hk))
      (Subgroup.mem_centralizer_iff.mpr fun k hk => hyk k (Subgroup.mem_sup_right hk))
    have hβ2 : (θ ^ (orderOf θ / s)) ^ 2 = 1 := by rw [← hy, ← map_pow, hy2, map_one]
    have hs2 : s ∣ 2 := hβord ▸ orderOf_dvd_of_pow_eq_one hβ2
    rw [(Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp hs2] at hsodd
    exact absurd hsodd (by decide)
  exact hb1 (hfaith b hb
    (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN hb) hθ1))

end Pair

section Alpha

open scoped Pointwise


theorem seven_le_of_prime_dvd_two_pow_sub_one {m s : ℕ} (hm : Odd m) (hs : s.Prime)
    (hsd : s ∣ 2 ^ m - 1) : 7 ≤ s := by
  obtain ⟨k, rfl⟩ := hm
  have h1 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  have hmod : ((2 : ZMod s) ^ (2 * k + 1)) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff _ s).mpr hsd
    rw [Nat.cast_sub h1] at h
    push_cast at h
    exact sub_eq_zero.mp h
  by_contra hlt
  push Not at hlt
  interval_cases s
  · exact absurd hs (by norm_num)
  · exact absurd hs (by norm_num)
  · rw [show (2 : ZMod 2) = 0 from rfl, zero_pow (by omega)] at hmod
    exact zero_ne_one hmod
  · rw [pow_succ, pow_mul, show (2 : ZMod 3) ^ 2 = 1 from rfl, one_pow, one_mul] at hmod
    exact absurd hmod (by decide)
  · exact absurd hs (by norm_num)
  · rw [pow_succ, pow_mul] at hmod
    have h4 : ∀ j : ℕ, ((2 : ZMod 5) ^ 2) ^ j = 1 ∨ ((2 : ZMod 5) ^ 2) ^ j = 4 := by
      intro j
      induction j with
      | zero => exact Or.inl rfl
      | succ j ih =>
          rw [pow_succ]
          rcases ih with h | h <;> rw [h]
          · exact Or.inr rfl
          · exact Or.inl rfl
    rcases h4 k with h | h <;> rw [h] at hmod <;> exact absurd hmod (by decide)
  · exact absurd hs (by norm_num)

theorem uc22s2112r34_false_of_mem_exc {G : Type} [Group G] [Finite G]
    (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hBN : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp5 : 5 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .PSp 2 p 1 ∨
      CFSG.Blueprint.LieModel (BarInf L) .G2 0 p 1)
    {b : G} (hbB : b ∈ c.B0) (hbT : b ∈ normalizer (D.T : Set G)) {s : ℕ} (hs : s.Prime)
    (hs7 : 7 ≤ s) (hsp : s ≠ p) (hbs : orderOf b = s) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  have hb : b ∈ normalizer (L : Set G) := hBN hbB
  have hadmS : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨hp, le_refl 1, le_refl 2, fun h => hp2 (by simpa using congrArg Prod.snd h)⟩
  have hadmG : StatedLieAdmissible .G2 0 p 1 := ⟨hp, le_refl 1, rfl, by rw [pow_one]; omega⟩
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
    refine not_dvd_card_solvableRadical hL.2.2 hs (by omega) ?_
    rcases hX with hXs | hXg
    · exact uc22s2112r34_not_dvd_center hGA CFSG.TauCetiBridge.typewiseBridges hL hp hp2 hXs hs
        (by omega) (uc22s2112r34_not_dvd_genericOrders (Or.inl rfl) hs hs7)
    · exact uc22s2112r34_not_dvd_center hGA CFSG.TauCetiBridge.typewiseBridges hL hp hp2 hXg hs
        (by omega) (uc22s2112r34_not_dvd_genericOrders (Or.inl trivial) hs hs7)
  have hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1 := fun h1 => by
    have hb1 := hfaith b hbB (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 hb h1)
    rw [hb1, orderOf_one] at hbs
    omega
  have hθs : orderOf (inducedBarInfAutHom L ⟨b, hb⟩) = s := by
    have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
    rw [Subgroup.orderOf_mk, hbs] at hd
    rcases (Nat.dvd_prime hs).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hθ1
    · exact h1
  have hsodd : Odd s := hs.odd_of_ne_two (by omega)
  have hinn : inducedBarInfAutHom L ⟨b, hb⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
    rcases hX with hXs | hXg
    · refine uc22s2112r34_inner_of_odd_f1 hp hp2 hXs (Or.inr ⟨rfl, le_refl 2⟩) ?_
        (by rw [hθs]; exact hsodd)
      intro r hr hr2 hdvd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hdvd.trans (Nat.gcd_dvd_left 2 (p ^ 1 - 1))))
    · exact uc22s2112r34_inner_of_squarefree_f1_exc hadmG hXg (Or.inr (Or.inr (Or.inl rfl)))
        (by rw [hθs]; exact hsodd) (by rw [hθs]; exact hs.squarefree)
        (fun h => absurd h (by decide))
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hinn
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  have hxs : orderOf x = s := by
    rw [← orderOf_injective _ hinj x, hx, hθs]
  have hZx : Nat.card (zpowers x) = s := by rw [Nat.card_zpowers, hxs]
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_barInf hL
  have hxP : x ∈ normalizer ((P : Subgroup (BarInf L)) : Set (BarInf L)) := by
    rw [hP]
    exact uc22s2112r34_mem_normalizer_map hb hbT hx.symm
  have hne : zpowers x ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hxs
    omega
  have hodd' : Odd (Nat.card (zpowers x)) := by
    rw [hZx]
    exact hsodd
  have h3 : ¬ 3 ∣ Nat.card (zpowers x) := fun h => by
    rw [hZx] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).1 h
    omega
  have hpx : ¬ p ∣ Nat.card (zpowers x) := fun h => by
    rw [hZx] at h
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).1 h).symm
  have hperm : ((zpowers x : Subgroup (BarInf L)) : Set (BarInf L)) * (P : Set (BarInf L)) =
      (P : Set (BarInf L)) * (zpowers x : Set (BarInf L)) :=
    set_mul_normalizer_comm (zpowers x : Set (BarInf L)) (P : Subgroup (BarInf L))
      (zpowers_le.2 hxP)
  have hrank : ∀ r : ℕ, r.Prime → r ∣ Nat.card (zpowers x) →
      CFSG.pRank r (zpowers x) ≤ 2 ∧ CFSG.pRank r (⊤ : Subgroup (BarInf L)) ≤ 3 := by
    intro r hr hrd
    rw [hZx] at hrd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hs).1 hrd
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      refine (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (k := 1) hr fun h => ?_).trans
        (by norm_num)
      rw [hZx] at h
      have := (Nat.pow_dvd_pow_iff_le_right hr.one_lt).1 (by rwa [pow_one] : r ^ (1 + 1) ∣ r ^ 1)
      omega
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← pRank_eq_pRank_barInf hr hsN]
      exact (CFSG.SectionRank.pRank_mono hr.one_lt hL.1.le).trans
        (uc22s2112r34_pRank_le_three hσ hH c hL
          ⟨hr, by rw [← hbs]; exact Subgroup.orderOf_dvd_natCard _ hbB⟩ (by omega))
  have hxC : ∀ K ∈ F14.FunSet (fundPred (p ^ 1)) (BarInf L) (P : Subgroup (BarInf L)),
      x ∈ centralizer (K : Set (BarInf L)) := by
    intro K hK
    have hxK : zpowers x ⊓ K = ⊥ := by
      have hd : Nat.card ↥(zpowers x ⊓ K) ∣ s := by
        rw [← hZx]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hs).1 hd with h1 | h1
      · exact Subgroup.card_eq_one.1 h1
      · exfalso
        have heq : zpowers x ⊓ K = zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hZx])
        have hx' : x ∈ zpowers x ⊓ K := by
          rw [heq]
          exact mem_zpowers x
        obtain ⟨k, hk⟩ := uc22s2112r34_orderOf_eq_three_pow_of_mem_funSet hK (mem_inf.1 hx').2
          hxP (by rw [hxs]; exact hsodd)
        rw [hxs] at hk
        have h3s : 3 ∣ s := by
          cases k with
          | zero =>
            rw [pow_zero] at hk
            omega
          | succ k =>
            rw [hk, pow_succ]
            exact dvd_mul_left 3 _
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).1 h3s
        omega
    have hspl : zpowers x = (zpowers x ⊓ K) ⊔ (zpowers x ⊓ centralizer (K : Set (BarInf L))) := by
      rcases hX with hXs | hXg
      · exact kFunSplit_holds (BarInf L) .PSp 2 p 1 hp hp2 hadmS hXs (by decide) (by decide) P
          (zpowers x) hne inferInstance hodd' h3 hpx hperm hrank K hK
      · exact kFunSplit_holds (BarInf L) .G2 0 p 1 hp hp2 hadmG hXg (by decide) (by decide) P
          (zpowers x) hne inferInstance hodd' h3 hpx hperm hrank K hK
    rw [hxK, bot_sup_eq] at hspl
    exact (mem_inf.1 (hspl.le (mem_zpowers x))).2
  have hx2 : x ^ 2 = 1 := by
    rcases hX with hXs | hXg
    · exact sq_eq_one_of_forall_funSet_psp hp2 hadmS hXs P hxC
    · exact sq_eq_one_of_forall_funSet_g2 hp2 (by rw [pow_one]; omega) hadmG hXg P hxC
  have hdvd := orderOf_dvd_of_pow_eq_one hx2
  rw [hxs] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem uc22s2112r34_false_alpha_exc {G : Type} [Group G] [Finite G]
    (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hBN : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp5 : 5 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .PSp 2 p 1 ∨
      CFSG.Blueprint.LieModel (BarInf L) .G2 0 p 1)
    {e m : ℕ} (hm : Odd m) (hn : c.n = 2 ^ e * m) {s : ℕ} (hs : s.Prime)
    (hsd : s ∣ 2 ^ m - 1) (hsp : s ≠ p) : False := by
  have hs7 : 7 ≤ s := seven_le_of_prime_dvd_two_pow_sub_one hm hs hsd
  have hmn : 2 ^ m - 1 ∣ 2 ^ c.n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 (2 ^ e)
    rwa [one_pow, ← pow_mul, mul_comm m, ← hn] at h
  have hsB : s ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hs, hsd.trans hmn⟩
  obtain ⟨b, hbB, hbs⟩ := uc22p22i_exists_elt_of_mem_piSet hsB
  have hbα : b ∈ oPi {q | q.Prime ∧ q ∣ 2 ^ m - 1} c.B0 :=
    uc22pwtb_mem_oPi c.hB0.2.1 hbB fun q hq hqd => by
      rw [hbs] at hqd
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hs).1 hqd
      exact ⟨hq, hsd⟩
  exact uc22s2112r34_false_of_mem_exc hGA hσ hH c hL hBN hfaith hp hp2 hp5 hX hbB
    (c.hα e m hm hn hbα) hs hs7 hsp hbs

end Alpha

section SwapPSp

open CFSG.Blueprint.Multiplier (genericOrders)


theorem uc22s2112r34_false_exc_psp_swap {G : Type} [Group G] [Finite G]
    (hGA : GriessAllModelsStatement) {D : Data G} (hσ : UC6S846.SigmaStd D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : 7 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .PSp 2 p 1)
    (hno : ∀ f : ℕ, ¬ CFSG.Blueprint.LieModel (BarInf L) .PSL 2 p f) {r : ℕ} (hr : r.Prime)
    (hrB : r ∣ Nat.card c.B0) (hr5 : 5 ≤ r) (hrp : r ≠ p) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hadm : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨hp, le_refl 1, le_refl 2, fun h => hp2 (by simpa using congrArg Prod.snd h)⟩
  have hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunCommute_of_funHypOmega
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunHypOmega_holds
  have hd : ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ (genericOrders .PSp 2 p 1).1 := by
    intro s hs hs2 hdvd
    have hgen : genericOrders .PSp 2 p 1 = (Nat.gcd 2 (p ^ 1 - 1), 1) := rfl
    rw [hgen] at hdvd
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1
      (hdvd.trans (Nat.gcd_dvd_left 2 (p ^ 1 - 1))))
  have hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hp hp2
      (uc22s2112r34_not_dvd_center_char hL hp hp2 (by simp) hX
        (Or.inl ⟨by rw [pow_one]; omega, by simp⟩))
  have hinn : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
    intro b hb
    refine uc22s2112r34_inner_of_odd_f1 hp hp2 hX (Or.inr ⟨rfl, le_refl 2⟩) hd ?_
    have hdvd : orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) ∣ orderOf b := by
      have h := orderOf_map_dvd (inducedBarInfAutHom L)
        (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G)))
      simpa [Subgroup.orderOf_mk] using h
    exact Odd.of_dvd_nat (ch214_odd_card c.hpi)
      (hdvd.trans (Subgroup.orderOf_dvd_natCard c.B0 hb))
  exact uc22s2112r34_false_swap_core kFunSplit_holds kFunCount_holds hFC hσ hH c hL hBN hfaith
    hp hp2 hadm rfl (by simpa using hp7) hX hno (uc22s2112r34_not_ree_of_exc hp hp2 (Or.inl hX))
    hpN hinn
    (uc22s2112r34_not_dvd_radical_of_gO hGA CFSG.TauCetiBridge.typewiseBridges c hL hp
      (by omega) hX hd)
    hr hrB hr5 hrp
    (fun b hb hb1 K₁ K₂ h₁ h₂ hne hc hfix => uc22s2112r34_exc_pair_faithful c hL hp hp2
      (by omega) (Or.inl hX) hBN hfaith hb hb1 h₁ h₂ hne hc hfix)
    (fun P K₁ K₂ h₁ h₂ hne => Or.inl (uc22s2112r34_exists_swap_of_lieModel hp hp2 hadm hX
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) P h₁ h₂ hne))
    (fun K K' hK hK' x hx hxr hx5 hxp => uc22s2112r34_eq_of_mem_inf_psp hp hp2 (le_refl 2) hadm
      hX hK hK' hx.1 hx.2 hxr (by omega) hxp)

end SwapPSp

section PGL

open scoped MatrixGroups


theorem mem_centralizer_of_pow_eq_one_of_mem_normalizer_funSet {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hadm : StatedLieAdmissible t n p 1) (hX : CFSG.Blueprint.LieModel X t n p 1)
    (htwo : FunTwoType t n) (hD4 : t ≠ .trialityD4) (P : Sylow 2 X) {x : X} (hxp : x ^ p = 1)
    (hxP : x ∈ normalizer ((P : Subgroup X) : Set X)) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ 1)) X (P : Subgroup X)) :
    x ∈ centralizer (K : Set X) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hconj : ∀ (g : X) {K' : Subgroup X}, fundPred (p ^ 1) (⊤ : Subgroup X) K' →
      fundPred (p ^ 1) (⊤ : Subgroup X) (K'.map (MulAut.conj g).toMonoidHom) :=
    fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h
  obtain ⟨K₁, K₂, -, hKeq⟩ :=
    Set.ncard_eq_two.1 (ncard_funSet_eq_two_of_funTwoType hp hp2 hadm hX htwo P)
  have hthree : ∀ {A B C : Subgroup X}, A ∈ F14.FunSet (fundPred (p ^ 1)) X (P : Subgroup X) →
      B ∈ F14.FunSet (fundPred (p ^ 1)) X (P : Subgroup X) →
      C ∈ F14.FunSet (fundPred (p ^ 1)) X (P : Subgroup X) → A ≠ B → C = A ∨ C = B := by
    intro A B C hA hB hC hAB
    rw [hKeq] at hA hB hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB hC
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> rcases hC with rfl | rfl <;>
      simp_all
  have hsq : ∀ g ∈ normalizer ((P : Subgroup X) : Set X), g ^ 2 ∈ normalizer (K : Set X) := by
    intro g hg
    have hcomp : ∀ A : Subgroup X, A.map (MulAut.conj (g ^ 2)).toMonoidHom =
        (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      intro A
      rw [Subgroup.map_map]
      congr 1
      ext y
      simp [pow_two, mul_assoc]
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    change K.map (MulAut.conj (g ^ 2)).toMonoidHom = K
    rw [hcomp]
    have hA := F14.mem_funSet_map_conj_of_mem_normalizer hconj hg hK
    by_cases h1 : K.map (MulAut.conj g).toMonoidHom = K
    · rw [h1, h1]
    · have hB := F14.mem_funSet_map_conj_of_mem_normalizer hconj hg hA
      rcases hthree hK hA hB (Ne.symm h1) with h | h
      · exact h
      · exact absurd (Subgroup.map_injective (MulAut.conj g).injective h) h1
  have hxK : x ∈ normalizer (K : Set X) := by
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    have hx : x = (x ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = p + 1 by omega, pow_succ, hxp, one_mul]
    rw [hx]
    exact pow_mem (hsq x hxP) _
  obtain ⟨F, _, _, _, ρ, hρ, hnc⟩ :=
    exists_rho_of_mem_funSet hp5 hadm hX htwo hD4 P (by rwa [pow_one] at hK)
  have hQN : (P : Subgroup X) ⊓ K ≤ normalizer (K : Set X) :=
    inf_le_right.trans Subgroup.le_normalizer
  have h2 : IsPGroup 2 ((((P : Subgroup X) ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ) := by
    have hQ2 : IsPGroup 2 ↥((P : Subgroup X) ⊓ K) := P.isPGroup'.to_le inf_le_left
    exact (hQ2.of_equiv (subgroupOfEquivOfLe hQN).symm).map _
  have hxQ : (⟨x, hxK⟩ : normalizer (K : Set X)) ∈
      normalizer ((((P : Subgroup X) ⊓ K).subgroupOf (normalizer (K : Set X)) :
        Subgroup (normalizer (K : Set X))) : Set (normalizer (K : Set X))) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, mem_inf]
    exact and_congr (mem_normalizer_iff.1 hxP h) (mem_normalizer_iff.1 hxK h)
  have hy : ρ ⟨x, hxK⟩ = 1 := by
    refine CFSG.LinearGroups.eq_one_of_pow_eq_one_of_normalizes_noncyclic_two hp5 h2 hnc ?_
      (Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hxQ))
    have hxp' : (⟨x, hxK⟩ : normalizer (K : Set X)) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [← map_pow, hxp', map_one]
  rw [mem_centralizer_iff]
  intro k hk
  have hk' := (hρ ⟨x, hxK⟩).1 hy k hk
  calc k * x = (x * k * x⁻¹) * x := by rw [hk']
    _ = x * k := by group

theorem eq_one_of_pow_eq_one_of_mem_normalizer_exc {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hX : CFSG.Blueprint.LieModel X .PSp 2 p 1 ∨ CFSG.Blueprint.LieModel X .G2 0 p 1)
    (P : Sylow 2 X) {x : X} (hxp : x ^ p = 1) (hxP : x ∈ normalizer ((P : Subgroup X) : Set X)) :
    x = 1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hadmS : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨hp, le_refl 1, le_refl 2, fun h => hp2 (by simpa using congrArg Prod.snd h)⟩
  have hadmG : StatedLieAdmissible .G2 0 p 1 := ⟨hp, le_refl 1, rfl, by rw [pow_one]; omega⟩
  have hx2 : x ^ 2 = 1 := by
    rcases hX with hXs | hXg
    · exact sq_eq_one_of_forall_funSet_psp hp2 hadmS hXs P fun K hK =>
        mem_centralizer_of_pow_eq_one_of_mem_normalizer_funSet hp5 hadmS hXs rfl (by decide) P
          hxp hxP hK
    · exact sq_eq_one_of_forall_funSet_g2 hp2 (by rw [pow_one]; omega) hadmG hXg P fun K hK =>
        mem_centralizer_of_pow_eq_one_of_mem_normalizer_funSet hp5 hadmG hXg trivial (by decide)
          P hxp hxP hK
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
  rw [hj, pow_succ, pow_mul, hx2, one_pow, one_mul] at hxp
  exact hxp

theorem uc22s2112r34_false_of_mem_exc_p {G : Type} [Group G] [Finite G] {D : Data G}
    {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .PSp 2 p 1 ∨
      CFSG.Blueprint.LieModel (BarInf L) .G2 0 p 1)
    {b : G} (hbB : b ∈ c.B0) (hbT : b ∈ normalizer (D.T : Set G)) (hbp : orderOf b = p) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  have hb : b ∈ normalizer (L : Set G) := hBN hbB
  have hadmG : StatedLieAdmissible .G2 0 p 1 := ⟨hp, le_refl 1, rfl, by rw [pow_one]; omega⟩
  have hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1 := fun h1 => by
    have hb1 := hfaith b hbB (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 hb h1)
    rw [hb1, orderOf_one] at hbp
    omega
  have hθp : orderOf (inducedBarInfAutHom L ⟨b, hb⟩) = p := by
    have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
    rw [Subgroup.orderOf_mk, hbp] at hd
    rcases (Nat.dvd_prime hp).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hθ1
    · exact h1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hinn : inducedBarInfAutHom L ⟨b, hb⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
    rcases hX with hXs | hXg
    · refine uc22s2112r34_inner_of_odd_f1 hp hp2 hXs (Or.inr ⟨rfl, le_refl 2⟩) ?_
        (by rw [hθp]; exact hpodd)
      intro r hr hr2 hdvd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hdvd.trans (Nat.gcd_dvd_left 2 (p ^ 1 - 1))))
    · exact uc22s2112r34_inner_of_squarefree_f1_exc hadmG hXg (Or.inr (Or.inr (Or.inl rfl)))
        (by rw [hθp]; exact hpodd) (by rw [hθp]; exact hp.squarefree)
        (fun h => absurd h (by decide))
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hinn
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  have hxp : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, hx, hθp]
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_barInf hL
  have hxP : x ∈ normalizer ((P : Subgroup (BarInf L)) : Set (BarInf L)) := by
    rw [hP]
    exact uc22s2112r34_mem_normalizer_map hb hbT hx.symm
  have h1 := eq_one_of_pow_eq_one_of_mem_normalizer_exc hp5 hX P
    (by rw [← hxp]; exact pow_orderOf_eq_one x) hxP
  rw [h1, orderOf_one] at hxp
  omega

theorem uc22s2112r34_false_alpha_exc_p {G : Type} [Group G] [Finite G] {D : Data G}
    {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .PSp 2 p 1 ∨
      CFSG.Blueprint.LieModel (BarInf L) .G2 0 p 1)
    {e m : ℕ} (hm : Odd m) (hn : c.n = 2 ^ e * m) (hpd : p ∣ 2 ^ m - 1) : False := by
  have hmn : 2 ^ m - 1 ∣ 2 ^ c.n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 (2 ^ e)
    rwa [one_pow, ← pow_mul, mul_comm m, ← hn] at h
  have hpB : p ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hp, hpd.trans hmn⟩
  obtain ⟨b, hbB, hbp⟩ := uc22p22i_exists_elt_of_mem_piSet hpB
  have hbα : b ∈ oPi {q | q.Prime ∧ q ∣ 2 ^ m - 1} c.B0 :=
    uc22pwtb_mem_oPi c.hB0.2.1 hbB fun q hq hqd => by
      rw [hbp] at hqd
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqd
      exact ⟨hq, hpd⟩
  exact uc22s2112r34_false_of_mem_exc_p c hL hBN hfaith hp hp2 hp5 hX hbB
    (c.hα e m hm hn hbα) hbp

end PGL

section Cases

open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL3EpsOdd17)


theorem uc22s2112r34_false_exc_g2_swap {G : Type} [Group G] [Finite G]
    (hGA : GriessAllModelsStatement) {D : Data G} (hσ : UC6S846.SigmaStd D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : 7 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .G2 0 p 1)
    (hno : ∀ f : ℕ, ¬ CFSG.Blueprint.LieModel (BarInf L) .PSL 2 p f)
    {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card c.B0) (hr5 : 5 ≤ r)
    (hrp : r ≠ p) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hadm : StatedLieAdmissible .G2 0 p 1 := ⟨hp, le_refl 1, rfl, by rw [pow_one]; omega⟩
  have ht2 : FunTwoType .G2 0 := trivial
  have hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunCommute_of_funHypOmega
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunHypOmega_holds
  have hd : ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ (genericOrders .G2 0 p 1).1 := by
    intro s hs _ hdvd
    have h1 : (genericOrders .G2 0 p 1).1 = 1 := rfl
    rw [h1] at hdvd
    exact hs.one_lt.ne' (Nat.dvd_one.1 hdvd)
  have hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hp hp2
      (uc22s2112r34_not_dvd_center_char hL hp hp2 (by simp) hX
        (Or.inl ⟨by rw [pow_one]; omega, by simp⟩))
  have hinn : ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
    intro b hb
    have hdvd : orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) ∣ orderOf b := by
      have h := orderOf_map_dvd (inducedBarInfAutHom L)
        (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G)))
      simpa [Subgroup.orderOf_mk] using h
    exact uc22s2112r34_inner_of_squarefree_f1_exc hadm hX (Or.inr (Or.inr (Or.inl rfl)))
      (Odd.of_dvd_nat (ch214_odd_card c.hpi) (hdvd.trans (Subgroup.orderOf_dvd_natCard c.B0 hb)))
      ((Ctx23L.orderOf_squarefree_of_mem_calB1 c.hB0 hb).squarefree_of_dvd hdvd)
      (fun h => absurd h (by decide))
  have hree := uc22s2112r34_not_ree_of_exc hp hp2 (Or.inr hX)
  have hL3 : ¬ IsL3EpsOdd17 (BarInf L) p := by
    obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht2
    obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1
      (fun h => hA3 ⟨h.1, h.2.1⟩) hRee hpN
    rcases h4 with ⟨hexc', -⟩ | h4
    · exact uc22s2112r34_not_isL3EpsOdd17_of_exc hp hX hexc'
    · exact uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
  obtain ⟨hswap, huniq⟩ := uc22ExcTwoFun_g2 (BarInf L) p hp hp7 hX
  exact uc22s2112r34_false_swap_core kFunSplit_holds kFunCount_holds hFC hσ hH c hL hBN hfaith
    hp hp2 hadm ht2 (by simpa using hp7) hX hno hree hpN hinn
    (uc22s2112r34_not_dvd_radical_of_gO hGA CFSG.TauCetiBridge.typewiseBridges c hL hp
      (by omega) hX hd)
    hr hrB hr5 hrp
    (fun b hb hb1 K₁ K₂ h₁ h₂ hne hc hfix => uc22s2112r34_exc_pair_faithful c hL hp hp2
      (by omega) (Or.inr hX) hBN hfaith hb hb1 h₁ h₂ hne hc hfix)
    (fun P K₁ K₂ h₁ h₂ hne => (hswap P K₁ K₂ (by simpa using h₁) (by simpa using h₂) hne
      (uc22s2112r34_funSet_commute_barInf hFC hL hp hp2 hX hno hL3 hree
        (by rw [pow_one]; omega) P h₁ h₂ hne)).imp_right fun h => ⟨h, Or.inl (by omega)⟩)
    (fun K K' hK hK' => huniq K K' (by simpa using hK) (by simpa using hK'))

theorem uc22s2112r34_false_exc {G : Type} [Group G] [Finite G]
    (hGA : GriessAllModelsStatement) {D : Data G} (hσ : UC6S846.SigmaStd D) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : 7 ≤ p)
    (hX : CFSG.Blueprint.LieModel (BarInf L) .PSp 2 p 1 ∨
      CFSG.Blueprint.LieModel (BarInf L) .G2 0 p 1)
    (hno : ∀ f : ℕ, ¬ CFSG.Blueprint.LieModel (BarInf L) .PSL 2 p f) : False := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : c.n ≠ 0)
  by_cases hm1 : m = 1
  · rw [hm1, mul_one] at hn
    have he : 2 ≤ e := by
      by_contra he
      interval_cases e <;> simp at hn <;> omega
    obtain ⟨k, hk⟩ : 4 ∣ c.n := by
      rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 he
    have h5 : 5 ∣ 2 ^ c.n - 1 := by
      have h := Nat.sub_dvd_pow_sub_pow (2 ^ 4) 1 k
      rw [one_pow, ← pow_mul, ← hk] at h
      exact (by norm_num : 5 ∣ 2 ^ 4 - 1).trans h
    have h5B : 5 ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨by norm_num, h5⟩
    rcases hX with hXs | hXg
    · exact uc22s2112r34_false_exc_psp_swap hGA hσ hH c hL hBN hfaith hp hp2 hp7 hXs hno
        h5B.1 h5B.2 le_rfl (by omega)
    · exact uc22s2112r34_false_exc_g2_swap hGA hσ hH c hL hBN hfaith hp hp2 hp7 hXg hno
        h5B.1 h5B.2 le_rfl (by omega)
  · have hm3 : 3 ≤ m := by
      obtain ⟨j, rfl⟩ := hm
      omega
    have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    obtain ⟨s, hs, hsd⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
    by_cases hsp : s = p
    · rw [hsp] at hsd
      exact uc22s2112r34_false_alpha_exc_p c hL hBN hfaith hp hp2 (by omega) hX hm hn hsd
    · exact uc22s2112r34_false_alpha_exc hGA hσ hH c hL hBN hfaith hp hp2 (by omega) hX hm hn hs
        hsd hsp

end Cases

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
