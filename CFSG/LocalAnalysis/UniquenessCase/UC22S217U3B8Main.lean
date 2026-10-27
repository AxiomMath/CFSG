module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3BMain
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B8
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U38
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U38Mat
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter
import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl3
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3
import CFSG.LocalAnalysis.UniquenessCase.UCKP898D
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts
import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

local notation "Z₉" => Multiplicative (ZMod 9)

private noncomputable def uc22s217u3b8_zhom {S : Type*} [Group S] (x : S) (hx : x ^ 9 = 1) :
    Z₉ →* S :=
  MonoidHom.mk' (fun k => x ^ (Multiplicative.toAdd k).val) (fun a b => by
    have key : ∀ n : ℕ, x ^ (n % 9) = x ^ n := fun n => by
      conv_rhs => rw [← Nat.div_add_mod n 9, pow_add, pow_mul, hx, one_pow, one_mul]
    simp only [toAdd_mul]
    rw [ZMod.val_add, key, pow_add])

private theorem uc22s217u3b8_zhom_apply {S : Type*} [Group S] (x : S) (hx : x ^ 9 = 1) (k : Z₉) :
    uc22s217u3b8_zhom x hx k = x ^ (Multiplicative.toAdd k).val :=
  rfl

theorem uc22s217u3b8_exists_elemAbelian_of_commute {P : Type*} [Group P] [Finite P]
    {C₀ C₁ H : Subgroup P} (hcomm : ∀ a ∈ C₀, ∀ b ∈ C₁, a * b = b * a) {v₀ v₁ : P}
    (hv₀ : v₀ ∈ C₀) (hv₁ : v₁ ∈ C₁) (hv₀H : v₀ ∈ H) (hv₁H : v₁ ∈ H) (h9₀ : v₀ ^ 9 = 1)
    (h9₁ : v₁ ^ 9 = 1) (hZ₀ : ∀ k : ℕ, v₀ ^ k ∈ C₁ → 3 ∣ k)
    (hZ₁ : ∀ k : ℕ, v₁ ^ k ∈ C₀ → 3 ∣ k) :
    ∃ E : Subgroup P, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  classical
  let w₀ : ↥H := ⟨v₀, hv₀H⟩
  let w₁ : ↥H := ⟨v₁, hv₁H⟩
  have hw₀ : w₀ ^ 9 = 1 := Subtype.ext (by simpa [w₀] using h9₀)
  have hw₁ : w₁ ^ 9 = 1 := Subtype.ext (by simpa [w₁] using h9₁)
  have hw : Commute w₀ w₁ := Subtype.ext (hcomm _ hv₀ _ hv₁)
  let Φ : Z₉ × Z₉ →* ↥H :=
    (uc22s217u3b8_zhom w₀ hw₀).noncommCoprod (uc22s217u3b8_zhom w₁ hw₁) (fun a b => by
      rw [uc22s217u3b8_zhom_apply, uc22s217u3b8_zhom_apply]
      exact hw.pow_pow _ _)
  have hker : Φ.ker ≤ (powMonoidHom 3 : Z₉ × Z₉ →* Z₉ × Z₉).range := by
    rintro ⟨a, b⟩ hab
    have h1 : v₀ ^ (Multiplicative.toAdd a).val * v₁ ^ (Multiplicative.toAdd b).val = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hab)
    have ha := hZ₀ _ (by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact C₁.inv_mem (C₁.pow_mem hv₁ _))
    have hb := hZ₁ _ (by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact C₀.inv_mem (C₀.pow_mem hv₀ _))
    obtain ⟨a', ha'⟩ := uc22s217u38_mem_range_pow a ha
    obtain ⟨b', hb'⟩ := uc22s217u38_mem_range_pow b hb
    refine ⟨(a', b'), ?_⟩
    rw [powMonoidHom_apply] at ha' hb' ⊢
    rw [Prod.pow_mk, ha', hb']
  obtain ⟨E, hEel, hEc⟩ := uc22s217u38_exists_elemAbelian Φ hker
  refine ⟨E.map H.subtype, Subgroup.map_subtype_le E, hEel.map _, ?_⟩
  rw [Subgroup.card_map_of_injective H.subtype_injective, hEc, uc22s217u38_card_ker_pow_prod,
    uc22s217u38_card_ker_pow_z9, sq]

variable {G : Type} [Group G] [Finite G]

theorem uc22s217u3b8_lift_pow {K : Subgroup G} {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) {y : G} (hyN : y ∈ normalizer (K : Set G)) (hyr : orderOf y = r)
    {u : Bar2 K} {e : ℕ} (hue : u ^ (q ^ e) = 1) (hu : rhoL K ⟨y, hyN⟩ u = u) :
    ∃ a : G, ∃ haK : a ∈ K, a ∈ centralizer (zpowers y : Set G) ∧ a ^ (q ^ e) = 1 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨a, haK⟩ = u := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hq).1 (orderOf_dvd_of_pow_eq_one hue)
  have huc : Nat.card (zpowers u) = q ^ m := by rw [Nat.card_zpowers, hm]
  obtain ⟨A, hAK, hAc, hAmap, hAcard, -⟩ := uc22s217u3b_lift hr hr2 hq hq2 hyN hyr (zpowers u)
    (IsPGroup.of_card huc) (fun e he => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      rw [map_zpow, hu])
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hAp : IsPGroup q (A.subgroupOf K) :=
    (IsPGroup.of_card (hAcard.trans huc) : IsPGroup q A).comap_subtype
  have hdisj : Disjoint (A.subgroupOf K) π.ker := Subgroup.disjoint_def.2 fun hx hk =>
    eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hAp hker hx hk
  have hcard : Nat.card ((A.subgroupOf K).map π) = Nat.card (zpowers u) := by
    rw [card_map_of_disjoint_ker π _ hdisj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hAcard]
  have heq : (A.subgroupOf K).map π = zpowers u := Subgroup.eq_of_le_of_card_ge hAmap hcard.ge
  obtain ⟨a, haA, hau⟩ : u ∈ (A.subgroupOf K).map π := by
    rw [heq]
    exact Subgroup.mem_zpowers u
  refine ⟨a, a.2, hAc haA, ?_, hau⟩
  rw [← orderOf_dvd_iff_pow_eq_one]
  refine (Subgroup.orderOf_dvd_natCard A haA).trans ?_
  rw [hAcard, Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one hue

theorem uc22s217u3b8_rank_three
    (hCen : UCK.U3Center) (hFF : UCK.U3FixField)
    {M : Subgroup G} :
    ∀ K₀ K₁ : Subgroup G, K₀ ∈ calC M → K₁ ∈ calC M → K₀ ≠ K₁ →
      IsSU3 (Bar2 K₀) 3 → IsSU3 (Bar2 K₁) 3 → ∀ y ∈ M, orderOf y = 7 →
      y ∈ normalizer (K₀ : Set G) → y ∈ normalizer (K₁ : Set G) →
      ∃ W : Subgroup G, W ≤ M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian 3 W ∧
        Nat.card W = 3 ^ 2 := by
  intro K₀ K₁ hK₀ hK₁ hne hX₀ hX₁ y hyM hyr hy₀ hy₁
  have hr : Nat.Prime 7 := by norm_num
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hv : ∀ {K : Subgroup G}, K ∈ calC M → IsSU3 (Bar2 K) 3 → y ∈ normalizer (K : Set G) →
      ∃ v : Bar2 M, v ∈ barImage M K ∧ v ∈ centralizer ({π ⟨y, hyM⟩} : Set (Bar2 M)) ∧
        v ^ 9 = 1 ∧ ∀ k : ℕ, (∀ b ∈ barImage M K, b * v ^ k = v ^ k * b) → 3 ∣ k := by
    intro K hK hX hyK
    obtain ⟨hαr, hα⟩ := uc22s217u3b_inner hFF hX ⟨1, rfl⟩ dvd_rfl hr (by norm_num) (by norm_num)
      hyK hyr
    obtain ⟨u, hu, hu9, huZ⟩ := uc22s217u3b8_exists_fix hX (hCen _ 3 hX) hαr hα
    obtain ⟨a, haK, hac, ha9, hau⟩ := uc22s217u3b8_lift_pow (e := 2) hr (by norm_num)
      Nat.prime_three (by norm_num) hyK hyr (by simpa using hu9) hu
    obtain ⟨e, he⟩ := uc22p22l_barImage_equiv hK
    have haM : a ∈ M := hK.1.le haK
    refine ⟨π ⟨a, haM⟩, ⟨⟨a, haM⟩, haK, rfl⟩, ?_, ?_, fun k hk => huZ k ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hac y (Subgroup.mem_zpowers y))
    · have h1 : (⟨a, haM⟩ : ↥M) ^ 9 = 1 := Subtype.ext (by simpa using ha9)
      rw [← map_pow, h1, map_one]
    · have h1 : ((e (u ^ k) : ↥(barImage M K)) : Bar2 M) = π ⟨a, haM⟩ ^ k := by
        rw [← hau, ← map_pow (QuotientGroup.mk' (CFSG.pCore 2 ↥K)), QuotientGroup.mk'_apply, he,
          map_pow, QuotientGroup.mk_pow]
        rfl
      rw [← e.symm_apply_apply (u ^ k)]
      refine (uc22p22l_mem_center_equiv e _).2 ?_
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h1]
      exact hk b b.2
  obtain ⟨v₀, hv₀K, hv₀c, hv₀9, hv₀Z⟩ := hv hK₀ hX₀ hy₀
  obtain ⟨v₁, hv₁K, hv₁c, hv₁9, hv₁Z⟩ := hv hK₁ hX₁ hy₁
  have hcomm := uc22p22l_barImage_commute hK₀ hK₁ hne
  obtain ⟨E, hEH, hEel, hEc⟩ := uc22s217u3b8_exists_elemAbelian_of_commute hcomm hv₀K hv₁K hv₀c
    hv₁c hv₀9 hv₁9 (fun k hk => hv₀Z k fun b hb => hcomm b hb _ hk)
    (fun k hk => hv₁Z k fun b hb => (hcomm _ hk b hb).symm)
  exact uc22s217u3b_exists_lift_cent hr (by norm_num) Nat.prime_three (by norm_num) hyM hyr hEel
    hEc fun w hw => Subgroup.mem_centralizer_iff.1 (hEH hw) _ (Set.mem_singleton _)

theorem uc22s217u3b_not_isSU3_three
    (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) (hSg : SigmaStd D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hCen : UCK.U3Center)
    (hFF : UCK.U3FixField) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnN : ¬ (L.subgroupOf D.M).Normal) : ¬ IsSU3 (Bar2 L) 3 := by
  intro hX
  obtain ⟨h3σ, hsp⟩ := uc22s217u38_three_mem_sig hSg hL hnN hX
  exact uc22s217u3b_false_of D Ch h211 hH c hSg hCen hFF hL hnN hX (s := 3) (r := 7) ⟨1, rfl⟩
    dvd_rfl (by norm_num) (by norm_num) (by norm_num) Nat.prime_three (by norm_num) hsp
    (h76 3 h3σ hsp) (fun X _ _ hK α hα7 hα => uc22s217u3b8_fix_three hCen hK hα7 hα)
    (uc22s217u3b8_rank_three hCen hFF)

theorem uc22s217u3b_not_isSU3_of_not_isPowTwo
    (D : Data G) (Ch : Choice2011 G)
    (h211 : S21_1 D Ch) (hH : H1930 D) (c : Ctx21 D Ch) (hSg : SigmaStd D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hCen : UCK.U3Center)
    (hSyl : UCK.U3Syl) (hFI : UCK.U3FixInner) (hFF : UCK.U3FixField) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) {n : ℕ} (hn : ¬ IsPowTwo n) :
    ¬ IsSU3 (Bar2 L) n := by
  rcases eq_or_ne n 3 with rfl | hn3
  · exact uc22s217u3b_not_isSU3_three D Ch h211 hH c hSg h76 hCen hFF hL hnN
  · exact uc22s217u3b_not_isSU3 D Ch h211 hH c hSg h76 hCen hSyl hFI hFF hL hnN hn hn3

theorem uc22s217u3b_not_isSU3_of_griess
    (hG : CFSG.Open.GriessAllModelsStatement) (D : Data G) (Ch : Choice2011 G)
    (h211 : S21_1 D Ch) (hH : H1930 D) (c : Ctx21 D Ch) (hSg : SigmaStd D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) {n : ℕ} (hn : ¬ IsPowTwo n) :
    ¬ IsSU3 (Bar2 L) n :=
  uc22s217u3b_not_isSU3_of_not_isPowTwo D Ch h211 hH c hSg h76 (UCK.u3Center_of_griess hG)
    (UCK.u3Syl_of_griess hG) (UCK.u3FixInner_of_griess hG) (UCK.u3FixField_holds hG) hL hnN hn

end CFSG.LocalAnalysis.UniquenessCase.UC22
