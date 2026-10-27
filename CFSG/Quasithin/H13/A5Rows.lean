module

public import CFSG.Quasithin.H13.A5Facts1321
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.Background.B5Models
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate17002
public import Certificates.Certificate17028
public import Certificates.Certificate17951
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import Certificates.Certificate19953
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Fischer.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.InternalSecRealB
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def RowType (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* ↥(alternatingGroup (Fin 6))) ∨
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨ Nonempty (X ≃* U33G)

section Identify

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_commutator_of_simple {G L J : Subgroup (MulAut V)} (hB4 : B4Hyp G L) (hLJ : L ≤ J)
    (hJG : J ≤ G) (hs : IsSimpleGroup ↥⁅J, J⁆) : L = ⁅J, J⁆ := by
  have hq : CFSG.IsQuasisimple ↥L := hB4.2.2.1
  have hperf : Group.IsPerfect ↥L := hq.1
  have hLJJ : L ≤ ⁅J, J⁆ := by
    calc L = ⁅L, L⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅J, J⁆ := Subgroup.commutator_mono hLJ hLJ
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB4.2.1 ▸ le_normalizer_quasithinGenFitting G
  have hnorm : (L.subgroupOf ⁅J, J⁆).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hGL (hJG (B5.commutator_le_self _ g.2))) _).mp hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf ⁅J, J⁆) with hbot | htop
  · exfalso
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
    apply hx
    have hxm : (⟨x, hLJJ x.2⟩ : ↥⁅J, J⁆) ∈ L.subgroupOf ⁅J, J⁆ := x.2
    rw [hbot, Subgroup.mem_bot] at hxm
    have h3 : (x : MulAut V) = 1 := congrArg (fun z : ↥⁅J, J⁆ => (z : MulAut V)) hxm
    exact Subtype.ext h3
  · exact le_antisymm hLJJ (Subgroup.subgroupOf_eq_top.1 htop)

theorem eq_commutator_ffJ (hV : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hB4 : B4Hyp G L) (hs : IsSimpleGroup ↥⁅ffJ G, ffJ G⁆)
    (h2 : 2 ∣ Nat.card ↥⁅ffJ G, ffJ G⁆) : L = ⁅ffJ G, ffJ G⁆ := by
  have h2' : 2 ∣ Nat.card ↥(ffJ G) :=
    h2.trans (Subgroup.card_dvd_of_le (B5.commutator_le_self _))
  exact eq_commutator_of_simple hB4 (Vol2.Ch10.SecA.le_ffJ_of_two_dvd hV hB4 h2') (B6.ffJ_le G) hs

theorem rowType_of_rows
    (hV : ∀ w : V, w ^ 2 = 1) {G L A : Subgroup (MulAut V)}
    (hB4 : B4Hyp G L) (hrow : Rows1321Remaining G L A) : RowType ↥L := by
  rcases hrow with h6 | hSp | h9 | h10 | hG2 | hG2'
  ·
    obtain ⟨-, ⟨π, hπ⟩, -⟩ := h6
    exact Or.inl (nonempty_mulEquiv_of_realizesVia (altDn_faithful_of_five_le (by norm_num)) hπ)
  ·
    obtain ⟨π, hπ⟩ := asSp4S6 _ _ _ _ hSp
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (G64.symDn_faithful (by norm_num)) hπ
    obtain ⟨f⟩ := nonempty_commutator_equiv_alternating (by norm_num) e
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have h2 : 2 ∣ Nat.card ↥⁅ffJ G, ffJ G⁆ := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have hL := eq_commutator_ffJ hV hB4 f.isSimpleGroup h2
    exact Or.inl ⟨(MulEquiv.subgroupCongr hL).trans f⟩
  ·
    obtain ⟨-, n, hn, hnat, -⟩ := h9
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hnat
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl ⟨e.symm.trans (statedSLEquivZModTwo hK2)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans (statedSLEquivZModTwo hK2)⟩))
  ·
    obtain ⟨⟨π, hπ⟩, -⟩ := h10
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (G64.extSq_faithful (by norm_num)) hπ
    exact Or.inr (Or.inl ⟨e.trans (statedSLEquivZModTwo (K := ZMod 2) (by simp))⟩)
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (zornQ_faithful le_rfl) hπ
    obtain ⟨f⟩ := nonempty_commutator_equiv e
    have : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ := isSimpleGroup_g2Two_commutator hK2
    obtain ⟨g⟩ := nonempty_g2Two_commutator_equiv hK2
    have h2 : 2 ∣ Nat.card ↥⁅ffJ G, ffJ G⁆ := by
      rw [Nat.card_congr ((f.trans g).trans u33EquivSubG2.symm).toEquiv, card_u33Pres]
      decide
    have hL := eq_commutator_ffJ hV hB4 f.isSimpleGroup h2
    exact Or.inr (Or.inr (Or.inr
      ⟨(MulEquiv.subgroupCongr hL).trans ((f.trans g).trans u33EquivSubG2.symm)⟩))
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := hG2'
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (zornQ_faithful (B5.commutator_le_self _)) hπ
    obtain ⟨g⟩ := nonempty_g2Two_commutator_equiv hK2
    exact Or.inr (Or.inr (Or.inr ⟨(e.trans g).trans u33EquivSubG2.symm⟩))

end Identify

theorem RowType.isSimpleGroup
    {X : Type} [Group X] (h : RowType X) : IsSimpleGroup X := by
  rcases h with h | h | h | h <;> obtain ⟨e⟩ := h
  · have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact e.isSimpleGroup
  · have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      isSimpleGroup_sl_zmodTwo (by norm_num)
    exact e.isSimpleGroup
  · have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      isSimpleGroup_sl_zmodTwo (by norm_num)
    exact e.isSimpleGroup
  · have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
    exact e.isSimpleGroup

theorem two_le_pRank_three {X : Type*} [Group X] [Finite X] {x y : X} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hy2 : y ≠ x)
    (hy3 : y ≠ x ^ 2) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine A3Facts.two_le_pRank_of_gens hx hy hxy hx1 fun n hn => ?_
  have hmod : x ^ n = x ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]
  rw [hmod] at hn
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · rw [h, pow_zero] at hn
    exact hy1 hn.symm
  · rw [h, pow_one] at hn
    exact hy2 hn.symm
  · rw [h] at hn
    exact hy3 hn.symm

@[expose] def a6x : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a6y : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem two_le_pRank_alt6 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin 6))) :=
  two_le_pRank_three (x := a6x) (y := a6y) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

@[expose] def gl4x : GL (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel, by decide +kernel⟩

@[expose] def gl4y : GL (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0], by decide +kernel, by decide +kernel⟩

theorem two_le_pRank_gl4 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (GL (Fin 4) (ZMod 2))) := by
  refine two_le_pRank_three (x := gl4x) (y := gl4y) (Units.ext ?_) (Units.ext ?_) (Units.ext ?_)
    (ne_of_apply_ne Units.val ?_) (ne_of_apply_ne Units.val ?_) (ne_of_apply_ne Units.val ?_)
    (ne_of_apply_ne Units.val ?_) <;> decide +kernel

@[expose] def gl5x : GL (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel, by decide +kernel⟩

@[expose] def gl5y : GL (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    by decide +kernel, by decide +kernel⟩

theorem two_le_pRank_gl5 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (GL (Fin 5) (ZMod 2))) := by
  refine two_le_pRank_three (x := gl5x) (y := gl5y) (Units.ext ?_) (Units.ext ?_) (Units.ext ?_)
    (ne_of_apply_ne Units.val ?_) (ne_of_apply_ne Units.val ?_) (ne_of_apply_ne Units.val ?_)
    (ne_of_apply_ne Units.val ?_) <;> decide +kernel

@[expose] def e9Word : List (Fin 2) := [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]

theorem e9Word_mats :
    matA2 ^ 3 = 1 ∧ wordEvalM ![matA2, matB2] e9Word ^ 3 = 1 ∧
      matA2 * wordEvalM ![matA2, matB2] e9Word = wordEvalM ![matA2, matB2] e9Word * matA2 ∧
      matA2 ≠ 1 ∧ wordEvalM ![matA2, matB2] e9Word ≠ 1 ∧
      wordEvalM ![matA2, matB2] e9Word ≠ matA2 ∧ wordEvalM ![matA2, matB2] e9Word ≠ matA2 ^ 2 := by
  decide +kernel

theorem two_le_pRank_subG2
    : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥subG2) := by
  have hle : subG2 ≤ cayleyGroup (ZMod 2) := (Subgroup.closure_le _).mpr (by
    rintro _ (rfl | rfl)
    · exact g2a.2
    · exact g2b.2)
  have : Finite U33G := u33Pres_finite_card_le.1
  have : Finite ↥subG2 := Finite.of_equiv _ u33EquivSubG2.toEquiv
  let S : Subgroup ↥(cayleyGroup (ZMod 2)) := subG2.subgroupOf (cayleyGroup (ZMod 2))
  let eS : ↥S ≃* ↥subG2 := Subgroup.subgroupOfEquivOfLe hle
  have : Finite ↥S := Finite.of_equiv _ eS.symm.toEquiv
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eS]
  have hxm : g2a ∈ S := Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨c, hcm, hym⟩ : ∃ c : ↥(cayleyGroup (ZMod 2)),
      cmat c = wordEvalM ![matA2, matB2] e9Word ∧ c ∈ S := by
    refine ⟨wordEval ![g2a, g2b] e9Word, cmat_wordEval _ _ cmat_ab e9Word, ?_⟩
    rw [Subgroup.mem_subgroupOf, coe_wordEval_sub]
    refine wordEval_mem_of_forall_mem _ _ (fun i => ?_) e9Word
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := e9Word_mats
  have hx3 : g2a ^ 3 = 1 := cmat_injective (by rw [map_pow, cmat_g2a, map_one, h1])
  have hc3 : c ^ 3 = 1 := cmat_injective (by rw [map_pow, hcm, map_one, h2])
  have hxc : g2a * c = c * g2a := cmat_injective (by rw [map_mul, map_mul, cmat_g2a, hcm, h3])
  have hx1 : g2a ≠ 1 := fun h => h4 (by rw [← cmat_g2a, h, map_one])
  have hc1 : c ≠ 1 := fun h => h5 (by rw [← hcm, h, map_one])
  have hcx : c ≠ g2a := fun h => h6 (by rw [← hcm, h, cmat_g2a])
  have hcx2 : c ≠ g2a ^ 2 := fun h => h7 (by rw [← hcm, h, map_pow, cmat_g2a])
  refine two_le_pRank_three (x := (⟨g2a, hxm⟩ : ↥S)) (y := ⟨c, hym⟩) (Subtype.ext ?_)
    (Subtype.ext ?_) (Subtype.ext hxc) ?_ ?_ ?_ ?_
  · rw [SubgroupClass.coe_pow]
    exact hx3
  · rw [SubgroupClass.coe_pow]
    exact hc3
  · intro h
    exact hx1 (congrArg Subtype.val h)
  · intro h
    exact hc1 (congrArg Subtype.val h)
  · intro h
    exact hcx (congrArg Subtype.val h)
  · intro h
    apply hcx2
    have h' := congrArg Subtype.val h
    rwa [SubgroupClass.coe_pow] at h'

theorem RowType.two_le_pRank
    {X : Type} [Group X] [Finite X] (h : RowType X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases h with h | h | h | h <;> obtain ⟨e⟩ := h
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact two_le_pRank_alt6
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4))]
    exact two_le_pRank_gl4
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 5))]
    exact two_le_pRank_gl5
  · have : Finite ↥subG2 := Finite.of_equiv _ (e.trans u33EquivSubG2).toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e.trans u33EquivSubG2)]
    exact two_le_pRank_subG2

theorem factRankRows1321
    : FactRankRows1321 := by
  intro V _ _ hV G L A hB4 hrow
  have h := rowType_of_rows hV hB4 hrow
  refine ⟨h.isSimpleGroup, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  exact h.two_le_pRank

end CFSG.Quasithin.H13.A5
