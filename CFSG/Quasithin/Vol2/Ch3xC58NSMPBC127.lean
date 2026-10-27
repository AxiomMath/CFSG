module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourJNative
public import CFSG.Quasithin.Vol2.Ch3xC58NSMPBAlt5

public section

namespace CFSG.QuasithinUnique.L246C127.MPB

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isBlock2_of_chi0Block (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat)
    (hodd : AltEvenExcluded) (h123 : L238.C123TwoCgsStatement (G := G))
    (hB42 : L238.AltBlockStatementJCat (G := G)) (hA7 : L238.C129A7StatementCat (G := G))
    {X T P K M : Subgroup G} (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hSQ : IsSQTKCat ↥X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hP : P ∈ uFamHat X T) (hK : IsChi0Block P K)
    (hKJ : ⁅K, thompsonJ T⁆ = K) (hPK : P = T ⊔ conjClosure K T) (hcgs : cgsIn X T ≤ M)
    (hMX : M ≤ X) (hKM : ¬ K ≤ M) : IsBlock2 X K := by
  have S : Setting X T P K := ⟨hX, hT, hP.1.1, hP.1.2.1.le, hK.1⟩
  have hPcgs : ¬ P ≤ cgsIn X T := fun h => hKM ((S.KP.trans h).trans hcgs)
  have hKZ := S.not_le_centralizer_omega hPK hPcgs
  have hUV := S.blockU_le_VZ hKZ
  have hV : IsElemAbelian 2 (VZ T X) := S.hred.2.2.1
  have hne := Setting.commutator_VZ_ne_bot (X := X) hKZ
  have hB := S.b113_concl h113 hSQ hV hUV hKJ hne
  have hq0 := S.isQuasisimple_or_card_three_autI hV hUV
  have hKaX : autI hV K ≤ autI hV X := autI_mono hV (S.KP.trans S.PX)
  have hself : IsSubnormal (autI hV K) (autI hV X) → IsBlock2 X K := by
    intro hsub
    obtain ⟨L, hL, -, -, -, -, -, hLK⟩ := S.exists_block_lift hV hUV hKaX hsub le_rfl hq0
      (fun N hN _ hKN => le_antisymm hN hKN)
    exact hLK rfl ▸ hL
  rcases hB with ⟨-, hF⟩ | hcomp | ⟨Lstar, hLcomp, hKL, m, ⟨eL⟩, hrest⟩
  · exact hself (isSubnormal_of_le_center_fitting hF)
  · exact hself hcomp.2.1
  obtain ⟨hLle, hLsub, hLqs⟩ := hLcomp
  have hqL : CFSG.IsQuasisimple ↥Lstar := B1Red.isQuasisimple_of_open hLqs
  have hm5 : 5 ≤ m := alt_five_le_of_quasisimple eL hqL
  have hsimpL : IsSimpleGroup ↥Lstar :=
    (MulEquiv.isSimpleGroup_congr eL).2 (Bridge.alt_isSimple hm5)
  have hKnt : Nontrivial ↥(autI hV K) := nontrivial_of_quasisimple_or_card_three hq0
  have hnc : ∀ N : Subgroup (MulAut (IntMod (VZ T X) hV)), N ≤ Lstar →
      (N.subgroupOf Lstar).Normal → autI hV K ≤ N → N = Lstar := by
    intro N hNL hNn hKN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Lstar) with h | h
    · exfalso
      have hN0 : N = ⊥ := disjoint_self.1 ((Subgroup.subgroupOf_eq_bot.1 h).mono_right hNL)
      rw [hN0] at hKN
      exact (Subgroup.nontrivial_iff_ne_bot _).1 hKnt (le_bot_iff.1 hKN)
    · exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.1 h)
  obtain ⟨L, hL, hKL', -, hULV, hautL, -, hLK⟩ :=
    S.exists_block_lift hV hUV hLle hLsub hKL (Or.inl hqL) hnc
  by_cases hKe : autI hV K = Lstar
  · exact hLK hKe ▸ hL
  exfalso
  have hLN : L ≤ Subgroup.normalizer (VZ T X : Set G) := hL.2.1.trans S.hXV
  have eL' : ↥(autI hV L) ≃* alternatingGroup (Fin m) := (MulEquiv.subgroupCongr hautL).trans eL
  have hLalt := isAltQuotient_of_equiv hV hLN eL'
  rcases hrest with ⟨n, -, ⟨eK⟩⟩ | ⟨⟨eK3⟩, -⟩
  swap
  · exact (S.isEmpty_equiv_sl3 hV hUV hK.2).false eK3
  have hn : n = 3 ∨ n = 5 := S.degree_eq_three_or_five hV hUV hK.2 eK
  have hm8 : m ≤ 8 := by
    by_contra hm9
    push Not at hm9
    obtain ⟨α, hαs, hαk⟩ := L246.exists_alt_pCore S.charTwo S.sylow hL hULV hLalt
    have h3L := L246.three_le_pRank_of_alt (by omega) α hαs hαk
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h4 : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 X :=
      CFSG.SectionRank.pRank_mono (by norm_num) hL.2.1
    have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
      pRank_top_subtype (p := 3) X
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 :=
      isStronglyQuasithin_iff.mp hSQ.1 3 Nat.prime_three (by norm_num)
    omega
  have hsyl : IsSylowTwoOf (autI hV T ⊓ Lstar) Lstar :=
    isSylowTwoOf_inf_of_isSubnormal' hLsub (B2F.isSylowTwoOf_autI hV S.hXV S.sylow)
  have hsubK : IsSubnormal (autI hV K) (autI hV K ⊔ (autI hV T ⊓ Lstar)) :=
    A3.subnormal_of_le_of_le (S.isSubnormal_autI_sup hV) le_sup_left
      (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  have hmodd : Odd m := by
    rcases Nat.even_or_odd m with he | ho
    · exfalso
      have h68 : m = 6 ∨ m = 8 := by
        obtain ⟨r, hr⟩ := he
        omega
      exact hodd _ Lstar (autI hV K) (autI hV T ⊓ Lstar) m n h68 hn ⟨eL⟩ hKL ⟨eK⟩ hsyl hsubK
    · exact ho
  have hm57 : m = 5 ∨ m = 7 := by
    obtain ⟨r, hr⟩ := hmodd
    omega
  rcases hm57 with rfl | rfl
  ·
    rcases hn with rfl | rfl
    · exact C58NS.MPB.alt5_three_excluded eL hKL eK hsyl hsubK
    · exact hKe (Subgroup.eq_of_le_of_card_ge hKL
        ((Nat.card_congr eL.toEquiv).trans (Nat.card_congr eK.toEquiv).symm).le)
  have hm : Odd 7 := ⟨3, rfl⟩
  have hJT : thompsonJ T ≤ T := (C1GN.thompsonJ_le_baum T).trans (C1GN.baum_le T)
  have hJN : thompsonJ T ≤ Subgroup.normalizer (L : Set G) :=
    L238.le_normalizer_of_isAltQuotient hX h38 hT hL hULV hm (by norm_num) hLalt hKL'
      (L238.not_isPGroup_two_of_isShort2 hK.1.1) hJT (hKJ.le.trans hKL')
  have hnotKC : ¬ K ≤ Subgroup.centralizer (VZ T X : Set G) :=
    C1GN.not_le_of_isAltQuotient (isAltQuotient_of_equiv hV S.hKN eK)
      (by rcases hn with rfl | rfl <;> norm_num)
  have hKLJ : K ≤ ⁅L, thompsonJ T⁆ :=
    calc K = ⁅K, thompsonJ T⁆ := hKJ.symm
      _ ≤ ⁅L, thompsonJ T⁆ := Subgroup.commutator_mono hKL' le_rfl
  have hnotLJ : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) := fun h =>
    hnotKC (hKLJ.trans h)
  have hLM : ¬ L ≤ M := fun h => hKM (hKL'.trans h)
  rcases hB42 X T L hX hSQ hT hL hULV hJN hnotLJ ⟨7, hm, by norm_num, hLalt⟩ with hchi | hexc
  · have hNL : ⁅L, thompsonJ T⁆ ≤ L := C1GN.commutator_le_of_le_normalizer hJN
    have hLN' : L ≤ Subgroup.normalizer ((⁅L, thompsonJ T⁆ : Subgroup G) : Set G) :=
      A3.le_normalizer_commutator_left L (thompsonJ T)
    have hEq : ⁅L, thompsonJ T⁆ = L :=
      C1GN.isShort2_eq_of_isAltQuotient hL.1 hm (by norm_num) hLalt hNL hLN' hnotLJ
    have hchi0 : IsChi0Block X L :=
      L238.isChi0Block_of_isChiBlock_cat hA7 hX hSQ hT hcgs hMX hchi hEq hLM
    have S' : Setting X T X L := ⟨hX, hT, le_rfl, hT.1, hchi0.1⟩
    have h7 := S'.degree_eq_three_or_five hV hULV hchi0.2 eL'
    omega
  · exact hLM (L238.le_of_isExceptionalA7Block_cat h123 hX hSQ h38 hT hcgs hL hexc)

end CFSG.QuasithinUnique.L246C127.MPB
