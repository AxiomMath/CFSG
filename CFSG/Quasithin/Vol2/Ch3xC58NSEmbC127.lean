module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.Quasithin.Vol2.Ch3xC58NSMPBAlt5

public section

namespace CFSG.QuasithinUnique.L246C127.Emb

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_autI_ne_three {X T P K : Subgroup G} (S : Setting X T P K)
    (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (hK5 : (∃ e : ℕ, 1 < e ∧ IsLin2Type K e) ∨ IsAltType K 5) :
    Nat.card ↥(autI hV K) ≠ 3 := by
  classical
  intro h3
  set π := toAutI hV K S.hKN with hπ
  have hπs : Function.Surjective π := toAutI_surjective hV K S.hKN
  have hker : π.ker ≤ CFSG.pCore 2 ↥K := S.ker_toAutI_le_pCore hV hUV
  have hπk : π.ker.index = 3 := by
    rw [Subgroup.index, ← h3]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv
  have key : ∀ {Q : Type} [Group Q] [Finite Q] (α : ↥K →* Q), Function.Surjective α →
      α.ker = CFSG.pCore 2 ↥K → Nat.card Q ≤ 3 := by
    intro Q _ _ α hα hαk
    have h1 : α.ker.index ∣ π.ker.index := Subgroup.index_dvd_of_le (hαk ▸ hker)
    have h2 : α.ker.index = Nat.card Q := by
      rw [Subgroup.index]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv
    rw [h2, hπk] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  rcases hK5 with ⟨e, he, F, hF, hFt, hcard, α, hα, hαk, -⟩ | ⟨α, hα, hαk, -⟩
  · have h4 := key α hα hαk
    have hinj : Function.Injective (fun a : F => (⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F)) := by
      intro a b hab
      have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
        (M : Matrix (Fin 2) (Fin 2) F) 0 1) hab
      simpa using this
    have h5 : Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
      Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := F), hcard] at h5
    have h6 : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  · have h4 := key α hα hαk
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    omega

theorem block_or_alt7 (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat)
    (hodd : AltEvenExcluded) {X T P K : Subgroup G} (hX : CharTwo X) (hT : IsSylowTwoOf T X)
    (hSQ : IsSQTKCat ↥X) (hPX : P ≤ X) (hTP : T ≤ P) (hK : IsChi0Block P K)
    (hK5 : (∃ e : ℕ, 1 < e ∧ IsLin2Type K e) ∨ IsAltType K 5) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hKZ : ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hV : IsElemAbelian 2 (VZ T X)) :
    IsBlock2 X K ∨ ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU L ≤ VZ T X ∧
      L ⊓ Subgroup.centralizer (VZ T X : Set G) = pCoreOf 2 L ∧
      Nonempty (↥(autI hV L) ≃* alternatingGroup (Fin 7)) ∧
      Nonempty (↥(autI hV K) ≃* alternatingGroup (Fin 5)) ∧
      IsSylowTwoOf (autI hV T ⊓ autI hV L) (autI hV L) := by
  have S : Setting X T P K := ⟨hX, hT, hPX, hTP, hK.1⟩
  have hUV := S.blockU_le_VZ hKZ
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
  · exact Or.inl (hself (isSubnormal_of_le_center_fitting hF))
  · exact Or.inl (hself hcomp.2.1)
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
  obtain ⟨L, hL, hKL', -, hULV, hautL, hCL, hLK⟩ :=
    S.exists_block_lift hV hUV hLle hLsub hKL (Or.inl hqL) hnc
  by_cases hKe : autI hV K = Lstar
  · exact Or.inl (hLK hKe ▸ hL)
  have hLN : L ≤ Subgroup.normalizer (VZ T X : Set G) := hL.2.1.trans S.hXV
  have eL' : ↥(autI hV L) ≃* alternatingGroup (Fin m) := (MulEquiv.subgroupCongr hautL).trans eL
  have hLalt := isAltQuotient_of_equiv hV hLN eL'
  rcases hrest with ⟨n, -, ⟨eK⟩⟩ | ⟨⟨eK3⟩, -⟩
  swap
  · exact ((S.isEmpty_equiv_sl3 hV hUV hK.2).false eK3).elim
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
  · exfalso
    rcases hn with rfl | rfl
    · exact CFSG.Quasithin.C58NS.MPB.alt5_three_excluded eL hKL eK hsyl hsubK
    · exact hKe (Subgroup.eq_of_le_of_card_ge hKL
        ((Nat.card_congr eL.toEquiv).trans (Nat.card_congr eK.toEquiv).symm).le)
  rcases hn with rfl | rfl
  · exfalso
    refine card_autI_ne_three S hV hUV hK5 ?_
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · right
    refine ⟨L, hL, hKL', hULV, hCL, ⟨eL'⟩, ⟨eK⟩, ?_⟩
    rw [hautL]
    exact hsyl

end CFSG.QuasithinUnique.L246C127.Emb
