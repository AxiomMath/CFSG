module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCTA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UElem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThirdP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_three_dvd_lBar_of_conc4_component
    (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {t : MulAut (Vtil V₀ V hV)}
    (hW : Conc4_136W (Mbar D.M V₀ V hV) t (lBar V₀ V hV L)) :
    3 ∣ Nat.card (lBar V₀ V hV L) := by
  rcases hW.2.2 with h133 | h2 | h3 | h4
  · exfalso
    obtain ⟨p, hp, hLp, hne, -⟩ := h133
    haveI : Fact p.Prime := ⟨hp⟩
    have hLpg : IsPGroup p ↥(lBar V₀ V hV L) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p (Mbar D.M V₀ V hV)).to_le hLp
    have hnil : Group.IsNilpotent ↥(lBar V₀ V hV L) := hLpg.isNilpotent
    have hnt : Nontrivial ↥(lBar V₀ V hV L) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 fun hbot =>
        hne (by rw [hbot, Subgroup.commutator_bot_left])
    haveI : Group.IsPerfect ↥(lBar V₀ V hV L) := Group.isPerfect_def.mpr hcomp.2.2.1
    haveI : Nontrivial ↥(lBar V₀ V hV L) := hnt
    exact Group.IsPerfect.not_isNilpotent (G := ↥(lBar V₀ V hV L)) hnil
  · obtain ⟨K, -, g, -, -, hLsup, hshape⟩ := h2
    have h3K : 3 ∣ Nat.card ↥K := by
      rcases hshape with ⟨h3, -⟩ | ⟨h2', -⟩ | ⟨h2', -⟩
      · exact s16h_three_dvd_of_lieFactor (K := ↥K) (Or.inl h3)
      · exact s16h_three_dvd_of_lieFactor (K := ↥K) (Or.inr (Or.inl h2'))
      · exact s16h_three_dvd_of_lieFactor (K := ↥K) (Or.inr (Or.inr h2'))
    exact h3K.trans (Subgroup.card_dvd_of_le (by rw [hLsup]; exact le_sup_left))
  · obtain ⟨hcomp', hsum, -⟩ := h3
    exact s16h_three_dvd_of_sumOfAtMostThreeNat hcomp' hsum
  · obtain ⟨-, -, hcomp', h135⟩ := h4
    exact s16h_three_dvd_of_conc4_135 hcomp' h135

theorem s16h_hyp154_of_component_three
    (D : Data G) (S : s16h_Std D)
    (hσ : D.sig = D.sig1) (h880 : F08.R880 D) (h163 : R16_3FComp D)
    (hSchur : RSchur153)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hs3 : 3 ≤ s15 D.M V₀ V h.hyp151.isElemAbelian L) : Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  have hc : Conc4_136 D V₀ V hV L := ⟨t, ht, ht2, ht1, htr, hW⟩
  have h3dvd : 3 ∣ Nat.card (lBar V₀ V hV L) :=
    s16h_three_dvd_lBar_of_conc4_component D hV hcomp hW
  have hσ3 : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M := by
    obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    exact ⟨q, hq, S.hSig.three_le q hq⟩
  rcases s16h_sig_dvd_or_strong_three_of_component D S h880 h163 hSchur h hcomp ht ht2 ht1 htr
      hW h3dvd (by omega) with ⟨q, hq, hq2, hqsig, hqL⟩ | hsp3
  · have hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup q P → ¬ IsCyclic ↥P →
        P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
      intro w hwV hw0 P hPp hPc hPC
      exact s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 hqsig hPp hPc hwV hw0 hPC
    have hU2 := s16h_condU2_of_dvd D h hc hq hqL hgood
    have hspq : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M :=
      S.hSig.sig1_sp q (hσ ▸ hqsig)
    rcases Nat.lt_or_ge (s15 D.M V₀ V hV L) 4 with hs4 | hs4
    · exact s16h_hyp154_of_condU2_dvd D S.h61 S.h127 h hσ3 hU2 (by omega) hq hq2 hspq hqL
    · exact s16h_hyp154_of_condU2 D S.h61 h hσ3 hU2 (by omega)
  · have hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup 3 P → ¬ IsCyclic ↥P →
        P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
      intro w hwV hw0 P hPp hPc hPC
      exact s16h_uniqueMax_cent_of_cElt_three D S.h61 S.h63 S.h127 hsp3 h.hyp16 hPp hPc hwV hw0 hPC
    have hU2 := s16h_condU2_of_dvd D h hc Nat.prime_three h3dvd hgood
    rcases Nat.lt_or_ge (s15 D.M V₀ V hV L) 4 with hs4 | hs4
    · exact s16h_hyp154_of_condU2_dvd D S.h61 S.h127 h hσ3 hU2 (by omega)
        Nat.prime_three (by norm_num) hsp3 h3dvd
    · exact s16h_hyp154_of_condU2 D S.h61 h hσ3 hU2 (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
