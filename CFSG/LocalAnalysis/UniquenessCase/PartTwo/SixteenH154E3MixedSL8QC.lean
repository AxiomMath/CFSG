module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8QB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_zz_normalizer
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x = ⊥) :
    ∃ P : Subgroup G,
      P ≤ D.M ⊓ normalizer ((D.T ⊓ centralizer
        ((v1Sub D.M ⊥ V h.hyp151.isElemAbelian L : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      IsPGroup 7 P ∧ ¬ IsCyclic ↥P := by
  classical
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (barSub ⊥ V hV D.T) (Mbar D.M ⊥ V hV) :=
    s16c7_isSylowOf_barSub (p := 2) ⊥ V hV D.sylowM hMs
  have hcase := s16h_sl28_zz_cent_eq_normalizer D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 h7 hxM hxn hZ0 _ hT
  obtain ⟨E, hEM, hE7, hEnc, hEn⟩ :=
    s16h_sl28_seven_of_C_TZ_eq_normalizer D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hbad hrow hZ4 h7 hxM hxn _ hT hcase
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨P, hPN, hP7, hPnc⟩ :=
    s16h_e3_normalizer_lift D hV hMs (imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L)) (p := 7) hEM hE7 hEnc hEn
  rw [s16h_e3_preTil_imgTil_eq hV (s15_Infra_v1Sub_le h125 hV)] at hPN
  exact ⟨P, hPN, hP7, hPnc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
