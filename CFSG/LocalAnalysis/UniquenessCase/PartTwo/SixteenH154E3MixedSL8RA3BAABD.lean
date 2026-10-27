module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_sylow_normalizer_shape
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian)) :
    ∃ TA TB : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      TA ≤ T ∧ TB ≤ T ∧
      CFSG.ABGLocalTools.IsSylowOf 2 TA (lBar ⊥ V h.hyp151.isElemAbelian L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 TB (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) ∧
      T ⊓ Subgroup.normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) =
        TA ⊔ TB := by
  classical
  let hV := h.hyp151.isElemAbelian
  let W := Vtil ⊥ V hV
  let Mb : Subgroup (MulAut W) := Mbar D.M ⊥ V hV
  let A : Subgroup (MulAut W) := lBar ⊥ V hV L
  let B : Subgroup (MulAut W) := barSub ⊥ V hV (conjSubgroup L x)
  let N : Subgroup (MulAut W) := Mb ⊓ Subgroup.normalizer (A : Set (MulAut W))
  let P : Subgroup (MulAut W) := T ⊓ N
  have hTM : T ≤ Mb := hT.le
  have hAM : A ≤ Mb := barSub_mono ⊥ V hV h.hyp151.le
  have hBM : B ≤ Mb := c23_barSub_conjSubgroup_le_Mbar D h.hyp151 hV hxM
  have hAB : ⁅A, B⁆ = ⊥ := (h.hyp151.commute x hxM hxn).1
  have hfixA : Nat.card ↥(autSub (Subgroup.centralizer (A : Set (MulAut W)))
      (commSub ⊤ A)) ∣ 7 :=
    s16h_sl28_centralizer_aut_card_dvd_seven (L := A)
      (fun w => s15_Infra_vtil_sq_eq_one ⊥ V hV w) hrow
  have hSL_A : IsSLn ↥A 2 3 := hrow.1
  have hSL_B : IsSLn ↥B 2 3 := s16h_sl28_isSLn_conj D S h hrow hxM
  have hfixB : Nat.card ↥(autSub (Subgroup.centralizer (B : Set (MulAut W)))
      (commSub ⊤ B)) ∣ 7 := s16h_sl28_centralizer_card_dvd_seven_conj D S h hrow hxM
  have hsup : commSub ⊤ A ⊔ commSub ⊤ B = ⊤ :=
    s16h_sl28_wTil_sup_conj_eq_top_of_setting16 D S h hs2 hW hxM hxn
  have hNnorm : Mb ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    (s16h_sl28_normalizer_index_two D S h hs2 hxM hxn).1
  have hNB : N ≤ Subgroup.normalizer (B : Set (MulAut W)) :=
    (s16h_sl28_normalizer_index_two D S h hs2 hxM hxn).2
  have hNA : N ≤ Subgroup.normalizer (A : Set (MulAut W)) := inf_le_right
  have hAN : A ≤ N := le_inf hAM (Subgroup.le_normalizer (H := A))
  have hBA : B ≤ Subgroup.centralizer (A : Set (MulAut W)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hAB
  have hBN : B ≤ N :=
    le_inf hBM (hBA.trans (Subgroup.centralizer_le_normalizer (A : Set (MulAut W))))
  have hPN : CFSG.ABGLocalTools.IsSylowOf 2 P N :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hT inf_le_left hNnorm
  have hcore : P = (P ⊓ A) ⊔ (P ⊓ B) :=
    s16h_sylow_two_eq_sup_of_aut_card (hW := fun w => s15_Infra_vtil_sq_eq_one ⊥ V hV w)
      hPN hAN hBN hNA hNB hAB hSL_A hSL_B hfixA hfixB hsup
  have hP_eq : P = T ⊓ Subgroup.normalizer (A : Set (MulAut W)) := by
    show T ⊓ N = T ⊓ Subgroup.normalizer (A : Set (MulAut W))
    rw [show N = Mb ⊓ Subgroup.normalizer (A : Set (MulAut W)) from rfl, ← inf_assoc,
      inf_eq_left.mpr hTM]
  refine ⟨P ⊓ A, P ⊓ B, le_trans inf_le_left inf_le_left, le_trans inf_le_left inf_le_left,
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPN hAN hNA,
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPN hBN hNB, ?_⟩
  rw [← hP_eq]
  exact hcore

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
