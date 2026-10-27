module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTwelve
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofHJ
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofExc
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofNormal

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2110Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup
open Item2113Proof (commGroupOf map_subtype_zpowers map_subtype_closure_pair
  map_eq_iff_mem_normalizer normalizer_le_of_forall transvection_data data_of_choice
  inv_apply_mem_of_map_eq apply_mem_of_map_eq fixSub_eq_closure apply_eq_mul_of_ne
  conj_comm_mem)

variable {G : Type} [Group G]

theorem map_closure_eq_of_twoGroupW [Finite G] {A : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {c d : G} (hcA : c ∈ A)
    (hdA : d ∈ A) (hc1 : (⟨c, hcA⟩ : A) ≠ 1) (hdc : (⟨d, hdA⟩ : A) ∉ zpowers (⟨c, hcA⟩ : A))
    {t : MulAut A} (htS : t ∈ wStar A) (htc : t ⟨c, hcA⟩ = ⟨c, hcA⟩)
    (htd : t ⟨d, hdA⟩ = ⟨d, hdA⟩) (ht1 : t ≠ 1)
    (htcomm : ∀ x, x⁻¹ * t x ∈ zpowers (⟨d, hdA⟩ : A))
    (hTG : ∀ x ∈ normalizer (A : Set G), x ∈ normalizer (closure ({c, d} : Set G) : Set G) →
      x * d * x⁻¹ = d → x * c * x⁻¹ ≠ c * d)
    {σ : MulAut A} (hσ : σ ∈ wStar A)
    (hσd : (zpowers (⟨d, hdA⟩ : A)).map σ.toMonoidHom = zpowers ⟨d, hdA⟩) :
    (closure ({⟨c, hcA⟩, ⟨d, hdA⟩} : Set A)).map σ.toMonoidHom =
      closure ({⟨c, hcA⟩, ⟨d, hdA⟩} : Set A) := by
  let _ : CommGroup A := commGroupOf hAe
  have h3 : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (hAe.2 x x.2)
  set cA : A := ⟨c, hcA⟩ with hcAdef
  set dA : A := ⟨d, hdA⟩ with hdAdef
  by_contra hne
  set t' := σ * t * σ⁻¹ with ht'
  have ht'S : t' ∈ wStar A := mul_mem (mul_mem hσ htS) (inv_mem hσ)
  have hσinvd : σ⁻¹ dA ∈ zpowers dA := inv_apply_mem_of_map_eq hσd (mem_zpowers dA)
  have hσdA : σ dA ∈ zpowers dA := apply_mem_of_map_eq hσd (mem_zpowers dA)
  have htz : ∀ y ∈ zpowers dA, t y = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [map_zpow, htd]
  have ht'd : t' dA = dA := by
    rw [ht', MulAut.mul_apply, MulAut.mul_apply, htz _ hσinvd, MulAut.apply_inv_self]
  have ht'comm : ∀ x, x⁻¹ * t' x ∈ zpowers dA := fun x =>
    (zpowers_le.mpr hσdA) (conj_comm_mem htcomm (g := σ) x)
  have ht'c : t' cA ≠ cA := by
    intro h
    apply hne
    have hfix : t (σ⁻¹ cA) = σ⁻¹ cA := by
      apply σ.injective
      rw [MulAut.apply_inv_self]
      simpa only [ht', MulAut.mul_apply] using h
    obtain ⟨hF, -⟩ := fixSub_eq_closure h3 h27 hc1 hdc htc htd ht1
    have hmem : σ⁻¹ cA ∈ closure ({cA, dA} : Set A) := by
      rw [← hF]
      exact hfix
    have hle : closure ({cA, dA} : Set A) ≤ (closure ({cA, dA} : Set A)).map σ.toMonoidHom := by
      rw [closure_le]
      rintro y (rfl | rfl)
      · exact ⟨σ⁻¹ cA, hmem, MulAut.apply_inv_self _ σ cA⟩
      · refine ⟨σ⁻¹ dA, ?_, MulAut.apply_inv_self _ σ dA⟩
        exact (zpowers_le.mpr (subset_closure (Set.mem_insert_of_mem cA (Set.mem_singleton dA))))
          hσinvd
    exact (eq_of_le_of_card_ge hle (by rw [card_map_of_injective σ.injective])).symm
  have hcases := apply_eq_mul_of_ne h3 ht'comm ht'c
  obtain ⟨y, hy⟩ := ht'S
  have hyd : (y : G) * d * (y : G)⁻¹ = d := by
    have h := congrArg Subtype.val ht'd
    rwa [← hy, normalizerMonoidHom_apply_apply_coe] at h
  have hyc : (y : G) * c * (y : G)⁻¹ = c * d ∨ (y : G) * c * (y : G)⁻¹ = c * d ^ 2 := by
    rcases hcases with h | h
    · left
      have h' := congrArg Subtype.val h
      rwa [← hy, normalizerMonoidHom_apply_apply_coe] at h'
    · right
      have h' := congrArg Subtype.val h
      rwa [← hy, normalizerMonoidHom_apply_apply_coe] at h'
  have hcD : c ∈ closure ({c, d} : Set G) := subset_closure (Set.mem_insert c _)
  have hdD : d ∈ closure ({c, d} : Set G) :=
    subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have hyD : (y : G) ∈ normalizer (closure ({c, d} : Set G) : Set G) := by
    apply Item2113Proof.mem_normalizer_of_map_le
    rw [MonoidHom.map_closure, Set.image_pair, closure_le]
    rintro z (rfl | rfl)
    · show (y : G) * c * (y : G)⁻¹ ∈ _
      rcases hyc with h | h <;> rw [h]
      · exact mul_mem hcD hdD
      · exact mul_mem hcD (pow_mem hdD 2)
    · show (y : G) * d * (y : G)⁻¹ ∈ _
      rw [hyd]
      exact hdD
  rcases hyc with h | h
  · exact hTG _ y.2 hyD hyd h
  · apply hTG _ (mul_mem y.2 y.2) (mul_mem hyD hyD)
    · calc (y : G) * y * d * ((y : G) * y)⁻¹ = (y : G) * ((y : G) * d * (y : G)⁻¹) * (y : G)⁻¹ :=
            by group
        _ = d := by rw [hyd, hyd]
    · have hd3 : d ^ 3 = 1 := hAe.2 d hdA
      calc (y : G) * y * c * ((y : G) * y)⁻¹ = (y : G) * ((y : G) * c * (y : G)⁻¹) * (y : G)⁻¹ :=
            by group
        _ = (y : G) * (c * d ^ 2) * (y : G)⁻¹ := by rw [h]
        _ = (y : G) * c * (y : G)⁻¹ * ((y : G) * d * (y : G)⁻¹) ^ 2 := by rw [conj_pow]; group
        _ = c * d := by
          rw [h, hyd, mul_assoc, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hd3,
            one_mul, pow_one]

theorem not_mem_zpowers_of_subtype {A : Subgroup G} {c d : G} (hcA : c ∈ A) (hdA : d ∈ A)
    (hdc : (⟨d, hdA⟩ : A) ∉ zpowers (⟨c, hcA⟩ : A)) : d ∉ zpowers c := by
  intro h
  apply hdc
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

section Normal


theorem item218Normal_of_ndW (h211 : Item211) (hch : Item2113Choice) (h2111 : Item2111)
    (h2 : Item2110Two) (hND : Item2112NDW) : Item218Normal := by
  intro G _ _ A E U c L hpair hL
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe := hpair.mem_S.1.1
  have hLc : L ≤ centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  obtain ⟨d, hdA, hd1, hdcen, t, htL, ht, htd⟩ := hch G A E U c L hpair hL
  obtain ⟨h27, hc1, hcA, hdc⟩ := data_of_choice h211 hpair hL hdA hd1 hdcen
  obtain ⟨htS, htc, htd', ht1, htcomm⟩ := transvection_data hcA hdA hLc htL ht htd
  let _ : CommGroup A := commGroupOf hAe
  have h3 : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (hAe.2 x x.2)
  have hc1' : (⟨c, hcA⟩ : A) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hred : ∃ B : Subgroup A, B ≠ ⊥ ∧ B ≠ ⊤ ∧ ∀ σ ∈ wStar A, B.map σ.toMonoidHom = B := by
    have h := h2111 G A E U c L hpair hL
    simp only [IsIrreducibleOn, not_forall, not_or] at h
    obtain ⟨B, hB, hB1, hB2⟩ := h
    exact ⟨B, hB1, hB2, hB⟩
  have hdcG : d ∉ zpowers c := not_mem_zpowers_of_subtype hcA hdA hdc
  have hTGW : ∀ x ∈ normalizer (A : Set G), x ∈ normalizer (closure ({c, d} : Set G) : Set G) →
      x * d * x⁻¹ = d → x * c * x⁻¹ ≠ c * d := fun _ hxA _ hxd =>
    Item2113Res2Proof.item2112TwoGroup_of_mem_W h2 hpair hL hdA hd1 hdcen hdcG hxA hxd
  have hdD : ∀ σ ∈ wStar A,
      (zpowers (⟨d, hdA⟩ : A)).map σ.toMonoidHom = zpowers ⟨d, hdA⟩ →
      (closure ({⟨c, hcA⟩, ⟨d, hdA⟩} : Set A)).map σ.toMonoidHom =
        closure ({⟨c, hcA⟩, ⟨d, hdA⟩} : Set A) := fun σ hσ h =>
    map_closure_eq_of_twoGroupW hAe h27 hcA hdA hc1' hdc htS htc htd' ht1 htcomm hTGW hσ h
  have hDc : ∀ σ ∈ wStar A,
      (closure ({⟨c, hcA⟩, ⟨d, hdA⟩} : Set A)).map σ.toMonoidHom =
        closure ({⟨c, hcA⟩, ⟨d, hdA⟩} : Set A) →
      (zpowers (⟨c, hcA⟩ : A)).map σ.toMonoidHom = zpowers ⟨c, hcA⟩ := by
    rintro _ ⟨w, rfl⟩ h
    rw [map_eq_iff_mem_normalizer, map_subtype_closure_pair] at h
    rw [map_eq_iff_mem_normalizer, map_subtype_zpowers]
    exact hND G A E U c L hpair hL d hdA hd1 hdcen ⟨w.2, h⟩
  have hall := Item2113Proof.normalizes_of_reducible h3 h27 hc1' hdc htS htc htd' ht1 htcomm hred
    hdD hDc
  have h := normalizer_le_of_forall hall
  rwa [map_subtype_zpowers] at h

theorem item218Normal_of_two
    (h211 : Item211) (h45 : Sec4.Item4_5) (h2 : Item2110Two)
    (hTGHJ : Item2112TwoGroupHJ) (hNF : Item2112NoFusion) : Item218Normal :=
  have hch : Item2113Choice := Item2113Res2Proof.item2113Choice_of h211 h45
    (Item2113Res3Proof.item2113ChoiceHJ_of h211 h45) Item2113Res3Proof.kf2113ExcCentral_holds
  item218Normal_of_ndW h211 hch (Item2113Res2Proof.item2111_of_noFusion h211 hch hNF) h2
    (item2112NDW_of h211 h45 h2 hTGHJ hNF)

end Normal

end CFSG.RankThree.PartTwo.Sec21.Item2110Res2Proof
