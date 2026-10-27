module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Proof
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item218FinalD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L U₀ : Subgroup G) (b : G)
    (K : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → U₀ ∈ fourGroupsMinus E → U₀ ≤ L →
    Sec21Pair G A E U₀ b K → IsList218 K → b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G) →
    b ∉ Subgroup.zpowers c →
    (Nonempty (starOf A L ≃* DihedralGroup 6) ∨ Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) →
    (Nonempty (starOf A K ≃* DihedralGroup 6) ∨ Nonempty (starOf A K ≃* Equiv.Perm (Fin 3))) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) →
    IsCentral218 L b → IsCentral218 K c →
    (∃ t ∈ starOf A L, IsTransvectionOn t ∧ (commOf t).map A.subtype = Subgroup.zpowers b) →
    (∃ t ∈ starOf A K, IsTransvectionOn t ∧ (commOf t).map A.subtype = Subgroup.zpowers c) →
    False

namespace Item2113Proof

variable {G : Type} [Group G]

theorem isCentral218_of_zpowers_eq {L : Subgroup G} {b d : G} (hd : IsCentral218 L d)
    (h : Subgroup.zpowers b = Subgroup.zpowers d) : IsCentral218 L b := by
  obtain ⟨S, hS, hdS⟩ := hd
  refine ⟨S, hS, ?_⟩
  have hb : b ∈ Subgroup.zpowers d := h ▸ Subgroup.mem_zpowers b
  exact (Subgroup.zpowers_le.mpr hdS) hb

theorem mem_closure_of_normalizes {A : Type*} [CommGroup A] [Finite A] (h3 : ∀ x : A, x ^ 3 = 1)
    (h27 : Nat.card A = 27) {b c d : A} {t : MulAut A} (hc : c ≠ 1) (hdc : d ∉ Subgroup.zpowers c)
    (htc : t c = c) (htd : t d = d) (ht1 : t ≠ 1)
    (htcomm : ∀ x, x⁻¹ * t x ∈ Subgroup.zpowers d) (hb1 : b ≠ 1)
    (htb : (Subgroup.zpowers b).map t.toMonoidHom = Subgroup.zpowers b) :
    b ∈ Subgroup.closure ({c, d} : Set A) := by
  obtain ⟨hFix, -⟩ := fixSub_eq_closure h3 h27 hc hdc htc htd ht1
  have htbm : t b ∈ Subgroup.zpowers b := apply_mem_of_map_eq htb (Subgroup.mem_zpowers b)
  have hδb : b⁻¹ * t b ∈ Subgroup.zpowers b :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)) htbm
  by_cases hδ : b⁻¹ * t b = 1
  · rw [← hFix]
    exact (inv_mul_eq_one.mp hδ).symm
  · have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
    have hbδ : Subgroup.zpowers b = Subgroup.zpowers (b⁻¹ * t b) :=
      eq_zpowers_of_card_three h3 (card_zpowers_three h3 hb1) hδb hδ
    have hdδ : Subgroup.zpowers d = Subgroup.zpowers (b⁻¹ * t b) :=
      eq_zpowers_of_card_three h3 (card_zpowers_three h3 hd1) (htcomm b) hδ
    have hbd : b ∈ Subgroup.zpowers d := by
      rw [hdδ, ← hbδ]
      exact Subgroup.mem_zpowers b
    have hdD : d ∈ Subgroup.closure ({c, d} : Set A) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
    exact (Subgroup.zpowers_le.mpr hdD) hbd

section Final

theorem closure_eq_of_normalizer_le [Finite G] (h211 : Item211) {A E U L : Subgroup G} {c d b : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdcen : IsCentral218 L d) {t : MulAut A} (htL : t ∈ starOf A L) (ht : IsTransvectionOn t)
    (htd : (commOf t).map A.subtype = Subgroup.zpowers d) (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hbc : b ∉ Subgroup.zpowers c)
    (hWb : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)) :
    Subgroup.closure ({c, d} : Set G) = Subgroup.closure ({c, b} : Set G) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe := hpair.mem_S.1.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  obtain ⟨h27, hc1, hcA, hdc⟩ := data_of_choice h211 hpair hL hdA hd1 hdcen
  obtain ⟨htS, htc, htd', ht1, htcomm⟩ := transvection_data hcA hdA hLc htL ht htd
  let _ : CommGroup A := commGroupOf hAe
  have h3 : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (hAe.2 x x.2)
  have hc1' : (⟨c, hcA⟩ : A) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hb1' : (⟨b, hbA⟩ : A) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have htb : (Subgroup.zpowers (⟨b, hbA⟩ : A)).map t.toMonoidHom =
      Subgroup.zpowers ⟨b, hbA⟩ := by
    obtain ⟨w, rfl⟩ := htS
    rw [map_eq_iff_mem_normalizer, map_subtype_zpowers]
    exact hWb w.2
  have hbD := mem_closure_of_normalizes h3 h27 hc1' hdc htc htd' ht1 htcomm hb1' htb
  have hbc' : (⟨b, hbA⟩ : A) ∉ Subgroup.zpowers (⟨c, hcA⟩ : A) := by
    intro h
    apply hbc
    have h' := Subgroup.mem_map_of_mem A.subtype h
    rwa [map_subtype_zpowers] at h'
  have hD9 := (fixSub_eq_closure h3 h27 hc1' hdc htc htd' ht1).2
  have heq := eq_closure_of_card_nine h3 h27 hD9
    (Subgroup.subset_closure (Set.mem_insert _ _)) hbD hc1' hbc'
  have h := congrArg (Subgroup.map A.subtype) heq
  rwa [map_subtype_closure_pair, map_subtype_closure_pair] at h

end Final

end Item2113Proof

end CFSG.RankThree.PartTwo.Sec21
