module

public import CFSG.CGT.Timmesfeld75.L2Basic
import CFSG.GroupTheory.DedekindNormalizer
import CFSG.CGT.Timmesfeld75.L2Orbit
import CFSG.CGT.Timmesfeld75.L2Aut
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.GH74.GLS.IVK.L2.TorusMatrices
import CFSG.RankThree.GF2n.Smith81.TiD2Alg
import CFSG.RankThree.GF2n.Stroth80.FieldModelAlgebra

public section

namespace CFSG.RankThree.GF2n.Smith81.SL2Torus

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75
open CFSG.GH74.GLS.IVK.L2Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem wElt_mul_self : (wElt : SL(2, F)) * wElt = 1 := by
  have h : (wElt : SL(2, F)) * wElt ∈ Subgroup.center SL(2, F) := by
    simpa [wElt] using
      CFSG.Glauberman.Dickson.standardSplitWeylSL_sq_mem_center F
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at h
  exact h

theorem wElt_inv : (wElt : SL(2, F))⁻¹ = wElt :=
  inv_eq_of_mul_eq_one_right wElt_mul_self

theorem wElt_conj_torusElt (a : Fˣ) :
    wElt * torusElt a * (wElt)⁻¹ = torusElt a⁻¹ := by
  simpa [wElt, torusElt, wElt_inv] using
    CFSG.Glauberman.Dickson.standardSplitWeylSL_conj (F := F) a

theorem wElt_conj_torusElt' (a : Fˣ) :
    wElt * torusElt a * wElt = torusElt a⁻¹ := by
  simpa [wElt_inv] using wElt_conj_torusElt a

theorem conjSubgroup_wElt_torus : conjSubgroup wElt (torus F) = torus F := by
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro hx
    rw [wElt_inv] at hx
    obtain ⟨a, ha⟩ := mem_torus_iff.1 hx
    have hxeq : x = wElt * torusElt a * wElt := by
      calc x = (wElt * wElt) * x * (wElt * wElt) := by rw [wElt_mul_self]; group
        _ = wElt * (wElt * x * wElt) * wElt := by group
        _ = wElt * torusElt a * wElt := by rw [ha]
    rw [hxeq, wElt_conj_torusElt']
    exact torusElt_mem_torus _
  · intro hx
    rw [wElt_inv]
    obtain ⟨a, rfl⟩ := mem_torus_iff.1 hx
    rw [wElt_conj_torusElt']
    exact torusElt_mem_torus _

theorem wElt_mem_normalizer_torus :
    (wElt : SL(2, F)) ∈ Subgroup.normalizer (torus F : Set SL(2, F)) :=
  mem_normalizer_iff_conjSubgroup_eq.2 conjSubgroup_wElt_torus

theorem wElt_not_mem_torus : (wElt : SL(2, F)) ∉ torus F := by
  rw [mem_torus_entries]
  intro h
  have h10 : (wElt : SL(2, F)) 1 0 = 0 := h.2
  rw [wElt_apply_10] at h10
  exact one_ne_zero h10

theorem exists_unit_ne_inv (h4 : 4 ≤ Nat.card F) : ∃ a : Fˣ, a ≠ a⁻¹ := by
  have hcardNat : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  haveI : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hcardNat
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  refine ⟨a, fun h => ha ?_⟩
  have hv : (a : F) = (a : F)⁻¹ := by simpa using congrArg Units.val h
  have h2 : ((a : F) * (a : F)) = 1 := by
    nth_rewrite 2 [hv]
    exact mul_inv_cancel₀ a.ne_zero
  exact Units.ext (CharTwo.sq_injective (by simpa [pow_two] using h2))

theorem mem_torus_or_antidiagonal_of_mem_normalizer (h4 : 4 ≤ Nat.card F)
    {g : SL(2, F)} (hg : g ∈ Subgroup.normalizer (torus F : Set SL(2, F))) :
    g ∈ torus F ∨ (g 0 0 = 0 ∧ g 1 1 = 0) := by
  obtain ⟨a, ha⟩ := exists_unit_ne_inv (F := F) h4
  have hconj : g * torusElt a * g⁻¹ ∈ torus F :=
    (Subgroup.mem_normalizer_iff.1 hg (torusElt a)).1 (torusElt_mem_torus a)
  have hne : (torusElt a : SL(2, F)) 0 0 ≠ (torusElt a : SL(2, F)) 1 1 := by
    rw [torusElt_apply_00, torusElt_apply_11]
    intro hab
    apply ha
    exact Units.ext (by simpa using hab)
  rcases mem_diagSub_or_antidiag (t := torusElt a) (torusElt_mem_torus a) hne hconj
    with hdiag | hanti
  · exact Or.inl hdiag
  · exact Or.inr hanti

theorem exists_eq_wElt_mul_torusElt_of_antidiagonal {g : SL(2, F)}
    (h00 : g 0 0 = 0) (h11 : g 1 1 = 0) :
    ∃ a : Fˣ, g = wElt * torusElt a := by
  obtain ⟨a, ha⟩ :=
    CFSG.Glauberman.Dickson.eq_standardSplitWeylSL_mul_splitTorusSLHom_of_diagonal_eq_zero
      g h00 h11
  exact ⟨a, by simpa [wElt, torusElt] using ha⟩

theorem card_normalizer_torus (h4 : 4 ≤ Nat.card F) :
    Nat.card (Subgroup.normalizer (torus F : Set SL(2, F))) = 2 * (Nat.card F - 1) := by
  let N := Subgroup.normalizer (torus F : Set SL(2, F))
  have hT : torus F ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := (torus F).subgroupOf N
  have hwN : (wElt : SL(2, F)) ∈ N := wElt_mem_normalizer_torus
  have hwH : (⟨wElt, hwN⟩ : N) ∉ H := by
    intro h
    exact wElt_not_mem_torus (Subgroup.mem_subgroupOf.1 h)
  have hindex : H.index = 2 := by
    refine Subgroup.index_eq_two_iff_exists_notMem_and.2 ⟨⟨wElt, hwN⟩, hwH, ?_⟩
    intro b
    by_cases hb : (b : SL(2, F)) ∈ torus F
    · exact Or.inr (Subgroup.mem_subgroupOf.2 hb)
    · left
      have hclass := mem_torus_or_antidiagonal_of_mem_normalizer (F := F) h4 b.2
      rcases hclass with hTb | hanti
      · exact (hb hTb).elim
      · obtain ⟨u, hu⟩ := exists_eq_wElt_mul_torusElt_of_antidiagonal hanti.1 hanti.2
        rw [Subgroup.mem_subgroupOf]
        change ((b : SL(2, F)) * wElt) ∈ torus F
        rw [hu, wElt_conj_torusElt']
        exact torusElt_mem_torus _
  have hcardH : Nat.card H = Nat.card F - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv, card_torus]
  have hcard := Subgroup.card_mul_index H
  rw [hindex, hcardH] at hcard
  change Nat.card N = 2 * (Nat.card F - 1)
  omega

theorem mul_self_eq_one_of_mem_normalizer_torus (h4 : 4 ≤ Nat.card F) {g : SL(2, F)}
    (hg : g ∈ Subgroup.normalizer (torus F : Set SL(2, F))) (hgT : g ∉ torus F) :
    g * g = 1 := by
  rcases mem_torus_or_antidiagonal_of_mem_normalizer (F := F) h4 hg with hT | hanti
  · exact (hgT hT).elim
  · obtain ⟨a, rfl⟩ := exists_eq_wElt_mul_torusElt_of_antidiagonal hanti.1 hanti.2
    calc (wElt * torusElt a) * (wElt * torusElt a)
        = (wElt * torusElt a * wElt) * torusElt a := by group
      _ = torusElt a⁻¹ * torusElt a := by rw [wElt_conj_torusElt']
      _ = 1 := by rw [← torusElt_mul, inv_mul_cancel, torusElt_one]

theorem exists_torusElt_conj_ltriElt {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Fˣ, torusElt a * ltriElt s * (torusElt a)⁻¹ = ltriElt t := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (s / t)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : s / t = 0 := by simpa using hr
    exact div_ne_zero hs ht h0
  refine ⟨Units.mk0 r hr0, ?_⟩
  rw [torusElt_mul_ltriElt_mul_inv]
  congr 1
  rw [Units.val_mk0]
  have h2 : s = r ^ 2 * t := by
    have h := hr
    field_simp [hs, ht] at h
    calc s = t * r ^ 2 := h
      _ = r ^ 2 * t := mul_comm _ _
  rw [h2, inv_mul_cancel_left₀ (pow_ne_zero 2 hr0)]

theorem utri_ne_bot : utri F ≠ (⊥ : Subgroup SL(2, F)) := by
  intro h
  have h1 : (utriElt (1 : F) : SL(2, F)) ∈ (⊥ : Subgroup SL(2, F)) := by
    rw [← h]
    exact utriElt_mem_utri 1
  exact utriElt_ne_one one_ne_zero (Subgroup.mem_bot.1 h1)

theorem ltri_ne_bot : ltri F ≠ (⊥ : Subgroup SL(2, F)) := by
  intro h
  have h1 : (ltriElt (1 : F) : SL(2, F)) ∈ (⊥ : Subgroup SL(2, F)) := by
    rw [← h]
    exact ltriElt_mem_ltri 1
  exact ltriElt_ne_one one_ne_zero (Subgroup.mem_bot.1 h1)

theorem isPGroup_ltri : IsPGroup 2 (ltri F) := by
  rw [← conjSubgroup_wElt_utri]
  exact isPGroup_utri.map (MulAut.conj wElt).toMonoidHom

theorem utri_le_of_inf_ne_bot {N : Subgroup SL(2, F)} (hT : torus F ≤ N)
    (h : N ⊓ utri F ≠ ⊥) : utri F ≤ N := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  have hx1' : (x : SL(2, F)) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  obtain ⟨s, hs⟩ := mem_utri_iff.1 x.2.2
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hs
    exact hx1' hs
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact N.one_mem
  · obtain ⟨t, ht⟩ := mem_utri_iff.1 hy
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [utriElt_zero] at ht
      exact hy1 ht
    obtain ⟨a, ha⟩ := exists_torusElt_conj_utriElt hs0 ht0
    have hxN : (x : SL(2, F)) ∈ N := x.2.1
    have haN : (torusElt a : SL(2, F)) ∈ N := hT (torusElt_mem_torus a)
    have hy' : y = torusElt a * (x : SL(2, F)) * (torusElt a)⁻¹ := by
      rw [ht, hs, ha]
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hxN) (N.inv_mem haN)

theorem ltri_le_of_inf_ne_bot {N : Subgroup SL(2, F)} (hT : torus F ≤ N)
    (h : N ⊓ ltri F ≠ ⊥) : ltri F ≤ N := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  have hx1' : (x : SL(2, F)) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  obtain ⟨s, hs⟩ := mem_ltri_iff.1 x.2.2
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [ltriElt_zero] at hs
    exact hx1' hs
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact N.one_mem
  · obtain ⟨t, ht⟩ := mem_ltri_iff.1 hy
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [ltriElt_zero] at ht
      exact hy1 ht
    obtain ⟨a, ha⟩ := exists_torusElt_conj_ltriElt hs0 ht0
    have hxN : (x : SL(2, F)) ∈ N := x.2.1
    have haN : (torusElt a : SL(2, F)) ∈ N := hT (torusElt_mem_torus a)
    have hy' : y = torusElt a * (x : SL(2, F)) * (torusElt a)⁻¹ := by
      rw [ht, hs, ha]
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hxN) (N.inv_mem haN)

theorem eq_top_of_inf_utri_ne_bot {N : Subgroup SL(2, F)} (hT : torus F ≤ N)
    (hO : ∀ P : Subgroup SL(2, F), P ≤ N →
      N ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥)
    (h : N ⊓ utri F ≠ ⊥) : N = ⊤ := by
  have hUleN : utri F ≤ N := utri_le_of_inf_ne_bot hT h
  by_cases hnorm : N ≤ Subgroup.normalizer (utri F : Set SL(2, F))
  · exact (utri_ne_bot (hO (utri F) hUleN hnorm isPGroup_utri)).elim
  · have hex : ∃ n : SL(2, F), n ∈ N ∧
        n ∉ Subgroup.normalizer (utri F : Set SL(2, F)) := by
      by_contra hcon
      exact hnorm (fun x hx => by
        by_contra hxH
        exact hcon ⟨x, hx, hxH⟩)
    obtain ⟨n, hnN, hnNot⟩ := hex
    have hne : conjSubgroup n (utri F) ≠ utri F := fun hEq =>
      hnNot (mem_normalizer_iff_conjSubgroup_eq.2 hEq)
    have htop : utri F ⊔ conjSubgroup n (utri F) = ⊤ := by
      simpa [conjSubgroup_one] using
        sup_conjSubgroup_utri_eq_top (a := 1) (b := n)
          (by simpa [conjSubgroup_one] using hne.symm)
    have hle : utri F ⊔ conjSubgroup n (utri F) ≤ N := by
      refine sup_le hUleN ?_
      intro x hx
      rw [mem_conjSubgroup] at hx
      have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN (hUleN hx)) (N.inv_mem hnN)
    have htop' : (⊤ : Subgroup SL(2, F)) ≤ N := by
      rw [← htop]
      exact hle
    exact top_le_iff.mp htop'

theorem eq_top_of_inf_ltri_ne_bot {N : Subgroup SL(2, F)} (hT : torus F ≤ N)
    (hO : ∀ P : Subgroup SL(2, F), P ≤ N →
      N ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥)
    (h : N ⊓ ltri F ≠ ⊥) : N = ⊤ := by
  have hLleN : ltri F ≤ N := ltri_le_of_inf_ne_bot hT h
  by_cases hnorm : N ≤ Subgroup.normalizer (ltri F : Set SL(2, F))
  · exact (ltri_ne_bot (hO (ltri F) hLleN hnorm isPGroup_ltri)).elim
  · have hex : ∃ n : SL(2, F), n ∈ N ∧
        n ∉ Subgroup.normalizer (ltri F : Set SL(2, F)) := by
      by_contra hcon
      exact hnorm (fun x hx => by
        by_contra hxH
        exact hcon ⟨x, hx, hxH⟩)
    obtain ⟨n, hnN, hnNot⟩ := hex
    have hne : conjSubgroup n (ltri F) ≠ ltri F := fun hEq =>
      hnNot (mem_normalizer_iff_conjSubgroup_eq.2 hEq)
    have hEq' : conjSubgroup n (ltri F) = conjSubgroup (n * wElt) (utri F) := by
      rw [← conjSubgroup_wElt_utri, conjSubgroup_conjSubgroup]
    have hne' : conjSubgroup wElt (utri F) ≠ conjSubgroup (n * wElt) (utri F) := by
      intro hEq
      apply hne
      exact hEq'.trans (hEq.symm.trans conjSubgroup_wElt_utri)
    have htop : conjSubgroup wElt (utri F) ⊔ conjSubgroup (n * wElt) (utri F) = ⊤ :=
      sup_conjSubgroup_utri_eq_top hne'
    rw [conjSubgroup_wElt_utri, ← hEq'] at htop
    have hle : ltri F ⊔ conjSubgroup n (ltri F) ≤ N := by
      refine sup_le hLleN ?_
      intro x hx
      rw [mem_conjSubgroup] at hx
      have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN (hLleN hx)) (N.inv_mem hnN)
    have htop' : (⊤ : Subgroup SL(2, F)) ≤ N := by
      rw [← htop]
      exact hle
    exact top_le_iff.mp htop'

theorem normalizer_ltri_eq : Subgroup.normalizer (ltri F : Set SL(2, F)) =
    ltri F ⊔ torus F := by
  have hN : conjSubgroup wElt (Subgroup.normalizer (utri F : Set SL(2, F))) =
      Subgroup.normalizer (conjSubgroup wElt (utri F) : Set SL(2, F)) := by
    simpa [conjSubgroup] using
      (Subgroup.map_normalizer_eq_of_bijective (utri F)
        (f := (MulAut.conj wElt).toMonoidHom) (MulAut.conj wElt).bijective)
  rw [conjSubgroup_wElt_utri, normalizer_utri, borel_eq_sup,
    conjSubgroup_sup_eq_sup, conjSubgroup_wElt_utri, conjSubgroup_wElt_torus] at hN
  exact hN.symm

theorem torus_le_normalizer_ltri : torus F ≤
    Subgroup.normalizer (ltri F : Set SL(2, F)) := by
  rw [normalizer_ltri_eq]
  exact le_sup_right

theorem inf_borel_eq_torus {N : Subgroup SL(2, F)} (hT : torus F ≤ N)
    (hU : N ⊓ utri F = ⊥) : N ⊓ borel F = torus F := by
  have hTnorm : torus F ≤ Subgroup.normalizer (utri F : Set SL(2, F)) := by
    intro t ht
    rw [normalizer_utri]
    exact torus_le_borel ht
  calc N ⊓ borel F = N ⊓ (torus F ⊔ utri F) := by rw [borel_eq_sup, sup_comm]
    _ = torus F ⊔ (N ⊓ utri F) :=
      CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hT hTnorm
    _ = torus F := by rw [hU, sup_bot_eq]

theorem inf_normalizer_ltri_eq_torus {N : Subgroup SL(2, F)} (hT : torus F ≤ N)
    (hL : N ⊓ ltri F = ⊥) :
    N ⊓ Subgroup.normalizer (ltri F : Set SL(2, F)) = torus F := by
  rw [normalizer_ltri_eq, sup_comm]
  calc N ⊓ (torus F ⊔ ltri F) = torus F ⊔ (N ⊓ ltri F) :=
      CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hT torus_le_normalizer_ltri
    _ = torus F := by rw [hL, sup_bot_eq]

@[expose] def ltriConj (s : F) : Subgroup SL(2, F) :=
  conjSubgroup (utriElt s) (ltri F)

theorem ltriConj_zero : ltriConj (0 : F) = ltri F := by
  simp [ltriConj, utriElt_zero, conjSubgroup_one]

theorem utri_ne_ltri : utri F ≠ ltri F := by
  intro h
  have hw : conjSubgroup wElt (utri F) = utri F := by
    rw [conjSubgroup_wElt_utri, h]
  have hmem : wElt ∈ Subgroup.normalizer (utri F : Set SL(2, F)) :=
    mem_normalizer_iff_conjSubgroup_eq.2 hw
  rw [normalizer_utri] at hmem
  exact wElt_not_mem_borel hmem

theorem exists_eq_utri_or_eq_ltri_conj (g : SL(2, F)) :
    conjSubgroup g (utri F) = utri F ∨
      ∃ s : F, conjSubgroup g (utri F) = conjSubgroup (utriElt s) (ltri F) := by
  by_cases hg : g ∈ borel F
  · exact Or.inl (mem_normalizer_iff_conjSubgroup_eq.1 (by rwa [normalizer_utri]))
  · obtain ⟨u, hu, h⟩ := exists_mem_utri_conj_eq_ltri hg
    obtain ⟨s, rfl⟩ := mem_utri_iff.1 hu
    exact Or.inr ⟨s, h⟩

theorem conjSubgroup_torusElt_ltri_conj (a : Fˣ) (s : F) :
    conjSubgroup (torusElt a) (conjSubgroup (utriElt s) (ltri F)) =
      conjSubgroup (utriElt ((a : F) ^ 2 * s)) (ltri F) := by
  have htu : (torusElt a : SL(2, F)) * utriElt s =
      utriElt ((a : F) ^ 2 * s) * torusElt a := by
    have h := torusElt_mul_utriElt_mul_inv a s
    have h' := congrArg (fun x : SL(2, F) => x * torusElt a) h
    simpa [mul_assoc] using h'
  calc conjSubgroup (torusElt a) (conjSubgroup (utriElt s) (ltri F))
      = conjSubgroup ((torusElt a) * utriElt s) (ltri F) :=
        conjSubgroup_conjSubgroup _ _ _
    _ = conjSubgroup (utriElt ((a : F) ^ 2 * s) * torusElt a) (ltri F) := by rw [htu]
    _ = conjSubgroup (utriElt ((a : F) ^ 2 * s))
          (conjSubgroup (torusElt a) (ltri F)) := by
        rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup (utriElt ((a : F) ^ 2 * s)) (ltri F) := by
        rw [conjSubgroup_torusElt_ltri]

theorem exists_torusElt_conj_ltri_conj {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Fˣ, conjSubgroup (torusElt a) (conjSubgroup (utriElt s) (ltri F)) =
      conjSubgroup (utriElt t) (ltri F) := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (t / s)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : t / s = 0 := by simpa using hr
    exact div_ne_zero ht hs h0
  refine ⟨Units.mk0 r hr0, ?_⟩
  rw [conjSubgroup_torusElt_ltri_conj, Units.val_mk0]
  congr 1
  have h2 : r ^ 2 * s = t := by
    have h := hr
    field_simp [hs] at h
    calc r ^ 2 * s = s * r ^ 2 := mul_comm _ _
      _ = t := h.symm
  rw [h2]

theorem exists_mem_normalizer_conjSubgroup_utri_eq_of_ltriConj
    {N : Subgroup SL(2, F)} (hT : torus F ≤ N) {n0 : SL(2, F)} (hn0 : n0 ∈ N)
    {s0 : F} (hs0 : s0 ≠ 0) (hP : conjSubgroup n0 (utri F) = ltriConj s0) :
    ∀ s : F, s ≠ 0 → ∃ k ∈ N, conjSubgroup k (utri F) = ltriConj s := by
  intro s hs
  obtain ⟨a, ha⟩ := exists_torusElt_conj_ltri_conj hs0 hs
  refine ⟨torusElt a * n0,
    Subgroup.mul_mem _ (hT (torusElt_mem_torus a)) hn0, ?_⟩
  calc conjSubgroup (torusElt a * n0) (utri F)
      = conjSubgroup (torusElt a) (conjSubgroup n0 (utri F)) :=
        (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup (torusElt a) (ltriConj s0) := by rw [hP]
    _ = ltriConj s := by simpa [ltriConj] using ha

theorem mem_normalizer_torus_of_conjSubgroup_utri_eq_ltri {N : Subgroup SL(2, F)}
    (hT : torus F ≤ N) (hL : N ⊓ ltri F = ⊥)
    {n : SL(2, F)} (hnN : n ∈ N) (hnL : conjSubgroup n (utri F) = ltri F) :
    n ∈ Subgroup.normalizer (torus F : Set SL(2, F)) := by
  have hNB : N ⊓ Subgroup.normalizer (ltri F : Set SL(2, F)) = torus F :=
    inf_normalizer_ltri_eq_torus hT hL
  have hle : conjSubgroup n (torus F) ≤ torus F := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    have hxN : x ∈ N := by
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN (hT hx)) (N.inv_mem hnN)
    have hxn : x ∈ Subgroup.normalizer (ltri F : Set SL(2, F)) := by
      rw [mem_normalizer_iff_conjSubgroup_eq]
      have h1 : conjSubgroup (n * (n⁻¹ * x * n) * n⁻¹) (ltri F) =
          conjSubgroup n (conjSubgroup (n⁻¹ * x * n) (conjSubgroup n⁻¹ (ltri F))) := by
        rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      rw [hx', h1]
      have h2 : conjSubgroup n⁻¹ (ltri F) = utri F := by
        rw [← hnL, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      rw [h2]
      have h3 : n⁻¹ * x * n ∈ torus F := hx
      have h4 : conjSubgroup (n⁻¹ * x * n) (utri F) = utri F :=
        mem_normalizer_iff_conjSubgroup_eq.1 (by
          rw [normalizer_utri]
          exact torus_le_borel h3)
      rw [h4]
      exact hnL
    rw [← hNB]
    exact ⟨hxN, hxn⟩
  have heq : conjSubgroup n (torus F) = torus F :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  exact mem_normalizer_iff_conjSubgroup_eq.2 heq

theorem false_of_exists_conjSubgroup_utri_eq_ltri (h4 : 4 ≤ Nat.card F)
    {N : Subgroup SL(2, F)} (hT : torus F ≤ N) (hU : N ⊓ utri F = ⊥)
    (hL : N ⊓ ltri F = ⊥)
    (horbit : ∀ s : F, s ≠ 0 →
      ∃ k ∈ N, conjSubgroup k (utri F) = ltriConj s)
    (hLor : ∃ k ∈ N, conjSubgroup k (utri F) = ltri F) : False := by
  obtain ⟨n1, hn1N, hn1L⟩ := hLor
  have hn1norm :=
    mem_normalizer_torus_of_conjSubgroup_utri_eq_ltri hT hL hn1N hn1L
  have hn1T : n1 ∉ torus F := by
    intro h
    have hUn : conjSubgroup n1 (utri F) = utri F :=
      mem_normalizer_iff_conjSubgroup_eq.1 (by
        rw [normalizer_utri]
        exact torus_le_borel h)
    exact utri_ne_ltri (hUn.symm.trans hn1L)
  have hn1sq : n1 * n1 = 1 :=
    mul_self_eq_one_of_mem_normalizer_torus h4 hn1norm hn1T
  have hn11 : n1 ≠ 1 := fun h => hn1T (by rw [h]; exact (torus F).one_mem)
  obtain ⟨P', hP'mem, -⟩ := existsUnique_sylow_of_mul_self_eq_one hn1sq hn11
  obtain ⟨g, hg⟩ := exists_conjSubgroup_utri_eq_of_sylow P'
  have hPorbit : ∃ k ∈ N, (P' : Subgroup SL(2, F)) = conjSubgroup k (utri F) := by
    rcases exists_eq_utri_or_eq_ltri_conj g with hUg | ⟨s, hs⟩
    · exact ⟨1, N.one_mem, by rw [← hg, hUg, conjSubgroup_one]⟩
    · by_cases hs0 : s = 0
      · refine ⟨n1, hn1N, ?_⟩
        rw [← hg, hs, hs0]
        simpa [utriElt_zero, conjSubgroup_one] using hn1L.symm
      · obtain ⟨k, hkN, hk⟩ := horbit s hs0
        exact ⟨k, hkN, by rw [← hg, hs]; exact hk.symm⟩
  obtain ⟨k, hkN, hk⟩ := hPorbit
  rw [hk] at hP'mem
  have hmemU : k⁻¹ * n1 * k ∈ utri F := mem_conjSubgroup.1 hP'mem
  have hmemN : k⁻¹ * n1 * k ∈ N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (N.inv_mem hkN) hn1N) hkN
  have hbot : k⁻¹ * n1 * k ∈ (⊥ : Subgroup SL(2, F)) := by
    rw [← hU]
    exact ⟨hmemN, hmemU⟩
  have hk1 : k⁻¹ * n1 * k = 1 := Subgroup.mem_bot.1 hbot
  have hn11' : n1 = 1 := by
    have h := congrArg (fun x : SL(2, F) => k * x * k⁻¹) hk1
    simpa [mul_assoc] using h
  exact hn11 hn11'

theorem not_exists_conjSubgroup_utri_ne_utri_ne_ltri (h4 : 4 ≤ Nat.card F)
    {N : Subgroup SL(2, F)} (hT : torus F ≤ N) (hU : N ⊓ utri F = ⊥)
    (hL : N ⊓ ltri F = ⊥) :
    ¬ ∃ n ∈ N, conjSubgroup n (utri F) ≠ utri F ∧
      conjSubgroup n (utri F) ≠ ltri F := by
  rintro ⟨n0, hn0N, hn0U, hn0L⟩
  obtain ⟨s0, hs0eq⟩ : ∃ s0 : F, conjSubgroup n0 (utri F) = ltriConj s0 := by
    rcases exists_eq_utri_or_eq_ltri_conj n0 with hU' | ⟨s, hs⟩
    · exact (hn0U hU').elim
    · exact ⟨s, by simpa [ltriConj] using hs⟩
  have hs00 : s0 ≠ 0 := by
    rintro rfl
    exact hn0L (by rw [hs0eq, ltriConj_zero])
  have horbit := exists_mem_normalizer_conjSubgroup_utri_eq_of_ltriConj hT hn0N hs00 hs0eq
  by_cases hLor : ∃ k ∈ N, conjSubgroup k (utri F) = ltri F
  · exact false_of_exists_conjSubgroup_utri_eq_ltri h4 hT hU hL horbit hLor
  · have hLfix : ∀ n : SL(2, F),
        ltri F = conjSubgroup n⁻¹ (conjSubgroup n (ltri F)) := by
      intro n
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hfix : ∀ n ∈ N, conjSubgroup n (ltri F) = ltri F := by
      intro n hnN
      by_contra hne
      have hconj : conjSubgroup n (ltri F) = conjSubgroup (n * wElt) (utri F) := by
        rw [← conjSubgroup_wElt_utri, conjSubgroup_conjSubgroup]
      rcases exists_eq_utri_or_eq_ltri_conj (n * wElt) with hUg | ⟨s, hs⟩
      · apply hLor
        refine ⟨n⁻¹, N.inv_mem hnN, ?_⟩
        calc conjSubgroup n⁻¹ (utri F) =
              conjSubgroup n⁻¹ (conjSubgroup n (ltri F)) := by rw [hconj, hUg]
          _ = ltri F := (hLfix n).symm
      · have hs0 : s ≠ 0 := by
          rintro rfl
          apply hne
          simpa [utriElt_zero, conjSubgroup_one] using hconj.trans hs
        obtain ⟨k, hkN, hk⟩ := horbit s hs0
        apply hLor
        refine ⟨n⁻¹ * k, Subgroup.mul_mem _ (N.inv_mem hnN) hkN, ?_⟩
        have hLs : ltriConj s = conjSubgroup n (ltri F) := (hconj.trans hs).symm
        calc conjSubgroup (n⁻¹ * k) (utri F)
            = conjSubgroup n⁻¹ (conjSubgroup k (utri F)) :=
              (conjSubgroup_conjSubgroup _ _ _).symm
          _ = conjSubgroup n⁻¹ (ltriConj s) := by rw [hk]
          _ = conjSubgroup n⁻¹ (conjSubgroup n (ltri F)) := by rw [hLs]
          _ = ltri F := (hLfix n).symm
    have hNleT : N ≤ torus F := by
      intro n hnN
      have hnNorm : n ∈ Subgroup.normalizer (ltri F : Set SL(2, F)) :=
        mem_normalizer_iff_conjSubgroup_eq.2 (hfix n hnN)
      have hmem : n ∈ N ⊓ Subgroup.normalizer (ltri F : Set SL(2, F)) := ⟨hnN, hnNorm⟩
      rwa [inf_normalizer_ltri_eq_torus hT hL] at hmem
    have hn0T : n0 ∈ torus F := hNleT hn0N
    have hUn : conjSubgroup n0 (utri F) = utri F :=
      mem_normalizer_iff_conjSubgroup_eq.1 (by
        rw [normalizer_utri]
        exact torus_le_borel hn0T)
    exact hn0U hUn

theorem le_normalizer_torus_or_eq_top (h4 : 4 ≤ Nat.card F) {N : Subgroup SL(2, F)}
    (hT : torus F ≤ N)
    (hO : ∀ P : Subgroup SL(2, F), P ≤ N →
      N ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥) :
    N ≤ Subgroup.normalizer (torus F : Set SL(2, F)) ∨ N = ⊤ := by
  by_cases hU : N ⊓ utri F = ⊥
  · by_cases hL : N ⊓ ltri F = ⊥
    · left
      have hno := not_exists_conjSubgroup_utri_ne_utri_ne_ltri h4 hT hU hL
      intro n hnN
      by_cases hnU : conjSubgroup n (utri F) = utri F
      · have hnNorm : n ∈ Subgroup.normalizer (utri F : Set SL(2, F)) :=
          mem_normalizer_iff_conjSubgroup_eq.2 hnU
        have hnB : n ∈ borel F := by
          rw [← normalizer_utri]
          exact hnNorm
        have hmem : n ∈ N ⊓ borel F := ⟨hnN, hnB⟩
        rw [inf_borel_eq_torus hT hU] at hmem
        exact Subgroup.le_normalizer hmem
      · have hnL : conjSubgroup n (utri F) = ltri F := by
          by_contra hnL
          exact hno ⟨n, hnN, hnU, hnL⟩
        exact mem_normalizer_torus_of_conjSubgroup_utri_eq_ltri hT hL hnN hnL
    · right
      exact eq_top_of_inf_ltri_ne_bot hT hO hL
  · right
    exact eq_top_of_inf_utri_ne_bot hT hO hU

theorem card_dvd_or_eq_top (h4 : 4 ≤ Nat.card F) {N : Subgroup SL(2, F)}
    (hT : torus F ≤ N)
    (hO : ∀ P : Subgroup SL(2, F), P ≤ N →
      N ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥) :
    Nat.card N ∣ 2 * (Nat.card F - 1) ∨ N = ⊤ := by
  rcases le_normalizer_torus_or_eq_top h4 hT hO with hle | htop
  · left
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [card_normalizer_torus h4] at hdvd
  · exact Or.inr htop

theorem exists_conj_mem_torus_of_orderOf (h4 : 4 ≤ Nat.card F) {g : SL(2, F)}
    (hord : orderOf g = Nat.card F - 1) :
    ∃ P : SL(2, F), P⁻¹ * g * P ∈ torus F := by
  letI : Fintype F := Fintype.ofFinite F
  have hqpos : 1 ≤ Nat.card F := Nat.card_pos
  have hpow : g ^ Fintype.card F = g := by
    have h1 : g ^ (Nat.card F - 1) = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one g
    calc g ^ Fintype.card F = g ^ Nat.card F := by rw [Nat.card_eq_fintype_card]
      _ = g ^ ((Nat.card F - 1) + 1) := by rw [Nat.sub_add_cancel hqpos]
      _ = g := by rw [pow_succ, h1, one_mul]
  have hmat : g.1 ^ Fintype.card F = g.1 := by
    have h := congrArg Subtype.val hpow
    simpa [Matrix.SpecialLinearGroup.coe_pow] using h
  obtain ⟨a, hdet⟩ := exists_det_sub_eq_zero F g.1 hmat
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : (g.1 - Matrix.scalar (Fin 2) (0 : F)).det = 1 := by
      simpa [Matrix.scalar_apply] using Matrix.SpecialLinearGroup.det_coe g
    rw [h1] at hdet
    exact one_ne_zero hdet
  have ha2 : a * a ≠ 1 := by
    intro ha2
    have ha1 : a = 1 := CharTwo.sq_injective (by simpa [pow_two] using ha2)
    have htrace := trace_eq_of_det_sub_eq_zero hdet
    have htr : g 0 0 + g 1 1 = 0 := by
      have h := htrace
      rw [ha1, one_mul, mul_one, CharTwo.add_self_eq_zero (1 : F)] at h
      simpa using h
    have hgg : g * g = 1 := mul_self_eq_one_of_trace_eq_zero htr
    have hdvd : Nat.card F - 1 ∣ 2 := by
      have h := orderOf_dvd_of_pow_eq_one (x := g) (n := 2) (by rw [pow_two]; exact hgg)
      rwa [hord] at h
    have hle : Nat.card F - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hne : a ≠ a⁻¹ := by
    intro h
    apply ha2
    have hv : a = (a : F)⁻¹ := by simpa using h
    nth_rewrite 2 [hv]
    exact mul_inv_cancel₀ ha0
  have htr : g 0 0 + g 1 1 = a + a⁻¹ := by
    have h := trace_eq_of_det_sub_eq_zero hdet
    field_simp [ha0] at h ⊢
    linear_combination h
  obtain ⟨P, hP⟩ := exists_conj_mem_diagSub_of_eigenvalue (g := g) (a := a) (b := a⁻¹)
    (mul_inv_cancel₀ ha0) hne htr
  exact ⟨P, hP⟩

theorem exists_eq_conjSubgroup_torus (h4 : 4 ≤ Nat.card F) {D : Subgroup SL(2, F)}
    (hD : IsCyclic D) (hc : Nat.card D = Nat.card F - 1) :
    ∃ g : SL(2, F), D = conjSubgroup g (torus F) := by
  obtain ⟨x, hxgen⟩ := hD.exists_generator
  let g : SL(2, F) := (x : SL(2, F))
  have hord : orderOf g = Nat.card F - 1 := by
    calc orderOf g = orderOf x := Subgroup.orderOf_coe x
      _ = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hxgen
      _ = Nat.card F - 1 := hc
  have hDgen : D = Subgroup.zpowers g := by
    apply le_antisymm
    · intro y hy
      have hmem := hxgen ⟨y, hy⟩
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      have h := congrArg (fun z : D => (z : SL(2, F))) hk
      simpa [g] using h
    · rw [Subgroup.zpowers_le]
      exact x.2
  obtain ⟨P, hP⟩ := exists_conj_mem_torus_of_orderOf h4 hord
  refine ⟨P, ?_⟩
  have hP' : g ∈ conjSubgroup P (torus F) := mem_conjSubgroup.2 hP
  have hle : D ≤ conjSubgroup P (torus F) := by
    rw [hDgen]
    exact Subgroup.zpowers_le.mpr hP'
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup, card_torus, hc])

theorem card_dvd_or_eq_top_of_conj (h4 : 4 ≤ Nat.card F) (g : SL(2, F))
    {N : Subgroup SL(2, F)} (hT : conjSubgroup g (torus F) ≤ N)
    (hO : ∀ P : Subgroup SL(2, F), P ≤ N →
      N ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥) :
    Nat.card N ∣ 2 * (Nat.card F - 1) ∨ N = ⊤ := by
  let M : Subgroup SL(2, F) := conjSubgroup g⁻¹ N
  have hgM : conjSubgroup g M = N := by
    change (N.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = N
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id SL(2, F) := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      change (MulAut.conj g) ((MulAut.conj g⁻¹) x) = x
      simp [MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hTM : torus F ≤ M := by
    have hmono : conjSubgroup g⁻¹ (conjSubgroup g (torus F)) ≤
        conjSubgroup g⁻¹ N := by
      simpa [conjSubgroup] using
        (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hT)
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hmono
  have hO' : ∀ P : Subgroup SL(2, F), P ≤ M →
      M ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥ := by
    intro P hPM hPN hPp
    let Q : Subgroup SL(2, F) := conjSubgroup g P
    have hQN : Q ≤ N := by
      have hmono : conjSubgroup g P ≤ conjSubgroup g M := by
        simpa [conjSubgroup] using (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hPM)
      rwa [hgM] at hmono
    have hQnorm : N ≤ Subgroup.normalizer (Q : Set SL(2, F)) := by
      have hnorm : conjSubgroup g (Subgroup.normalizer (P : Set SL(2, F))) =
          Subgroup.normalizer (Q : Set SL(2, F)) := by
        simpa [Q, conjSubgroup] using
          (Subgroup.map_normalizer_eq_of_bijective P
            (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective)
      have hmono : conjSubgroup g M ≤
          conjSubgroup g (Subgroup.normalizer (P : Set SL(2, F))) := by
        simpa [conjSubgroup] using
          (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hPN)
      rwa [hgM, hnorm] at hmono
    have hQp : IsPGroup 2 Q := hPp.map (MulAut.conj g).toMonoidHom
    have hQbot : Q = ⊥ := hO Q hQN hQnorm hQp
    have hPbot : P = ⊥ := by
      have hPQ : P = conjSubgroup g⁻¹ Q := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      rw [hPQ, hQbot, conjSubgroup_bot]
    exact hPbot
  rcases card_dvd_or_eq_top h4 hTM hO' with hdvd | htop
  · left
    rwa [card_conjSubgroup] at hdvd
  · right
    rw [← hgM, htop, conjSubgroup_top]

theorem isPGroup_eq_bot_of_le_sup {Γ₁ D : Subgroup SL(2, F)}
    (hNorm : Γ₁ ⊔ D ≤ Subgroup.normalizer (Γ₁ : Set SL(2, F)))
    (hDcard : Nat.card D = Nat.card F - 1)
    (hO : ∀ P : Subgroup SL(2, F), P ≤ Γ₁ →
      Γ₁ ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥) :
    ∀ P : Subgroup SL(2, F), P ≤ Γ₁ ⊔ D →
      Γ₁ ⊔ D ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥ := by
  let N : Subgroup SL(2, F) := Γ₁ ⊔ D
  have hΓN : Γ₁ ≤ N := le_sup_left
  have hDN : D ≤ N := le_sup_right
  let H : Subgroup N := Γ₁.subgroupOf N
  haveI hHn : H.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΓN).mpr hNorm
  have hsup : H ⊔ D.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hΓN hDN]
    exact Subgroup.subgroupOf_self N
  have hrel : H.relIndex ⊤ = H.relIndex (D.subgroupOf N) := by
    have h := Subgroup.relIndex_sup_left (H := D.subgroupOf N) (K := H)
    rwa [hsup] at h
  have hdvdD : H.index ∣ Nat.card D := by
    rw [← Subgroup.relIndex_top_right H, hrel]
    have h := Subgroup.relIndex_dvd_card H (D.subgroupOf N)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv] at h
  have hdvd : H.index ∣ Nat.card F - 1 := by
    rwa [hDcard] at hdvdD
  intro P hPN hPnorm hPp
  have hbot : P ⊓ Γ₁ = ⊥ := by
    refine hO (P ⊓ Γ₁) inf_le_right ?_ hPp.to_inf_left
    exact (le_inf (fun x hx => hPnorm (hΓN hx)) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hPp ⟨x, hx⟩
  have hpowH : (⟨x, hPN hx⟩ : N) ^ H.relIndex ⊤ ∈ H :=
    H.pow_relIndex_mem (K := ⊤) (g := ⟨x, hPN hx⟩) (Subgroup.mem_top _)
  have hpowΓ : x ^ (Nat.card F - 1) ∈ Γ₁ := by
    obtain ⟨c, hc⟩ := hdvd
    have hmem : (⟨x, hPN hx⟩ : N) ^ (Nat.card F - 1) ∈ H := by
      rw [hc, pow_mul]
      refine Subgroup.pow_mem H ?_ c
      simpa [Subgroup.relIndex_top_right] using hpowH
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hxpow1 : x ^ (Nat.card F - 1) = 1 := by
    have hmem : x ^ (Nat.card F - 1) ∈ (⊥ : Subgroup SL(2, F)) := by
      rw [← hbot]
      exact ⟨Subgroup.pow_mem P hx _, hpowΓ⟩
    exact Subgroup.mem_bot.mp hmem
  have hxpow1' : (⟨x, hx⟩ : P) ^ (Nat.card F - 1) = 1 := by
    apply Subtype.ext
    simpa using hxpow1
  have hdvd2 : 2 ^ k ∣ Nat.card F - 1 := by
    rw [← hk]
    exact orderOf_dvd_of_pow_eq_one hxpow1'
  letI : Fintype F := Fintype.ofFinite F
  have hq2 : 2 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.dvd_of_mod_eq_zero (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hqpos : 0 < Nat.card F := Nat.card_pos
  have hk0 : k = 0 := by
    by_contra hkne
    have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hkne
    obtain ⟨m, hm⟩ := hq2
    obtain ⟨c, hc⟩ := h2dvd.trans hdvd2
    omega
  have hone : (⟨x, hx⟩ : P) = 1 :=
    orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
  simpa using congrArg Subtype.val hone

theorem card_dvd_of_mem_normalizer (h4 : 4 ≤ Nat.card F) {Γ₁ : Subgroup SL(2, F)}
    {h : SL(2, F)} (hord : orderOf h = Nat.card F - 1)
    (hN : h ∈ Subgroup.normalizer (Γ₁ : Set SL(2, F)))
    (hO : ∀ P : Subgroup SL(2, F), P ≤ Γ₁ →
      Γ₁ ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥)
    (htop : Γ₁ ≠ ⊤) : Nat.card Γ₁ ∣ 2 * (Nat.card F - 1) := by
  let D : Subgroup SL(2, F) := Subgroup.zpowers h
  have hDcyc : IsCyclic D := Subgroup.isCyclic_zpowers h
  have hDcard : Nat.card D = Nat.card F - 1 := by
    rw [Nat.card_zpowers, hord]
  obtain ⟨g, hg⟩ := exists_eq_conjSubgroup_torus (F := F) h4 hDcyc hDcard
  let N : Subgroup SL(2, F) := Γ₁ ⊔ D
  have hΓN : Γ₁ ≤ N := le_sup_left
  have hDN : D ≤ N := le_sup_right
  have hnormN : N ≤ Subgroup.normalizer (Γ₁ : Set SL(2, F)) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hN)
  have hON := isPGroup_eq_bot_of_le_sup hnormN hDcard hO
  rcases card_dvd_or_eq_top_of_conj (F := F) h4 g (by rw [← hg]; exact hDN) hON with hdvdN | htopN
  · exact (Subgroup.card_dvd_of_le hΓN).trans hdvdN
  · have hnormal : Subgroup.normalizer (Γ₁ : Set SL(2, F)) = ⊤ := by
      rw [eq_top_iff, ← htopN]
      exact hnormN
    haveI : Γ₁.Normal := Subgroup.normalizer_eq_top_iff.mp hnormal
    rcases CFSG.RankThree.GF2n.Smith81.D2.sl2_normal_eq_bot_or_top (K := F) h4 Γ₁ with
      hbot | htopN'
    · rw [hbot, Subgroup.card_bot]
      exact one_dvd _
    · exact absurd htopN' htop

theorem orderOf_torusElt (a : Fˣ) : orderOf (torusElt a) = orderOf a :=
  orderOf_injective (CFSG.Glauberman.Dickson.splitTorusSLHom F) torusElt_injective a

theorem orderOf_pow_half {δ : F} (hδord : orderOf δ = Nat.card F - 1) :
    orderOf (δ ^ (Nat.card F / 2)) = Nat.card F - 1 := by
  letI : Fintype F := Fintype.ofFinite F
  have hδcard : δ ^ Nat.card F = δ := by
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hqeven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hqhalf : Nat.card F / 2 * 2 = Nat.card F := by
    obtain ⟨m, hm⟩ := hqeven
    omega
  have hδpow : δ ^ (Nat.card F - 1) = 1 := by
    rw [← hδord]
    exact pow_orderOf_eq_one δ
  have hs_dvd : orderOf (δ ^ (Nat.card F / 2)) ∣ Nat.card F - 1 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, hδpow, one_pow]
  have hs2 : δ ^ (Nat.card F / 2) * δ ^ (Nat.card F / 2) = δ := by
    rw [← pow_two, ← pow_mul, hqhalf, hδcard]
  have hδdvd : Nat.card F - 1 ∣ orderOf (δ ^ (Nat.card F / 2)) := by
    have hs2' : (δ ^ (Nat.card F / 2)) ^ 2 = δ := by
      rw [pow_two]
      exact hs2
    have hp : δ ^ orderOf (δ ^ (Nat.card F / 2)) = 1 := by
      calc δ ^ orderOf (δ ^ (Nat.card F / 2))
          = ((δ ^ (Nat.card F / 2)) ^ 2) ^ orderOf (δ ^ (Nat.card F / 2)) := by rw [hs2']
        _ = ((δ ^ (Nat.card F / 2)) ^ orderOf (δ ^ (Nat.card F / 2))) ^ 2 := by
              rw [← pow_mul, mul_comm, pow_mul]
        _ = 1 := by rw [pow_orderOf_eq_one, one_pow]
    have := orderOf_dvd_of_pow_eq_one hp
    rwa [hδord] at this
  exact Nat.dvd_antisymm hs_dvd hδdvd

theorem trace_eq_add_inv_of_eigenvalue {h : SL(2, F)} {u₀ : Fin 2 → F} (hu₀ : u₀ ≠ 0)
    {lam : F} (heigen : Matrix.vecMul u₀ (h : Matrix (Fin 2) (Fin 2) F) = lam • u₀)
    (hlam0 : lam ≠ 0) :
    (h : Matrix (Fin 2) (Fin 2) F) 0 0 + (h : Matrix (Fin 2) (Fin 2) F) 1 1 =
      lam + lam⁻¹ := by
  have hvec : Matrix.vecMul u₀
      ((h : Matrix (Fin 2) (Fin 2) F) - Matrix.scalar (Fin 2) lam) = 0 := by
    rw [Matrix.vecMul_sub, heigen,
      show Matrix.scalar (Fin 2) lam = lam • (1 : Matrix (Fin 2) (Fin 2) F) by
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.one_apply, hij],
      Matrix.vecMul_smul, Matrix.vecMul_one, sub_self]
  have hdetlam : ((h : Matrix (Fin 2) (Fin 2) F) - Matrix.scalar (Fin 2) lam).det = 0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨u₀, hu₀, hvec⟩
  have h := trace_eq_of_det_sub_eq_zero hdetlam
  field_simp [hlam0] at h ⊢
  linear_combination h

theorem orderOf_eq_card_of_diagonal (h4 : 4 ≤ Nat.card F) {h : SL(2, F)} {lam : F}
    (h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (htr : (h : Matrix (Fin 2) (Fin 2) F) 0 0 + (h : Matrix (Fin 2) (Fin 2) F) 1 1 =
      lam + lam⁻¹)
    (hlamord : orderOf lam = Nat.card F - 1) : orderOf h = Nat.card F - 1 := by
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hp := pow_orderOf_eq_one lam
    rw [hlamord, h0] at hp
    have hq1 : 0 < Nat.card F - 1 := by omega
    rw [zero_pow (Nat.ne_of_gt hq1)] at hp
    exact zero_ne_one hp
  let x : F := (h : Matrix (Fin 2) (Fin 2) F) 0 0
  have hxy : x * (h : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe h
    rw [Matrix.det_fin_two, h10, h01] at hd
    simpa [x] using hd
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hsum : x + (h : Matrix (Fin 2) (Fin 2) F) 1 1 = lam + lam⁻¹ := by
    simpa [x] using htr
  have hfac : (x + lam) * (x * lam + 1) = 0 := by
    have hy : (h : Matrix (Fin 2) (Fin 2) F) 1 1 = x⁻¹ :=
      eq_inv_of_mul_eq_one_right hxy
    rw [hy] at hsum
    have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
    field_simp [hx0, hlam0] at hsum ⊢
    linear_combination hsum + (x * lam ^ 2 + x) * h2F
  have hxcase : x = lam ∨ x = lam⁻¹ := by
    rcases mul_eq_zero.mp hfac with h | h
    · left
      have h' : x = -lam := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at h'
    · right
      have h' : x * lam = -1 := by linear_combination h
      rw [CharTwo.neg_eq] at h'
      exact eq_inv_of_mul_eq_one_left h'
  have hhtor : h = torusElt (Units.mk0 x hx0) := by
    apply CFSG.GH74.GLS.IVK.L2Torus.sl2_ext
    · rw [torusElt_apply_00, Units.val_mk0]
    · rw [torusElt_apply_01, h01]
    · rw [torusElt_apply_10, h10]
    · rw [torusElt_apply_11, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact eq_inv_of_mul_eq_one_right hxy
  have hunitsx : orderOf (Units.mk0 x hx0) = orderOf x := by
    simpa using (orderOf_units (y := Units.mk0 x hx0)).symm
  rw [hhtor, orderOf_torusElt, hunitsx]
  rcases hxcase with hxcase | hxcase
  · rw [hxcase]
    exact hlamord
  · rw [hxcase, CFSG.RankThree.GF2n.Stroth80.FieldModel.orderOf_inv_field]
    exact hlamord

theorem orderOf_eq_card_of_eigenvalue (h4 : 4 ≤ Nat.card F) {h : SL(2, F)}
    {u₀ : Fin 2 → F} (hu₀ : u₀ ≠ 0) {lam : F}
    (heigen : Matrix.vecMul u₀ (h : Matrix (Fin 2) (Fin 2) F) = lam • u₀)
    (hlamord : orderOf lam = Nat.card F - 1) : orderOf h = Nat.card F - 1 := by
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hp := pow_orderOf_eq_one lam
    rw [hlamord, h0] at hp
    have hq1 : 0 < Nat.card F - 1 := by omega
    rw [zero_pow (Nat.ne_of_gt hq1)] at hp
    exact zero_ne_one hp
  have hne : lam ≠ lam⁻¹ := by
    intro h
    have hsq : lam * lam = 1 := by
      nth_rewrite 2 [h]
      exact mul_inv_cancel₀ hlam0
    have hdvd : orderOf lam ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rwa [pow_two]
    rw [hlamord] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have htr := trace_eq_add_inv_of_eigenvalue hu₀ heigen hlam0
  have hab : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam0
  have htor : dg lam lam⁻¹ hab = torusElt (Units.mk0 lam hlam0) := by
    apply CFSG.GH74.GLS.IVK.L2Torus.sl2_ext
    · rw [dg_apply_00, torusElt_apply_00, Units.val_mk0]
    · simp [dg, sl2, torusElt_apply_01]
    · simp [dg, sl2, torusElt_apply_10]
    · rw [dg_apply_11, torusElt_apply_11, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hunits : orderOf (Units.mk0 lam hlam0) = orderOf lam := by
    simpa using (orderOf_units (y := Units.mk0 lam hlam0)).symm
  by_cases hz : (h : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0
  · obtain ⟨P, hP⟩ := exists_conj_dg_of_ne_zero_10 (g := h) hab hne htr hz
    have hsem : SemiconjBy P⁻¹ h (dg lam lam⁻¹ hab) := by
      rw [SemiconjBy, ← hP]
      group
    rw [SemiconjBy.orderOf_eq P⁻¹ hsem, htor, orderOf_torusElt, hunits, hlamord]
  · push Not at hz
    by_cases hz01 : (h : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0
    · obtain ⟨P, hP⟩ := exists_conj_mem_diagSub_of_ne_zero_01 (g := h) hab hne htr hz01
      have hsem : SemiconjBy P⁻¹ h (dg lam lam⁻¹ hab) := by
        rw [SemiconjBy, ← hP]
        group
      rw [SemiconjBy.orderOf_eq P⁻¹ hsem, htor, orderOf_torusElt, hunits, hlamord]
    · push Not at hz01
      exact orderOf_eq_card_of_diagonal h4 hz hz01 htr hlamord

theorem exists_smul_mem_of_eigenvector {H : GL (Fin 2) F} {u₀ : Fin 2 → F}
    {μ : F} (hμ : Matrix.vecMul u₀ (H : Matrix (Fin 2) (Fin 2) F) = μ • u₀)
    (hdet : orderOf (H : Matrix (Fin 2) (Fin 2) F).det = Nat.card F - 1)
    (hrel : μ * μ * (H : Matrix (Fin 2) (Fin 2) F).det = 1 ∨ μ = 1) :
    ∃ (r : F) (h : SL(2, F)) (lam : F), r ≠ 0 ∧
      (h : Matrix (Fin 2) (Fin 2) F) = r • (H : Matrix (Fin 2) (Fin 2) F) ∧
      Matrix.vecMul u₀ (h : Matrix (Fin 2) (Fin 2) F) = lam • u₀ ∧
      orderOf lam = Nat.card F - 1 := by
  let M : Matrix (Fin 2) (Fin 2) F := (H : Matrix (Fin 2) (Fin 2) F)
  let δ : F := M.det
  have hδord : orderOf δ = Nat.card F - 1 := hdet
  have hδ0 : δ ≠ 0 := by
    simpa [δ, M] using Matrix.GeneralLinearGroup.det_ne_zero H
  letI : Fintype F := Fintype.ofFinite F
  have hδcard : δ ^ Nat.card F = δ := by
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hqeven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hqhalf : Nat.card F / 2 * 2 = Nat.card F := by
    obtain ⟨m, hm⟩ := hqeven
    omega
  let s : F := δ ^ (Nat.card F / 2)
  have hs2 : s * s = δ := by
    rw [← pow_two, show s = δ ^ (Nat.card F / 2) from rfl, pow_two, ← pow_add,
      show Nat.card F / 2 + Nat.card F / 2 = Nat.card F by omega, hδcard]
  have hs0 : s ≠ 0 := by
    intro hs
    apply hδ0
    rw [← hs2, hs, mul_zero]
  let r : F := s⁻¹
  have hr0 : r ≠ 0 := inv_ne_zero hs0
  have hr2δ : r * r * δ = 1 := by
    rw [show r = s⁻¹ from rfl, ← hs2]
    field_simp
  have hhr : (r • M).det = 1 := by
    rw [Matrix.det_smul, show Fintype.card (Fin 2) = 2 by norm_num, show M.det = δ from rfl,
      pow_two]
    exact hr2δ
  let h : SL(2, F) := ⟨r • M, hhr⟩
  have hcoe : (h : Matrix (Fin 2) (Fin 2) F) = r • M := rfl
  let lam : F := r * μ
  have hlam_eigen : Matrix.vecMul u₀ (h : Matrix (Fin 2) (Fin 2) F) = lam • u₀ := by
    rw [hcoe, Matrix.vecMul_smul, hμ, smul_smul]
  have hsord : orderOf s = Nat.card F - 1 := by
    rw [show s = δ ^ (Nat.card F / 2) from rfl]
    exact orderOf_pow_half hδord
  have hlamcase : lam = δ⁻¹ ∨ lam = s⁻¹ := by
    rcases hrel with hrel | hμ1
    · left
      have hμ2 : μ * μ = δ⁻¹ := eq_inv_of_mul_eq_one_left hrel
      have hlam2 : lam * lam = δ⁻¹ * δ⁻¹ := by
        rw [show lam = s⁻¹ * μ from rfl, ← hs2]
        field_simp [hs0]
        rw [pow_two, hs2, pow_two, hμ2]
        exact mul_inv_cancel₀ hδ0
      have hpow : lam ^ 2 = (δ⁻¹) ^ 2 := by simpa [pow_two] using hlam2
      exact CharTwo.sq_injective hpow
    · right
      rw [show lam = r * μ from rfl, hμ1, mul_one]
  have hlamord : orderOf lam = Nat.card F - 1 := by
    rcases hlamcase with hcase | hcase
    · rw [hcase, CFSG.RankThree.GF2n.Stroth80.FieldModel.orderOf_inv_field, hδord]
    · rw [hcase, CFSG.RankThree.GF2n.Stroth80.FieldModel.orderOf_inv_field, hsord]
  exact ⟨r, h, lam, hr0, rfl, hlam_eigen, hlamord⟩

theorem exists_smul_mem_orderOf (h4 : 4 ≤ Nat.card F) {H : GL (Fin 2) F} {u₀ : Fin 2 → F}
    (hu₀ : u₀ ≠ 0) {μ : F} (hμ : Matrix.vecMul u₀ (H : Matrix (Fin 2) (Fin 2) F) = μ • u₀)
    (hdet : orderOf (H : Matrix (Fin 2) (Fin 2) F).det = Nat.card F - 1)
    (hrel : μ * μ * (H : Matrix (Fin 2) (Fin 2) F).det = 1 ∨ μ = 1) :
    ∃ (r : F) (h : SL(2, F)), r ≠ 0 ∧
      (h : Matrix (Fin 2) (Fin 2) F) = r • (H : Matrix (Fin 2) (Fin 2) F) ∧
      orderOf h = Nat.card F - 1 := by
  obtain ⟨r, h, lam, hr0, hcoe, heigen, hlamord⟩ :=
    exists_smul_mem_of_eigenvector hμ hdet hrel
  exact ⟨r, h, hr0, hcoe, orderOf_eq_card_of_eigenvalue h4 hu₀ heigen hlamord⟩

end CFSG.RankThree.GF2n.Smith81.SL2Torus
