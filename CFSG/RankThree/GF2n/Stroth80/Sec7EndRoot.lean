module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section OmegaThree

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

private theorem endgE_conj_one : conjSubgroup (1 : X) A = A := by
  ext x
  simp [mem_conjSubgroup]

private theorem endgE_conj_mem {g a : X} (ha : a ∈ A) : g * a * g⁻¹ ∈ conjSubgroup g A := by
  rw [mem_conjSubgroup, show g⁻¹ * (g * a * g⁻¹) * g = a by group]
  exact ha

private theorem endgE_conj_ne_one {g a : X} (ha1 : a ≠ 1) : g * a * g⁻¹ ≠ 1 := by
  intro h
  apply ha1
  calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
    _ = 1 := by rw [h, mul_one, inv_mul_cancel]

private theorem endgE_exists_of_mem {g x : X} (hx : x ∈ conjSubgroup g A) (hx1 : x ≠ 1) :
    ∃ a ∈ A, a ≠ 1 ∧ g * a * g⁻¹ = x := by
  refine ⟨g⁻¹ * x * g, mem_conjSubgroup.mp hx, ?_, by group⟩
  intro h
  apply hx1
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

private theorem endgE_exists_ne_one (hO : EndOmegaHyp A) : ∃ a ∈ A, a ≠ 1 := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO.ne_bot
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

private theorem endgE_conj_eq_of_mem (hO : EndOmegaHyp A) {g u : X} (hu : u ∈ A) (hu1 : u ≠ 1)
    (hug : u ∈ conjSubgroup g A) : conjSubgroup g A = A := by
  have hn : g⁻¹ ∈ Subgroup.normalizer (A : Set X) :=
    hO.ti g⁻¹ u hu hu1 (by rw [inv_inv]; exact mem_conjSubgroup.mp hug)
  ext x
  rw [mem_conjSubgroup]
  have hx := Subgroup.mem_normalizer_iff.mp hn x
  rw [inv_inv] at hx
  exact hx.symm

private theorem endgE_inOmega_of_commute (hO : EndOmegaHyp A) {k a x : X} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hx : x ∈ conjSubgroup k A) (hx1 : x ≠ 1) (hc : a * x = x * a) :
    InOmegaA A k := by
  have ha' : a ∈ conjSubgroup (1 : X) A := by rw [endgE_conj_one]; exact ha
  intro z hz y hy
  have hz' : z ∈ conjSubgroup (1 : X) A := by rw [endgE_conj_one]; exact hz
  exact hO.n1 1 k a ha' ha1 x hx hx1 hc z hz' y hy

private theorem endgE_ne_one_of_isConj {t τ : X} (ht1 : t ≠ 1) (h : IsConj t τ) : τ ≠ 1 := by
  rintro rfl
  exact ht1 (isConj_one_left.mp h)

private theorem endgE_mul_self_of_mem (hO : EndOmegaHyp A) {g x : X} (hx : x ∈ conjSubgroup g A) :
    x * x = 1 := by
  have hsq := hO.sq _ (mem_conjSubgroup.mp hx)
  calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [hsq, mul_one, mul_inv_cancel]

private theorem endgE_le_egen {k : X} (hk : InOmegaA A k) : conjSubgroup k A ≤ EgenX A :=
  le_iSup₂_of_le (f := fun g (_ : InOmegaA A g) => conjSubgroup g A) k hk le_rfl

theorem endg_exists_ne (hO : EndOmegaHyp A) (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) :
    ∃ g : X, InOmegaA A g ∧ conjSubgroup g A ≠ A := by
  by_contra hcon
  push_neg at hcon
  have hle : EgenX A ≤ A := iSup₂_le fun g hg => (hcon g hg).le
  have hcomm : ⁅A, A⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hO.comm a ha b hb
  apply hne
  exact eq_bot_iff.mpr ((Subgroup.commutator_mono hle hle).trans hcomm.le)

theorem endg_six_five_a (hO : EndOmegaHyp A) (F : OmegaPart1 A) (G : OmegaPart2 A)
    (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) {s t : X} (hs : s ∈ A) (ht : t ∈ A) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) : IsConj s t := by
  by_cases hst : s = t
  · subst hst
    exact IsConj.refl _
  obtain ⟨g, hg, hgA⟩ := endg_exists_ne hO hne
  obtain ⟨a, ha, ha1⟩ := endgE_exists_ne_one hO
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ conjSubgroup g A, x ≠ 1 :=
    ⟨g * a * g⁻¹, endgE_conj_mem ha, endgE_conj_ne_one ha1⟩
  have hxs : s * x = x * s := hg s hs x hx
  have hxt : t * x = x * t := hg t ht x hx
  have hxA : x ∉ A := fun h => hgA (endgE_conj_eq_of_mem hO h hx1 hx)
  have hxt1 : x * t ≠ 1 := by
    intro h
    apply hxA
    rw [eq_inv_of_mul_eq_one_left h]
    exact A.inv_mem ht
  have hxs1 : x * s ≠ 1 := by
    intro h
    apply hxA
    rw [eq_inv_of_mul_eq_one_left h]
    exact A.inv_mem hs
  have hne₁ : conjSubgroup g A ≠ conjSubgroup (1 : X) A := by
    rw [endgE_conj_one]
    exact hgA
  have hc₁ : ∀ z ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup (1 : X) A, z * y = y * z := by
    intro z hz y hy
    rw [endgE_conj_one] at hy
    exact (hg y hy z hz).symm
  have hs' : s ∈ conjSubgroup (1 : X) A := by rw [endgE_conj_one]; exact hs
  have ht' : t ∈ conjSubgroup (1 : X) A := by rw [endgE_conj_one]; exact ht
  obtain ⟨w₁, hw₁⟩ := G.six_four_gen hne hne₁ hc₁ ht' ht1 x hx
  obtain ⟨w₂, hw₂⟩ := G.six_four_gen hne hne₁ hc₁ hs' hs1 x hx
  have hxtm : x * t ∈ conjSubgroup w₁ A := by
    rw [← hw₁]
    exact endgE_conj_mem ht
  have hxsm : x * s ∈ conjSubgroup w₂ A := by
    rw [← hw₂]
    exact endgE_conj_mem hs
  have e1 : x * t * (x * s) = t * s := by
    calc x * t * (x * s) = x * (t * x) * s := by group
      _ = x * (x * t) * s := by rw [hxt]
      _ = (x * x) * (t * s) := by group
      _ = t * s := by rw [endgE_mul_self_of_mem hO hx, one_mul]
  have e2 : x * s * (x * t) = s * t := by
    calc x * s * (x * t) = x * (s * x) * t := by group
      _ = x * (x * s) * t := by rw [hxs]
      _ = (x * x) * (s * t) := by group
      _ = s * t := by rw [endgE_mul_self_of_mem hO hx, one_mul]
  have hcomm : x * t * (x * s) = x * s * (x * t) := by
    rw [e1, e2, hO.comm t ht s hs]
  have hts1 : t * s ≠ 1 := by
    intro h
    apply hst
    calc s = t⁻¹ := eq_inv_of_mul_eq_one_right h
      _ = t := inv_eq_of_mul_eq_one_right (hO.sq t ht)
  have hδ : conjSubgroup w₁ A ≠ conjSubgroup w₂ A := by
    intro heq
    have htsm : t * s ∈ conjSubgroup w₁ A := by
      rw [← e1]
      exact (conjSubgroup w₁ A).mul_mem hxtm (by rw [heq]; exact hxsm)
    have hδA : conjSubgroup w₁ A = A :=
      endgE_conj_eq_of_mem hO (A.mul_mem ht hs) hts1 htsm
    have hxtA : x * t ∈ A := by
      rw [← hδA]
      exact hxtm
    apply hxA
    have hxA' := A.mul_mem hxtA (A.inv_mem ht)
    rwa [mul_inv_cancel_right] at hxA'
  have hcn := hO.n1 w₁ w₂ (x * t) hxtm hxt1 (x * s) hxsm hxs1 hcomm
  obtain ⟨u₁, hu₁⟩ := G.six_four_gen hne hδ hcn hxsm hxs1 (x * t) hxtm
  obtain ⟨u₂, hu₂⟩ := G.six_four_gen hne (Ne.symm hδ)
    (fun z hz y hy => (hcn y hy z hz).symm) hxtm hxt1 (x * s) hxsm
  have c1 : IsConj s (x * s) := isConj_iff.mpr ⟨w₂, hw₂⟩
  have c2 : IsConj (x * s) (t * s) := isConj_iff.mpr ⟨u₁, by rw [hu₁, e1]⟩
  have c3 : IsConj (x * t) (s * t) := isConj_iff.mpr ⟨u₂, by rw [hu₂, e2]⟩
  have c4 : IsConj t (x * t) := isConj_iff.mpr ⟨w₁, hw₁⟩
  have c5 : IsConj (t * s) (x * t) := by
    rw [hO.comm t ht s hs]
    exact c3.symm
  exact c1.trans (c2.trans (c5.trans c4.symm))

theorem endg_six_five_b (hO : EndOmegaHyp A) (F : OmegaPart1 A) (G : OmegaPart2 A)
    (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) {t : X} (ht : t ∈ A) (ht1 : t ≠ 1) :
    ∀ τ : X, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ) := by
  intro τ hcomm hconj hτt
  obtain ⟨k, hk⟩ := isConj_iff.mp hconj
  have hτk : τ ∈ conjSubgroup k A := by
    rw [mem_conjSubgroup, ← hk, show k⁻¹ * (k * t * k⁻¹) * k = t by group]
    exact ht
  have hτ1 : τ ≠ 1 := endgE_ne_one_of_isConj ht1 hconj
  have hkO : InOmegaA A k := endgE_inOmega_of_commute hO ht ht1 hτk hτ1 hcomm.symm
  by_cases hkA : conjSubgroup k A = A
  · have hτA : τ ∈ A := by
      rw [← hkA]
      exact hτk
    have htτA : t * τ ∈ A := A.mul_mem ht hτA
    have htτ1 : t * τ ≠ 1 := by
      intro h
      apply hτt
      calc τ = t⁻¹ := eq_inv_of_mul_eq_one_right h
        _ = t := inv_eq_of_mul_eq_one_right (hO.sq t ht)
    exact endg_six_five_a hO F G hne ht htτA ht1 htτ1
  · have hne' : conjSubgroup (1 : X) A ≠ conjSubgroup k A := by
      rw [endgE_conj_one]
      exact fun h => hkA h.symm
    have hc : ∀ z ∈ conjSubgroup (1 : X) A, ∀ y ∈ conjSubgroup k A, z * y = y * z := by
      intro z hz y hy
      rw [endgE_conj_one] at hz
      exact hkO z hz y hy
    obtain ⟨w, hw⟩ :=
      G.six_four_gen hne hne' hc hτk hτ1 t (by rw [endgE_conj_one]; exact ht)
    exact hconj.trans (isConj_iff.mpr ⟨w, hw⟩)

theorem endg_conjCent_le (hO : EndOmegaHyp A) {t : X} (ht : t ∈ A) (ht1 : t ≠ 1) :
    ∀ τ : X, τ * t = t * τ → IsConj t τ → τ ∈ EgenX A := by
  intro τ hcomm hconj
  obtain ⟨k, hk⟩ := isConj_iff.mp hconj
  have hτk : τ ∈ conjSubgroup k A := by
    rw [mem_conjSubgroup, ← hk, show k⁻¹ * (k * t * k⁻¹) * k = t by group]
    exact ht
  have hτ1 : τ ≠ 1 := endgE_ne_one_of_isConj ht1 hconj
  exact endgE_le_egen (endgE_inOmega_of_commute hO ht ht1 hτk hτ1 hcomm.symm) hτk

theorem endg_corB_setup (hO : EndOmegaHyp A) (F : OmegaPart1 A) (G : OmegaPart2 A)
    (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) {t : X} (ht : t ∈ A) (ht1 : t ≠ 1) :
    CFSG.Timmesfeld.CorB.Setup t := by
  have hWle : CFSG.Timmesfeld.CorB.weakClosure t ≤ EgenX A := by
    rw [CFSG.Timmesfeld.CorB.weakClosure, Subgroup.closure_le]
    intro τ hτ
    obtain ⟨hτc, hτi⟩ := hτ
    exact endg_conjCent_le hO ht ht1 τ hτc hτi
  have hWW : ⁅CFSG.Timmesfeld.CorB.weakClosure t, CFSG.Timmesfeld.CorB.weakClosure t⁆ ≤ A :=
    (Subgroup.commutator_mono hWle hWle).trans hO.e
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact hO.sq t ht) ht1
  · exact IsPGroup.to_le F.pgroup hWle
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro g hg k hk
    have hgA : g ∈ A := hWW hg
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (F.comm_A k (hWle hk) g hgA).symm
  · intro τ hcomm hconj hτt
    exact endg_six_five_b hO F G hne ht ht1 τ hcomm hconj hτt

theorem endg_eight_one (hO : EndOmegaHyp A) (F : OmegaPart1 A) (G : OmegaPart2 A)
    (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) {t : X} (ht : t ∈ A) (ht1 : t ≠ 1) :
    CFSG.Timmesfeld.rootSet {x : X | IsConj t x} t = {x | x ∈ A ∧ x ≠ 1} := by
  ext x
  simp only [CFSG.Timmesfeld.rootSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxD, hxc⟩
    have hx1 : x ≠ 1 := endgE_ne_one_of_isConj ht1 hxD
    have hxt : Commute x t := (hxc t (IsConj.refl t)).2 (Commute.refl t)
    obtain ⟨k, hk⟩ := isConj_iff.mp hxD
    have hxk : x ∈ conjSubgroup k A := by
      rw [mem_conjSubgroup, ← hk, show k⁻¹ * (k * t * k⁻¹) * k = t by group]
      exact ht
    have hkO : InOmegaA A k := endgE_inOmega_of_commute hO ht ht1 hxk hx1 hxt.eq.symm
    by_cases hkA : conjSubgroup k A = A
    · refine ⟨?_, hx1⟩
      rw [← hkA]
      exact hxk
    · exfalso
      obtain ⟨h, hh, y, hy, hxy⟩ := G.exists_noncomm hne hkO hkA hxk hx1
      have hy1 : y ≠ 1 := by
        rintro rfl
        exact hxy (by group)
      obtain ⟨a, ha, ha1, hay⟩ := endgE_exists_of_mem hy hy1
      have hat : IsConj t a := endg_six_five_a hO F G hne ht ha ht1 ha1
      have hyD : IsConj t y := hat.trans (isConj_iff.mpr ⟨h, hay⟩)
      have hty : Commute t y := hh t ht y hy
      exact hxy ((hxc y hyD).2 hty).eq
  · rintro ⟨hxA, hx1⟩
    have hxD : IsConj t x := endg_six_five_a hO F G hne ht hxA ht1 hx1
    refine ⟨hxD, fun f hfD => ?_⟩
    obtain ⟨k, hk⟩ := isConj_iff.mp hfD
    have hfk : f ∈ conjSubgroup k A := by
      rw [mem_conjSubgroup, ← hk, show k⁻¹ * (k * t * k⁻¹) * k = t by group]
      exact ht
    have hf1 : f ≠ 1 := endgE_ne_one_of_isConj ht1 hfD
    constructor
    · intro hxf
      have hkO : InOmegaA A k := endgE_inOmega_of_commute hO hxA hx1 hfk hf1 hxf.eq
      exact hkO t ht f hfk
    · intro htf
      have hkO : InOmegaA A k := endgE_inOmega_of_commute hO ht ht1 hfk hf1 htf.eq
      exact hkO x hxA f hfk

theorem endg_eight_one_card (hO : EndOmegaHyp A) (F : OmegaPart1 A) (G : OmegaPart2 A)
    (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) {t : X} (ht : t ∈ A) (ht1 : t ≠ 1) :
    ∀ d : X, IsConj t d →
      Nat.card ↥(CFSG.Timmesfeld.rootGroup {x : X | IsConj t x} d) = Nat.card A := by
  have hroot : CFSG.Timmesfeld.rootGroup {x : X | IsConj t x} t = A := by
    rw [CFSG.Timmesfeld.rootGroup, endg_eight_one hO F G hne ht ht1]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro a ⟨haA, -⟩
      exact haA
    · intro a haA
      by_cases ha1 : a = 1
      · rw [ha1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (show a ∈ {x : X | x ∈ A ∧ x ≠ 1} from ⟨haA, ha1⟩)
  intro d hd
  obtain ⟨k, hk⟩ := isConj_iff.mp hd
  rw [← hk, CFSG.Timmesfeld.rootGroup_conj (D := {x : X | IsConj t x}) ⟨t, rfl⟩ k t, hroot]
  exact Subgroup.card_map_of_injective (MulAut.conj k).injective

end OmegaThree

end CFSG.RankThree.GF2n.Stroth80
