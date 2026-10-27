module

public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct

import CFSG.LargeExtraspecial.S12InspXOrd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.RankThree.GF2n.Stroth78.Sec4Three
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Moore
import CFSG.Monster.B.TwoA.Base.ElemAut

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Equiv Equiv.Perm
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

variable {X : Type} [Group X] {E : Set X}

theorem exists_minimalNormal_commutator_eq (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X)
    {d : X} (hd : d ∈ E) :
    ∃ N : Subgroup (X ⧸ Subgroup.center X), N.Normal ∧ IsSimpleGroup ↥N ∧
      ¬ Group.IsSolvable ↥N ∧ Subgroup.centralizer (N : Set (X ⧸ Subgroup.center X)) = ⊥ ∧
      ⁅threeResidualQuot d, threeResidualQuot d⁆ = N := by
  haveI : Finite X := Pair.finite hP
  obtain ⟨N, hNn, hNbot, hNs, hNsol, hcent⟩ := exists_minimalNormal_quotient_center hP h2 h3
  have hPq : Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E) :=
    pair_quot_center hP h2
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    Pair.center_quotient_center_eq_bot hP
  have hNle : N ≤ commutator (X ⧸ Subgroup.center X) :=
    le_commutator_of_isSimpleGroup_of_not_isSolvable hNs hNsol
  have hOeq : CFSG.Quasithin.pResidualOf 3 (commutator (X ⧸ Subgroup.center X)) = N :=
    pResidualOf_three_commutator_eq hPq hZ hNn hNbot hNs hNsol hNle
  have hquot := threeResidualQuot_eq_Kgrp hPq hZ hNn hNs hNbot hOeq hd
  refine ⟨N, hNn, hNs, hNsol, hcent, ?_⟩
  rw [hquot]
  exact CFSG.RankThree.PartOne.FIS.commutator_Kgrp hPq hZ hNn hNs hNsol hNbot
    ⟨d, hd, rfl⟩

theorem threeResidualQuot_eq_top_of_normal (hP : Pair X E) {d : X} (hd : d ∈ E)
    (hn : (threeResidualQuot d).Normal) : threeResidualQuot d = ⊤ := by
  have hdW : (QuotientGroup.mk d : X ⧸ Subgroup.center X) ∈ threeResidualQuot d :=
    ⟨d, Subgroup.mem_sup_right (Subgroup.mem_zpowers d), rfl⟩
  obtain ⟨e, he⟩ := hP.2.1
  have hEW : E ⊆ (threeResidualQuot d).comap (QuotientGroup.mk' (Subgroup.center X)) := by
    intro x hx
    have hde : d ∈ {x | IsConj e x} := he ▸ hd
    have hxe : x ∈ {x | IsConj e x} := he ▸ hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp ((IsConj.symm hde).trans hxe)
    have hc := hn.conj_mem _ hdW (QuotientGroup.mk c : X ⧸ Subgroup.center X)
    simpa using hc
  have hcl : (⊤ : Subgroup X) ≤
      (threeResidualQuot d).comap (QuotientGroup.mk' (Subgroup.center X)) := by
    rw [← hP.2.2.2.2]
    exact (Subgroup.closure_le _).mpr hEW
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact hcl (Subgroup.mem_top x)

theorem nonempty_mulEquiv_alternating {Y : Type} [Group Y] {W N : Subgroup Y} {k : ℕ}
    (hk : 5 ≤ k) (φ : ↥W ≃* Perm (Fin k)) (hN : ⁅W, W⁆ = N) :
    Nonempty (↥N ≃* alternatingGroup (Fin k)) := by
  have h1 : (commutator ↥W).map W.subtype = N := (Subgroup.map_subtype_commutator W).trans hN
  have h3 : commutator (Perm (Fin k)) = alternatingGroup (Fin k) :=
    alternatingGroup.commutator_perm_eq (by simpa using hk)
  exact ⟨((MulEquiv.subgroupCongr h1.symm).trans
    (Subgroup.equivMapOfInjective (commutator ↥W) W.subtype W.subtype_injective).symm).trans
    ((MulEquiv.commutatorCongr φ).trans (MulEquiv.subgroupCongr h3))⟩

theorem center_eq_bot_of_simple {N : Type} [Group N] (hs : IsSimpleGroup N)
    (hns : ¬ Group.IsSolvable N) : Subgroup.center N = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center N) with h | h
  · exact h
  · exfalso
    apply hns
    refine Group.isSolvable_of_comm fun x y => ?_
    exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x

private theorem exists_card_dvd_of_perm {k : ℕ} (hk : 5 ≤ k) (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X) {d : X}
    (hd : d ∈ E) (φ : ↥(threeResidualQuot d) ≃* Perm (Fin k)) :
    ∃ N : Subgroup (X ⧸ Subgroup.center X), ∃ _ : ↥N ≃* alternatingGroup (Fin k),
      Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card N * Nat.card (Outer N) := by
  haveI : Finite X := Pair.finite hP
  obtain ⟨N, hNn, hNs, hNsol, hcent, hcomm⟩ := exists_minimalNormal_commutator_eq hP h2 h3 hd
  obtain ⟨e⟩ := nonempty_mulEquiv_alternating hk φ hcomm
  haveI := hNn
  exact ⟨N, e, CFSG.LargeExtraspecial.card_dvd_card_mul_card_outer_of_normal hcent
    (center_eq_bot_of_simple hNs hNsol)⟩

theorem threeResidualQuot_eq_top_of_perm_six (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X) {d : X}
    (hd : d ∈ E) (φ : ↥(threeResidualQuot d) ≃* Perm (Fin 6)) :
    threeResidualQuot d = ⊤ := by
  haveI : Finite X := Pair.finite hP
  obtain ⟨N, e, hdvd⟩ := exists_card_dvd_of_perm (by norm_num) hP h2 h3 hd φ
  have hNcard : Nat.card N = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 6),
      Fintype.card_fin]
    rfl
  have hOut : Nat.card (Outer N) ≤ 4 :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four_of_equiv
      e
  have hW : Nat.card (threeResidualQuot d) = 720 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6),
      Fintype.card_fin]
    rfl
  have hmul := Subgroup.card_mul_index (threeResidualQuot d)
  have hpos : 0 < Nat.card (X ⧸ Subgroup.center X) := Nat.card_pos
  have hle : Nat.card (X ⧸ Subgroup.center X) ≤ 1440 := by
    haveI : Finite (Outer N) := inferInstance
    have h1 := Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) hdvd
    rw [hNcard] at h1
    calc Nat.card (X ⧸ Subgroup.center X) ≤ 360 * Nat.card (Outer N) := h1
      _ ≤ 360 * 4 := Nat.mul_le_mul_left _ hOut
  have hidx : (threeResidualQuot d).index ≤ 2 := by
    rw [hW] at hmul
    omega
  have hidx0 : (threeResidualQuot d).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : (threeResidualQuot d).index = 1 ∨ (threeResidualQuot d).index = 2 := by omega
  rcases this with h1 | h2'
  · exact Subgroup.index_eq_one.mp h1
  · exact threeResidualQuot_eq_top_of_normal hP hd (Subgroup.normal_of_index_eq_two h2')

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_mulEquiv_Xsub_perm_six (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1)
    (φ : ↥(threeResidualQuot (alphaInX S h hα₀)) ≃* Perm (Fin 6))
    (hφ : ∀ g, g ∈ threeResidualClass (alphaInX S h hα₀) ↔ (φ g).IsSwap) :
    ∃ Ψ : ↥(Xsub S a) ≃* Perm (Fin 6),
      ∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap := by
  classical
  have hP := pair_Xsub S h h217 h3
  have h2 := twoCore_Xsub S (a := a)
  have h3c := threeCore_Xsub S h h217
  let d := alphaInX S h hα₀
  have hdE : d ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀ hα₀1)
  have hW : threeResidualQuot d = ⊤ := threeResidualQuot_eq_top_of_perm_six hP h2 h3c hdE φ
  let π : ↥(Xsub S a) →* ↥(threeResidualQuot d) :=
    (QuotientGroup.mk' (Subgroup.center ↥(Xsub S a))).codRestrict _
      (fun x => hW ▸ Subgroup.mem_top _)
  let Ψ₀ : ↥(Xsub S a) →* Perm (Fin 6) := φ.toMonoidHom.comp π
  have hπc : ∀ x, ((π x : ↥(threeResidualQuot d)) : ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) =
      QuotientGroup.mk x := fun x => rfl
  have hker : Ψ₀.ker = Subgroup.center ↥(Xsub S a) := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : π x = 1 := φ.injective (by simpa [Ψ₀] using hx)
      have h2' : (QuotientGroup.mk x : ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) = 1 := by
        rw [← hπc, h1]; rfl
      exact QuotientGroup.eq_one_iff x |>.mp h2'
    · intro hx
      have h1 : π x = 1 := Subtype.ext (by
        rw [hπc]; exact (QuotientGroup.eq_one_iff x).mpr hx)
      simp [Ψ₀, h1]
  have hdD : ∀ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)),
      ∃ g : ↥(Xsub S a), x = g * d * g⁻¹ := by
    intro x hx
    obtain ⟨e, he⟩ := hP.2.1
    have hde : d ∈ {x | IsConj e x} := he ▸ hdE
    have hxe : x ∈ {x | IsConj e x} := he ▸ hx
    obtain ⟨c, hc⟩ := isConj_iff.mp ((IsConj.symm hde).trans hxe)
    exact ⟨c, hc.symm⟩
  have hΨd : (Ψ₀ d).IsSwap := by
    have : π d = ⟨QuotientGroup.mk d, mk_mem_threeResidualQuot_self d⟩ := rfl
    exact (hφ _).mp (alphaBar_mem S h hα₀)
  have hswap : ∀ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), (Ψ₀ x).IsSwap := by
    intro x hx
    obtain ⟨g, rfl⟩ := hdD x hx
    have h1 : Ψ₀ (g * d * g⁻¹) = Ψ₀ g * Ψ₀ d * (Ψ₀ g)⁻¹ := by simp [map_mul, map_inv]
    rw [h1]
    refine Equiv.Perm.card_support_eq_two.mp ?_
    rw [Equiv.Perm.card_support_conj]
    exact Equiv.Perm.card_support_eq_two.mpr hΨd
  have hlift : ∀ p : Perm (Fin 6), p.IsSwap →
      ∃ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), Ψ₀ x = p := by
    intro p hp
    have hmem : φ.symm p ∈ threeResidualClass d := (hφ _).mpr (by simpa using hp)
    obtain ⟨w, hw, hwq⟩ := hmem
    refine ⟨w * d * w⁻¹, ?_, ?_⟩
    · have h1 := Eset_conj_mem S a (hdE : (d : Hbar z) ∈ Eset S a) (w : Hbar z)
      simpa [Subgroup.coe_mul] using h1
    · have h1 : π (w * d * w⁻¹) = φ.symm p := Subtype.ext (by rw [hπc]; exact hwq)
      simp [Ψ₀, h1]
  have hodd : Odd (Nat.card Ψ₀.ker) := by rw [hker]; exact odd_card_center_Xsub S a
  have hself : ∀ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)), x * x = 1 := by
    intro x hx
    have h1 := pow_orderOf_eq_one x
    rw [hP.2.2.1 x hx, pow_two] at h1
    exact h1
  have hconj : ∀ x ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)),
      ∀ y ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)),
      x * y * x⁻¹ ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := by
    intro x _ y hy
    have h1 := Eset_conj_mem S a (hy : (y : Hbar z) ∈ Eset S a) (x : Hbar z)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hinj : Function.Injective Ψ₀ :=
    injective_of_closure_eq_top_of_moore Ψ₀ hP.2.2.2.2 hker.le hodd hself hP.2.2.2.1 hconj hswap
      hlift
  have hsurj : Function.Surjective Ψ₀ := by
    intro p
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective ((φ.symm p).1)
    refine ⟨x, ?_⟩
    have h1 : π x = φ.symm p := Subtype.ext (by rw [hπc]; exact hx)
    simp [Ψ₀, h1]
  refine ⟨MulEquiv.ofBijective Ψ₀ ⟨hinj, hsurj⟩, fun x => ⟨hswap x, fun hx => ?_⟩⟩
  obtain ⟨y, hyD, hyx⟩ := hlift (Ψ₀ x) hx
  exact (hinj hyx) ▸ hyD

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
