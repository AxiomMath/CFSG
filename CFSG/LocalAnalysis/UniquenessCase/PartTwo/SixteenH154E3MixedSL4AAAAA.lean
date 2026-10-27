module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA1AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_scalar_mbar
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
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∃ φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ orderOf φ = 3 ∧
      (∀ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L,
        φ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L) ∧
      (∀ z ∈ wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x),
        φ z ∈ wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) ∧
      (∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L),
        φ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
      (∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L), φ z = z → z = 1) := by
  obtain ⟨φ, hφM, hφ3, hcent, hcentx, hnontriv⟩ :=
    s16h_sl4_scalar_mbar_central_of_bad_core D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
        hrow hZ4 hxM hxn
  have hfpf := s16h_sl4_scalar_mbar_fpf D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
    hbad hrow hZ4 hxM hxn hφM hφ3 hcent hcentx hnontriv
  have hV := h.hyp151.isElemAbelian
  have hconjW : ∀ p ∈ lBar ⊥ V hV L, φ * p * φ⁻¹ ∈ lBar ⊥ V hV L := by
    intro p hp
    rw [show φ * p * φ⁻¹ = p from by rw [hcent p hp, mul_assoc, mul_inv_cancel, mul_one]]
    exact hp
  have hconjW' : ∀ p ∈ lBar ⊥ V hV L, φ⁻¹ * p * φ ∈ lBar ⊥ V hV L := by
    intro p hp
    rw [show φ⁻¹ * p * φ = p from by
      rw [mul_assoc, (hcent p hp).symm, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact hp
  have hstabW : φ ∈ stabSub (commSub ⊤ (lBar ⊥ V hV L)) := by
    have h := mem_stabSub_commV (P := lBar ⊥ V hV L) (g := φ) hconjW hconjW'
    rwa [commV_eq_commSub] at h
  have hstabZ : φ ∈ stabSub (fixV (lBar ⊥ V hV L)) :=
    mem_stabSub_fixV_of_commute (B := lBar ⊥ V hV L) (g := φ) fun b hb => (hcent b hb).symm
  have hconjWx : ∀ p ∈ lBar ⊥ V hV (conjSubgroup L x),
      φ * p * φ⁻¹ ∈ lBar ⊥ V hV (conjSubgroup L x) := by
    intro p hp
    rw [show φ * p * φ⁻¹ = p from by rw [hcentx p hp, mul_assoc, mul_inv_cancel, mul_one]]
    exact hp
  have hconjWx' : ∀ p ∈ lBar ⊥ V hV (conjSubgroup L x),
      φ⁻¹ * p * φ ∈ lBar ⊥ V hV (conjSubgroup L x) := by
    intro p hp
    rw [show φ⁻¹ * p * φ = p from by
      rw [mul_assoc, (hcentx p hp).symm, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact hp
  have hstabWx : φ ∈ stabSub (commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x))) := by
    have h := mem_stabSub_commV (P := lBar ⊥ V hV (conjSubgroup L x)) (g := φ) hconjWx hconjWx'
    rwa [commV_eq_commSub] at h
  refine ⟨φ, hφM, hφ3, ?_, ?_, ?_, hfpf⟩
  · intro z hz
    have hz' : z ∈ commSub ⊤ (lBar ⊥ V hV L) := by
      simpa only [wTil, lBar] using hz
    exact (mem_stabSub.mp hstabW z).mpr hz'
  · intro z hz
    have hz' : z ∈ commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)) := by
      simpa only [wTil, lBar] using hz
    exact (mem_stabSub.mp hstabWx z).mpr hz'
  · intro z hz
    exact ⟨(mem_stabSub.mp hstabW z).mpr hz.1, (mem_stabSub.mp hstabZ z).mpr hz.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
