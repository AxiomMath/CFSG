module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA2A1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA2A2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA2B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_scalar_mbar_fpf
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
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hφM : φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hφ3 : orderOf φ = 3)
    (hcent : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian L, φ * a = a * φ)
    (hcentx : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x), φ * a = a * φ)
    (hnontriv : ∃ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L, φ z ≠ z) :
    ∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L), φ z = z → z = 1 := by
  have hV := h.hyp151.isElemAbelian
  have hgen := s16h_sl4_commSub_commSub_self D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4
  have hfree := s16h_sl4_quotient_fixV D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 hxM hxn hφM hφ3 hcent hcentx hnontriv
  have hmapL : (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom = lBar ⊥ V hV L := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      change φ * b * φ⁻¹ ∈ lBar ⊥ V hV L
      rw [hcent b hb, mul_assoc, mul_inv_cancel, mul_one]
      exact hb
    · intro ha
      refine ⟨a, ha, ?_⟩
      change φ * a * φ⁻¹ = a
      rw [hcent a ha, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm := CFSG.Quasithin.Asc81c.commSub_map_conj (lBar ⊥ V hV L) φ
  have hstab : ∀ v ∈ commSub ⊤ (lBar ⊥ V hV L), φ v ∈ commSub ⊤ (lBar ⊥ V hV L) := by
    intro v hv
    have h1 : φ v ∈ (commSub ⊤ (lBar ⊥ V hV L)).map φ.toMonoidHom := ⟨v, hv, rfl⟩
    rw [← hcomm, hmapL] at h1
    exact h1
  have hVY : ∀ y ∈ lBar ⊥ V hV L, ∀ v ∈ commSub ⊤ (lBar ⊥ V hV L),
      y v ∈ commSub ⊤ (lBar ⊥ V hV L) :=
    fun y hy v hv => CFSG.Quasithin.Asc81c.commSub_stable' hy hv
  have hred := s16h_commSub_inf_fixV_zpowers_eq (W := Vtil ⊥ V hV)
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) (Y := lBar ⊥ V hV L) (g := φ)
    (by rw [hφ3]; decide) hcent hVY hstab hgen
  have hCZ : commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (Subgroup.zpowers φ) ≤
      commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) := by
    rintro c ⟨hcW, hcC⟩
    have hfix : φ c = c := mem_fixV_zpowers_iff_apply.1 hcC
    exact ⟨hcW, (hfree c hcW (by rw [hfix, mul_inv_cancel]; exact Subgroup.one_mem _)).2⟩
  have hZbot : commSub (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L))
      (lBar ⊥ V hV L) = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
  have hle : commSub (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (Subgroup.zpowers φ))
      (lBar ⊥ V hV L) ≤ ⊥ := (commSub_mono hCZ le_rfl).trans (le_of_eq hZbot)
  have hCbot : commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (Subgroup.zpowers φ) = ⊥ := by
    rw [hred]
    exact le_bot_iff.mp hle
  intro z hz hzφ
  have hzC : z ∈ commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (Subgroup.zpowers φ) :=
    ⟨hz.1, mem_fixV_zpowers_iff_apply.2 hzφ⟩
  rw [hCbot] at hzC
  exact Subgroup.mem_bot.mp hzC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
