module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA2C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_kbar_faithful_on_Z
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
    {d : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hdk : d ∈ kBar D.M ⊥ V h.hyp151.isElemAbelian L) (hd7 : orderOf d = 7)
    (hdnt : d ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    d ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  intro hdz
  set Lb : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)) :=
    lBar ⊥ V h.hyp151.isElemAbelian L with hLb
  have hgen : commSub (commSub ⊤ Lb) Lb = commSub ⊤ Lb :=
    s16h_sl28_commSub_commSub_self (W := Vtil ⊥ V h.hyp151.isElemAbelian) hrow
  have hfree := s16h_sl28_quotient_fixV D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
    hZ hbad hrow hZ4 h7 hdk hd7 hdnt
  have hdcen : ∀ a ∈ Lb, d * a = a * d := by
    have hdk' := hdk
    rw [kBar] at hdk'
    have hcen : d ∈ Subgroup.centralizer (Lb : Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
      have h := (Subgroup.mem_inf.mp hdk').2
      rwa [← hLb] at h
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp hcen a ha).symm
  have hVY : ∀ y ∈ Lb, ∀ v ∈ commSub ⊤ Lb, y v ∈ commSub ⊤ Lb :=
    s16jp_commSub_stable (L := Lb) (Y := ⊤) (fun l _ y _ => Subgroup.mem_top (l y))
  have hmapL : Lb.map (MulAut.conj d).toMonoidHom = Lb := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      change d * b * d⁻¹ ∈ Lb
      rw [hdcen b hb, mul_assoc, mul_inv_cancel, mul_one]
      exact hb
    · intro ha
      refine ⟨a, ha, ?_⟩
      change d * a * d⁻¹ = a
      rw [hdcen a ha, mul_assoc, mul_inv_cancel, mul_one]
  have hVg : ∀ v ∈ commSub ⊤ Lb, d v ∈ commSub ⊤ Lb := by
    intro v hv
    have hcomm := CFSG.Quasithin.Asc81c.commSub_map_conj (X := Lb) d
    have h1 : d v ∈ (commSub ⊤ Lb).map d.toMonoidHom := ⟨v, hv, rfl⟩
    rw [← hcomm, hmapL] at h1
    exact h1
  have hdodd : Odd (orderOf d) := by rw [hd7]; exact ⟨3, by norm_num⟩
  have hZpow : commSub ⊤ Lb ⊓ fixV (Subgroup.zpowers d) =
      commSub (commSub ⊤ Lb ⊓ fixV (Subgroup.zpowers d)) Lb :=
    s16h_coprime_commSub_inf_fixV_eq
      (W := Vtil ⊥ V h.hyp151.isElemAbelian)
      (hW := s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian)
      (Y := Lb) (g := d) (V := commSub ⊤ Lb) hdodd hdcen hVY hVg hgen
  have hCZ : commSub ⊤ Lb ⊓ fixV (Subgroup.zpowers d) ≤ commSub ⊤ Lb ⊓ fixV Lb := by
    rintro v ⟨hvW, hvd⟩
    have hfix : d v = v := CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp hvd
    exact hfree v hvW (by rw [hfix, mul_inv_cancel]; exact Subgroup.one_mem _)
  have hZle : commSub ⊤ Lb ⊓ fixV Lb ≤ commSub ⊤ Lb ⊓ fixV (Subgroup.zpowers d) := by
    rintro v ⟨hvW, hvfix⟩
    exact ⟨hvW, CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr (hdz v ⟨hvW, hvfix⟩)⟩
  have hle : commSub (commSub ⊤ Lb ⊓ fixV (Subgroup.zpowers d)) Lb ≤
      commSub (commSub ⊤ Lb ⊓ fixV Lb) Lb := commSub_mono hCZ le_rfl
  have hZbot : commSub (commSub ⊤ Lb ⊓ fixV Lb) Lb = ⊥ :=
    commSub_eq_bot_iff.mpr inf_le_right
  have hbot : commSub ⊤ Lb ⊓ fixV (Subgroup.zpowers d) = ⊥ := by
    rw [hZpow]
    exact le_bot_iff.mp (hle.trans (le_of_eq hZbot))
  exact hZ (le_bot_iff.mp (hZle.trans (le_of_eq hbot)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
