module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_mem_stabSub_inf_commSub_fixV {W : Type*} [CommGroup W]
    {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.centralizer (X : Set (MulAut W))) :
    g ∈ stabSub (commSub ⊤ X ⊓ fixV X) := by
  have hcomm : ∀ x ∈ X, g * x = x * g := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have hnorm : ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro x hx
    rw [hcomm x hx, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hcomm' : ∀ x ∈ X, g⁻¹ * x = x * g⁻¹ := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.centralizer (X : Set (MulAut W))).inv_mem hg) x hx).symm
  have hnorm' : ∀ x ∈ X, g⁻¹ * x * g ∈ X := by
    intro x hx
    rw [hcomm' x hx, mul_assoc, inv_mul_cancel, mul_one]
    exact hx
  have hstabW : g ∈ stabSub (commSub ⊤ X) := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      simpa using commSub_top_stable151b hnorm' (g u) hu
    · exact fun hu => commSub_top_stable151b hnorm u hu
  have hstabF : g ∈ stabSub (fixV X) := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu x hx
      have h1 : (g * x * g⁻¹) (g u) = g u := hu _ (hnorm x hx)
      have h2 : g (x u) = g u := by simpa [MulAut.mul_apply] using h1
      exact g.injective h2
    · intro hu x hx
      have h1 : (g⁻¹ * x * g) u = u := hu _ (hnorm' x hx)
      have h2 : g⁻¹ (x (g u)) = u := by simpa [MulAut.mul_apply] using h1
      have h3 : x (g u) = g u := by
        have := congrArg g h2
        simpa using this
      exact h3
  rw [mem_stabSub] at hstabW hstabF ⊢
  intro u
  exact ⟨fun hu => ⟨(hstabW u).1 hu.1, (hstabF u).1 hu.2⟩,
    fun hu => ⟨(hstabW u).2 hu.1, (hstabF u).2 hu.2⟩⟩

theorem s16h_sl28_seven_scalar_exists
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
    (h7 : 7 ∈ D.sig) :
    ∃ d : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      d ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ orderOf d = 7 ∧
      d ∈ stabSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
      d ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  obtain ⟨d, hdk, hd7, hdnt⟩ :=
    s16h_sl28_seven_kbar_element D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 h7
  have hdk' := hdk
  rw [kBar] at hdk'
  have hdM : d ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian := (Subgroup.mem_inf.mp hdk').1
  have hdcen : d ∈ Subgroup.centralizer
      (lBar ⊥ V h.hyp151.isElemAbelian L : Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :=
    (Subgroup.mem_inf.mp hdk').2
  have hdstab : d ∈ stabSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) :=
    s16h_mem_stabSub_inf_commSub_fixV (X := lBar ⊥ V h.hyp151.isElemAbelian L) hdcen
  have hdcent : d ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) :=
    s16h_sl28_seven_kbar_faithful_on_Z D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hbad hrow hZ4 h7 hdk hd7 hdnt
  exact ⟨d, hdM, hd7, hdstab, hdcent⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
