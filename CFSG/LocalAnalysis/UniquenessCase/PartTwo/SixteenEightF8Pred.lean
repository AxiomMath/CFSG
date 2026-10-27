module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowLiftB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def FixNc {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (p : ℕ) : Prop :=
  ∀ a : Multiplicative (ι → K), a ≠ 1 → ∃ B : Subgroup ↥Γ, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
    ∀ b ∈ B, natAct Γ b a = a

@[expose] def FixOrd {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (p : ℕ) : Prop :=
  ∀ a : Multiplicative (ι → K), a ≠ 1 → ∃ g : ↥Γ, orderOf g = p ∧ natAct Γ g a = a

variable {G : Type} [Group G] [Finite G]

theorem s16g_realizes_top {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hconc : Conc4_136 D V₀ V hV L) (hs : s15 D.M V₀ V hV L = 1) {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    (FFModel.nat Γ).Realizes (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) := by
  have hw : commSub ⊤ (lBar V₀ V hV L) = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  rw [hw, top_inf_eq] at hR
  exact hR

theorem s16g_false_of_fixNc (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hne : ∃ a : Multiplicative (ι → K), a ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpσ : p ∈ D.sig) (hfix : FixNc Γ p) : False := by
  have hR' := s16g_realizes_top hconc hs Γ hR
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hZ : ∀ h ∈ lBar V₀ V hV L, ∀ z ∈ fixV (lBar V₀ V hV L), h z = z :=
    fun h hh z hz => (mem_fixV.1 hz) h hh
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hset.hyp151.le
  refine s16g_false_of_fix D hS (hV := hV) hset hp hpσ ?_
  intro x hx1
  obtain ⟨B, hBH, hBp, hBc, hBfix⟩ := s16g_transport_fix Γ hR' hW hZ hne hp hp2 hfix hx1
  exact ⟨B, hBH.trans hle, hBp, hBc, hBfix⟩

theorem s16g_false_of_fixOrd (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hne : ∃ a : Multiplicative (ι → K), a ≠ 1)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    (hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L)))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    (hmult : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)))
    (hker : p ∣ Nat.card (F11.CTilde D.M V₀ V)) (hfix : FixOrd Γ p) : False := by
  have hR' := s16g_realizes_top hconc hs Γ hR
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hZ : ∀ h ∈ lBar V₀ V hV L, ∀ z ∈ fixV (lBar V₀ V hV L), h z = z :=
    fun h hh z hz => (mem_fixV.1 hz) h hh
  refine s16g_false_of_fix_lBar D hS (hV := hV) hset hq hz hp hp2 hpσ hmult hker ?_
  intro x hx1
  exact s16g_transport_fix_ord Γ hR' hW hZ hne hp hp2 hfix hx1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
