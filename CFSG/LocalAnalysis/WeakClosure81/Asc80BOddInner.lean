module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
public import CFSG.ClassicalInvolution.Balance.Q27D4Parts
import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance.Q27 (InvolutionCentralizersGenerate)

@[expose] def SeitzFourInner (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (L E : Subgroup G), L.Normal → IsSimpleGroup ↥L →
    (∃ a b : ↥L, a * b ≠ b * a) → P ↥L → centralizer (L : Set G) = ⊥ →
    IsElemAbelian 2 E → Nat.card E = 4 → E ≤ L → ¬ SeitzFourExc ↥L →
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)) = L

@[expose] def SeitzFourOuter (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (L E : Subgroup G), L.Normal → IsSimpleGroup ↥L →
    (∃ a b : ↥L, a * b ≠ b * a) → P ↥L → centralizer (L : Set G) = ⊥ →
    IsElemAbelian 2 E → Nat.card E = 4 → ¬ E ≤ L →
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)) = L

theorem seitzFour_of_inner_outer {P : ∀ (X : Type) [Group X], Prop} (hi : SeitzFourInner P)
    (ho : SeitzFourOuter P) : SeitzFour P := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 hx
  by_cases hEL : E ≤ L
  · exact hi L E hLn hLs hnab hP hC hE h4 hEL fun h => hx ⟨hEL, h⟩
  · exact ho L E hLn hLs hnab hP hC hE h4 hEL

theorem involutionCentralizersGenerate_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : InvolutionCentralizersGenerate X) : InvolutionCentralizersGenerate Y := by
  intro u₁ u₂ h1 h2 h1' h2' h12 hc
  have key := h (e.symm u₁) (e.symm u₂) (by rw [← map_mul, h1, map_one])
    (by rw [← map_mul, h2, map_one]) (by simpa using h1') (by simpa using h2')
    (fun h => h12 (e.symm.injective h)) (by rw [← map_mul, ← map_mul, hc])
  have hmap := congrArg (Subgroup.map (e : X →* Y)) key
  rw [Subgroup.map_top_of_surjective _ e.surjective] at hmap
  rw [← hmap, Subgroup.map_sup, Subgroup.map_sup]
  have hc' : ∀ x : X, (centralizer ({x} : Set X)).map (e : X →* Y) =
      centralizer ({e x} : Set Y) := by
    intro x
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      change e z * e x = e x * e z
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simpa using hy
  rw [hc', hc', hc', map_mul]
  simp

theorem seitzFourInner_of_involutionCentralizersGenerate {P : ∀ (X : Type) [Group X], Prop}
    (h : ∀ (X : Type) [Group X], P X → InvolutionCentralizersGenerate X) :
    SeitzFourInner P := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 hEL _
  classical
  have hEne : E ≠ ⊥ := fun hb => by rw [hb] at h4; simp at h4
  obtain ⟨⟨a, haE⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEne
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  obtain ⟨b, hbE, hb1, hba⟩ := exists_mem_ne_one_ne_of_four_le_card (A := E) (by omega) a
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hE.2 a haE
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hE.2 b hbE
  have hab : a * b = b * a := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)
  have hab1 : a * b ≠ 1 := fun h => hba (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_left ha2])
  set a' : ↥L := ⟨a, hEL haE⟩
  set b' : ↥L := ⟨b, hEL hbE⟩
  have hgen := h ↥L hP a' b' (Subtype.ext ha2) (Subtype.ext hb2)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hba (congrArg Subtype.val h).symm) (Subtype.ext hab)
  have hle : ∀ x ∈ E, x ≠ 1 → ∀ (hx : x ∈ L),
      (centralizer ({(⟨x, hx⟩ : ↥L)} : Set ↥L)).map L.subtype ≤
        ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) := by
    intro x hxE hx1 hx
    refine le_trans ?_ (le_iSup₂_of_le x hxE (le_iSup_of_le hx1 le_rfl))
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    show (y : G) ∈ centralizer ({x} : Set G)
    have hy' : y * ⟨x, hx⟩ = ⟨x, hx⟩ * y := mem_centralizer_singleton_iff.mp hy
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy'
  refine le_antisymm (iSup₂_le fun x _ => iSup_le fun _ => inf_le_left) ?_
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥L) ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top _
  rw [← hgen] at hy'
  have hmap : (centralizer ({a'} : Set ↥L) ⊔ centralizer ({b'} : Set ↥L) ⊔
      centralizer ({a' * b'} : Set ↥L)).map L.subtype ≤
      ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) := by
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le (sup_le (hle a haE ha1 _) (hle b hbE hb1 _))
      (hle (a * b) (E.mul_mem haE hbE) hab1 (L.mul_mem (hEL haE) (hEL hbE)))
  exact hmap ⟨⟨y, hy⟩, hy', rfl⟩

theorem involutionCentralizersGenerate_g2_td4
    {X : Type} [Group X]
    (hX : ∃ p f : ℕ, p ≠ 2 ∧ (CFSG.Models.LieModel X .trialityD4 0 p f ∨
      (5 ≤ p ^ f ∧ CFSG.Models.LieModel X .G2 0 p f))) :
    InvolutionCentralizersGenerate X := by
  obtain ⟨p, f, hp2, hm⟩ := hX
  rcases hm with hm | ⟨hq, hm⟩
  · have hadm := hm.1
    have hp : p.Prime := hadm.1
    have : Fact p.Prime := ⟨hp⟩
    have hB := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm
    obtain ⟨-, hY⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .trialityD4 0 p f hp
      trivial hadm
    obtain ⟨eX⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique (t := .trialityD4) hp2 trivial hB hY
    have hZ := CFSG.ClassicalInvolution.RouteD.center_modelUniv_triality 0 p f hp hadm.2.1
    let eK : (modelUniv .trialityD4 0 p f hp).K ⧸ center (modelUniv .trialityD4 0 p f hp).K ≃*
        (modelUniv .trialityD4 0 p f hp).K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact involutionCentralizersGenerate_of_mulEquiv (eK.symm.trans eX.symm)
      (CFSG.ClassicalInvolution.G2D4Models.involutionCentralizersGenerate_td4_proved hp2 hadm)
  · have hadm := hm.1
    have hp : p.Prime := hadm.1
    have : Fact p.Prime := ⟨hp⟩
    have hB := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm
    obtain ⟨-, hY⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .G2 0 p f hp
      trivial hadm
    obtain ⟨eX⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique (t := .G2) hp2 trivial hB hY
    have hZ := CFSG.ClassicalInvolution.RouteD.center_modelUniv_G2 0 p f hp
    let eK : (modelUniv .G2 0 p f hp).K ⧸ center (modelUniv .G2 0 p f hp).K ≃*
        (modelUniv .G2 0 p f hp).K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have hG := (CFSG.ClassicalInvolution.Asc77.T3CII.T3U.g2d4_model_facts hp2 hq (Or.inl rfl)
      trivial hadm (Or.inl rfl)).2.2.2
    exact involutionCentralizersGenerate_of_mulEquiv (eK.symm.trans eX.symm) hG

theorem seitzFourInner_g2_td4
    :
    SeitzFourInner fun X _ => ∃ p f : ℕ, p ≠ 2 ∧ (CFSG.Models.LieModel X .trialityD4 0 p f ∨
      (5 ≤ p ^ f ∧ CFSG.Models.LieModel X .G2 0 p f)) :=
  seitzFourInner_of_involutionCentralizersGenerate fun _ _ hX =>
    involutionCentralizersGenerate_g2_td4 hX

end CFSG.LocalAnalysis.WeakClosure81
