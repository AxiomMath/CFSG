module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomyBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_center_of_simple_quotient {X Q : Type*} [Group X] [Group Q] [Finite X]
    (hX : Subgroup.center X = ⊥) {Z : Subgroup Q} [Z.Normal]
    (hZc : Z ≤ Subgroup.center Q) (e : X ≃* Q ⧸ Z) :
    Z = Subgroup.center Q := by
  have h1 : Subgroup.center (Q ⧸ Z) = ⊥ := by
    have h2 := Subgroup.map_center_eq e.symm
    rw [hX] at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h2
  have h2 : Subgroup.center Q ≤ Z := by
    intro z hz
    have hz' : (QuotientGroup.mk' Z) z ∈ Subgroup.center (Q ⧸ Z) :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective Z)
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hz)
    rw [h1] at hz'
    simpa using hz'
  exact le_antisymm hZc h2

theorem commute_barX_of_ne {p : ℕ} [Fact p.Prime] {H M M' : Subgroup G}
    (hM : GLAPComponent p H M) (hM' : GLAPComponent p H M') (hne : M ≠ M') :
    ∀ a ∈ barX p H M, ∀ b ∈ barX p H M', Commute a b := by
  have hcommO : (⁅M, M'⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p H := by
    have hMl : CFSG.Open.lBalanceIsPComponent p H M := ((i183_glaPComponent_iff).1 hM).2
    have hM'l : CFSG.Open.lBalanceIsPComponent p H M' := ((i183_glaPComponent_iff).1 hM').2
    have h := CFSG.StandardType.GGDichotomy.commutator_le_primeCore_of_ne hMl hM'l hne
    rwa [CFSG.ComponentClassification.LBalance.primeCore_eq_map] at h
  have hcommBar : (⁅barX p H M, barX p H M'⁆ : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) = ⊥ := by
    have h1 : barX p H (⁅M, M'⁆ : Subgroup G) =
        (⁅barX p H M, barX p H M'⁆ : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) :=
      barX_commutator (p := p) (X := H) (A := M) (B := M') hM.1 hM'.1
    have h2 : barX p H (⁅M, M'⁆ : Subgroup G) = ⊥ :=
      (i183_barX_eq_bot_iff (commutator_le_of_le' (A := M) (B := M') hM.1 hM'.1)).2 hcommO
    exact h1.symm.trans h2
  intro a ha b hb
  have hmem : ⁅a, b⁆ = 1 := by
    have h := Subgroup.commutator_le.mp
      (le_of_eq hcommBar : (⁅barX p H M, barX p H M'⁆ : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) ≤ ⊥)
      a ha b hb
    simpa using h
  exact commutatorElement_eq_one_iff_mul_comm.1 hmem

theorem disjoint_barX_of_ne {p : ℕ} [Fact p.Prime] {H M M' : Subgroup G}
    (hM : GLAPComponent p H M) (hM' : GLAPComponent p H M') (hne : M ≠ M')
    (hZ : Subgroup.center (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥) :
    (barX p H M ⊓ barX p H M' : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) = ⊥ := by
  have hp : p.Prime := Fact.out
  have hZbar : Subgroup.center ↥(barX p H M) = ⊥ := by
    have h1 := Subgroup.map_center_eq (quotEquivBarX hp hM.1 hM.2.1)
    rw [hZ, Subgroup.map_bot] at h1
    exact h1.symm
  have hcomm := commute_barX_of_ne hM hM' hne
  refine le_antisymm ?_ bot_le
  rintro z ⟨hzM, hzM'⟩
  have hzcent : (⟨z, hzM⟩ : ↥(barX p H M)) ∈ Subgroup.center ↥(barX p H M) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 z hzM').eq
  rw [hZbar] at hzcent
  simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hzcent)

theorem card_quotient_mul_card_quotient_dvd_card_sup {p : ℕ} [Fact p.Prime]
    {H M M' : Subgroup G} (hM : GLAPComponent p H M) (hM' : GLAPComponent p H M')
    (hne : M ≠ M')
    (hZ : Subgroup.center (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥) :
    Nat.card (↥M ⧸ GLAPPrimeCore p ↥M) * Nat.card (↥M' ⧸ GLAPPrimeCore p ↥M') ∣
      Nat.card ↥(M ⊔ M') := by
  have hp : p.Prime := Fact.out
  have hcomm := commute_barX_of_ne hM hM' hne
  have hdisj := disjoint_barX_of_ne hM hM' hne hZ
  have hnorm : barX p H M' ≤ Subgroup.normalizer ((barX p H M : Subgroup _) : Set _) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hba : b * a = a * b := (hcomm a ha b hb).eq.symm
    have hcalc : b * a * b⁻¹ = a := by
      calc b * a * b⁻¹ = (a * b) * b⁻¹ := by rw [hba]
        _ = a := by group
    rw [hcalc]
    exact ha
  have hdisj' : Disjoint (barX p H M) (barX p H M') := by
    rw [disjoint_iff]
    exact hdisj
  have hcardSup : Nat.card ↥(barX p H M ⊔ barX p H M') =
      Nat.card (barX p H M) * Nat.card (barX p H M') :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj'
  have hcardM : Nat.card (barX p H M) = Nat.card (↥M ⧸ GLAPPrimeCore p ↥M) :=
    (Nat.card_congr (quotEquivBarX hp hM.1 hM.2.1).toEquiv).symm
  have hcardM' : Nat.card (barX p H M') = Nat.card (↥M' ⧸ GLAPPrimeCore p ↥M') :=
    (Nat.card_congr (quotEquivBarX hp hM'.1 hM'.2.1).toEquiv).symm
  have hsupBar : barX p H M ⊔ barX p H M' = barX p H (M ⊔ M') :=
    (i183_barX_sup hM.1 hM'.1).symm
  have hdvd : Nat.card (barX p H (M ⊔ M')) ∣ Nat.card ↥(M ⊔ M') := by
    have h1 := Subgroup.card_map_dvd (H := (M ⊔ M').subgroupOf H)
      (f := QuotientGroup.mk' (GLAPPrimeCore p ↥H))
    have h2 : Nat.card ((M ⊔ M').subgroupOf H) = Nat.card ↥(M ⊔ M') :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hM.1 hM'.1)).toEquiv
    rwa [h2] at h1
  calc Nat.card (↥M ⧸ GLAPPrimeCore p ↥M) * Nat.card (↥M' ⧸ GLAPPrimeCore p ↥M')
      = Nat.card (barX p H M) * Nat.card (barX p H M') := by rw [hcardM, hcardM']
    _ = Nat.card ↥(barX p H M ⊔ barX p H M') := hcardSup.symm
    _ = Nat.card (barX p H (M ⊔ M')) := by rw [hsupBar]
    _ ∣ Nat.card ↥(M ⊔ M') := hdvd

end CFSG.GroupTheory

end
