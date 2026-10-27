module

public import CFSG.RankThree.PartOne.S12.Facts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover

theorem three_le_of_dvd {p f : ℕ} (h5 : 5 ≤ p) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1) : 3 ≤ f := by
  by_contra hlt
  have hpos : 0 < 2 ^ f - 1 := by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega
  have hle := Nat.le_of_dvd hpos hpq
  have hf : f = 1 ∨ f = 2 := by omega
  rcases hf with rfl | rfl <;> omega

theorem center_eq_bot_of_multiplier
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ} (hqs : IsQuasisimple X)
    (hm : Models.LieModel (X ⧸ Subgroup.center X) t n 2 f)
    (hmult : Nat.card (Blueprint.Multiplier.generic t n 2 f ×
      Blueprint.Multiplier.exceptional t n 2 f) = 1) :
    Subgroup.center X = ⊥ := by
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ t n 2 f hm
  have : Group.IsPerfect (X ⧸ Subgroup.center X) := ⟨hcomm⟩
  have : Group.IsPerfect X := hqs.1
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _) hker
  have hdvd : Nat.card (QuotientGroup.mk' (Subgroup.center X)).ker ∣
      Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rw [Nat.card_congr (hopfMultiplierEquivGriess _).symm.toEquiv, Nat.card_congr e.toEquiv,
    hmult, Nat.dvd_one, QuotientGroup.ker_mk'] at hdvd
  rw [← Subgroup.card_eq_one]
  exact hdvd

theorem coprime_two_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Nat.Coprime 2 (2 ^ f - 1) := by
  rw [Nat.coprime_two_left]
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  obtain ⟨m, hm⟩ := h2
  exact ⟨m - 1, by omega⟩

theorem card_multiplier_psp_two {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSp 2 2 f ×
      Blueprint.Multiplier.exceptional .PSp 2 2 f) = 1 := by
  have hcop := coprime_two_two_pow_sub_one hf
  have hgen : Blueprint.Multiplier.genericOrders .PSp 2 2 f = (1, 1) := by
    change (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
    rw [hcop]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSp 2 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem card_multiplier_psl_four {f : ℕ} (hf : 2 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSL 4 2 f ×
      Blueprint.Multiplier.exceptional .PSL 4 2 f) = 1 := by
  have hcop : Nat.Coprime 4 (2 ^ f - 1) := by
    have h2 := coprime_two_two_pow_sub_one (f := f) (by omega)
    simpa using Nat.Coprime.pow_left 2 h2
  have hgen : Blueprint.Multiplier.genericOrders .PSL 4 2 f = (1, 1) := by
    change (Nat.gcd 4 (2 ^ f - 1), 1) = (1, 1)
    rw [hcop]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 4 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem card_multiplier_psu_five {f : ℕ} (h5 : ¬ 5 ∣ 2 ^ f + 1) :
    Nat.card (Blueprint.Multiplier.generic .PSU 5 2 f ×
      Blueprint.Multiplier.exceptional .PSU 5 2 f) = 1 := by
  have hcop : Nat.Coprime 5 (2 ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5
  have hgen : Blueprint.Multiplier.genericOrders .PSU 5 2 f = (1, 1) := by
    change (Nat.gcd 5 (2 ^ f + 1), 1) = (1, 1)
    rw [hcop]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 5 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem psp_two_center_trivial
    (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {f : ℕ} (hf : 1 ≤ f) (hqs : IsQuasisimple X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp 2 2 f) :
    Subgroup.center X = ⊥ :=
  center_eq_bot_of_multiplier hGA hqs ⟨hmodel.1, .inl hmodel⟩ (card_multiplier_psp_two hf)

theorem psl_four_center_trivial
    (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {f : ℕ} (hf : 2 ≤ f) (hqs : IsQuasisimple X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 4 2 f) :
    Subgroup.center X = ⊥ :=
  center_eq_bot_of_multiplier hGA hqs ⟨hmodel.1, .inl hmodel⟩ (card_multiplier_psl_four hf)

theorem psu_five_center_bot
    (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {f : ℕ} (h5 : ¬ 5 ∣ 2 ^ f + 1) (hqs : IsQuasisimple X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 5 2 f) :
    Subgroup.center X = ⊥ :=
  center_eq_bot_of_multiplier hGA hqs ⟨hmodel.1, .inl hmodel⟩ (card_multiplier_psu_five h5)

theorem sec12TwoGeneric_of_center_bot {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (hF : Sec12Facts G p A c L E) (hZ : Subgroup.center L = ⊥) :
    Sec12TwoGeneric p c L E := by
  rcases hF.two with hG | hS
  · exact hG
  · exfalso
    have h5 := hS.center_card
    rw [hZ] at h5
    simp at h5

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne

theorem Sec12Facts.isQuasisimple_L {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (hF : Sec12Facts G p A c L E) : CFSG.IsQuasisimple L :=
  hF.two.elim (fun hG => hG.quasisimple) (fun hS => hS.quasisimple)

end CFSG.RankThree.PartOne
