module

public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.S12.InputsTable

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover

variable {G : Type} [Group G] [Finite G]

theorem card_ker_dvd_card_hopfMultiplier {S L : Type} [Group S] [Finite S] [Group L] [Finite L]
    (hS : Group.IsPerfect S) (hL : Group.IsPerfect L) (p : L →* S)
    (hp : Function.Surjective p) (hpc : p.ker ≤ Subgroup.center L) :
    Nat.card p.ker ∣ Nat.card (hopfMultiplier S) := by
  have : Group.IsPerfect S := hS
  have : Group.IsPerfect L := hL
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e, -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier p hp hpc
  rw [← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem card_hopfMultiplier_of_model
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n p f : ℕ}
    (hm : Models.LieModel X t n p f) :
    Group.IsPerfect X ∧ Nat.card (hopfMultiplier X) =
      Nat.card (Blueprint.Multiplier.generic t n p f ×
        Blueprint.Multiplier.exceptional t n p f) := by
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA X t n p f hm
  have hperf : Group.IsPerfect X := ⟨hcomm⟩
  refine ⟨hperf, ?_⟩
  rw [Nat.card_congr (hopfMultiplierEquivGriess _).symm.toEquiv, Nat.card_congr e.toEquiv]

namespace Table123Generic

variable {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)

include h in
theorem localRank_quot_le_three
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) : localRank r (↥L ⧸ Subgroup.center ↥L) ≤ 3 := by
  have h1 := CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 (Subgroup.center ↥L)
    (hZ r hr hr2)
  exact h1.trans ((CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le)

include h in
theorem evenRank_quot_le
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L)) :
    evenRank (↥L ⧸ Subgroup.center ↥L) ≤ 3 :=
  CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le (m := 3) fun _ hr hr2 =>
    h.localRank_quot_le_three hZ hr hr2

include h in
theorem card_center_dvd_multiplier
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {t : StatedLieTag} {n f : ℕ} (hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) t n 2 f) :
    Nat.card (Subgroup.center ↥L) ∣
      Nat.card (Blueprint.Multiplier.generic t n 2 f ×
        Blueprint.Multiplier.exceptional t n 2 f) := by
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hd := card_ker_dvd_card_hopfMultiplier hperf h.quasisimple.1
    (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk', hcard] at hd

end Table123Generic

end CFSG.RankThree.PartOne
