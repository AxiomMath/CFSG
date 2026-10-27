module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.SylowPQMaximal.Defs
import CFSG.GroupTheory.SylowPQMaximal.Extension

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem uc22s2112r34q35_isPGroup_scalars_subgroupOf {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Finite K] (H : Subgroup (GL ι K)) {n : ℕ} (hK : Nat.card K - 1 ∣ 2 ^ n) :
    IsPGroup 2 ((StatedScalars ι K).subgroupOf H) := by
  let f : (StatedScalars ι K).subgroupOf H →* StatedScalars ι K :=
    { toFun := fun g => ⟨((g : H) : GL ι K), g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : StatedScalars ι K => (z : GL ι K)) h))
  have h2 : Nat.card (StatedScalars ι K) ∣ Nat.card Kˣ := Subgroup.card_range_dvd _
  rw [Nat.card_units] at h2
  exact IsPGroup.of_card_dvd_pow ((Subgroup.card_dvd_of_injective f hf).trans (h2.trans hK))

theorem uc22s2112r34q35_sylowPQMaximal_psp {X : Type} [Group X] {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hX : LieModel X .PSp 2 p 1)
    (hE : ∀ (K : Type) [Field K], Nat.card K = p →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedSp 2 K)) :
    CFSG.GroupTheory.SylowPQMaximal 2 5 X := by
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let := hField
  let := hFinite
  have hZ := uc22s2112r34q35_isPGroup_scalars_subgroupOf (StatedSp 2 K) (n := 2) (by
    rcases hp with rfl | rfl <;> rw [hK] <;> decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((hE K (by simpa using hK)).quotient_of_isPGroup _ hZ).of_mulEquiv eX.symm

theorem uc22s2112r34q35_sylowPQMaximal_psu {X : Type} [Group X] (hX : LieModel X .PSU 4 3 1)
    (hE : ∀ (K : Type) [Field K], Nat.card K = 9 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedSU 4 3 K)) :
    CFSG.GroupTheory.SylowPQMaximal 2 5 X := by
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let := hField
  let := hFinite
  have hZ := uc22s2112r34q35_isPGroup_scalars_subgroupOf (StatedSU 4 (3 ^ 1) K) (n := 3) (by
    rw [hK]; decide)
  have hE' : CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedSU 4 (3 ^ 1) K) :=
    hE K (by simpa using hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (hE'.quotient_of_isPGroup _ hZ).of_mulEquiv eX.symm

theorem uc22s2112r34q35_sylowPQMaximal_omegaOdd {X : Type} [Group X]
    (hX : LieModel X .POmegaOdd 3 3 1)
    (hE : ∀ (K : Type) [Field K], Nat.card K = 3 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedOmega (StatedQuadOdd 3 K))) :
    CFSG.GroupTheory.SylowPQMaximal 2 5 X := by
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let := hField
  let := hFinite
  have hZ := uc22s2112r34q35_isPGroup_scalars_subgroupOf (StatedOmega (StatedQuadOdd 3 K))
    (n := 1) (by rw [hK]; decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((hE K (by simpa using hK)).quotient_of_isPGroup _ hZ).of_mulEquiv eX.symm

theorem uc22s2112r34q35_sylowPQMaximal_g2 {X : Type} [Group X] (hX : LieModel X .G2 0 5 1)
    (hE : ∀ (K : Type) [Field K], Nat.card K = 5 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (CFSG.Blueprint.AdjointQuotient .G2 K)) :
    CFSG.GroupTheory.SylowPQMaximal 2 5 X := by
  obtain ⟨-, K, hField, -, hK, ⟨eX⟩⟩ := hX.chevalleyExceptionalModel (by decide)
  let := hField
  exact (hE K (by simpa using hK)).of_mulEquiv eX.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
