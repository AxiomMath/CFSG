module

public import CFSG.Quasithin.Background.SmithB42Sp4Excl

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.Quasithin.B42Sp4

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem exists_label {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) :
    ∃ (d : ℕ) (S : Finset ℕ), 1 ≤ d ∧ Nat.card (EndRing (repOf π)) = 2 ^ d ∧ S.Nonempty ∧
      f ≤ S.card * d ∧ Module.finrank (EndRing (repOf π)) M = 4 ^ S.card ∧
      (S.card = 1 → ∃ j : ℕ, ∀ z : antiSp F, z * z = 1 →
        dispRank (π z) = d * (if j % 2 = 0 then rk0 z else rk1 z)) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sp4_descent hF hf hnt
  have : Module.Finite (EndRing (repOf π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, S, hSne, hS, ⟨Φ⟩, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOf π)) M)
  let _ : Algebra F E := ιF.toAlgebra
  refine ⟨d, S, hd1, hDcard, hSne, ?_, hdimW, fun hS1 => ?_⟩
  · have h := n_le_card_mul (n := 2 * f) (d := 2 * d) (by omega) (by omega)
      (fun i hi => Finset.mem_range.mp (hS hi)) hSne hshift
    nlinarith
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS1
    refine ⟨j, fun z hz => ?_⟩
    have hdisp : dispRank (π z) = d * (tensorRepS (F := F) E {j} z - 1).rank :=
      finrank_range_eq hDcard _ ιF ιD {j} Φ hdimW z
    have h1 := rank_tensorRepS_sub_one E ({j} : Finset ℕ) hz
    have h2 := rank_natRepS_sub_one_le E hz j
    rw [Finset.prod_coe_sort ({j} : Finset ℕ)
      (fun i => 4 - 2 * (natRepS (F := F) E i z - 1).rank), Finset.prod_singleton,
      Finset.card_singleton, pow_one] at h1
    have h3 : (tensorRepS (F := F) E {j} z - 1).rank = (natRepS (F := F) E j z - 1).rank := by
      omega
    rw [hdisp, h3, rank_natRepS_sub_one_eq]

end CFSG.Quasithin.G11.Harris.Sp4
