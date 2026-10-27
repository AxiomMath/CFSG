module

import CFSG.Models.Blueprint
public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement

@[expose] def Shape186OddTriv (S : Type) [Group S] : Prop :=
  CFSG.Quasithin.F6.IsL2 2 2 S ∨ LieModel S .PSU 3 2 2 ∨ LieModel S .PSL 3 2 1 ∨
  LieModel S .PSp 2 2 2 ∨ CFSG.Quasithin.F6.IsL2 5 2 S ∨ LieModel S .PSp 2 5 1 ∨
  LieModel S .PSp 2 3 1

@[expose] def OddMultiplier186Triv : Prop :=
  ∀ (S : Type) [Group S], Shape186OddTriv S →
    ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal], Z ≤ Subgroup.center X →
      Odd (Nat.card ↥Z) → ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ →
        Nonempty ((X ⧸ Z) ≃* S) → Z = ⊥

private theorem w183_shape186_isSimpleGroup {S : Type} [Group S] (h : Shape186OddTriv S) :
    IsSimpleGroup S := by
  rcases h with hS | hS | hS | hS | hS | hS | hS
  · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hS
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS
  · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hS
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS

private theorem w183_center_eq_bot_of_simple_perfect {S : Type} [Group S]
    (hS : IsSimpleGroup S) (hperf : Group.IsPerfect S) : Subgroup.center S = ⊥ := by
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative S := Subgroup.center_eq_top_iff.mp h
    haveI : Group.IsPerfect S := hperf
    haveI : Subsingleton S := inferInstance
    exact (not_subsingleton S) inferInstance

theorem Shape186OddTriv.exists_lieModel_table_dvd_two {S : Type} [Group S]
    (h : Shape186OddTriv S) :
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ), CFSG.Models.LieModel S t n p f ∧
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) ∣ 2 := by
  rcases h with hS | hS | hS | hS | hS | hS | hS
  ·
    refine ⟨.PSL, 2, 2, 2, ⟨hS.1, Or.inl hS⟩, ?_⟩
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 2 2 2 =
        (Nat.gcd 2 (2 ^ 2 - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 2 2 = (2, 1) := rfl
    rw [hgen, hexc]
    norm_num
  ·
    refine ⟨.PSU, 3, 2, 2, CFSG.Models.LieModel.of_blueprint (by decide) hS, ?_⟩
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 2 =
        (Nat.gcd 3 (2 ^ 2 + 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 2 = (1, 1) := rfl
    rw [hgen, hexc]
    norm_num
  ·
    refine ⟨.PSL, 3, 2, 1, CFSG.Models.LieModel.of_blueprint (by decide) hS, ?_⟩
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 2 1 =
        (Nat.gcd 3 (2 ^ 1 - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 1 = (2, 1) := rfl
    rw [hgen, hexc]
    norm_num
  ·
    refine ⟨.PSp, 2, 2, 2, CFSG.Models.LieModel.of_blueprint (by decide) hS, ?_⟩
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSp 2 2 2 =
        (Nat.gcd 2 (2 ^ 2 - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 2 2 = (1, 1) := rfl
    rw [hgen, hexc]
    norm_num
  ·
    refine ⟨.PSL, 2, 5, 2, ⟨hS.1, Or.inl hS⟩, ?_⟩
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 2 5 2 =
        (Nat.gcd 2 (5 ^ 2 - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 5 2 = (1, 1) := rfl
    rw [hgen, hexc]
    norm_num
  ·
    refine ⟨.PSp, 2, 5, 1, CFSG.Models.LieModel.of_blueprint (by decide) hS, ?_⟩
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSp 2 5 1 =
        (Nat.gcd 2 (5 ^ 1 - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 5 1 = (1, 1) := rfl
    rw [hgen, hexc]
    norm_num
  ·
    refine ⟨.PSp, 2, 3, 1, CFSG.Models.LieModel.of_blueprint (by decide) hS, ?_⟩
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSp 2 3 1 =
        (Nat.gcd 2 (3 ^ 1 - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 3 1 = (1, 1) := rfl
    rw [hgen, hexc]
    norm_num

theorem oddMultiplier186Triv_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    OddMultiplier186Triv := by
  intro S _ hS X _ _ Z _ hZc hZodd hperf hiso
  obtain ⟨e⟩ := hiso
  haveI : Finite S := Finite.of_equiv (X ⧸ Z) e.toEquiv
  haveI hsimp : IsSimpleGroup S := w183_shape186_isSimpleGroup hS
  haveI hperfX : Group.IsPerfect X := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    exact hperf
  haveI hperfS : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' Z))
      (e.surjective.comp (QuotientGroup.mk'_surjective Z))
  have hcenterS : Subgroup.center S = ⊥ :=
    w183_center_eq_bot_of_simple_perfect hsimp hperfS
  have hcenter_le_Z : Subgroup.center X ≤ Z := by
    intro c hc
    have hcS : e (c : X ⧸ Z) ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨u, rfl⟩ := e.surjective s
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z u
      change e (a : X ⧸ Z) * e (c : X ⧸ Z) = e (c : X ⧸ Z) * e (a : X ⧸ Z)
      rw [← map_mul, ← map_mul]
      congr 1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.mp hc a]
    rw [hcenterS, Subgroup.mem_bot] at hcS
    have h1 : (c : X ⧸ Z) = 1 := e.injective (by rw [hcS, map_one])
    exact (QuotientGroup.eq_one_iff c).mp h1
  have hZeq : Z = Subgroup.center X := le_antisymm hZc hcenter_le_Z
  obtain ⟨t, n, p, f, hm, hdvd⟩ := hS.exists_lieModel_table_dvd_two
  have hdvd' : Nat.card (Subgroup.center X) ∣ 2 :=
    (CFSG.RankThree.PartTwo.Sec21.Item221Proof.card_center_dvd_table hGA hperfX
      ((QuotientGroup.quotientMulEquivOfEq hZeq.symm).trans e) hm).trans hdvd
  have hZdvd : Nat.card ↥Z ∣ 2 := by rwa [hZeq]
  have hZ1 : Nat.card ↥Z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hZdvd with h | h
    · exact h
    · exfalso
      rw [h] at hZodd
      norm_num at hZodd
  exact Subgroup.eq_bot_of_card_eq Z hZ1

end CFSG.LocalAnalysis.WeakClosure81

end
