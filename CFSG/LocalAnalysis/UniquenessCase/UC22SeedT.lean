module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Seed
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedG
import CFSG.RankThree.PartTwo.Sec21.Item22L2
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.RankThree.PartOne (InClassG omegaOne)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open Matrix (SpecialLinearGroup)

theorem exists_seedSetting {S H : Type} [Group S] [Group H] [Finite H] {ι : S →* H} (hG : InClassG S H ι) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (π : H →* SpecialLinearGroup (Fin 2) k)
      (T : Sylow 2 H), (T : Subgroup H) = ι.range ∧ SeedSetting (T : Subgroup H) π := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, K, hK, ⟨φ⟩, hsupp⟩ := hG.quotient
  obtain ⟨T, hT⟩ := inClassG_exists_sylow hG
  let ψ : H ⧸ K ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    φ.trans (CFSG.RankThree.PartTwo.Sec21.projSLTwoEquivSL (GaloisField 2 n))
  let π : H →* SpecialLinearGroup (Fin 2) (GaloisField 2 n) := ψ.toMonoidHom.comp (QuotientGroup.mk' K)
  have hker : π.ker = K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ x ∈ K
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance, π, T, hT, ?_⟩
  refine ⟨ψ.surjective.comp (QuotientGroup.mk'_surjective K), ?_, ?_, ?_⟩
  · rw [hT]
    exact hG.sylow
  · unfold CharTwo
    rw [pCoreOf_top_eq_pCore_two]
    intro x hx
    have hfit := hG.fitting_eq
    have hcen : x ∈ Subgroup.centralizer (CFSG.generalizedFitting H : Set H) := by
      rw [hfit]
      exact hx.2
    rw [← hfit]
    exact CFSG.centralizer_generalizedFitting_le H hcen
  · intro Y hY hYK
    rw [hker] at hYK
    exact hsupp Y (lt_top_iff_ne_top.mpr hY) hYK

theorem seed_hnc {S H : Type} [Group S] [Group H] {ι : S →* H} (hι : Function.Injective ι)
    (h : ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center S)).map ι⁆ ≠ ⊥) :
    ⁅(⊤ : Subgroup H), quasithinOmegaOneCenter ι.range⁆ ≠ ⊥ := by
  clear hι
  intro hbot
  refine h (eq_bot_iff.mpr ?_)
  rw [← hbot]
  refine Subgroup.commutator_mono le_rfl ?_
  unfold omegaOne quasithinOmegaOneCenter
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxc, hx2⟩, rfl⟩
  refine ⟨⟨⟨x, rfl⟩, ?_⟩, by rw [← map_pow, hx2, map_one]⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨s, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hxc s]

theorem seed_hJ {S H : Type} [Group S] [Finite S] [Group H] [Finite H] {ι : S →* H}
    (hι : Function.Injective ι)
    (h : Subgroup.centralizer (elemThompsonCenterTorsion S 2 : Set S) = ⊤) :
    omegaOneCenterOf (thompsonJ ι.range) ≤ Subgroup.centralizer (ι.range : Set H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : S ≃* ι.range := MonoidHom.ofInjective hι
  rw [← CFSG.Quasithin.elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf ι.range,
    ← CFSG.QuasithinUnique.Setup.Campbell.elemThompsonCenterTorsion_map_mulEquiv e 2]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ Subgroup.centralizer (elemThompsonCenterTorsion S 2 : Set S) := by
    rw [h]
    exact Subgroup.mem_top s
  have hxs := Subgroup.mem_centralizer_iff.mp hs x hx
  change ι s * ι x = ι x * ι s
  rw [← map_mul, ← map_mul, hxs]

end CFSG.LocalAnalysis.UniquenessCase.UC22
