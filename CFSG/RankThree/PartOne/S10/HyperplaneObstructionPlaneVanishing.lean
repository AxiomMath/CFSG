module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
import CFSG.RankThree.GroupTheory.SteinbergCDCentralizedSylowTwo

public section

namespace CFSG.RankThree.PartOne.HyperplaneObstruction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem vanishing_centralizes_plane_invariant_two_subgroups [Finite G] {p : ℕ} (hp : p.Prime)
    (hvan : AschVanishing G p) {A B : Subgroup G} (hAe : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (hBA : B ≤ A) (hBcard : Nat.card B = p ^ 2) {c : G}
    (hcA : c ∈ A) (hc1 : c ≠ 1) {U : Subgroup G}
    (hU : U ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)))
    (hU2 : IsPGroup 2 U) (hUB : B ≤ normalizer (U : Set G)) : ⁅U, B⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := inSubgroup (aschbacherSolvableCore p) C with hX
  have hBe : IsElementaryAbelian p B := SteinbergBM.isElementaryAbelian_of_le hAe hBA
  obtain ⟨-, ⟨T, hT⟩, -⟩ := hvan A hAe hAcard B hBA hBcard c hcA hc1
  have hAC : A ≤ C := by
    intro a ha
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAe.is_comm.comm (⟨a, ha⟩ : A) ⟨c, hcA⟩)
  have hBX : B ≤ normalizer (X : Set G) :=
    le_normalizer_theta_of_le_normalizer hp ((hBA.trans hAC).trans Subgroup.le_normalizer)
  let _ : MulDistribMulAction B X := conjActionOn hBX
  have hsmul : ∀ (b : B) (x : X), ((b • x : X) : G) = (b : G) * x * (b : G)⁻¹ := fun _ _ => rfl
  have hpX : ¬ p ∣ Nat.card X := by
    have h := (solvable_prime_complement_core_characterization (H := C) hp).2.2.1
    rwa [hX, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
  have hT' : ∀ b : B, ∀ x ∈ (T : Subgroup X), b • x = x := by
    intro b x hx
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hT
    have hxc := hle (Subgroup.mem_map_of_mem X.subtype hx)
    have h : (b : G) * (x : G) = (x : G) * (b : G) :=
      Subgroup.mem_centralizer_iff.mp hxc (b : G) (hBA b.2)
    apply Subtype.ext
    rw [hsmul]
    calc (b : G) * x * (b : G)⁻¹ = x * b * (b : G)⁻¹ := by rw [h]
      _ = x := by group
  have hU2' : IsPGroup 2 (U.subgroupOf X) := hU2.comap_subtype
  have hUinv : ∀ b : B, ∀ x ∈ U.subgroupOf X, b • x ∈ U.subgroupOf X := by
    intro b x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hUB b.2) x).mp hx
  have hmain := CFSG.RankThree.GroupTheory.centralized_sylow_two_controls_invariant_two_subgroups
    (p := p) (IsElementaryAbelian.isPGroup p B) hpX T hT' (U.subgroupOf X) hU2' hUinv
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h := hmain ⟨b, hb⟩ ⟨u, hU hu⟩ (by rw [Subgroup.mem_subgroupOf]; exact hu)
  have h' := congrArg Subtype.val h
  rw [hsmul] at h'
  calc b * u = b * u * (b : G)⁻¹ * b := by group
    _ = u * b := by simp only at h'; rw [h']

end CFSG.RankThree.PartOne.HyperplaneObstruction
