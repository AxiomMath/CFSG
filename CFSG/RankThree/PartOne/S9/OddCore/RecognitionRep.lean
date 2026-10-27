module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionModule
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionQD32
public import CFSG.RankThree.GroupTheory.SteinbergBMMinimalExtraspecialModule
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.OddCore37

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FixedRank36
  CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement IsMulCommutative

theorem isCyclic_inf_centralizer_of_qd32 {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {D R S : Subgroup G} [D.Normal] (hD : IsPGroup q D)
    (hrel : (inSubgroup frattini D).relIndex D = q ^ 4) (hR2 : IsPGroup 2 R)
    (hRD : R ⊓ Subgroup.centralizer (D : Set G) = ⊥) (hSR : S ≤ R)
    (hS : Nonempty (S ≃* QD32)) : IsCyclic ↥(R ⊓ Subgroup.centralizer (S : Set G)) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hel : IsElementaryAbelian q (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  have hfd : FiniteDimensional (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  set ρ : ↥R →* MulAut ↥D := conjRep R D with hρ
  have hdim : Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) = 2 ^ 2 := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) = q ^ 4 := by
      rw [← relIndex_inSubgroup_frattini_eq_card, hrel]
    have h2 : Nat.card (Additive (↥D ⧸ frattini ↥D)) = q ^ 4 := by
      rw [← h1]
      exact Nat.card_congr Additive.toMul
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod] at h2
    rw [Nat.pow_right_injective hq.two_le h2]
    norm_num
  have hinj : Function.Injective (frattiniRep q ρ) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : ρ r = 1 :=
      frattiniRep_eq_one hD hq2 ρ r (isPGroup_zpowers_map hR2 ρ r) hr
    have hmem : (r : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := by
      refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h := congrArg (fun f : MulAut ↥D => ((f ⟨g, hg⟩ : ↥D) : G)) h1
      simp only [hρ, coe_conjRep, MulAut.one_apply] at h
      calc g * (r : G) = ((r : G) * g * (r : G)⁻¹) * r := by rw [h]
        _ = r * g := by group
    rw [hRD, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨hSext, hS32, -⟩ := qd32_facts hS
  obtain ⟨z, hz, -⟩ := exists_center_generator_of_extraspecial hSext
  set ρS : Representation (ZMod q) ↥S (Additive (↥D ⧸ frattini ↥D)) :=
    (frattiniRep q ρ).comp (Subgroup.inclusion hSR) with hρS
  have hρSinj : Function.Injective ρS := fun x y h =>
    Subgroup.inclusion_injective hSR (hinj h)
  obtain ⟨-, -, -, hcyc⟩ :=
    SteinbergBM.minimal_extraspecial_module_scalar_centralizer.{0, 0, 0, 0}
      (S := ↥S) (n := 2) hSext (by rw [hS32]; norm_num) hz (K := ZMod q)
      (by rw [ZMod.ringChar_zmod_n]; exact hq2) hdim ρS hρSinj
  set C : Subgroup G := R ⊓ Subgroup.centralizer (S : Set G) with hC
  have hCR : C ≤ R := inf_le_left
  set ψ : ↥C →* (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ :=
    (frattiniRep q ρ).asGroupHom.comp (Subgroup.inclusion hCR) with hψ
  have hψinj : Function.Injective ψ := by
    intro x y h
    have h1 : frattiniRep q ρ (Subgroup.inclusion hCR x) =
        frattiniRep q ρ (Subgroup.inclusion hCR y) := by
      have := congrArg (fun u : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ =>
        (u : Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))) h
      exact this
    exact Subgroup.inclusion_injective hCR (hinj h1)
  have hH : ψ.range ≤ Subgroup.centralizer (Set.range ρS.asGroupHom) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    have hcs : (s : G) * (c : G) = (c : G) * (s : G) :=
      Subgroup.mem_centralizer_iff.1 c.2.2 (s : G) s.2
    have h1 : (Subgroup.inclusion hSR s) * (Subgroup.inclusion hCR c) =
        (Subgroup.inclusion hCR c) * (Subgroup.inclusion hSR s) := Subtype.ext hcs
    have h2 := congrArg (frattiniRep q ρ).asGroupHom h1
    rw [map_mul, map_mul] at h2
    exact h2
  have hcycH : IsCyclic ψ.range := hcyc (by infer_instance) _ hH
  exact (MulEquiv.isCyclic (MonoidHom.ofInjective hψinj)).2 hcycH

end CFSG.RankThree.PartOne.OddCore37
