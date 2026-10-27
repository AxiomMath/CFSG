module

import CFSG.GroupTheory.FrattiniQuotient
import CFSG.GroupTheory.LocalCores.NormalPKernelPreimage
import CFSG.GroupTheory.LocalCores.PrimeSetCoreIsomorphism
import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport
import CFSG.RankThree.Coprime.SolvableLinearPStability
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

public section

namespace CFSG.LocalAnalysis.SteinbergBQ

open CFSG Subgroup

open scoped IsMulCommutative

theorem solvable_action_p_stability {p : ℕ} (hp : p.Prime) (hodd : Odd p) {G : Type*} [Group G]
    [Finite G] [Group.IsSolvable G] {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : G →* MulAut P) (halt : 5 ≤ p ∨ Odd (Nat.card G)) {x : G}
    (hx : ∀ u : P, ρ x (u⁻¹ * ρ x u) = u⁻¹ * ρ x u) :
    (QuotientGroup.mk x : G ⧸ ρ.ker) ∈ pCore p (G ⧸ ρ.ker) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, helem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  obtain ⟨hqA, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hP
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  set qA := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P)
    with hqAdef
  set τ := CFSG.Semidihedral.ElementaryActionTransport.primeFieldAction (p := p) (qA.comp ρ)
    with hτ
  have hΦmap : (frattini P).map (ρ x).toMonoidHom = frattini P :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance (ρ x)
  have hτx : ((τ x : LinearMap.GeneralLinearGroup (ZMod p) (Additive (P ⧸ frattini P))) :
      Module.End (ZMod p) (Additive (P ⧸ frattini P))) =
      CFSG.LinearGroups.quotientLinearMap p (frattini P) (ρ x)
        (CFSG.LinearGroups.le_comap_of_map_eq (frattini P) hΦmap) := by
    apply LinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    obtain rfl : v = Additive.ofMul (u : P ⧸ frattini P) := by rw [hu]; rfl
    rw [CFSG.LinearGroups.quotientLinearMap_apply, hτ,
      CFSG.Semidihedral.ElementaryActionTransport.primeFieldAction_apply]
    exact congrArg Additive.ofMul (hqA (ρ x) u)
  have hquad := CFSG.LinearGroups.quadratic_elementary_quotient p (frattini P) (ρ x) hΦmap hx
  have hlin := CFSG.RankThree.Coprime.solvable_linear_p_stability hp hodd τ halt (x := x)
    (by rw [hτx]; exact hquad)
  have hτker : τ.ker = (qA.comp ρ).ker :=
    CFSG.Semidihedral.ElementaryActionTransport.primeFieldAction_kernel _
  have hle : ρ.ker ≤ τ.ker := by
    intro g hg
    rw [hτker, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]
  set N : Subgroup (G ⧸ ρ.ker) := τ.ker.map (QuotientGroup.mk' ρ.ker) with hN
  have hNn : N.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hNp : IsPGroup p N := by
    refine (hker.comap_of_injective (QuotientGroup.kerLift ρ)
      (QuotientGroup.kerLift_injective ρ)).to_le ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [hτker, SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk, MonoidHom.mem_ker]
    exact hg
  have hπ : ({⟨p, hp⟩} : Set Nat.Primes) = {q : Nat.Primes | q.val = p} := by
    ext q
    exact ⟨fun h => show q.val = p by rw [Set.mem_singleton_iff.1 h],
      fun h => Set.mem_singleton_iff.2 (Subtype.ext h)⟩
  have hlin' : (QuotientGroup.mk x : G ⧸ τ.ker) ∈
      piCore ({⟨p, hp⟩} : Set Nat.Primes) (G ⧸ τ.ker) := by
    rw [hπ, ← pCore_eq_piCore]
    exact hlin
  have h1 : ((QuotientGroup.mk x : G ⧸ ρ.ker) : (G ⧸ ρ.ker) ⧸ N) ∈
      piCore ({⟨p, hp⟩} : Set Nat.Primes) ((G ⧸ ρ.ker) ⧸ N) := by
    rw [← CFSG.LocalCores.prime_set_core_isomorphism
      (QuotientGroup.quotientQuotientEquivQuotient ρ.ker τ.ker hle).symm]
    exact ⟨_, hlin', rfl⟩
  rw [pCore_eq_piCore, ← hπ, ← CFSG.LocalCores.normal_p_kernel_core_preimage hp N hNp]
  exact h1

end CFSG.LocalAnalysis.SteinbergBQ
