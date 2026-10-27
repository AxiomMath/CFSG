module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.RankThree.CentralLiftU

open CFSG.LieType.Steinberg

universe u v

section Lift

variable {H : Type u} {E : Type v} {G : Type*} [Group H] [Group E] [Group G] {π : E →* G}

theorem exists_lift_of_forall_section_prime [Finite H] [Finite E] {p : ℕ}
    (hsplit : ∀ (R : Type (max u v)) [Group R] [Finite R] (ρ : R →* H),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center R → IsPGroup p ρ.ker →
        ∃ s : H →* R, ∀ x, ρ (s x) = x)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker)
    (α : H →* G) : ∃ β : H →* E, π.comp β = α := by
  obtain ⟨s, hs⟩ := hsplit _ (pullbackFst α π) (pullbackFst_surjective hπ)
    (ker_pullbackFst_le_center hcen) (isPGroup_ker_pullbackFst hp)
  refine ⟨(MonoidHom.snd H E).comp ((pullback α π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : pullback α π) : H × E).1 = x := hs x
  have h2 := mem_pullback.1 (s x).2
  rw [h1] at h2
  exact h2.symm

end Lift

section Derived

variable {R : Type u} {S : Type v} [Group R] [Group S]

theorem derived_restrict_facts [Group.IsPerfect S] (ρ : R →* S) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center R) :
    Group.IsPerfect (commutator R) ∧ Function.Surjective (ρ.comp (commutator R).subtype) ∧
      (ρ.comp (commutator R).subtype).ker ≤ Subgroup.center (commutator R) := by
  obtain ⟨-, hperf, hsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective ρ hρ hcen inferInstance
  refine ⟨hperf, hsurj, fun x hx => ?_⟩
  exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 (hcen hx) y)

theorem isPGroup_ker_comp_subtype {p : ℕ} (ρ : R →* S) (hp : IsPGroup p ρ.ker) (D : Subgroup R) :
    IsPGroup p (ρ.comp D.subtype).ker := by
  refine hp.of_injective ((D.subtype.comp (ρ.comp D.subtype).ker.subtype).codRestrict ρ.ker
    fun x => x.2) fun x y hxy => ?_
  have h : ((x : D) : R) = ((y : D) : R) := congrArg (fun z : ρ.ker => (z : R)) hxy
  exact Subtype.ext (Subtype.ext h)

theorem exists_section_of_ker_comp_eq_bot (ρ : R →* S) (D : Subgroup R)
    (hsurj : Function.Surjective (ρ.comp D.subtype)) (hker : (ρ.comp D.subtype).ker = ⊥) :
    ∃ s : S →* R, ∀ x, ρ (s x) = x := by
  have hbij : Function.Bijective (ρ.comp D.subtype) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).1 hker, hsurj⟩
  let e := MulEquiv.ofBijective _ hbij
  exact ⟨D.subtype.comp e.symm.toMonoidHom, fun x => e.apply_symm_apply x⟩

end Derived

section Sylow

variable {R : Type u} {S : Type v} [Group R] [Group S]

theorem ker_eq_bot_of_sylow_commute [Finite R] [Group.IsPerfect R] {p : ℕ} [Fact p.Prime]
    (ρ : R →* S) (hcen : ρ.ker ≤ Subgroup.center R) (hp : IsPGroup p ρ.ker) (P : Sylow p R)
    (hP : ∀ x ∈ (P : Subgroup R), ∀ y ∈ (P : Subgroup R), x * y = y * x) : ρ.ker = ⊥ := by
  have h := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived P ρ.ker hcen
    hp).1
  have hbot : ⁅(P : Subgroup R), (P : Subgroup R)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hP y hy x hx
  rw [hbot] at h
  exact le_bot_iff.1 h

theorem sylow_commute_of_isCyclic_map (ρ : R →* S) (hcen : ρ.ker ≤ Subgroup.center R)
    (P : Subgroup R) (hcyc : IsCyclic (P.map ρ)) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  intro x hx y hy
  let f : P →* P.map ρ := (ρ.comp P.subtype).codRestrict _ fun z => ⟨z, z.2, rfl⟩
  have hf : f.ker ≤ Subgroup.center P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hz' : (z : R) ∈ ρ.ker := by
      have := congrArg Subtype.val hz
      exact this
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen hz') w)
  have := (f.isMulCommutative_of_isCyclic_of_ker_le_center hf).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

end Sylow

end CFSG.RankThree.CentralLiftU
