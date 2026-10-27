module

public import CFSG.Sporadic.ONOddCore.PointwiseInner
public import CFSG.Sporadic.Schreier.ONSchreier

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

abbrev Mv :
    Subgroup Pv := onM.subgroupOf Pv

theorem mem_Mv
    {x : Pv} : x ∈ Mv ↔ (x : Equiv.Perm (Fin N)) ∈ onM := Subgroup.mem_subgroupOf

theorem mem_M_of_conj_mem_stabilizer
    {g : Pv} (hg : MulAut.conj g ∈ stabilizer Mv) :
    (g : Equiv.Perm (Fin N)) ∈ onM := by
  have hgM : ∀ x : Pv, (x : Equiv.Perm (Fin N)) ∈ onM ↔
      (g : Equiv.Perm (Fin N)) * x * (g : Equiv.Perm (Fin N))⁻¹ ∈ onM := fun x => by
    have := hg x
    rwa [mem_Mv, mem_Mv] at this
  set gz : Equiv.Perm (Fin N) := g * onz * (g : Equiv.Perm (Fin N))⁻¹ with hgz
  have hgzM : gz ∈ onM := (hgM zP).1 onz_mem_M
  have hgzc : gz ∈ CFSG.centerIn onM := by
    refine Subgroup.mem_inf.2 ⟨hgzM, Subgroup.mem_centralizer_iff.2 fun m hm => ?_⟩
    have hm' : (g : Equiv.Perm (Fin N))⁻¹ * m * g ∈ onM := by
      have h1 := (hgM ⟨(g : Equiv.Perm (Fin N))⁻¹ * m * g,
        mul_mem (mul_mem (inv_mem g.2) (onM_le hm)) g.2⟩).2
      simp only at h1
      exact h1 (by rwa [show (g : Equiv.Perm (Fin N)) * ((g : Equiv.Perm (Fin N))⁻¹ * m * g) *
        (g : Equiv.Perm (Fin N))⁻¹ = m by group])
    have hcomm := onz_comm_M hm'
    calc m * gz = g * (((g : Equiv.Perm (Fin N))⁻¹ * m * g) * onz) *
          (g : Equiv.Perm (Fin N))⁻¹ := by rw [hgz]; group
      _ = g * (onz * ((g : Equiv.Perm (Fin N))⁻¹ * m * g)) * (g : Equiv.Perm (Fin N))⁻¹ := by
          rw [hcomm]
      _ = gz * m := by rw [hgz]; group
  rw [onM_centerIn, mem_zpowers_iff_mem_range_orderOf, orderOf_onz, Finset.mem_image] at hgzc
  obtain ⟨k, hk, hkz⟩ := hgzc
  rw [Finset.mem_range] at hk
  have hgz_eq : gz = onz := by
    interval_cases k
    · exfalso
      apply onz_ne_one
      have h1 : gz = 1 := by rw [← hkz, pow_zero]
      calc onz = (g : Equiv.Perm (Fin N))⁻¹ * gz * g := by rw [hgz]; group
        _ = 1 := by rw [h1]; group
    · rw [← hkz, pow_one]
  rw [onM_eq_centralizer_z]
  refine Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc (g : Equiv.Perm (Fin N)) * onz = gz * g := by rw [hgz]; group
    _ = onz * g := by rw [hgz_eq]

theorem Mv_conjugacyInvariant :
    ConjugacyInvariant Mv := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := intrinsicCentralizer_conjugacyInvariant 2 onTSylow
  rwa [on_intrinsicCentralizer] at h

theorem innerQuotientOuterHom_Mv_injective :
    Function.Injective (innerQuotientOuterHom Mv) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (subgroupInner Mv) q
  have hβ : (β : MulAut Pv) ∈ inner Pv := (QuotientGroup.eq_one_iff _).1 hq
  obtain ⟨g, hg⟩ := hβ
  have hgs : MulAut.conj g ∈ stabilizer Mv := by
    rw [hg]
    exact β.2
  have hgM := mem_M_of_conj_mem_stabilizer hgs
  rw [Subgroup.mem_bot]
  apply (QuotientGroup.eq_one_iff _).2
  refine ⟨⟨g, mem_Mv.2 hgM⟩, Subtype.ext ?_⟩
  exact hg

theorem innerQuotientRestriction_Mv_injective :
    Function.Injective (innerQuotientRestriction Mv) := by
  rw [← MonoidHom.ker_eq_bot_iff, innerQuotientRestriction_ker, eq_bot_iff]
  rintro _ ⟨β, rfl⟩
  have hfix : ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → ((β : stabilizer Mv) : MulAut Pv) m = m :=
    fun m hm => pointwiseKernel_fixes Mv β m (mem_Mv.2 hm)
  rw [Subgroup.mem_bot]
  apply (QuotientGroup.eq_one_iff _).2
  have hzM : zP ∈ Mv := mem_Mv.2 (show (zP : Equiv.Perm (Fin N)) ∈ onM from onz_mem_M)
  rcases pointwise_M_cases _ hfix with h1 | hz
  · refine ⟨1, Subtype.ext ?_⟩
    show ((subgroupInnerHom Mv 1 : stabilizer Mv) : MulAut Pv) = ((β : stabilizer Mv) : MulAut Pv)
    rw [map_one, h1]
    rfl
  · refine ⟨⟨zP, hzM⟩, Subtype.ext ?_⟩
    show ((subgroupInnerHom Mv ⟨zP, hzM⟩ : stabilizer Mv) : MulAut Pv) =
      ((β : stabilizer Mv) : MulAut Pv)
    rw [hz]
    rfl

@[expose] def outerPvEquiv :
    InnerQuotient Mv ≃* Outer Pv :=
  MulEquiv.ofBijective (innerQuotientOuterHom Mv)
    ⟨innerQuotientOuterHom_Mv_injective, innerQuotientOuterHom_surjective Mv Mv_conjugacyInvariant⟩

@[expose] def outerPvToM :
    Outer Pv →* Outer onM :=
  (equivalence (Subgroup.subgroupOfEquivOfLe onM_le)).toMonoidHom.comp
    ((innerQuotientRestriction Mv).comp outerPvEquiv.symm.toMonoidHom)

theorem outerPvToM_injective :
    Function.Injective outerPvToM :=
  (equivalence (Subgroup.subgroupOfEquivOfLe onM_le)).injective.comp
    (innerQuotientRestriction_Mv_injective.comp outerPvEquiv.symm.injective)

@[expose] def outerONToM :
    Outer Blueprint.NativeSporadic.ON →* Outer onM :=
  outerPvToM.comp (equivalence (G := Blueprint.NativeSporadic.ON) (H := Pv)
    (by exact onEquivPv)).toMonoidHom

theorem outerONToM_injective :
    Function.Injective outerONToM := by
  rw [outerONToM, MonoidHom.coe_comp]
  exact outerPvToM_injective.comp (MulEquiv.injective _)

theorem r3e_on_outer_action_embeds_in_local_outer_group :
    (∃ f : Outer Pv →* Outer onM, Function.Injective f) ∧
      ∃ f : Outer Blueprint.NativeSporadic.ON →* Outer onM, Function.Injective f :=
  ⟨⟨outerPvToM, outerPvToM_injective⟩, ⟨outerONToM, outerONToM_injective⟩⟩

end CFSG.Sporadic.ONOddCore
