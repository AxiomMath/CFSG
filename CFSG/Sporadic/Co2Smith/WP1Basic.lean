module

public import CFSG.Sporadic.Co2Smith.Bridge

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace LocalConfig

variable (c : LocalConfig.{u})

theorem eq_one_of_mA_trivial
    {s : S0} (hs : ∀ m : c.M, c.mA s m = m) : s = 1 := by
  let K0 : Subgroup S0 :=
    { carrier := {g | ∀ m, c.mA g m = m}
      mul_mem' := fun {g h} hg hh m => by
        rw [Set.mem_ofPred_eq] at hg hh
        rw [c.mA_mul, hh, hg]
      one_mem' := fun m => c.mA_one m
      inv_mem' := fun {g} hg m => by
        rw [Set.mem_ofPred_eq] at hg
        have := hg (c.mA g⁻¹ m)
        rw [c.mA_inv] at this
        exact this.symm }
  have hK0 : K0.Normal := ⟨fun g hg h m => by
    show c.mA (h * g * h⁻¹) m = m
    rw [c.mA_mul, c.mA_mul, hg, c.mA_inv]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K0 with h | h
  · have : s ∈ K0 := hs
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have hy : frS 0 ∈ K0 := h ▸ Subgroup.mem_top _
    exact c.w_ne_one (c.y1_fpf c.w (hy c.w))

theorem centralizer_E
    (g : c.H) (hg : ∀ e : c.E, g * e = e * g) :
    ∃ e₀ ∈ Subgroup.center c.E, g = e₀ := by
  obtain ⟨s, hs⟩ := c.ψ_bijective.2 (QuotientGroup.mk g)
  have hs1 : ∀ m : c.M, c.mA s m = m := by
    intro m
    obtain ⟨e, rfl⟩ := c.piM_surjective m
    rw [c.mA_piM_of hs.symm]
    congr 1
    apply Subtype.ext
    rw [c.cE_val, hg e, mul_inv_cancel_right]
  have h1 := c.eq_one_of_mA_trivial hs1
  have hgE : g ∈ c.E := by
    rw [← QuotientGroup.eq_one_iff, ← hs, h1, map_one]
  refine ⟨⟨g, hgE⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro e
  apply Subtype.ext
  exact (hg e).symm

end LocalConfig

theorem z0_mem_Qsub :
    z0 ∈ Qsub := Subgroup.subset_closure (Set.mem_insert _ _)

theorem centralizer_Q
    (g : K) (hg : g ∈ Cz) (hc : ∀ q ∈ Qsub, g * q = q * g) :
    g = 1 ∨ g = z0 := by
  have hcen := cfgCz.centralizer_E ⟨g, hg⟩ fun e => by
    have he : ((e.1 : Cz) : K) ∈ Qsub := by
      have h2 : e.1 ∈ CFSG.pCore 2 Cz := e.2
      rw [pCore_Cz, Subgroup.mem_subgroupOf] at h2
      exact h2
    exact Subtype.ext (hc _ he)
  obtain ⟨e₀, he₀, hge⟩ := hcen
  have hval : g = ((e₀.1 : Cz) : K) := congrArg Subtype.val hge
  rcases (cfgCz.mem_center_iff e₀).mp he₀ with h | h
  · left
    rw [hval, h]
    rfl
  ·
    right
    rw [hval, h]
    have hz0E : (⟨z0, z0_mem_Cz⟩ : Cz) ∈ CFSG.pCore 2 Cz := by
      rw [pCore_Cz, Subgroup.mem_subgroupOf]
      exact z0_mem_Qsub
    have hz0c : (⟨⟨z0, z0_mem_Cz⟩, hz0E⟩ : cfgCz.E) ∈ Subgroup.center cfgCz.E := by
      rw [Subgroup.mem_center_iff]
      intro e
      apply Subtype.ext
      apply Subtype.ext
      exact comm_of_mem_Cz e.1.2
    rcases (cfgCz.mem_center_iff _).mp hz0c with h1 | h1
    · exact absurd (congrArg (fun x : cfgCz.E => ((x.1 : Cz) : K)) h1) z0_ne_one
    · exact (congrArg (fun x : cfgCz.E => ((x.1 : Cz) : K)) h1).symm

end CFSG.Sporadic.Co2Smith
