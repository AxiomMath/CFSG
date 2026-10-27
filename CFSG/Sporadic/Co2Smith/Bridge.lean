module

public import CFSG.Sporadic.Co2Smith.RigidIso

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem inclusion_range_inf :
    (Subgroup.inclusion S0_le_Cz).range ⊓ CFSG.pCore 2 Cz = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨⟨y, hy⟩, hyx⟩, hxQ⟩ := Subgroup.mem_inf.mp hx
  have hxQ' : x ∈ Qsub.subgroupOf Cz := by rw [← pCore_Cz]; exact hxQ
  rw [Subgroup.mem_subgroupOf] at hxQ'
  have hyx' : y = (x : K) := congrArg Subtype.val hyx
  have hmem : (x : K) ∈ S0 ⊓ Qsub := ⟨hyx' ▸ hy, hxQ'⟩
  rw [S0_inf_Q, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext hmem

noncomputable abbrev cfgCz :
    SmithConfig.{0} :=
  SmithConfig.ofComplement Cz smithLocal_Cz (Subgroup.inclusion S0_le_Cz)
    (Subgroup.inclusion_injective S0_le_Cz) inclusion_range_inf

theorem complement_bijective {H : Type u} [Group H] {E S : Subgroup H} [E.Normal]
    (h1 : S ⊓ E = ⊥) (h2 : S ⊔ E = ⊤) :
    Function.Bijective ((QuotientGroup.mk' E).comp S.subtype) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro s hs
    have hsE : (s : H) ∈ E := (QuotientGroup.eq_one_iff _).mp hs
    have hmem : (s : H) ∈ S ⊓ E := ⟨s.2, hsE⟩
    rw [h1, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · intro q
    have htop : S.map (QuotientGroup.mk' E) = ⊤ := by
      have h := congrArg (Subgroup.map (QuotientGroup.mk' E)) h2
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective E)] at h
      exact h
    have hq : q ∈ S.map (QuotientGroup.mk' E) := htop ▸ Subgroup.mem_top q
    obtain ⟨s, hs, rfl⟩ := hq
    exact ⟨⟨s, hs⟩, rfl⟩

@[expose] noncomputable def complementEquiv
    {H : Type u} [Group H] (hH : SmithLocal H)
    {S : Subgroup H} (h1 : S ⊓ CFSG.pCore 2 H = ⊥) (h2 : S ⊔ CFSG.pCore 2 H = ⊤) : S0 ≃* S :=
  (MulEquiv.ofBijective resS0 resS0_bijective).trans
    ((Classical.choice hH.quotient_equiv).symm.trans
      (MulEquiv.ofBijective _ (complement_bijective h1 h2)).symm)

@[expose] noncomputable def cfgOf
    {H : Type u} [Group H] [Finite H] (hH : SmithLocal H)
    (S : Subgroup H) (h1 : S ⊓ CFSG.pCore 2 H = ⊥) (h2 : S ⊔ CFSG.pCore 2 H = ⊤) :
    SmithConfig.{u} :=
  SmithConfig.ofComplement H hH (S.subtype.comp (complementEquiv hH h1 h2).toMonoidHom)
    (S.subtype_injective.comp (complementEquiv hH h1 h2).injective) (by
      rw [eq_bot_iff]
      rintro x ⟨⟨y, rfl⟩, hx⟩
      have hmem : (S.subtype.comp (complementEquiv hH h1 h2).toMonoidHom y) ∈
          S ⊓ CFSG.pCore 2 H := ⟨(complementEquiv hH h1 h2 y).2, hx⟩
      rwa [h1] at hmem)

theorem smith_local_bridge
    {H : Type u} [Group H] [Finite H] (hH : SmithLocal H)
    (S : Subgroup H) (h1 : S ⊓ CFSG.pCore 2 H = ⊥) (h2 : S ⊔ CFSG.pCore 2 H = ⊤) :
    Nonempty (H ≃* Subgroup.centralizer ({z0} : Set K)) :=
  ⟨(cfgOf hH S h1 h2).compareEquiv cfgCz⟩

end CFSG.Sporadic.Co2Smith
