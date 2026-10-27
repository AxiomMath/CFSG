module

public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuProfile
public import CFSG.LieType.Ree.TitsSylowLocalSchreier

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

theorem mem_subgroupOf_iff {H K : Subgroup G} (x : H) : x ∈ K.subgroupOf H ↔ (x : G) ∈ K :=
  Subgroup.mem_subgroupOf

theorem normalizer_subgroupOf {P K : Subgroup G} (hK : K ≤ P) :
    Subgroup.normalizer ((K.subgroupOf P : Subgroup P) : Set P) =
      (Subgroup.normalizer (K : Set G)).subgroupOf P := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      have := (h ⟨g, hK hg⟩).1 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hg
      have hgP : g ∈ P := by
        have h1 : (x : G) * g * (x : G)⁻¹ ∈ P := hK hg
        have : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x := by group
        rw [this]
        exact P.mul_mem (P.mul_mem (P.inv_mem x.2) h1) x.2
      have := (h ⟨g, hgP⟩).2 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 this
  · intro h g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h g

theorem centralizer_subgroupOf {P K : Subgroup G} (hK : K ≤ P) :
    Subgroup.centralizer ((K.subgroupOf P : Subgroup P) : Set P) =
      (Subgroup.centralizer (K : Set G)).subgroupOf P := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    exact congrArg Subtype.val (h ⟨g, hK hg⟩ (Subgroup.mem_subgroupOf.2 hg))
  · intro h g hg
    exact Subtype.ext (h g (Subgroup.mem_subgroupOf.1 hg))

theorem inf_subgroupOf {P A B : Subgroup G} :
    (A ⊓ B).subgroupOf P = A.subgroupOf P ⊓ B.subgroupOf P := by
  ext x
  simp [Subgroup.mem_subgroupOf]

abbrev ruSP : Subgroup ruP := ruS.subgroupOf ruP

theorem ruSP_center :
    ((Subgroup.center (ruSP : Subgroup ruP)).map ruSP.subtype : Subgroup ruP) =
      (Subgroup.zpowers ruZ).subgroupOf ruP := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← center_ruS]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyS : ((y : ruP) : Equiv.Perm (Fin 4060)) ∈ ruS := Subgroup.mem_subgroupOf.1 y.2
    refine ⟨⟨_, hyS⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    have hg : (g : Equiv.Perm (Fin 4060)) ∈ ruP := ruS_le g.2
    have := Subgroup.mem_center_iff.1 hy ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 g.2⟩
    exact congrArg (fun u : ruSP => ((u : ruP) : Equiv.Perm (Fin 4060))) this
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨x, Subgroup.mem_subgroupOf.2 (hyx ▸ y.2)⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    have := Subgroup.mem_center_iff.1 hy ⟨_, Subgroup.mem_subgroupOf.1 g.2⟩
    have h' := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h' ⊢
    rw [← hyx]
    exact h'

theorem ruCP_eq :
    ruC.subgroupOf ruP = Subgroup.centralizer
    (((Subgroup.center (ruSP : Subgroup ruP)).map ruSP.subtype : Subgroup ruP) : Set ruP) := by
  rw [ruSP_center, centralizer_subgroupOf ((Subgroup.zpowers_le).2 ruZ_mem),
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, ruC_eq_centralizer, inf_subgroupOf,
    Subgroup.subgroupOf_self, top_inf_eq]

theorem ruNP_eq :
    ruN.subgroupOf ruP =
    Subgroup.normalizer ((ruK.subgroupOf ruP : Subgroup ruP) : Set ruP) := by
  rw [normalizer_subgroupOf ruK_le, ruN_eq_normalizer, inf_subgroupOf, Subgroup.subgroupOf_self,
    top_inf_eq]

theorem isSolvable_mulAut_ruSP :
    Group.IsSolvable (MulAut (ruSP : Subgroup ruP)) := by
  have := AT_Ru_Sylow_order_profile_automorphisms.2.2.2.2
  exact Group.isSolvable_of_surjective
    (f := (MulAut.congr (Subgroup.subgroupOfEquivOfLe ruS_le).symm).toMonoidHom)
    (MulEquiv.surjective _)

theorem AT_Ru_permutation_Schreier :
    Group.IsSolvable (Outer ruP) := by
  have hcrit := CFSG.LieType.Ree.tits_Sylow_local_Schreier_criterion (G := ruP) ruSylow
    (ruC.subgroupOf ruP) ruCP_eq (ruK.subgroupOf ruP) (Subgroup.subgroupOf_mono _ ruK_leS)
    (ruN.subgroupOf ruP) ruNP_eq (ruJ.subgroupOf ruP)
    (isPGroup_ruJ.of_equiv (Subgroup.subgroupOfEquivOfLe ruJ_le).symm)
    (Subgroup.subgroupOf_mono _ ruJ_leS) (Subgroup.subgroupOf_mono _ ruJ_leC) ?_ ?_ ?_ ?_
  · exact hcrit.2.2.1 isSolvable_mulAut_ruSP
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono _ ruJ_leC)]
    intro h k hh hk
    rw [mem_subgroupOf_iff] at hh hk ⊢
    exact (Subgroup.normal_subgroupOf_iff ruJ_leC).1 ruJ_normal h k hh hk
  · intro x hx
    obtain ⟨hxC, hxJ⟩ := Subgroup.mem_inf.1 hx
    rw [centralizer_subgroupOf ruJ_le, mem_subgroupOf_iff] at hxJ
    rw [mem_subgroupOf_iff] at hxC ⊢
    exact ruCentralizer_J ⟨hxC, hxJ⟩
  · intro x hx
    obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.1 hx
    rw [centralizer_subgroupOf ruK_le, mem_subgroupOf_iff] at hxK
    rw [mem_subgroupOf_iff] at hxN ⊢
    exact ruCentralizer_K ⟨hxN, hxK⟩
  · rw [← Subgroup.subgroupOf_sup ruC_le ruN_le, ← ruP_eq_sup, Subgroup.subgroupOf_self]

end CFSG.Sporadic.RuSchreier
