module

public import CFSG.Quasithin.Background.G11Basic
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

theorem fstar_facts {M : Type*} [Group M] (G L : Subgroup M) [Finite ↥G]
    (hL : L = (CFSG.generalizedFitting ↥G).map G.subtype) :
    L ≤ G ∧ (∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) ∧
      (∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L) := by
  have hN : (CFSG.generalizedFitting ↥G).Normal := by
    rw [CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal _
  subst hL
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hN.conj_mem x hx ⟨g, hg⟩, rfl⟩
  · intro g hg hc
    have hmem : (⟨g, hg⟩ : ↥G) ∈
        Subgroup.centralizer (CFSG.generalizedFitting ↥G : Set ↥G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subtype.ext (hc x.1 ⟨x, hx, rfl⟩).symm
    exact ⟨⟨g, hg⟩, CFSG.centralizer_generalizedFitting_le ↥G hmem, rfl⟩

theorem exists_elemAbelian_twoRank {M : Type*} [Group M] (G : Subgroup M) [Finite ↥G] :
    ∃ E : Subgroup M, E ≤ G ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ twoRank ↥G := by
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (G := ↥G) Nat.one_lt_two (⊤ : Subgroup ↥G)
  refine ⟨E.map G.subtype, ?_, CFSG.SectionRank.isElemAbelian_map hE G.subtype, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective G)]
    exact hcard

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem two_lt_finrank_of_quasisimple {L : Subgroup (GLV V)} (hq : CFSG.IsQuasisimple ↥L) :
    2 < Module.finrank (ZMod 2) V := by
  by_contra hle
  push Not at hle
  have hcard : Nat.card V ≤ 4 := by
    haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
    calc 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
      _ = 4 := by norm_num
  have hsolv : Group.IsSolvable (GLV V) := by
    have := Equiv.Perm.isSolvable (α := V) hcard
    exact Group.isSolvable_of_isSolvable_injective (linToPerm_injective V)
  haveI : Group.IsSolvable ↥L := solvable_of_solvable_injective L.subtype_injective
  haveI : Group.IsPerfect ↥L := hq.1
  haveI : Nontrivial ↥L := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim a' b'])
  exact Group.IsPerfect.not_isSolvable ↥L inferInstance

end CFSG.Quasithin.RonanG73
