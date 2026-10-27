module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalTwo
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentGroup
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.RankThree.PartOne.KCOrthogonal

private theorem tbkls5b_map_inf_centralizer {H K : Type*} [Group H] [Group K] {f : H →* K}
    (hf : Function.Injective f) (R : Subgroup H) (S : Set H) :
    (R ⊓ Subgroup.centralizer S).map f = R.map f ⊓ Subgroup.centralizer (f '' S) := by
  ext k
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_image]
  constructor
  · rintro ⟨h, ⟨hR, hc⟩, rfl⟩
    refine ⟨⟨h, hR, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hc s hs]
  · rintro ⟨⟨h, hR, rfl⟩, hc⟩
    refine ⟨h, ⟨hR, fun s hs => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc _ ⟨s, hs, rfl⟩

private theorem tbkls5b_weight_cases : ∀ u : Fin 3 → ZMod 3,
    u = 0 ∨ Two.weight u = 1 ∨ Two.weight u = 2 ∨ Two.weight u = 3 := by
  decide +kernel

theorem two_weight_eq_one_of_end_setup {G : Type} [Group G] [Finite G] {Bs L D J : Subgroup G}
    {x y z : G} {k : ℤ} {u : Fin 3 → ZMod 3} (ψ : ↥L ≃* ↥Two.omega) (hzL : z ∈ L)
    (hψz : ((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut) = Two.tor u)
    (htor : ∀ g : ↥L, (g : G) ∈ Bs ↔ ((ψ g : ↥Two.omega) : Two.Aut) ∈ (cm (ZMod 2)).range)
    (hyz : y = x ^ k * z) (hyx : y ∉ Subgroup.zpowers x) (hxL : x ∉ L) (hxD : x ∈ D)
    (hzD : z ∈ D) (hDcard : Nat.card ↥D = 9) (hJL : J ≤ L)
    (hJD : J ≤ Subgroup.centralizer (D : Set G)) (hJJ : ⁅J, J⁆ = J) (hJbot : J ≠ ⊥)
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) = D) : Two.weight u = 1 := by
  let Ψ : ↥L →* Two.Aut := Two.omega.subtype.comp ψ.toMonoidHom
  have hΨinj : Function.Injective Ψ := Two.omega.subtype_injective.comp ψ.injective
  have hΨz : Ψ ⟨z, hzL⟩ = Two.tor u := hψz
  set J' : Subgroup Two.Aut := (J.subgroupOf L).map Ψ with hJ'def
  have hJLperf : ⁅J.subgroupOf L, J.subgroupOf L⁆ = J.subgroupOf L :=
    CFSG.Quasithin.J4ZCent.perfect_subgroupOf hJL hJJ
  have hJ'perf : ⁅J', J'⁆ = J' := by
    rw [hJ'def, ← Subgroup.map_commutator, hJLperf]
  have hJ'bot : J' ≠ ⊥ := by
    intro h
    rw [hJ'def] at h
    have hLbot : J.subgroupOf L = ⊥ := by
      apply Subgroup.map_injective hΨinj
      rw [Subgroup.map_bot]
      exact h
    apply hJbot
    have hmap := Subgroup.map_subgroupOf_eq_of_le hJL
    rw [hLbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hJ'le : J' ≤ Two.omega ⊓ Subgroup.centralizer {Two.tor u} := by
    rw [hJ'def]
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    refine Subgroup.mem_inf.mpr ⟨(ψ g).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgJ : (g : G) ∈ J := Subgroup.mem_subgroupOf.mp hg
    have hgz : (g : G) * z = z * (g : G) :=
      (Subgroup.mem_centralizer_iff.mp (hJD hgJ) z hzD).symm
    have hgzL : g * ⟨z, hzL⟩ = ⟨z, hzL⟩ * g := by
      apply Subtype.ext
      simpa using hgz
    calc Ψ g * Two.tor u = Ψ g * Ψ ⟨z, hzL⟩ := by rw [← hΨz]
      _ = Ψ (g * ⟨z, hzL⟩) := (map_mul Ψ g ⟨z, hzL⟩).symm
      _ = Ψ (⟨z, hzL⟩ * g) := by rw [hgzL]
      _ = Ψ ⟨z, hzL⟩ * Ψ g := map_mul Ψ ⟨z, hzL⟩ g
      _ = Two.tor u * Ψ g := by rw [← hΨz]
  rcases tbkls5b_weight_cases u with h0 | h1 | h2 | h3
  · exfalso
    have hz1 : z = 1 := by
      have hψ1 : ((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut) = 1 := by
        rw [hψz, h0]
        simp [Two.tor]
      have h2' : (⟨z, hzL⟩ : ↥L) = 1 := by
        apply ψ.injective
        rw [map_one]
        exact Two.omega.subtype_injective hψ1
      simpa using Subtype.ext_iff.mp h2'
    apply hyx
    rw [hyz, hz1, mul_one]
    exact Subgroup.zpow_mem_zpowers x k
  · exact h1
  · exfalso
    have h3ne : (3 : ZMod 2) ≠ 0 := by decide +kernel
    have hbc : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide +kernel
    obtain ⟨c, hc⟩ : ∃ c : Multiplicative (Fin 3 → ZMod 3) →* ↥Two.omega,
        ∀ w, (c w : Two.Aut) = cm (ZMod 2) w := ⟨cmOmega h3ne hbc, fun _ => rfl⟩
    have hcm : cm (ZMod 2) = Two.omega.subtype.comp c := MonoidHom.ext fun w => (hc w).symm
    have htorus : (Bs.subgroupOf L).map Ψ = (cm (ZMod 2)).range := by
      ext t
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact (htor g).mp (Subgroup.mem_subgroupOf.mp hg)
      · intro ht
        have htω : t ∈ Two.omega := by
          have ht' : t ∈ (Two.omega.subtype.comp c).range := by rwa [← hcm]
          obtain ⟨w, hw⟩ := ht'
          rw [MonoidHom.comp_apply] at hw
          rw [← hw]
          exact (c w).2
        refine ⟨ψ.symm ⟨t, htω⟩, ?_, ?_⟩
        · change (ψ.symm ⟨t, htω⟩ : G) ∈ Bs
          apply (htor _).mpr
          show Two.omega.subtype (ψ (ψ.symm ⟨t, htω⟩)) ∈ (cm (ZMod 2)).range
          rw [MulEquiv.apply_symm_apply]
          simpa using ht
        · show Two.omega.subtype (ψ (ψ.symm ⟨t, htω⟩)) = t
          rw [MulEquiv.apply_symm_apply]
          rfl
    have hcent : Subgroup.centralizer ((J.subgroupOf L : Subgroup ↥L) : Set ↥L) =
        (Subgroup.centralizer (J : Set G)).subgroupOf L := by
      ext g
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      constructor
      · intro h k hk
        simpa using Subtype.ext_iff.mp (h ⟨k, hJL hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
      · intro h j hj
        exact Subtype.ext (h (j : G) (Subgroup.mem_subgroupOf.mp hj))
    have hDsub : D.subgroupOf L =
        Bs.subgroupOf L ⊓ Subgroup.centralizer ((J.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [hcent, ← hCJ]
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hDmap : (D.subgroupOf L).map Ψ =
        (cm (ZMod 2)).range ⊓ Subgroup.centralizer (J' : Set Two.Aut) := by
      rw [hDsub, tbkls5b_map_inf_centralizer hΨinj (Bs.subgroupOf L)
        ((J.subgroupOf L : Subgroup ↥L) : Set ↥L), htorus]
      have hcoe : Ψ '' ((J.subgroupOf L : Subgroup ↥L) : Set ↥L) =
          ((J' : Subgroup Two.Aut) : Set Two.Aut) := by
        rw [hJ'def, Subgroup.coe_map]
      rw [hcoe]
    have h9 := Two.card_torus_inf_centralizer_of_weight_eq_two u h2 J' hJ'le hJ'perf hJ'bot
    have hcardD : Nat.card ↥(D ⊓ L) = 9 := by
      rw [← hDmap, Subgroup.card_map_of_injective hΨinj] at h9
      have hcard_sub : Nat.card ↥(D.subgroupOf L) = Nat.card ↥(D ⊓ L) :=
        Nat.card_congr
          { toFun := fun g => ⟨(g.1 : G), Subgroup.mem_subgroupOf.mp g.2, g.1.2⟩
            invFun := fun t => ⟨⟨t.1, t.2.2⟩, Subgroup.mem_subgroupOf.mpr t.2.1⟩
            left_inv := fun g => by ext; rfl
            right_inv := fun t => by ext; rfl }
      rw [hcard_sub] at h9
      exact h9
    have hDL : D ≤ L := by
      have hcard_le : Nat.card ↥D ≤ Nat.card ↥(D ⊓ L) := by rw [hcardD, hDcard]
      have heq : D ⊓ L = D := Subgroup.eq_of_le_of_card_ge inf_le_left hcard_le
      exact heq ▸ inf_le_right
    exact hxL (hDL hxD)
  · exfalso
    have hsolv := Two.isSolvable_centralizer_of_weight_eq_three u h3
    have hbot : J' = ⊥ :=
      CFSG.Quasithin.J4ZCent.eq_bot_of_perfect_of_le_solvable hsolv hJ'le hJ'perf
    apply hJbot
    rw [hJ'def] at hbot
    have hLbot : J.subgroupOf L = ⊥ := by
      apply Subgroup.map_injective hΨinj
      rw [Subgroup.map_bot]
      exact hbot
    have hmap := Subgroup.map_subgroupOf_eq_of_le hJL
    rw [hLbot, Subgroup.map_bot] at hmap
    exact hmap.symm

end CFSG.StandardType

end
