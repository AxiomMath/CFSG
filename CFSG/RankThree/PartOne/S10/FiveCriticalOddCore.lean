module

public import CFSG.RankThree.PartOne.S10.Defs
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBKSylowTwoCentralQuotient
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.RankThree.PartOne.FiveCritical

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem le_normalizer_of_characteristic_subgroupOf {G : Type} [Group G] {A L D : Subgroup G}
    (hAL : A ≤ normalizer (L : Set G)) (hDL : D ≤ L) (hD : (D.subgroupOf L).Characteristic) :
    A ≤ normalizer (D : Set G) := by
  refine le_normalizer_of_conj_mem_forall fun a ha d hd => ?_
  have h := Subgroup.characteristic_iff_le_comap.1 hD (L.normalizerMonoidHom ⟨a, hAL ha⟩)
  have h2 : L.normalizerMonoidHom ⟨a, hAL ha⟩ ⟨d, hDL hd⟩ ∈ D.subgroupOf L :=
    h (show (⟨d, hDL hd⟩ : ↥L) ∈ D.subgroupOf L from hd)
  exact h2

theorem oddThetaCore_le {G : Type} [Group G] [Finite G] (p : ℕ) (L : Subgroup G) :
    oddThetaCore p L ≤ L := by
  rw [oddThetaCore_eq_map]
  exact Subgroup.map_subtype_le _

theorem oddThetaCore_subgroupOf_eq {G : Type} [Group G] [Finite G] (p : ℕ) (L : Subgroup G) :
    (oddThetaCore p L).subgroupOf L =
      inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L) := by
  rw [oddThetaCore_eq_map, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

theorem oddThetaCore_subgroupOf_normal {G : Type} [Group G] [Finite G] (p : ℕ)
    (L : Subgroup G) : ((oddThetaCore p L).subgroupOf L).Normal := by
  rw [oddThetaCore_subgroupOf_eq]
  exact CFSG.RankThree.GroupTheory.SteinbergBK.inSubgroup_pPrimeCore_normal 2 _

theorem le_normalizer_oddThetaCore {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A L : Subgroup G} (hAL : A ≤ normalizer (L : Set G)) :
    A ≤ normalizer ((oddThetaCore p L : Subgroup G) : Set G) := by
  intro a ha
  have hθ := le_normalizer_theta_of_le_normalizer hp hAL ha
  rw [mem_normalizer_iff_map_conj_eq] at hθ ⊢
  have hθ' : (inSubgroup (aschbacherSolvableCore p) L).map (MulAut.conj a).toMonoidHom =
      inSubgroup (aschbacherSolvableCore p) L := hθ
  have h := map_inSubgroup_pPrimeCore_of_injective 2 (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective (inSubgroup (aschbacherSolvableCore p) L)
  rw [hθ'] at h
  rw [oddThetaCore, inSubgroup_oddCore_eq]
  exact h

theorem oddThetaCore_subgroupOf_isSolvable {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (L : Subgroup G) : Group.IsSolvable ((oddThetaCore p L).subgroupOf L) := by
  have hsol := (solvable_prime_complement_core_characterization (H := L) hp).1
  have hle : (oddThetaCore p L).subgroupOf L ≤ aschbacherSolvableCore p L := by
    rw [oddThetaCore_subgroupOf_eq]
    exact Subgroup.map_subtype_le _
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem oddThetaCore_subgroupOf_odd {G : Type} [Group G] [Finite G] (p : ℕ) (L : Subgroup G) :
    Odd (Nat.card ((oddThetaCore p L).subgroupOf L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := pPrimeCore_coprime_card (p := 2) (G := ↥(aschbacherSolvableCore p L))
  rw [oddThetaCore_subgroupOf_eq, inSubgroup,
    Subgroup.card_map_of_injective (aschbacherSolvableCore p L).subtype_injective]
  exact Nat.coprime_two_left.mp h

theorem oddThetaCore_subgroupOf_not_dvd {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (L : Subgroup G) : ¬ p ∣ Nat.card ((oddThetaCore p L).subgroupOf L) := by
  have hcop := (solvable_prime_complement_core_characterization (H := L) hp).2.2.1
  have hle : (oddThetaCore p L).subgroupOf L ≤ aschbacherSolvableCore p L := by
    rw [oddThetaCore_subgroupOf_eq]
    exact Subgroup.map_subtype_le _
  exact fun h => hcop (h.trans (Subgroup.card_dvd_of_le hle))

theorem inv_mul_mem_of_central_displacement {X : Type*} [Group X] {N O : Subgroup X}
    [O.Normal] (hperf : Group.IsPerfect X) (hNc : ∀ n ∈ N, ∀ x : X, n * x * n⁻¹ * x⁻¹ ∈ O)
    (α : MulAut X) (hαO : ∀ x ∈ O, α x ∈ O) (hαN : ∀ x : X, x⁻¹ * α x ∈ N) (x : X) :
    x⁻¹ * α x ∈ O := by
  have : Group.IsPerfect (X ⧸ O) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
  set φ : X ⧸ O →* X ⧸ O := QuotientGroup.map O O α.toMonoidHom (fun y hy => hαO y hy) with hφ
  have hφmk : ∀ y : X, φ (y : X ⧸ O) = ((α y : X) : X ⧸ O) := fun y =>
    QuotientGroup.map_mk O O α.toMonoidHom _ y
  have hcen : ∀ g : X ⧸ O, g⁻¹ * φ g ∈ Subgroup.center (X ⧸ O) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H y =>
      rw [hφmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H z =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have h := hNc _ (N.inv_mem (hαN y)) z⁻¹
        have e : (y⁻¹ * α y)⁻¹ * z⁻¹ * ((y⁻¹ * α y)⁻¹)⁻¹ * z⁻¹⁻¹ =
            (z * (y⁻¹ * α y))⁻¹ * ((y⁻¹ * α y) * z) := by group
        rw [e] at h
        exact h
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hcen
  have h1 := congrArg (fun f : X ⧸ O →* X ⧸ O => f (x : X ⧸ O)) hid
  simp only [hφmk, MonoidHom.id_apply] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem five_E_trivial_mod_O {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A L : Subgroup G} (hAL : A ≤ normalizer (L : Set G)) (hperf : Group.IsPerfect L)
    (hcomm : ⁅inSubgroup (aschbacherSolvableCore p) L, L⁆ ≤ oddThetaCore p L) {e : G}
    (he : e ∈ thetaQuotientCentralizer p A L) :
    ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ oddThetaCore p L := by
  have heA : e ∈ A := (mem_thetaQuotientCentralizer_iff.mp he).1
  have heN : e ∈ normalizer (L : Set G) := hAL heA
  have hker := ((sectionTen_quotient_action_kernel p hAL).2 e).mp he
  have hOn := oddThetaCore_subgroupOf_normal p L
  have hNn : (aschbacherSolvableCore p L).Normal := inferInstance
  set α : MulAut L := L.normalizerMonoidHom ⟨e, heN⟩ with hα
  have hαcoe : ∀ x : L, ((α x : L) : G) = e * x * e⁻¹ := fun x => rfl
  have hαO : ∀ x ∈ (oddThetaCore p L).subgroupOf L, α x ∈ (oddThetaCore p L).subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hαcoe]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_oddThetaCore hp hAL heA) (x : G)).mp hx
  have hαN : ∀ x : L, x⁻¹ * α x ∈ aschbacherSolvableCore p L := by
    intro x
    have h2 : α x * x⁻¹ ∈ aschbacherSolvableCore p L :=
      (Subgroup.mem_map_iff_mem L.subtype_injective).mp (hker.2 x x.2)
    have h3 := hNn.conj_mem _ h2 x⁻¹
    have e3 : x⁻¹ * (α x * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * α x := by group
    rwa [e3] at h3
  have hNc : ∀ n ∈ aschbacherSolvableCore p L, ∀ x : L,
      n * x * n⁻¹ * x⁻¹ ∈ (oddThetaCore p L).subgroupOf L := by
    intro n hn x
    rw [Subgroup.mem_subgroupOf]
    have h := hcomm (Subgroup.commutator_mem_commutator
      (Subgroup.mem_map_of_mem L.subtype hn) x.2)
    rwa [commutatorElement_def] at h
  intro l hl
  have h1 := inv_mul_mem_of_central_displacement hperf hNc α hαO hαN ⟨l, hl⟩
  have h2 := hOn.conj_mem _ h1 ⟨l, hl⟩
  have h3 : l * (l⁻¹ * (e * l * e⁻¹)) * l⁻¹ ∈ oddThetaCore p L := Subgroup.mem_subgroupOf.mp h2
  have e3 : l * (l⁻¹ * (e * l * e⁻¹)) * l⁻¹ = e * l * e⁻¹ * l⁻¹ := by group
  rwa [e3] at h3

end CFSG.RankThree.PartOne.FiveCritical
