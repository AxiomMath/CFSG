module

public import CFSG.RankThree.PartOne.KE.CoreInner

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement

theorem core_fixes_of_normal_quasisimple {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C} {K : Subgroup C}
    (hKq : CFSG.IsQuasisimple K) (hKD : K ≤ Subgroup.centralizer ({x} : Set C))
    (hKn : ∀ d ∈ Subgroup.centralizer ({x} : Set C), ∀ k ∈ K, d * k * d⁻¹ ∈ K) :
    ∀ η ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))),
        ∀ k ∈ K, η k = k := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set Int : C →* MulAut C := MulAut.conj with hInt
  set D : Subgroup C := Subgroup.centralizer ({x} : Set C) with hD
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  have hmx : ∀ m ∈ M, m x = x := by
    intro m hm
    rw [hM] at hm
    refine fixes_of_commute_conj hC m x ?_
    have h := Subgroup.mem_centralizer_iff.1 hm.2 (MulAut.conj x) rfl
    exact h.symm
  have hmD : ∀ m ∈ M, ∀ d ∈ D, m d ∈ D := by
    intro m hm d hd
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h := Subgroup.mem_centralizer_singleton_iff.1 hd
    calc m d * x = m d * m x := by rw [hmx m hm]
      _ = m (d * x) := (map_mul m d x).symm
      _ = m (x * d) := by rw [h]
      _ = m x * m d := map_mul m x d
      _ = x * m d := by rw [hmx m hm]
  have hIntD : ∀ d ∈ D, Int d ∈ M := by
    intro d hd
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    exact congrArg Int (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
  set N : Subgroup ↥M := (D.map Int).subgroupOf M with hN
  have hNnormal : N.Normal := ⟨fun n hn g => by
    obtain ⟨d, hd, hdn⟩ := (Subgroup.mem_subgroupOf.1 hn)
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(g : MulAut C) d, hmD _ g.2 d hd, ?_⟩
    change Int ((g : MulAut C) d) = (g : MulAut C) * (n : MulAut C) * (g : MulAut C)⁻¹
    rw [← hdn]
    exact (aut_mul_conj_mul_inv (g : MulAut C) d).symm⟩
  set K' : Subgroup ↥M := (K.map Int).subgroupOf M with hK'
  have hKM : K.map Int ≤ M := by
    rintro _ ⟨k, hk, rfl⟩
    exact hIntD k (hKD hk)
  have hK'N : K' ≤ N := by
    intro k hk
    obtain ⟨k₀, hk₀, hkk⟩ := Subgroup.mem_subgroupOf.1 hk
    rw [Subgroup.mem_subgroupOf]
    exact ⟨k₀, hKD hk₀, hkk⟩
  have hK'sub : (K'.subgroupOf N).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun k hk n => ?_⟩
    obtain ⟨d, hd, hdn⟩ := Subgroup.mem_subgroupOf.1 n.2
    obtain ⟨k₀, hk₀, hkk⟩ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hk)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    refine ⟨d * k₀ * d⁻¹, hKn d hd k₀ hk₀, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [map_mul, map_mul, map_inv, hdn, hkk]
  have hK'comp : CFSG.IsComponent K' := by
    refine ⟨?_, Subgroup.IsSubnormal.trans hK'N hK'sub hNnormal.isSubnormal⟩
    have e1 : K' ≃* K.map Int := Subgroup.subgroupOfEquivOfLe hKM
    have e2 : K ≃* K.map Int := Subgroup.equivMapOfInjective K Int hinj
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e2.trans e1.symm) hKq
  have hRsol : Group.IsSolvable (aschbacherSolvableCore p M) :=
    (solvable_prime_complement_core_characterization (H := M) hp).1
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRsol
    (aschbacherSolvableCore_normal p M).isSubnormal).1 K' hK'comp
  rintro η ⟨η', hη', rfl⟩ k hk
  have hkM : Int k ∈ M := hIntD k (hKD hk)
  have hk' : (⟨Int k, hkM⟩ : ↥M) ∈ K' := Subgroup.mem_subgroupOf.2 ⟨k, hk, rfl⟩
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hk'
  have h2 := Subgroup.mem_centralizer_iff.1 h1 η' hη'
  refine fixes_of_commute_conj hC (η' : MulAut C) k ?_
  exact congrArg Subtype.val h2

end CFSG.RankThree.PartOne.KE
