module

public import CFSG.RankThree.PartOne.KE.A1Group
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.KE

theorem quasisimple_solvable_normal_central {K : Type*} [Group K] (hK : CFSG.IsQuasisimple K)
    (N : Subgroup K) [N.Normal] [hN : Group.IsSolvable N] : ∀ n ∈ N, ∀ x : K, n * x = x * n := by
  intro n hn x
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK (inferInstance : N.Normal) with h | h
  · exfalso
    rw [h] at hN
    have hsolK : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := K)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := K)).symm.injective
    have := hK.1
    have := CFSG.LocalCores.isQuasisimple_nontrivial hK
    exact Group.IsPerfect.not_isSolvable _ hsolK
  · exact (Subgroup.mem_center_iff.1 (h hn) x).symm

theorem commutes_of_quasisimple_embedding {D G : Type*} [Group D] [Group G] (ψ : D →* G)
    (hψ : Function.Injective ψ) (P : Subgroup G) (hPψ : P ≤ ψ.range)
    (hP : CFSG.IsQuasisimple P) (hnorm : ∀ d : D, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P)
    (V : Subgroup D) [hVn : V.Normal] [hV : Group.IsSolvable V] :
    ∀ v ∈ V, ∀ u ∈ P, ψ v * u = u * ψ v := by
  set PD : Subgroup D := P.comap ψ with hPD
  have hPDnormal : PD.Normal := ⟨fun u hu d => by
    change ψ (d * u * d⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hnorm d _ hu⟩
  have hmapPD : PD.map ψ = P := by
    rw [hPD, Subgroup.map_comap_eq, inf_of_le_right hPψ]
  have hPDeq : PD ≃* P := (Subgroup.equivMapOfInjective PD ψ hψ).trans
    (MulEquiv.subgroupCongr hmapPD)
  have hPDq : CFSG.IsQuasisimple PD := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv hPDeq.symm hP
  have hPDperf : ⁅PD, PD⁆ = PD := Subgroup.isPerfect_iff.1 hPDq.1
  have hsol : ∀ N : Subgroup D, N ≤ PD → (∀ x ∈ PD, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      Group.IsSolvable N → ∀ n ∈ N, ∀ x ∈ PD, n * x = x * n := by
    intro N hNP hNnorm hNsol n hn x hx
    let N' : Subgroup PD := N.subgroupOf PD
    have hN'norm : N'.Normal := ⟨fun m hm g => by
      change ((g : D) * (m : D) * (g : D)⁻¹) ∈ N
      exact hNnorm g g.2 m hm⟩
    have hN'sol : Group.IsSolvable N' := by
      have e : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNP
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have := hN'norm
    have := hN'sol
    have h := quasisimple_solvable_normal_central hPDq N' ⟨n, hNP hn⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨x, hx⟩
    exact congrArg Subtype.val h
  have : PD.Normal := hPDnormal
  have hc := solvable_normal_centralizes_of_perfect PD hPDperf hsol V
  intro v hv u hu
  obtain ⟨x', hx'⟩ := hPψ hu
  have hx'P : x' ∈ PD := by
    change ψ x' ∈ P
    rw [hx']
    exact hu
  have := hc v hv x' hx'P
  rw [← hx', ← map_mul, ← map_mul, this]

theorem solvable_normal_cyclic_of_embedding_family {D G ι : Type*} [Group D] [Group G]
    (ψ : D →* G) (hψ : Function.Injective ψ) (P : ι → Subgroup G) (Z : Subgroup G)
    (hPψ : ∀ i, P i ≤ ψ.range) (hP : ∀ i, CFSG.IsQuasisimple (P i))
    (hnorm : ∀ i, ∀ d : D, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i)
    [hZ : IsCyclic Z] (hcent : ∀ d : D, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z)
    (V : Subgroup D) [hVn : V.Normal] [hV : Group.IsSolvable V] : IsCyclic V := by
  set ZD : Subgroup D := Z.comap ψ with hZD
  have : IsCyclic ZD := isCyclic_of_injective
    ((ψ.comp ZD.subtype).codRestrict Z (fun z => z.2)) (fun a b hab =>
      Subtype.ext (hψ (congrArg Subtype.val hab)))
  have hVZ : V ≤ ZD := fun v hv =>
    hcent v fun i u hu => commutes_of_quasisimple_embedding ψ hψ (P i) (hPψ i) (hP i)
      (hnorm i) V v hv u hu
  exact isCyclic_of_injective (Subgroup.inclusion hVZ) (Subgroup.inclusion_injective hVZ)

theorem solvable_normal_cyclic_of_embedding {D G : Type*} [Group D] [Group G] (ψ : D →* G)
    (hψ : Function.Injective ψ) (P Z : Subgroup G) (hPψ : P ≤ ψ.range)
    (hP : CFSG.IsQuasisimple P) (hnorm : ∀ d : D, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P)
    [hZ : IsCyclic Z] (hcent : ∀ d : D, (∀ u ∈ P, ψ d * u = u * ψ d) → ψ d ∈ Z)
    (V : Subgroup D) [hVn : V.Normal] [hV : Group.IsSolvable V] : IsCyclic V :=
  solvable_normal_cyclic_of_embedding_family (ι := Unit) ψ hψ (fun _ => P) Z (fun _ => hPψ)
    (fun _ => hP) (fun _ => hnorm) (hcent := fun d h => hcent d (h ()))  V

end CFSG.RankThree.PartOne.KE
