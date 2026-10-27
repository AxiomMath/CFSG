module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringD4

open CFSG

theorem inSubgroup_perfectResidual_le_commutator {G : Type*} [Group G] (C : Subgroup G) :
    inSubgroup perfectResidual C ≤ ⁅C, C⁆ := by
  have h1 : perfectResidual C ≤ derivedSeries C 1 := iInf_le _ 1
  rw [derivedSeries_one] at h1
  calc inSubgroup perfectResidual C = (perfectResidual C).map C.subtype := rfl
    _ ≤ (commutator C).map C.subtype := Subgroup.map_mono h1
    _ = ⁅C, C⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]

theorem inSubgroup_perfectResidual_eq_bot_of_solvable {G : Type*} [Group G] (C : Subgroup G)
    (hC : Group.IsSolvable C) : inSubgroup perfectResidual C = ⊥ := by
  obtain ⟨n, hn⟩ := hC.solvable
  have : perfectResidual C = ⊥ := le_bot_iff.mp (hn ▸ iInf_le _ n)
  rw [inSubgroup, this, Subgroup.map_bot]

theorem eq_bot_of_isPerfect_of_isSolvable' {H : Type*} [Group H] {P : Subgroup H}
    (hp : Group.IsPerfect P) (hs : Group.IsSolvable P) : P = ⊥ := by
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  exact Group.IsPerfect.not_isSolvable P hs

theorem map_commutator_centralizer_conj {G : Type*} [Group G] (g x : G) :
    (⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆).map
        (MulAut.conj g).toMonoidHom =
      ⁅Subgroup.centralizer ({g * x * g⁻¹} : Set G),
        Subgroup.centralizer ({g * x * g⁻¹} : Set G)⁆ := by
  rw [Subgroup.map_commutator,
    Sec21.Item228Census3Proof.map_centralizer_singleton (MulAut.conj g) x]
  rfl

theorem fixed_on_commutator_of_conj {G : Type*} [Group G] (φ : MulAut G) (g x : G)
    (hg : φ g = g)
    (h : ∀ d ∈ ⁅Subgroup.centralizer ({g * x * g⁻¹} : Set G),
      Subgroup.centralizer ({g * x * g⁻¹} : Set G)⁆, φ d = d) :
    ∀ d ∈ ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆, φ d = d := by
  intro d hd
  have hd' : g * d * g⁻¹ ∈ ⁅Subgroup.centralizer ({g * x * g⁻¹} : Set G),
      Subgroup.centralizer ({g * x * g⁻¹} : Set G)⁆ := by
    rw [← map_commutator_centralizer_conj]
    exact ⟨d, hd, rfl⟩
  have h2 := h _ hd'
  rw [map_mul, map_mul, map_inv, hg] at h2
  exact mul_left_cancel (mul_right_cancel h2)

theorem false_of_conj_B_A {G : Type*} [Group G] {A : Subgroup G} (hA : Group.IsPerfect A)
    (hA1 : A ≠ ⊥) (hAcen : ∀ s ∈ A, (∀ t ∈ A, t * s = s * t) → s ^ 3 = 1 → s = 1)
    {y h : G} (hyA : ∀ t ∈ A, t * y = y * t)
    (hcomm : ∀ x ∈ Subgroup.centralizer ({y} : Set G), ∀ x' ∈ Subgroup.centralizer ({y} : Set G),
      x * x' * x⁻¹ * x'⁻¹ ∈ A)
    (hshape : Group.IsSolvable (Subgroup.centralizer ({h * y * h⁻¹} : Set G)) ∨
      ∃ N : Subgroup G, N ≤ Subgroup.centralizer ({h * y * h⁻¹} : Set G) ∧
        (∀ x ∈ Subgroup.centralizer ({h * y * h⁻¹} : Set G),
          ∀ x' ∈ Subgroup.centralizer ({h * y * h⁻¹} : Set G), x * x' * x⁻¹ * x'⁻¹ ∈ N) ∧
        IsQuasisimple N ∧ ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1) :
    False := by
  have hAC : A ≤ Subgroup.centralizer ({y} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hyA t ht
  have hCA : ⁅Subgroup.centralizer ({y} : Set G), Subgroup.centralizer ({y} : Set G)⁆ = A := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun x hx x' hx' => ?_) ?_
    · rw [commutatorElement_def]
      exact hcomm x hx x' hx'
    · calc A = ⁅A, A⁆ := (Subgroup.isPerfect_iff.mp hA).symm
        _ ≤ _ := Subgroup.commutator_mono hAC hAC
  have hmapC : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer ({h * y * h⁻¹} : Set G) :=
    Sec21.Item228Census3Proof.map_centralizer_singleton (MulAut.conj h) y
  rcases hshape with hsol | ⟨N, hNC, hNcomm, hNq, x, hxN, hxc, hx1, hx3⟩
  ·
    let e : Subgroup.centralizer ({y} : Set G) ≃* Subgroup.centralizer ({h * y * h⁻¹} : Set G) :=
      ((Subgroup.centralizer ({y} : Set G)).equivMapOfInjective _
        (MulAut.conj h).injective).trans (MulEquiv.subgroupCongr hmapC)
    have hsolC : Group.IsSolvable (Subgroup.centralizer ({y} : Set G)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have hsolA : Group.IsSolvable A :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAC)
        (Subgroup.inclusion_injective hAC)
    exact hA1 (eq_bot_of_isPerfect_of_isSolvable' hA hsolA)
  ·
    have hcomm' : ⁅Subgroup.centralizer ({h * y * h⁻¹} : Set G),
        Subgroup.centralizer ({h * y * h⁻¹} : Set G)⁆ = A.map (MulAut.conj h).toMonoidHom := by
      rw [← hmapC, ← Subgroup.map_commutator, hCA]
    have hle1 : ⁅Subgroup.centralizer ({h * y * h⁻¹} : Set G),
        Subgroup.centralizer ({h * y * h⁻¹} : Set G)⁆ ≤ N :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact hNcomm a ha b hb
    have hle2 : N ≤ ⁅Subgroup.centralizer ({h * y * h⁻¹} : Set G),
        Subgroup.centralizer ({h * y * h⁻¹} : Set G)⁆ :=
      calc N = ⁅N, N⁆ := (Subgroup.isPerfect_iff.mp hNq.1).symm
        _ ≤ _ := Subgroup.commutator_mono hNC hNC
    have hNeq : N = A.map (MulAut.conj h).toMonoidHom := by
      rw [← hcomm']
      exact le_antisymm hle2 hle1
    have hxA : x ∈ A.map (MulAut.conj h).toMonoidHom := hNeq ▸ hxN
    obtain ⟨s, hsA, hsx⟩ := hxA
    have hsx' : h * s * h⁻¹ = x := hsx
    have hcen : ∀ t ∈ A, t * s = s * t := fun t ht => by
      have htN : h * t * h⁻¹ ∈ N := hNeq ▸ ⟨t, ht, rfl⟩
      have h1 := hxc _ htN
      rw [← hsx'] at h1
      have h2 : h * s * h⁻¹ * (h * t * h⁻¹) = h * t * h⁻¹ * (h * s * h⁻¹) := h1
      have h3 : h * (s * t) * h⁻¹ = h * (t * s) * h⁻¹ := by
        calc h * (s * t) * h⁻¹ = h * s * h⁻¹ * (h * t * h⁻¹) := by group
          _ = h * t * h⁻¹ * (h * s * h⁻¹) := h2
          _ = h * (t * s) * h⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h3)).symm
    have hs3 : s ^ 3 = 1 := by
      have h1 : (h * s * h⁻¹) ^ 3 = 1 := by rw [hsx']; exact hx3
      rw [conj_pow] at h1
      have h2 : h * s ^ 3 * h⁻¹ = h * 1 * h⁻¹ := by rw [h1]; group
      exact mul_left_cancel (mul_right_cancel h2)
    have hs1 := hAcen s hsA hcen hs3
    apply hx1
    rw [← hsx', hs1]
    group

theorem isSolvable_centralizer_of_conj {G : Type*} [Group G] (c w : G)
    (h : Group.IsSolvable (Subgroup.centralizer ({c * w * c⁻¹} : Set G))) :
    Group.IsSolvable (Subgroup.centralizer ({w} : Set G)) := by
  have hmapC : (Subgroup.centralizer ({w} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * w * c⁻¹} : Set G) :=
    Sec21.Item228Census3Proof.map_centralizer_singleton (MulAut.conj c) w
  let e : Subgroup.centralizer ({w} : Set G) ≃* Subgroup.centralizer ({c * w * c⁻¹} : Set G) :=
    ((Subgroup.centralizer ({w} : Set G)).equivMapOfInjective _
      (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmapC)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_of_commutator_le {G : Type*} [Group G] (D R : Subgroup G) (hDR : ⁅D, D⁆ ≤ R)
    (hR : Group.IsSolvable R) : Group.IsSolvable D := by
  have hDDsol : Group.IsSolvable (⁅D, D⁆ : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDR)
      (Subgroup.inclusion_injective hDR)
  have hmap : (commutator D).map D.subtype = ⁅D, D⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let e : commutator D ≃* (⁅D, D⁆ : Subgroup G) :=
    (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have : Group.IsSolvable (commutator D) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_commutator_iff.1 this

end CFSG.RankThree.PartTwo.Sec8.HeringD4
