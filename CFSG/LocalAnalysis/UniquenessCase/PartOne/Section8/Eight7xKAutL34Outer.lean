module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.Quasithin.Background.C41PfF
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter
open CFSG.RankThree.PartTwo.KFacts.L34
open Matrix

private theorem right_action_of_mem_center {G : Type*} [CommGroup G]
    {s : G ⋊[inversionAction G] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))}
    (hs : s ∈ Subgroup.center _) (x : G) : inversionAction G s.right x = x := by
  have h := Subgroup.mem_center_iff.mp hs (SemidirectProduct.inl x)
  rw [← SemidirectProduct.inl_left_mul_inr_right s] at h
  have hleft := congrArg SemidirectProduct.left h
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inl,
    SemidirectProduct.left_inr, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
    MulAut.one_apply, map_one, one_mul, mul_one] at hleft
  have h2 : x = inversionAction G s.right x := by
    rw [mul_comm x s.left] at hleft
    exact mul_left_cancel hleft
  exact h2.symm

private theorem not_mem_center_of_right_eq_inl {G : Type*} [CommGroup G] {u : G}
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    {s : G ⋊[inversionAction G] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))}
    (hs : s ∈ Subgroup.center _)
    (hright : s.right = (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (0 : ZMod 2))) :
    False := by
  have hact := right_action_of_mem_center hs u
  rw [hright, inversionAction_apply] at hact
  simp only [add_zero, one_ne_zero, ↓reduceIte] at hact
  have h2 : u * u = 1 := by
    have := congrArg (fun z => u * z) hact
    simpa using this.symm
  refine hu1 ?_
  calc u = u ^ 3 * (u * u)⁻¹ := by group
    _ = 1 := by rw [hu3, h2, inv_one, mul_one]

private theorem not_mem_center_of_right_eq_inr {G : Type*} [CommGroup G] {u : G}
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    {s : G ⋊[inversionAction G] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))}
    (hs : s ∈ Subgroup.center _)
    (hright : s.right = (Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2))) :
    False := by
  have hact := right_action_of_mem_center hs u
  rw [hright, inversionAction_apply] at hact
  simp only [zero_add, one_ne_zero, ↓reduceIte] at hact
  have h2 : u * u = 1 := by
    have := congrArg (fun z => u * z) hact
    simpa using this.symm
  refine hu1 ?_
  calc u = u ^ 3 * (u * u)⁻¹ := by group
    _ = 1 := by rw [hu3, h2, inv_one, mul_one]

private theorem isSolvable_centralizer_projectiveSL
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (α : MulAut (projectiveSL 3 K)) (hα : α * α = 1)
    (hout : α ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (hcentral : ∀ β : MulAut (projectiveSL 3 K),
      β * α * β⁻¹ * α⁻¹ ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    IsSolvable ↥(Subgroup.centralizer ({α} : Set (MulAut (projectiveSL 3 K)))) := by
  classical
  have := LinearFieldFour.finite_of_card_eq_four hK
  have := LinearFieldFour.charP_two_of_card_eq_four hK
  have : Finite (MulAut (projectiveSL 3 K)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hK]; norm_num)
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hK
  have hker : Ψ.ker = (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
    ker_eq_range_conj hσ hK hΨ
  have hsurj : Function.Surjective Ψ := surjective_of_nf hΨ
  have hc : ∀ A : GL (Fin 3) K,
      Ψ (conjAut 3 K A) = SemidirectProduct.inl (GeneralLinearGroup.det A) := fun A => by
    rw [← nf_zero_zero (σ := frobeniusEquiv K 2), hΨ]
    rfl
  have hf : Ψ (fieldAut 3 K (frobeniusEquiv K 2)) =
      SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2),
        Multiplicative.ofAdd (0 : ZMod 2)) := by
    rw [← nf_one_zero (σ := frobeniusEquiv K 2), hΨ, map_one]
    rfl
  have hd : Ψ (dualAut 3 K) =
      SemidirectProduct.inr (Multiplicative.ofAdd (0 : ZMod 2),
        Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [← nf_zero_one (σ := frobeniusEquiv K 2), hΨ, map_one]
    rfl
  have hcenterΨ : Ψ α ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨β, rfl⟩ := hsurj s
    have hmem : β * α * β⁻¹ * α⁻¹ ∈ Ψ.ker := by rw [hker]; exact hcentral β
    have h1 : Ψ β * Ψ α * (Ψ β)⁻¹ * (Ψ α)⁻¹ = 1 := by
      have := MonoidHom.mem_ker.mp hmem
      simpa only [map_mul, map_inv] using this
    calc Ψ β * Ψ α = (Ψ β * Ψ α * (Ψ β)⁻¹ * (Ψ α)⁻¹) * (Ψ α * Ψ β) := by group
      _ = 1 * (Ψ α * Ψ β) := by rw [h1]
      _ = Ψ α * Ψ β := one_mul _
  obtain ⟨u, hu1⟩ := exists_units_ne_one hK
  have hu3 : u ^ 3 = 1 := units_pow_three hK u
  rcases involution_cases_card hK hσ hα with
    hinn | ⟨⟨H, hH⟩, hcard⟩ | ⟨⟨H, hH⟩, hcard⟩ | ⟨⟨_, _⟩, hcard⟩
  · exact absurd hinn hout
  · exfalso
    have hright : (Ψ α).right =
        (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (0 : ZMod 2)) := by
      rw [hH, map_mul, map_mul, map_inv, hc, hf]
      simp
    exact not_mem_center_of_right_eq_inl hu1 hu3 hcenterΨ hright
  · exfalso
    have hright : (Ψ α).right =
        (Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)) := by
      rw [hH, map_mul, map_mul, map_inv, hc, hd]
      simp
    exact not_mem_center_of_right_eq_inr hu1 hu3 hcenterΨ hright
  · set C := Subgroup.centralizer ({α} : Set (MulAut (projectiveSL 3 K))) with hC
    set Q := (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓ C with hQ
    have hQmap : Q =
        (autFixed α).map (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) := by
      rw [hQ, hC, map_conj_autFixed (conj_injective hK)]
    have hQcard : Nat.card ↥Q = 72 := by
      rw [hQmap, Subgroup.card_map_of_injective (conj_injective hK), hcard]
    have : Group.IsSolvable ↥Q :=
      CFSG.Quasithin.C41Pf.isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 3) (b := 2)
        Nat.prime_two Nat.prime_three (by norm_num) (by rw [hQcard]; norm_num)
    have hScard : Nat.card (Kˣ ⋊[inversionAction Kˣ]
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) = 12 := by
      rw [SemidirectProduct.card, Nat.card_prod, card_units_eq_three hK]
      simp [Nat.card_eq_fintype_card]
    have : Finite (Kˣ ⋊[inversionAction Kˣ]
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
      Nat.finite_of_card_ne_zero (by rw [hScard]; norm_num)
    have : Group.IsSolvable (Kˣ ⋊[inversionAction Kˣ]
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
      CFSG.Quasithin.C41Pf.isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 2) (b := 1)
        Nat.prime_two Nat.prime_three (by norm_num) (by rw [hScard]; norm_num)
    have hker_eq : (Ψ.comp C.subtype).ker = Q.subgroupOf C := by
      rw [← MonoidHom.comap_ker, Subgroup.comap_subtype, hker]
      apply le_antisymm
      · intro x hx
        rw [Subgroup.mem_subgroupOf] at hx
        rw [Subgroup.mem_subgroupOf, hQ, Subgroup.mem_inf]
        exact ⟨hx, x.2⟩
      · intro x hx
        rw [Subgroup.mem_subgroupOf, hQ, Subgroup.mem_inf] at hx
        rw [Subgroup.mem_subgroupOf] at ⊢
        exact hx.1
    have hrange_eq : (Subgroup.inclusion (show Q ≤ C from inf_le_right)).range = Q.subgroupOf C :=
      Subgroup.inclusion_range _
    exact Group.isSolvable_of_ker_le_range
      (Subgroup.inclusion (show Q ≤ C from inf_le_right)) (Ψ.comp C.subtype) (by
        rw [hker_eq, hrange_eq])

theorem card_outer_psl_three_four {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2) : Nat.card (Outer L) = 12 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : Finite K := LinearFieldFour.finite_of_card_eq_four hK4
  have hcard : Nat.card (Outer L) = Nat.card (Outer (projectiveSL 3 K)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv
  rw [hcard]
  have hinner : Nat.card (inner (projectiveSL 3 K)) = 20160 := by
    have h : inner (projectiveSL 3 K) =
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := rfl
    rw [h, ← Nat.card_congr (MonoidHom.ofInjective (conj_injective hK4)).toEquiv,
      card_projectiveSL hK4]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner (projectiveSL 3 K))
  rw [card_mulAut hK4, hinner] at h
  exact (show Nat.card (MulAut (projectiveSL 3 K) ⧸ inner (projectiveSL 3 K)) = 12 by omega)

theorem isSolvable_centralizer_of_graphField_psl_three_four {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2) (α : MulAut L) (hα : α ^ 2 = 1)
    (hout : α ∉ inner L) (hcentral : ∀ β : MulAut L, β * α * β⁻¹ * α⁻¹ ∈ inner L) :
    IsSolvable ↥(Subgroup.centralizer ({α} : Set (MulAut L))) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : Finite K := LinearFieldFour.finite_of_card_eq_four hK4
  let e : MulAut L ≃* MulAut (projectiveSL 3 K) := MulAut.congr φ
  have hinnerimg : (inner L).map e.toMonoidHom =
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ
  have hαmul : α * α = 1 := by rw [← sq]; exact hα
  have hα'e : e α * e α = 1 := by rw [← map_mul, hαmul, map_one]
  have hout'e : e α ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    intro h
    apply hout
    have hmem : e α ∈ (inner L).map e.toMonoidHom := by rw [hinnerimg]; exact h
    obtain ⟨x, hx, hxeq⟩ := hmem
    rw [e.injective hxeq] at hx
    exact hx
  have hcentral'e : ∀ β' : MulAut (projectiveSL 3 K),
      β' * e α * β'⁻¹ * (e α)⁻¹ ∈
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    intro β'
    have hmem := hcentral (e.symm β')
    have hmem' : e (e.symm β' * α * (e.symm β')⁻¹ * α⁻¹) ∈ (inner L).map e.toMonoidHom :=
      ⟨_, hmem, rfl⟩
    rw [hinnerimg] at hmem'
    have h2 : e (e.symm β' * α * (e.symm β')⁻¹ * α⁻¹) =
        β' * e α * β'⁻¹ * (e α)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply]
    rwa [h2] at hmem'
  have : Group.IsSolvable ↥(Subgroup.centralizer ({e α} : Set (MulAut (projectiveSL 3 K)))) :=
    isSolvable_centralizer_projectiveSL hK4 (e α) hα'e hout'e hcentral'e
  have himg2 : (Subgroup.centralizer ({α} : Set (MulAut L))).map e.toMonoidHom =
      Subgroup.centralizer ({e α} : Set (MulAut (projectiveSL 3 K))) := by
    apply le_antisymm
    · have hsub := Subgroup.map_centralizer_le_centralizer_image ({α} : Set (MulAut L))
        e.toMonoidHom
      simpa using hsub
    · intro β hβ
      refine ⟨e.symm β, ?_, e.apply_symm_apply β⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hβ
      change e.symm β ∈ Subgroup.centralizer ({α} : Set (MulAut L))
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hβ
  have θ : ↥(Subgroup.centralizer ({α} : Set (MulAut L))) ≃*
      ↥(Subgroup.centralizer ({e α} : Set (MulAut (projectiveSL 3 K)))) :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr himg2)
  exact Group.isSolvable_of_isSolvable_injective (f := θ.toMonoidHom) θ.injective

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
