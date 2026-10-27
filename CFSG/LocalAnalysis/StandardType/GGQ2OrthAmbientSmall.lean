module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneForm
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthType
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Quasithin.Background.SzG11G94Solv
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.GroupTheory.WeirSylow
open CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
private theorem hirr_one_one (hK : Nat.card K = 2) :
    ∀ s : K, s ^ 2 + (1 : K) * s + 1 ≠ 0 := by
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · obtain ⟨y, hy0, hyuniq⟩ := (Nat.card_eq_two_iff' (x := (0 : K))).mp hK
      have hy : y = 1 := (hyuniq 1 one_ne_zero).symm
      exact Or.inr ((hyuniq c hc).trans hy)
  intro s
  rcases h01 s with rfl | rfl
  · norm_num
  · rw [one_pow, mul_one]
    rw [show (1 : K) + 1 + 1 = 1 by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]]
    exact one_ne_zero

omit [CharP K 2] in
private theorem card_quadPlus_one (hK : Nat.card K = 2) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 1 K)) = 2 := by
  have h := natCard_orthogonalGroup_quadPlus (K := K) 0
  rw [hK] at h
  norm_num at h ⊢
  exact_mod_cast h

omit [CharP K 2] in
private theorem card_quadPlus_two (hK : Nat.card K = 2) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 2 K)) = 72 := by
  have h := natCard_orthogonalGroup_quadPlus (K := K) 1
  rw [hK, Finset.Icc_self, Finset.prod_singleton] at h
  norm_num at h ⊢
  exact_mod_cast h

private theorem card_quadMinus_one (hK : Nat.card K = 2) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 1 K 1 1)) = 6 := by
  have h := natCard_orthogonalGroup_quadMinus (K := K) (b := (1 : K)) (c := (1 : K))
    (hirr_one_one hK) 0
  rw [hK] at h
  norm_num at h ⊢
  exact_mod_cast h

omit [Finite K] [CharP K 2] in
private theorem isSolvable_quadPlus_zero :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 0 K)) :=
  Group.isSolvable_of_comm fun _ _ =>
    Subtype.ext (LinearEquiv.ext fun _ => Subsingleton.elim _ _)

omit [CharP K 2] in
private theorem isSolvable_quadPlus_one (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 1 K)) := by
  refine CFSG.Quasithin.SzG11G94.isSolvable_of_card_eq_pow_mul_pow
    (p := 2) (q := 3) (a := 1) (b := 0) Nat.prime_two Nat.prime_three ?_
  rw [card_quadPlus_one hK]
  norm_num

omit [CharP K 2] in
private theorem isSolvable_quadPlus_two (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 2 K)) := by
  refine CFSG.Quasithin.SzG11G94.isSolvable_of_card_eq_pow_mul_pow
    (p := 2) (q := 3) (a := 3) (b := 2) Nat.prime_two Nat.prime_three ?_
  rw [card_quadPlus_two hK]
  norm_num

private theorem isSolvable_quadMinus_one (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 1 K 1 1)) := by
  refine CFSG.Quasithin.SzG11G94.isSolvable_of_card_eq_pow_mul_pow
    (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three ?_
  rw [card_quadMinus_one hK]
  norm_num

omit [Finite K] [CharP K 2] in
private theorem isSolvable_largeEvenOrthGroup_of_isometry {V : Type} [AddCommGroup V]
    [Module K V] {Qc : QuadraticForm K V} (s : ℕ) (δ : Fin 2)
    (e : (planeQForm K s δ).IsometryEquiv Qc)
    (h : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Qc)) :
    Group.IsSolvable ↥(LargeEvenOrthGroup (planeQ (K := K) s δ)) := by
  let H := TauCeti.QuadraticMap.orthogonalGroup (planeQForm K s δ)
  have h1 : Group.IsSolvable ↥H :=
    @solvable_of_solvable_injective _ _ _ _
      (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom
      (TauCeti.QuadraticMap.orthogonalGroupCongr e).injective h
  have hO : LargeEvenOrthGroup (planeQ (K := K) s δ) =
      H.comap (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
        (Fin (s + δ.val) ⊕ Fin (s + δ.val)) K).toMonoidHom := by
    rw [largeEvenOrthGroup_def]
    exact CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (Q := planeQForm K s δ) (Q₀ := planeQ (K := K) s δ)
      (coe_planeQForm (K := K) (t := s) (δ := δ))
  rw [hO]
  let g : GL (Fin (s + δ.val) ⊕ Fin (s + δ.val)) K ≃*
      ((Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) ≃ₗ[K]
        (Fin (s + δ.val) ⊕ Fin (s + δ.val) → K)) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ K
  let f : ↥(H.comap g.toMonoidHom) →* ↥H :=
    { toFun := fun x => ⟨g (x : GL _ K), x.2⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun x y => Subtype.ext (map_mul g (x : GL _ K) (y : GL _ K)) }
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (g.injective (congrArg Subtype.val hxy))
  exact @solvable_of_solvable_injective _ _ _ _ f hf h1

private theorem isSolvable_largeEvenOrthGroup_four (hK : Nat.card K = 2) (s : ℕ) (δ : Fin 2)
    (hs : ¬ ((Even s ∧ 3 ≤ s + δ.val) ∨ (Odd s ∧ 2 ≤ s + δ.val))) :
    Group.IsSolvable ↥(LargeEvenOrthGroup (planeQ (K := K) s δ)) := by
  have hle : s + δ.val ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ s + δ.val := by omega
    rcases Nat.even_or_odd s with he | ho
    · exact hs (Or.inl ⟨he, h3⟩)
    · exact hs (Or.inr ⟨ho, by omega⟩)
  fin_cases δ
  · have hs2 : s ≤ 2 := by simpa using hle
    interval_cases s
    · obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadPlus (K := K) 0 0 ⟨0, rfl⟩
      exact isSolvable_largeEvenOrthGroup_of_isometry 0 0 e isSolvable_quadPlus_zero
    · obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadMinus (K := K) 1 0 ⟨0, by norm_num⟩
      exact isSolvable_largeEvenOrthGroup_of_isometry 1 0 e (isSolvable_quadMinus_one hK)
    · obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadPlus (K := K) 2 0 ⟨1, by norm_num⟩
      exact isSolvable_largeEvenOrthGroup_of_isometry 2 0 e (isSolvable_quadPlus_two hK)
  · change s + 1 ≤ 2 at hle
    have hs1 : s ≤ 1 := by omega
    interval_cases s
    · obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadPlus (K := K) 0 1 ⟨0, rfl⟩
      exact isSolvable_largeEvenOrthGroup_of_isometry 0 1 e (isSolvable_quadPlus_one hK)
    · exfalso
      exact hs (Or.inr ⟨⟨0, by norm_num⟩, by norm_num⟩)

theorem isSolvable_omegaQ_of_not_admissible (hK : Nat.card K = 2) (s : ℕ) (δ : Fin 2)
    (hs : ¬ ((Even s ∧ 3 ≤ s + δ.val) ∨ (Odd s ∧ 2 ≤ s + δ.val))) :
    Group.IsSolvable ↥(omegaQ (K := K) s δ) := by
  have hO := isSolvable_largeEvenOrthGroup_four hK s δ hs
  rw [omegaQ, largeEvenOmega_def]
  exact @solvable_of_solvable_injective _ _ _ _
    (Subgroup.inclusion (Subgroup.commutator_le_self
      (LargeEvenOrthGroup (planeQ (K := K) s δ))))
    (Subgroup.inclusion_injective _) hO

end CFSG.StandardType.GGQ2Frame.OrthBlocks
