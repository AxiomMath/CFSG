module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofG2Cent

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint

@[expose] def KS611G2TorusE27 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ChevalleyExceptionalModel Y .G2 3 1 →
    ∃ r₁ r₂ r₃ h h' : Y, r₁ * r₂ = r₂ * r₁ ∧ r₁ * r₃ = r₃ * r₁ ∧ r₂ * r₃ = r₃ * r₂ ∧
      r₁ ^ 3 = 1 ∧ r₂ ^ 3 = 1 ∧ r₃ ^ 3 = 1 ∧
      Nat.card (Subgroup.closure ({r₁, r₂, r₃} : Set Y)) = 27 ∧
      h * r₁ * h⁻¹ = r₁ ∧ h * r₂ * h⁻¹ = r₂⁻¹ ∧ h * r₃ * h⁻¹ = r₃⁻¹ ∧
      h' * r₁ * h'⁻¹ = r₁⁻¹ ∧ h' * r₂ * h'⁻¹ = r₂⁻¹ ∧ h' * r₃ * h'⁻¹ = r₃

@[expose] def KS611G2CoverE81 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card (Subgroup.center X) = 3 →
    ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 →
    ∃ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 81

namespace Res611Fix

theorem isElemAbelian_closure {X : Type*} [Group X] {S : Set X} (hS : S.Pairwise Commute)
    (h3 : ∀ x ∈ S, x ^ 3 = 1) : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure S) := by
  have hc : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h3 x hx
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      exact this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

open Sec4.Res417Five.SepCover in
theorem ks611G2CoverE81_of (hS : KS611G2TorusE27) : KS611G2CoverE81 := by
  intro X _ _ hZ3 hM
  obtain ⟨r₁, r₂, r₃, h, h', h12, h13, h23, hr1, hr2, hr3, hcard, hh1, hh2, hh3, hh'1, hh'2,
    hh'3⟩ := hS _ hM
  obtain ⟨u₁, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) r₁
  obtain ⟨u₂, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) r₂
  obtain ⟨u₃, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) r₃
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) h
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) h'
  set Z := Subgroup.center X with hZdef
  set π : X →* X ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker ≤ Subgroup.center X := by rw [hπ, QuotientGroup.ker_mk']
  have hZ3' : ∀ z ∈ π.ker, z ^ 3 = 1 := by
    intro z hz
    rw [hπ, QuotientGroup.ker_mk'] at hz
    have h1 := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ3] at h1
    simpa using congrArg Subtype.val h1
  have c12 : u₁ * u₂ = u₂ * u₁ := commute_of_sep π hker hZ3' h12 hh1 hh2
  have c13 : u₁ * u₃ = u₃ * u₁ := commute_of_sep π hker hZ3' h13 hh1 hh3
  have c23 : u₂ * u₃ = u₃ * u₂ := (commute_of_sep π hker hZ3' h23.symm hh'3 hh'2).symm
  have p1 : u₁ ^ 3 = 1 := pow_three_eq_one_of_inv π hker hZ3' hr1 hh'1
  have p2 : u₂ ^ 3 = 1 := pow_three_eq_one_of_inv π hker hZ3' hr2 hh2
  have p3 : u₃ ^ 3 = 1 := pow_three_eq_one_of_inv π hker hZ3' hr3 hh3
  set S : Set X := {u₁, u₂, u₃} ∪ (Z : Set X) with hSdef
  have hcen : ∀ z ∈ (Z : Set X), ∀ x : X, Commute z x := fun z hz x =>
    ((Subgroup.mem_center_iff.mp hz) x).symm
  have hSc : S.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals first
          | exact Commute.refl _
          | exact c12 | exact c13 | exact c23
          | exact c12.symm | exact c13.symm | exact c23.symm
      · exact (hcen y hy x).symm
    · exact hcen x hx y
  have hS3 : ∀ x ∈ S, x ^ 3 = 1 := by
    intro x hx
    rcases hx with hx | hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact p1
      · exact p2
      · exact p3
    · have h1 := pow_card_eq_one' (G := Z) (x := ⟨x, hx⟩)
      rw [hZ3] at h1
      simpa using congrArg Subtype.val h1
  set B := Subgroup.closure S with hBdef
  refine ⟨B, isElemAbelian_closure hSc hS3, ?_⟩
  have hZB : Z ≤ B := by
    intro z hz
    exact Subgroup.subset_closure (Or.inr hz)
  have hmap : B.map π = Subgroup.closure ({π u₁, π u₂, π u₃} : Set (X ⧸ Z)) := by
    rw [hBdef, MonoidHom.map_closure]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        all_goals exact Subgroup.subset_closure (by simp)
      · have h1 : π x = 1 := by
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hx
        rw [SetLike.mem_coe, h1]
        exact Subgroup.one_mem _
    · apply Subgroup.closure_mono
      rintro _ hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨u₁, Or.inl (by simp), rfl⟩
      · exact ⟨u₂, Or.inl (by simp), rfl⟩
      · exact ⟨u₃, Or.inl (by simp), rfl⟩
  set f : B →* X ⧸ Z := π.comp B.subtype with hf
  have hrange : f.range = B.map π := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hfker : Nat.card f.ker = 3 := by
    have hkerZ : f.ker = Z.subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, hπ,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl
    rw [hkerZ, ← hZ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hmap, hcard,
    hfker] at h1
  exact h1

end Res611Fix


namespace Res611Fix

open Multiplicative in
theorem closure_basis_eq_top :
    Subgroup.closure ({ofAdd (Pi.single 0 1), ofAdd (Pi.single 1 1), ofAdd (Pi.single 2 1)} :
      Set (Multiplicative (Fin 3 → ZMod 3))) = ⊤ := by
  have hdec : ∀ v : Multiplicative (Fin 3 → ZMod 3), v = ofAdd (Pi.single 0 1) ^ (toAdd v 0).val *
      (ofAdd (Pi.single 1 1) ^ (toAdd v 1).val * ofAdd (Pi.single 2 1) ^ (toAdd v 2).val) := by
    decide
  rw [eq_top_iff]
  intro v _
  rw [hdec v]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))

end Res611Fix

section Torus


open Multiplicative CFSG.LieType.Chevalley in
theorem ks611G2TorusE27_holds : KS611G2TorusE27 := by
  intro Y _ _ hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hY.2
  have := Fintype.ofFinite K
  have hK3 : Fintype.card (ZMod 3) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Nat.card_zmod, pow_one]
  set ι : ZMod 3 ≃+ K := (FiniteField.ringEquivOfCardEq hK3).toAddEquiv with hι
  set Ψ : Multiplicative (Fin 3 → ZMod 3) →* Y := e.symm.toMonoidHom.comp (g2Param ι) with hΨ
  have hΨi : Function.Injective Ψ := e.symm.injective.comp (g2Param_injective ι)
  have hc₁ : ∀ v, e.symm (torusElement .G2 K (0 : Fin 2) (-1)) * Ψ v *
      (e.symm (torusElement .G2 K (0 : Fin 2) (-1)))⁻¹ =
        Ψ (ofAdd (![1, -1, -1] * toAdd v)) := by
    intro v
    rw [hΨ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_inv,
      ← map_mul, ← map_mul, torusElement_conj_g2Param_zero]
  have hc₂ : ∀ v, e.symm (torusElement .G2 K (1 : Fin 2) (-1)) * Ψ v *
      (e.symm (torusElement .G2 K (1 : Fin 2) (-1)))⁻¹ =
        Ψ (ofAdd (![-1, -1, 1] * toAdd v)) := by
    intro v
    rw [hΨ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_inv,
      ← map_mul, ← map_mul, torusElement_conj_g2Param_one]
  have hcomm : ∀ a b, Ψ a * Ψ b = Ψ b * Ψ a := fun a b => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hcube : ∀ i : Fin 3, Ψ (ofAdd (Pi.single i 1)) ^ 3 = 1 := by
    intro i
    rw [← map_pow]
    have h3 : (ofAdd (Pi.single i (1 : ZMod 3)) : Multiplicative (Fin 3 → ZMod 3)) ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, toAdd_ofAdd, toAdd_one, Pi.smul_apply, Pi.zero_apply]
      by_cases hj : j = i
      · subst hj
        simp only [Pi.single_eq_same]
        decide
      · simp [Pi.single_eq_of_ne hj]
    rw [h3, map_one]
  refine ⟨Ψ (ofAdd (Pi.single 0 1)), Ψ (ofAdd (Pi.single 1 1)), Ψ (ofAdd (Pi.single 2 1)),
    e.symm (torusElement .G2 K (0 : Fin 2) (-1)), e.symm (torusElement .G2 K (1 : Fin 2) (-1)),
    hcomm _ _, hcomm _ _, hcomm _ _, hcube 0, hcube 1, hcube 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have himg : ({Ψ (ofAdd (Pi.single 0 1)), Ψ (ofAdd (Pi.single 1 1)),
        Ψ (ofAdd (Pi.single 2 1))} : Set Y) =
        Ψ '' {ofAdd (Pi.single 0 1), ofAdd (Pi.single 1 1), ofAdd (Pi.single 2 1)} := by
      simp only [Set.image_insert_eq, Set.image_singleton]
    rw [himg, ← MonoidHom.map_closure, Res611Fix.closure_basis_eq_top,
      Subgroup.card_map_of_injective hΨi, Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  · rw [hc₁]
    congr 1
    decide
  · rw [hc₁, ← map_inv]
    congr 1
    decide
  · rw [hc₁, ← map_inv]
    congr 1
    decide
  · rw [hc₂, ← map_inv]
    congr 1
    decide
  · rw [hc₂, ← map_inv]
    congr 1
    decide
  · rw [hc₂]
    congr 1
    decide

theorem ks611G2CoverE81_holds : KS611G2CoverE81 :=
  Res611Fix.ks611G2CoverE81_of ks611G2TorusE27_holds

end Torus

end CFSG.RankThree.PartTwo.Sec6
