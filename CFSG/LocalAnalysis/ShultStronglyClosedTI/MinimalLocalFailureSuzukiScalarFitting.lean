module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddFieldSemilinearFittingCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiRootAutomorphismSemilinear

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Fitting

variable {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A']

omit [Finite A'] in
theorem map_fittingSubgroup_le (φ : A ≃* A') :
    (CFSG.fittingSubgroup A).map φ.toMonoidHom ≤ CFSG.fittingSubgroup A' :=
  CFSG.WholeGroup.fittingSubgroup_map_le_of_surjective φ.toMonoidHom φ.surjective

theorem map_fittingSubgroup_mulEquiv (φ : A ≃* A') :
    (CFSG.fittingSubgroup A).map φ.toMonoidHom = CFSG.fittingSubgroup A' := by
  refine le_antisymm (map_fittingSubgroup_le φ) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (map_fittingSubgroup_le φ.symm)
  rwa [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id A' by
    ext; simp, Subgroup.map_id] at h

omit [Finite A'] in
theorem fittingSubgroup_subgroupOf_le (L : Subgroup A) (h : CFSG.fittingSubgroup A ≤ L) :
    (CFSG.fittingSubgroup A).subgroupOf L ≤ CFSG.fittingSubgroup L := by
  have hnormal : ((CFSG.fittingSubgroup A).subgroupOf L).Normal :=
    (CFSG.fittingSubgroup_normal).subgroupOf L
  have : Group.IsNilpotent ((CFSG.fittingSubgroup A).subgroupOf L) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h).symm
  exact le_sSup ⟨hnormal, this⟩

omit [Finite A'] in
theorem pCore_le_of_not_dvd_index {p : ℕ} [Fact p.Prime] {L : Subgroup A}
    (hL : ¬ p ∣ L.index) : CFSG.pCore p A ≤ L := by
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p L))
  have hP₀ : ((P₀ : Subgroup L).map L.subtype).relIndex L = (P₀ : Subgroup L).index := by
    change (((P₀ : Subgroup L).map L.subtype).subgroupOf L).index = _
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hP : ¬ p ∣ ((P₀ : Subgroup L).map L.subtype).index := by
    rw [← Subgroup.relIndex_mul_index (Subgroup.map_subtype_le _), hP₀,
      Nat.Prime.dvd_mul Fact.out]
    rintro (h1 | h1)
    · exact P₀.not_dvd_index h1
    · exact hL h1
  have := CFSG.fitting_pCore_le_sylow ((P₀.isPGroup'.map L.subtype).toSylow hP)
  rw [IsPGroup.toSylow_coe] at this
  exact this.trans (Subgroup.map_subtype_le _)

end Fitting

section Semilinear

variable {k Q : Type*} [Field k] [Finite k] [Group Q] (e : Multiplicative k ≃* Q)

theorem fittingSubgroup_eq_comap_scalar {m : ℕ} (hk : Nat.card k = 2 ^ (2 * m + 1))
    {A : Type*} [Group A] [Finite A] (j : A →* MulAut Q) (hj : Function.Injective j)
    (sc : kˣ →* MulAut Q) (hsci : Function.Injective sc)
    (hsc : ∀ (c : kˣ) (b : k), sc c (e (.ofAdd b)) = e (.ofAdd (c * b)))
    (hsemi : ∀ a : A, j a ∈ coordSemilinearGroup e) (hscal : ∀ c : kˣ, sc c ∈ j.range) :
    CFSG.fittingSubgroup A = sc.range.comap j := by
  let jE := MonoidHom.ofInjective hj
  let ι : kˣ →* A := jE.symm.toMonoidHom.comp (sc.codRestrict j.range hscal)
  have hjι : ∀ c, j (ι c) = sc c := fun c => by
    change ((jE (jE.symm ⟨sc c, hscal c⟩) : j.range) : MulAut Q) = sc c
    rw [MulEquiv.apply_symm_apply]
  have hιinj : Function.Injective ι := fun c d hcd => hsci (by rw [← hjι, ← hjι, hcd])
  have hscmul : ∀ (c d : kˣ) (σ : k ≃+* k), coordSemilinearAut e c σ * sc d *
      (coordSemilinearAut e c σ)⁻¹ = sc (ringAutUnits k σ d) := fun c d σ => by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨b, rfl⟩ := (coordSemilinearAut e c σ).surjective y
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      show b = .ofAdd b.toAdd from rfl, hsc, coordSemilinearAut_apply, coordSemilinearAut_apply,
      hsc, map_mul σ, coe_ringAutUnits_apply]
    congr 2
    ring
  have hform : ∀ a : A, ∃ (c : kˣ) (σ : k ≃+* k), j a = coordSemilinearAut e c σ := fun a => by
    obtain ⟨c, σ, h⟩ := hsemi a
    refine ⟨c, σ, MulEquiv.ext fun y => ?_⟩
    obtain ⟨b, rfl⟩ := e.surjective y
    rw [show b = .ofAdd b.toAdd from rfl, h, coordSemilinearAut_apply]
  have hconj : ∀ a : A, ∃ σ : RingAut k, ∀ d : kˣ, a * ι d * a⁻¹ = ι (ringAutUnits k σ d) := by
    intro a
    obtain ⟨c, σ, hca⟩ := hform a
    exact ⟨σ, fun d => hj (by rw [map_mul, map_mul, map_inv, hjι, hjι, hca, hscmul])⟩
  have hcent : ∀ a : A, (∀ d : kˣ, a * ι d = ι d * a) → a ∈ ι.range := by
    intro a ha
    obtain ⟨c, σ, hca⟩ := hform a
    have hσ : σ = RingEquiv.refl k := RingEquiv.ext fun b => by
      by_cases hb : b = 0
      · rw [hb, map_zero, RingEquiv.refl_apply]
      have h1 := congrArg j (ha (Units.mk0 b hb))
      rw [map_mul, map_mul, hjι, hca] at h1
      have h2 := congrArg (fun α : MulAut Q => α (e (.ofAdd 1))) h1
      simp only [MulAut.mul_apply, hsc, coordSemilinearAut_apply, Units.val_mk0, mul_one,
        map_one, EmbeddingLike.apply_eq_iff_eq] at h2
      rw [RingEquiv.refl_apply]
      exact mul_left_cancel₀ c.ne_zero (h2.trans (mul_comm _ _))
    refine ⟨c, hj ?_⟩
    rw [hjι, hca, hσ]
    refine MulEquiv.ext fun y => ?_
    obtain ⟨b, rfl⟩ := e.surjective y
    rw [show b = .ofAdd b.toAdd from rfl, hsc, coordSemilinearAut_apply, RingEquiv.refl_apply]
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := k) Nat.prime_two (by omega) hk
  obtain ⟨hF, -⟩ := CFSG.ShultStronglyClosedTI.MiscAlgebra.fittingSubgroup_eq_range_of_conj_ringAut
    Nat.prime_two (odd_two_mul_add_one m) hk ι hιinj hconj hcent
  rw [hF]
  ext a
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (hjι c).symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hj (by rw [hjι]; exact hc)⟩

end Semilinear

theorem pCore_eq_bot_of_transitive {Q : Type*} [Group Q] [Finite Q]
    {Abar : Subgroup (MulAut Q)}
    (htrans : ∀ y₀ y : Q, y₀ ≠ 1 → y ≠ 1 → ∃ a ∈ Abar, a y₀ = y)
    {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card Q - 1) : CFSG.pCore p Abar = ⊥ := by
  set U := CFSG.pCore p Abar
  let _ : MulAction U Q := MulAction.compHom Q (Abar.subtype.comp U.subtype)
  have hsmul : ∀ (u : U) (y : Q), u • y = ((u : Abar) : MulAut Q) y := fun u y => rfl
  have hU : IsPGroup p U := CFSG.pCore_isPGroup
  have hmod := hU.card_modEq_card_fixedPoints Q
  have h1 : (1 : Q) ∈ MulAction.fixedPoints U Q := fun u => by rw [hsmul, map_one]
  obtain ⟨y₀, hy₀, hy₀1⟩ : ∃ y₀ ∈ MulAction.fixedPoints U Q, y₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hfix : MulAction.fixedPoints U Q = {1} := Set.eq_singleton_iff_unique_mem.mpr ⟨h1, hcon⟩
    have hc : Nat.card ↥({1} : Set Q) = 1 := Nat.card_unique
    rw [hfix, hc] at hmod
    exact hp ((Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm)
  have hall : ∀ (u : U) (y : Q), ((u : Abar) : MulAut Q) y = y := by
    intro u y
    by_cases hy : y = 1
    · rw [hy, map_one]
    obtain ⟨a, ha, hay⟩ := htrans y₀ y hy₀1 hy
    have hconj : (⟨a, ha⟩ : Abar)⁻¹ * (u : Abar) * (⟨a, ha⟩ : Abar)⁻¹⁻¹ ∈ U :=
      CFSG.pCore_normal.conj_mem _ u.2 _
    have h2 := hy₀ ⟨_, hconj⟩
    rw [hsmul] at h2
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply,
      MulAut.inv_apply] at h2
    rw [← hay]
    have h3 := congrArg a h2
    rwa [MulEquiv.apply_symm_apply] at h3
  refine eq_bot_iff.mpr fun u hu => ?_
  rw [Subgroup.mem_bot]
  exact Subtype.ext (MulEquiv.ext fun y => hall ⟨u, hu⟩ y)

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
