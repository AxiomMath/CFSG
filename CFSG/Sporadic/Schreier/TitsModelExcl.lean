module

public import CFSG.Sporadic.Schreier.TitsInter
public import CFSG.Sporadic.Schreier.TitsOuter

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def titsModelConj {X : Type*} [Group X] (θ : GeneralizedFitting.subgroup X ≃* titsD) :
    X →* MulAut titsD :=
  haveI := GeneralizedFitting.normal X
  (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal

theorem titsModelConj_apply {X : Type*} [Group X] (θ : GeneralizedFitting.subgroup X ≃* titsD)
    (x : X) (y : GeneralizedFitting.subgroup X) :
    ((θ.symm (titsModelConj θ x (θ y)) : GeneralizedFitting.subgroup X) : X) = x * y * x⁻¹ := by
  simp [titsModelConj, MulAut.congr]

theorem map_centralizer_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (z : G) :
    (Subgroup.centralizer {z}).map f = f.range ⊓ Subgroup.centralizer {f z} := by
  ext w
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, by rw [← map_mul, ← map_mul, hu]⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    refine ⟨u, hf ?_, rfl⟩
    rw [map_mul, map_mul, hu]

theorem CTUC_Tits_model_almost_simple_full_involution_centralizer_exclusion
    (X : Type) [Group X]
    [Finite X] (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hmodel : CFSG.Blueprint.ReeTitsModel (GeneralizedFitting.subgroup X) .Tits 2 1) :
    Nonempty (GeneralizedFitting.subgroup X ≃* titsD) ∧
    (∀ θ : GeneralizedFitting.subgroup X ≃* titsD,
      (∀ (x : X) (y : GeneralizedFitting.subgroup X),
        ((θ.symm (titsModelConj θ x (θ y)) : GeneralizedFitting.subgroup X) : X) =
          x * y * x⁻¹) ∧
      Function.Injective (titsModelConj θ) ∧
      (GeneralizedFitting.subgroup X).map (titsModelConj θ) = inner titsD) ∧
    (∀ z : X, orderOf z = 2 → z ∈ GeneralizedFitting.subgroup X ∧
      (∀ R : Subgroup ↥(Subgroup.centralizer {z}), R.Normal → Odd (Nat.card R) → R = ⊥) ∧
      CFSG.oddCore ↥(Subgroup.centralizer {z}) = ⊥ ∧
      CFSG.piCore {p : Nat.Primes | p.val ≠ 2} ↥(Subgroup.centralizer {z}) = ⊥) ∧
    ¬ ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) ≠ ⊥ := by
  set F := GeneralizedFitting.subgroup X
  have := GeneralizedFitting.normal X
  have hcenter : Subgroup.center F = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  have hCF : ∀ x : X, (∀ y ∈ F, x * y * x⁻¹ = y) → x = 1 := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hx y hy
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    have hxF := GeneralizedFitting.centralizer_le X hxC
    have hz : (⟨x, hxF⟩ : F) ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC) y y.2)
    rw [hcenter, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hinj : ∀ θ : F ≃* titsD, Function.Injective (titsModelConj θ) := by
    intro θ
    rw [injective_iff_map_eq_one]
    intro x hx
    refine hCF x fun y hy => ?_
    have := titsModelConj_apply θ x ⟨y, hy⟩
    rw [hx, MulAut.one_apply, MulEquiv.symm_apply_apply] at this
    exact this.symm
  have himg : ∀ θ : F ≃* titsD, F.map (titsModelConj θ) = inner titsD := by
    intro θ
    ext φ
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨θ ⟨y, hy⟩, MulEquiv.ext fun d => ?_⟩
      apply θ.symm.injective
      apply Subtype.ext
      rw [← θ.apply_symm_apply d, titsModelConj_apply]
      simp
    · rintro ⟨d, rfl⟩
      refine ⟨θ.symm d, (θ.symm d).2, MulEquiv.ext fun d' => ?_⟩
      apply θ.symm.injective
      apply Subtype.ext
      rw [← θ.apply_symm_apply d', titsModelConj_apply]
      simp
  obtain ⟨θ⟩ := titsModelEquiv F 2 1 hmodel
  have key : ∀ z : X, orderOf z = 2 → z ∈ F ∧
      (∀ R : Subgroup ↥(Subgroup.centralizer {z}), R.Normal → Odd (Nat.card R) → R = ⊥) ∧
      CFSG.oddCore ↥(Subgroup.centralizer {z}) = ⊥ ∧
      CFSG.piCore {p : Nat.Primes | p.val ≠ 2} ↥(Subgroup.centralizer {z}) = ⊥ := by
    intro z hz
    set ρ := titsModelConj θ
    have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ (hinj θ) z, hz]
    have hY : inner titsD ≤ ρ.range := by
      rw [← himg θ]
      exact Subgroup.map_le_range _ _
    obtain ⟨hinner, hnoodd, -, -⟩ :=
      CTUC_Tits_all_intermediate_involution_centralizers_odd_core_free ρ.range hY (ρ z) ⟨z, rfl⟩
        hρz
    have hzF : z ∈ F := by
      rw [← himg θ] at hinner
      obtain ⟨y, hy, e⟩ := hinner
      rwa [← hinj θ e]
    have e : Subgroup.centralizer {z} ≃* ↥(ρ.range ⊓ Subgroup.centralizer {ρ z}) :=
      ((Subgroup.centralizer {z}).equivMapOfInjective ρ (hinj θ)).trans
        (MulEquiv.subgroupCongr (map_centralizer_of_injective ρ (hinj θ) z))
    have hno : NoOddNormal (Subgroup.centralizer {z}) := NoOddNormal.of_equiv e hnoodd
    exact ⟨hzF, hno, hno.oddCore_eq_bot, hno.piCore_eq_bot⟩
  refine ⟨⟨θ⟩, fun θ' => ⟨titsModelConj_apply θ', hinj θ', himg θ'⟩, key, ?_⟩
  rintro ⟨z, hz, hne⟩
  exact hne (key z hz).2.2.1

end CFSG.Sporadic.Schreier.Tits
