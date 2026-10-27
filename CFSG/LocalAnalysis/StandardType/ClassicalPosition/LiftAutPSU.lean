module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNotDvd
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSU
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal CFSG.StandardType.TableCRes

theorem mulAut_apply_liftHom_PSU_eq
    {X : Type} [Group X] {n g p : ℕ} (hn : 1 ≤ n)
    (ψ : ↥(Unitary.SU (PSUσ g) n) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    (B : Subgroup X) (ℓ : B →* ↥(Unitary.SU (PSUσ g) n))
    (hℓ : ∀ (b : B) (u : ↥(Unitary.SU (PSUσ g) n)),
      (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hpow : ∀ b : B, ℓ b ^ p = 1) {t : X}
    (ht : t ∈ Subgroup.centralizer (B : Set X))
    (α : MulAut ↥(Unitary.SU (PSUσ g) n))
    (hα : ∀ u, ψ (α u) = t⁻¹ * ψ u * t) (b : B) : α (ℓ b) = ℓ b := by
  let a := α (ℓ b)
  have hap : a ^ p = 1 := by
    change α (ℓ b) ^ p = 1
    rw [← map_pow, hpow b, map_one]
  have hal : IsGLLift (PSUj n g) ψ (a : GL (Fin n) (PSUF g)) (b : X) := by
    intro u
    refine ⟨a * u * a⁻¹, rfl, ?_⟩
    let v := α.symm u
    have hav : α v = u := α.apply_symm_apply u
    have hprod : a * u * a⁻¹ = α (ℓ b * v * (ℓ b)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hav]
    have hψu : ψ u = t⁻¹ * ψ v * t := by
      simpa only [hav] using hα v
    rw [hprod, hα, ← hℓ b v, hψu]
    have hbt : (b : X) * t = t * (b : X) :=
      Subgroup.mem_centralizer_iff.mp ht (b : X) b.property
    calc
      (b : X)⁻¹ * (t⁻¹ * ψ v * t) * (b : X) =
          (t * (b : X))⁻¹ * ψ v * (t * (b : X)) := by group
      _ = ((b : X) * t)⁻¹ * ψ v * ((b : X) * t) := by rw [← hbt]
      _ = t⁻¹ * ((b : X)⁻¹ * ψ v * (b : X)) * t := by group
  have hll : IsGLLift (PSUj n g) ψ (ℓ b : GL (Fin n) (PSUF g)) (b : X) := by
    intro u
    exact ⟨ℓ b * u * (ℓ b)⁻¹, rfl, hℓ b u⟩
  apply Subtype.ext
  exact eq_of_isGLLift_pow_eq_one_PSU hn hψ hp hpq a.property.2 (ℓ b).property.2
    (congrArg (fun z : ↥(Unitary.SU (PSUσ g) n) => (z : GL (Fin n) (PSUF g))) hap)
    (congrArg (fun z : ↥(Unitary.SU (PSUσ g) n) => (z : GL (Fin n) (PSUF g))) (hpow b))
    hal hll

open CFSG.StandardType.RootDetectSU CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix in
theorem exists_mulAut_lift_PSU
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n)
    {G : Type*} [Group G] {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (α : MulAut (SU (unitaryInvolution F 2 f) n))
      (A : GL (Fin n) F) (φ : F ≃+* F),
      (∀ u, ψ (α u) = c⁻¹ * ψ u * c) ∧
        ∀ u, ((α u : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) =
          A * glAut φ (u : GL (Fin n) F) * A⁻¹ := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h => by omega
  let h : UnitaryFieldData 2 f F := unitaryFieldData_two hF hf
  let C₀ : GL (Fin n) F :=
    ⟨antidiag n, antidiag n, antidiag_mul_self n, antidiag_mul_self n⟩
  have hC : IsPrimeFormGram C₀ := isPrimeFormGram_of_eq_antidiag rfl
  let C : Matrix (Fin n) (Fin n) F := (C₀ : Matrix (Fin n) (Fin n) F)
  have hE : SU (unitaryInvolution F 2 f) n = gramSU h C := SU_eq_gramSU_antidiag h
  let E : SU (unitaryInvolution F 2 f) n ≃* gramSU h C := MulEquiv.subgroupCongr hE
  let ψ' : gramSU h C →* G := ψ.comp E.symm.toMonoidHom
  have hψ'E : ∀ u, ψ' (E u) = ψ u := fun u => by
    simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
  have hrange : ψ'.range = ψ.range := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨E.symm u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨E u, hψ'E u⟩
  have hker' : ψ'.ker ≤ Subgroup.center (gramSU h C) := by
    intro u hu
    have hz : E.symm u ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n) := hker hu
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro v
    have he := congrArg E (hz (E.symm v))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using he
  have hperf : ⁅(⊤ : Subgroup (gramSU h C)), (⊤ : Subgroup (gramSU h C))⁆ = ⊤ := by
    have := (isQuasisimple_SU hF hn3
      (fun h' => hq ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩)).1
    have : Group.IsPerfect (gramSU h C) :=
      Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hN : normOneScalars h (gramSU h C) n = Subgroup.center (gramSU h C) :=
    (CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h hC hn3 hq).symm
  have hc' : c ∈ Subgroup.normalizer (ψ'.range : Set G) := by simpa only [hrange] using hc
  obtain ⟨δ, hδ⟩ := RootDetect.exists_quotAut hN hperf hker' hc'
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn3 hq δ
  rw [primeFormPsi_apply] at hAφ
  let β : MulAut (gramSU h C) := primeFormConjSU h C A * primeFormFieldSU h hC φ
  have hδβ : ∀ u : gramSU h C, δ (u : primeFormP h C) = (β u : primeFormP h C) := by
    intro u
    rw [← hAφ, MulAut.mul_apply]
    change primeFormConjAut h C A (primeFormFieldAut h hC φ _) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk]
    rfl
  have hβψ : ∀ u, ψ' (β u) = c⁻¹ * ψ' u * c := by
    intro u
    have h1 := conj_eq_of_quotAut_eq hN hperf hc' hδ (a := 1)
      (β := β.toMonoidHom) (fun v => by simpa using hδβ v) u
    simpa only [map_one, mul_one, MulEquiv.coe_toMonoidHom] using h1.symm
  let α : MulAut (SU (unitaryInvolution F 2 f) n) := MulAut.congr E.symm β
  refine ⟨α, (A : GL (Fin n) F), φ, ?_, ?_⟩
  · intro u
    change ψ' (β (E u)) = c⁻¹ * ψ u * c
    simpa only [hψ'E] using hβψ (E u)
  · intro u
    rfl

end CFSG.StandardType.ClassicalPosition

end
