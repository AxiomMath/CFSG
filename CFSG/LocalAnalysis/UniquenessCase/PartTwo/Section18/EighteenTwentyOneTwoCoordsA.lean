module

import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneKHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneTwoModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneKHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open Subgroup CFSG.Quasithin CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Unitary (SUid)

section Helpers

variable {W : Type} [CommGroup W] [Finite W] {n : ℕ} {F : Type} [Field F] [Finite F]
  {σ : F ≃+* F} {H : Subgroup (MulAut W)}
  {ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F)} {ψ : W ≃* Multiplicative (Fin 4 → F)}

private theorem coordsE_zpowers_T3J4 (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F)
    {a : MulAut W} (haH : a ∈ H) (hza : Subgroup.zpowers a ≤ H) :
    coordsE (ε := ε) hza hS = Subgroup.zpowers (coordsEps (ε := ε) hS ⟨a, haH⟩) := by
  have hE : coordsE (ε := ε) hza hS =
      ((coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hza)).range := rfl
  rw [hE]
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : (Subgroup.inclusion hza y : ↥H) = (⟨a, haH⟩ : ↥H) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion, Subgroup.coe_zpow, ← hk]
    change (coordsEps (ε := ε) hS ⟨a, haH⟩) ^ k =
      coordsEps (ε := ε) hS (Subgroup.inclusion hza y)
    rw [h1, map_zpow]
  · intro hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨⟨a ^ k, Subgroup.zpow_mem_zpowers a k⟩, ?_⟩
    change coordsEps (ε := ε) hS (Subgroup.inclusion hza ⟨a ^ k, Subgroup.zpow_mem_zpowers a k⟩) =
      (coordsEps (ε := ε) hS ⟨a, haH⟩) ^ k
    rw [← map_zpow]
    congr 1

private theorem card_commV_coords_T3J4 {A : Subgroup (MulAut W)} (hAH : A ≤ H)
    (hψ : NatCoordsSU4 H n F ε ψ) (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) :
    Nat.card ↥(commV A) = Nat.card ↥(commSp (coordsE (ε := ε) hAH hS)) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨Multiplicative.toAdd (ψ x.1),
        (mem_commV_coords hAH hψ hS x.1).mp x.2⟩
      invFun := fun y => ⟨ψ.symm (Multiplicative.ofAdd y.1), by
        refine (mem_commV_coords hAH hψ hS _).mpr ?_
        simpa using y.2⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun y => by apply Subtype.ext; simp }

private theorem setup_T3J4 {A : Subgroup (MulAut W)}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hAH : A ≤ H) (hA : IsElemAbelian2 A)
    (hrk : 4 * n - 1 ≤ rk ↥A) :
    ∃ σ : F ≃+* F, IsUnitaryInvolution σ ∧ (2 : F) = 0 ∧
      ∃ hS : SUid σ 4 = StatedSU 4 (2 ^ n) F,
        ∃ E : Subgroup (SUid σ 4),
          E = ((coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)).range ∧
          (∀ a ∈ E, a * a = 1) ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
          2 ^ (4 * n - 1) ≤ Nat.card ↥E := by
  classical
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  set σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := hσdef.symm ▸ isUnitaryInvolution_unitaryInvolution hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hS : SUid σ 4 = StatedSU 4 (2 ^ n) F := by
    rw [hσdef]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  let f : ↥A →* ↥(SUid σ 4) :=
    (coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)
  refine ⟨σ, hσ, h2, hS, f.range, rfl, ?_, ?_, ?_⟩
  · rintro x ⟨a, rfl⟩
    rw [← map_mul]
    have ha : a * a = 1 := by
      apply Subtype.ext
      show (a : MulAut W) * (a : MulAut W) = 1
      simpa [pow_two] using hA.2 a.1 a.2
    rw [ha, map_one]
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    have hab : a * b = b * a := by
      apply Subtype.ext
      exact hA.1 a.1 a.2 b.1 b.2
    rw [hab]
  · have hfinj : Function.Injective f :=
      (coordsEps (ε := ε) hS).injective.comp (Subgroup.inclusion_injective hAH)
    have hEcardA : Nat.card ↥f.range = Nat.card ↥A :=
      (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
    have hAcard : Nat.card ↥A = 2 ^ rk ↥A := by
      have hV : ∀ v : ↥A, v ^ 2 = 1 := fun v => Subtype.ext (hA.2 v.1 v.2)
      exact card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
    rw [hEcardA, hAcard]
    exact Nat.pow_le_pow_right (by norm_num) hrk

private theorem ne_sup_T3J4 {A : Subgroup (MulAut W)} {a₁ a₂ : ↥A}
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (hψ : NatCoordsSU4 H n F ε ψ)
    (f : ↥A →* ↥(SUid σ 4))
    (hz₁ : Subgroup.zpowers (a₁ : MulAut W) ≤ H)
    (hz₂ : Subgroup.zpowers (a₂ : MulAut W) ≤ H)
    (e₁ : coordsE (ε := ε) hz₁ hS = Subgroup.zpowers (f a₁))
    (e₂ : coordsE (ε := ε) hz₂ hS = Subgroup.zpowers (f a₂))
    (hne : fixSp (Subgroup.zpowers (f a₁)) ≠ fixSp (Subgroup.zpowers (f a₂)))
    (hsup : fixSp (Subgroup.zpowers (f a₁)) ⊔ fixSp (Subgroup.zpowers (f a₂)) = ⊤) :
    fixV (Subgroup.zpowers (a₁ : MulAut W)) ≠ fixV (Subgroup.zpowers (a₂ : MulAut W)) ∧
    fixV (Subgroup.zpowers (a₁ : MulAut W)) ⊔ fixV (Subgroup.zpowers (a₂ : MulAut W)) = ⊤ := by
  have hmem₁ : ∀ w : W, w ∈ fixV (Subgroup.zpowers (a₁ : MulAut W)) ↔
      Multiplicative.toAdd (ψ w) ∈ fixSp (Subgroup.zpowers (f a₁)) := by
    intro w
    rw [mem_fixV_coords hz₁ hψ hS w, e₁]
  have hmem₂ : ∀ w : W, w ∈ fixV (Subgroup.zpowers (a₂ : MulAut W)) ↔
      Multiplicative.toAdd (ψ w) ∈ fixSp (Subgroup.zpowers (f a₂)) := by
    intro w
    rw [mem_fixV_coords hz₂ hψ hS w, e₂]
  constructor
  · intro h
    apply hne
    ext v
    have h1 := hmem₁ (ψ.symm (Multiplicative.ofAdd v))
    have h2 := hmem₂ (ψ.symm (Multiplicative.ofAdd v))
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1 h2
    rw [← h1, ← h2, h]
  · rw [eq_top_iff]
    intro w _
    have hw : Multiplicative.toAdd (ψ w) ∈
        fixSp (Subgroup.zpowers (f a₁)) ⊔ fixSp (Subgroup.zpowers (f a₂)) := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hw
    have hwyz : w = ψ.symm (Multiplicative.ofAdd y) * ψ.symm (Multiplicative.ofAdd z) := by
      apply ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← ofAdd_add, hyz]
      simp
    rw [hwyz]
    exact Subgroup.mul_mem_sup ((hmem₁ _).2 (by simpa using hy)) ((hmem₂ _).2 (by simpa using hz))

private theorem pullback_T3J4 {A : Subgroup (MulAut W)} {E : Subgroup (SUid σ 4)}
    (hAH : A ≤ H) (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (hψ : NatCoordsSU4 H n F ε ψ)
    (hEeq : E = ((coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)).range)
    (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hcard : 2 ^ (4 * n - 1) ≤ Nat.card ↥E) :
    ∃ a₁ a₂ : ↥A,
      rk ↥(commV (Subgroup.zpowers (a₁ : MulAut W))) = 2 * n ∧
      rk ↥(fixV (Subgroup.zpowers (a₁ : MulAut W))) = 6 * n ∧
      rk ↥(commV (Subgroup.zpowers (a₂ : MulAut W))) = 2 * n ∧
      rk ↥(fixV (Subgroup.zpowers (a₂ : MulAut W))) = 6 * n ∧
      fixV (Subgroup.zpowers (a₁ : MulAut W)) ≠ fixV (Subgroup.zpowers (a₂ : MulAut W)) ∧
      fixV (Subgroup.zpowers (a₁ : MulAut W)) ⊔ fixV (Subgroup.zpowers (a₂ : MulAut W)) = ⊤ := by
  let f : ↥A →* ↥(SUid σ 4) :=
    (coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)
  obtain ⟨a₁', a₂', ha₁, ha₂, hc₁, hf₁, hc₂, hf₂, hne, hsup⟩ :=
    exists_two_transvections_of_card_ge hσ h2 hE2 hEc hn hF hcard
  rw [hEeq] at ha₁ ha₂
  obtain ⟨a₁, rfl⟩ := MonoidHom.mem_range.mp ha₁
  obtain ⟨a₂, rfl⟩ := MonoidHom.mem_range.mp ha₂
  have hz₁ : Subgroup.zpowers (a₁ : MulAut W) ≤ H := Subgroup.zpowers_le.mpr (hAH a₁.2)
  have hz₂ : Subgroup.zpowers (a₂ : MulAut W) ≤ H := Subgroup.zpowers_le.mpr (hAH a₂.2)
  have e₁ := coordsE_zpowers_T3J4 (ε := ε) hS (hAH a₁.2) hz₁
  have e₂ := coordsE_zpowers_T3J4 (ε := ε) hS (hAH a₂.2) hz₂
  have hcm₁ := card_commV_coords_T3J4 (ε := ε) hz₁ hψ hS
  have hcm₂ := card_commV_coords_T3J4 (ε := ε) hz₂ hψ hS
  have hfx₁ := card_fixV_coords hz₁ hψ hS
  have hfx₂ := card_fixV_coords hz₂ hψ hS
  rw [e₁] at hcm₁ hfx₁
  rw [e₂] at hcm₂ hfx₂
  refine ⟨a₁, a₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rk, hcm₁, show coordsEps (ε := ε) hS ⟨(a₁ : MulAut W), hAH a₁.2⟩ = f a₁ from rfl,
      hc₁, padicValNat.prime_pow]
  · rw [rk, hfx₁, show coordsEps (ε := ε) hS ⟨(a₁ : MulAut W), hAH a₁.2⟩ = f a₁ from rfl,
      hf₁, padicValNat.prime_pow]
  · rw [rk, hcm₂, show coordsEps (ε := ε) hS ⟨(a₂ : MulAut W), hAH a₂.2⟩ = f a₂ from rfl,
      hc₂, padicValNat.prime_pow]
  · rw [rk, hfx₂, show coordsEps (ε := ε) hS ⟨(a₂ : MulAut W), hAH a₂.2⟩ = f a₂ from rfl,
      hf₂, padicValNat.prime_pow]
  · exact (ne_sup_T3J4 hS hψ f hz₁ hz₂ e₁ e₂ hne hsup).1
  · exact (ne_sup_T3J4 hS hψ f hz₁ hz₂ e₁ e₂ hne hsup).2

end Helpers

theorem exists_two_transvections_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H A : Subgroup (MulAut W)} {n : ℕ} (hn : 2 ≤ n) (hNat : NatSUn H ⊤ ⊥ 4 n)
    (hAH : A ≤ H) (hA : IsElemAbelian2 A) (hrk : 4 * n - 1 ≤ rk ↥A) :
    ∃ a₁ a₂ : MulAut W, a₁ ∈ A ∧ a₂ ∈ A ∧
      rk ↥(commV (Subgroup.zpowers a₁)) = 2 * n ∧
      rk ↥(fixV (Subgroup.zpowers a₁)) = 6 * n ∧
      rk ↥(commV (Subgroup.zpowers a₂)) = 2 * n ∧
      rk ↥(fixV (Subgroup.zpowers a₂)) = 6 * n ∧
      fixV (Subgroup.zpowers a₁) ≠ fixV (Subgroup.zpowers a₂) ∧
      fixV (Subgroup.zpowers a₁) ⊔ fixV (Subgroup.zpowers a₂) = ⊤ := by
  obtain ⟨F, hFld, hFfin, hF, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  letI := hFld
  letI := hFfin
  classical
  obtain ⟨σ, hσ, h2, hS, E, hEeq, hE2, hEc, hcard⟩ := setup_T3J4 hF hAH hA hrk
  obtain ⟨a₁, a₂, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    pullback_T3J4 (ε := ε) (ψ := ψ) hAH hS hψ hEeq hσ h2 hn hF hE2 hEc hcard
  exact ⟨(a₁ : MulAut W), (a₂ : MulAut W), a₁.2, a₂.2, h₁, h₂, h₃, h₄, h₅, h₆⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
