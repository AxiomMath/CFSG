module

import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneKHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneKHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open Subgroup CFSG.Quasithin CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Unitary (SUid)

section Helpers

variable {W : Type} [CommGroup W] [Finite W] {n : ℕ} {F : Type} [Field F] [Finite F]
  {σ : F ≃+* F} {H A : Subgroup (MulAut W)}
  {ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F)} {ψ : W ≃* Multiplicative (Fin 4 → F)}

private noncomputable def fH_T3J5 (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) :
    ↥(SUid σ 4) →* MulAut W :=
  H.subtype.comp (coordsEps (ε := ε) hS).symm.toMonoidHom

private theorem fH_injective_T3J5 (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) :
    Function.Injective (fH_T3J5 (ε := ε) hS) :=
  H.subtype_injective.comp (coordsEps (ε := ε) hS).symm.injective

private theorem map_le_T3J5 (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (B : Subgroup (SUid σ 4)) :
    B.map (fH_T3J5 (ε := ε) hS) ≤ H := by
  rintro x ⟨z, hz, rfl⟩
  exact ((coordsEps (ε := ε) hS).symm z).2

private theorem coordsE_map_T3J5 (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (B : Subgroup (SUid σ 4))
    (hBwH : B.map (fH_T3J5 (ε := ε) hS) ≤ H) :
    coordsE (ε := ε) hBwH hS = B := by
  have hE : coordsE (ε := ε) hBwH hS =
      ((coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hBwH)).range := rfl
  rw [hE]
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z0, hz0, hz0x⟩ := Subgroup.mem_map.mp y.2
    have hys : (Subgroup.inclusion hBwH y : ↥H) = (coordsEps (ε := ε) hS).symm z0 := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
      change (y : MulAut W) = ((coordsEps (ε := ε) hS).symm z0 : MulAut W)
      rw [← hz0x]
      rfl
    change coordsEps (ε := ε) hS (Subgroup.inclusion hBwH y) ∈ B
    rw [hys]
    simpa using hz0
  · intro hz
    let y0 : ↥(B.map (fH_T3J5 (ε := ε) hS)) :=
      ⟨fH_T3J5 (ε := ε) hS z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩⟩
    refine MonoidHom.mem_range.mpr ⟨y0, ?_⟩
    have hys : (Subgroup.inclusion hBwH y0 : ↥H) = (coordsEps (ε := ε) hS).symm z := by
      apply Subtype.ext
      rfl
    change coordsEps (ε := ε) hS (Subgroup.inclusion hBwH y0) = z
    rw [hys]
    simp

private theorem transport_T3J5 (hψ : NatCoordsSU4 H n F ε ψ)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (B : Subgroup (SUid σ 4))
    (hH : B.map (fH_T3J5 (ε := ε) hS) ≤ H) :
    (∀ w : W, w ∈ fixV (B.map (fH_T3J5 (ε := ε) hS)) ↔
        Multiplicative.toAdd (ψ w) ∈ fixSp B) ∧
      Nat.card ↥(fixV (B.map (fH_T3J5 (ε := ε) hS))) = Nat.card ↥(fixSp B) := by
  constructor
  · intro w
    rw [mem_fixV_coords hH hψ hS w, coordsE_map_T3J5 (ε := ε) hS B hH]
  · rw [card_fixV_coords hH hψ hS, coordsE_map_T3J5 (ε := ε) hS B hH]

private theorem map_inclusion_le_T3J5 (hAH : A ≤ H)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (B : Subgroup (SUid σ 4))
    (hB : B ≤ coordsE (ε := ε) hAH hS) :
    B.map (fH_T3J5 (ε := ε) hS) ≤ A := by
  let f : ↥A →* ↥(SUid σ 4) :=
    (coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨a, rfl⟩ := hB hz
  have hfa : fH_T3J5 (ε := ε) hS (f a) = (a : MulAut W) := by simp [fH_T3J5, f]
  rw [hfa]
  exact a.2

private theorem rank_map_T3J5 (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (B : Subgroup (SUid σ 4))
    (hcard : Nat.card ↥B = 2 ^ n) : rk ↥(B.map (fH_T3J5 (ε := ε) hS)) = n := by
  rw [rk, Subgroup.card_map_of_injective (fH_injective_T3J5 (ε := ε) hS), hcard,
    padicValNat.prime_pow]

private theorem rank_fixV_T3J5 (hψ : NatCoordsSU4 H n F ε ψ)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (B : Subgroup (SUid σ 4))
    (hH : B.map (fH_T3J5 (ε := ε) hS) ≤ H)
    (hfix : Nat.card ↥(fixSp B) = 2 ^ (6 * n)) :
    rk ↥(fixV (B.map (fH_T3J5 (ε := ε) hS))) = 6 * n := by
  rw [rk, (transport_T3J5 (ε := ε) hψ hS B hH).2, hfix, padicValNat.prime_pow]

private theorem ne_top_T3J5 (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    {S : Submodule F (Fin 4 → F)} (hS6 : Nat.card ↥S = 2 ^ (6 * n)) : S ≠ ⊤ := by
  intro h
  rw [h] at hS6
  have h1 : Nat.card ↥(⊤ : Submodule F (Fin 4 → F)) = Nat.card (Fin 4 → F) :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  rw [h1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF, ← pow_mul,
    ← pow_mul] at hS6
  have := Nat.pow_right_injective (le_refl 2) hS6
  omega

private theorem fixV_ne_T3J5 (hψ : NatCoordsSU4 H n F ε ψ)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    {B₁ B₂ : Subgroup (SUid σ 4)} (hH₁ : B₁.map (fH_T3J5 (ε := ε) hS) ≤ H)
    (hH₂ : B₂.map (fH_T3J5 (ε := ε) hS) ≤ H)
    (hfix₂ : Nat.card ↥(fixSp B₂) = 2 ^ (6 * n)) (hsup : fixSp B₁ ⊔ fixSp B₂ = ⊤) :
    fixV (B₁.map (fH_T3J5 (ε := ε) hS)) ≠ fixV (B₂.map (fH_T3J5 (ε := ε) hS)) := by
  intro h
  have hm₁ := (transport_T3J5 (ε := ε) hψ hS B₁ hH₁).1
  have hm₂ := (transport_T3J5 (ε := ε) hψ hS B₂ hH₂).1
  have hfs : fixSp B₁ = fixSp B₂ := by
    ext v
    have h1 := hm₁ (ψ.symm (Multiplicative.ofAdd v))
    have h2 := hm₂ (ψ.symm (Multiplicative.ofAdd v))
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1 h2
    rw [← h1, ← h2, h]
  rw [hfs, sup_idem] at hsup
  exact ne_top_T3J5 hF hn hfix₂ hsup

private theorem fixV_sup_T3J5 (hψ : NatCoordsSU4 H n F ε ψ)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) {B₁ B₂ : Subgroup (SUid σ 4)}
    (hH₁ : B₁.map (fH_T3J5 (ε := ε) hS) ≤ H) (hH₂ : B₂.map (fH_T3J5 (ε := ε) hS) ≤ H)
    (hsup : fixSp B₁ ⊔ fixSp B₂ = ⊤) :
    fixV (B₁.map (fH_T3J5 (ε := ε) hS)) ⊔ fixV (B₂.map (fH_T3J5 (ε := ε) hS)) = ⊤ := by
  have hm₁ := (transport_T3J5 (ε := ε) hψ hS B₁ hH₁).1
  have hm₂ := (transport_T3J5 (ε := ε) hψ hS B₂ hH₂).1
  rw [eq_top_iff]
  intro w _
  have hw : Multiplicative.toAdd (ψ w) ∈ fixSp B₁ ⊔ fixSp B₂ := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hw
  have hwyz : w = ψ.symm (Multiplicative.ofAdd y) * ψ.symm (Multiplicative.ofAdd z) := by
    apply ψ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← ofAdd_add, hyz]
    simp
  rw [hwyz]
  exact Subgroup.mul_mem_sup ((hm₁ _).2 (by simpa using hy)) ((hm₂ _).2 (by simpa using hz))

private theorem exists_from_roots_T3J5 (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hAH : A ≤ H) (hψ : NatCoordsSU4 H n F ε ψ)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) {B₁ B₂ : Subgroup (SUid σ 4)}
    (hB₁c : Nat.card ↥B₁ = 2 ^ n) (hB₂c : Nat.card ↥B₂ = 2 ^ n)
    (hB₁E : B₁ ≤ coordsE (ε := ε) hAH hS) (hB₂E : B₂ ≤ coordsE (ε := ε) hAH hS)
    (hfix₁ : Nat.card ↥(fixSp B₁) = 2 ^ (6 * n))
    (hfix₂ : Nat.card ↥(fixSp B₂) = 2 ^ (6 * n)) (hsup : fixSp B₁ ⊔ fixSp B₂ = ⊤) :
    ∃ B₁' B₂' : Subgroup (MulAut W), B₁' ≤ A ∧ B₂' ≤ A ∧ rk ↥B₁' = n ∧ rk ↥B₂' = n ∧
      rk ↥(fixV B₁') = 6 * n ∧ rk ↥(fixV B₂') = 6 * n ∧
      fixV B₁' ≠ fixV B₂' ∧ fixV B₁' ⊔ fixV B₂' = ⊤ := by
  have hH₁ := map_le_T3J5 (ε := ε) hS B₁
  have hH₂ := map_le_T3J5 (ε := ε) hS B₂
  exact ⟨B₁.map (fH_T3J5 (ε := ε) hS), B₂.map (fH_T3J5 (ε := ε) hS),
    map_inclusion_le_T3J5 (ε := ε) hAH hS B₁ hB₁E,
    map_inclusion_le_T3J5 (ε := ε) hAH hS B₂ hB₂E,
    rank_map_T3J5 (ε := ε) hS B₁ hB₁c,
    rank_map_T3J5 (ε := ε) hS B₂ hB₂c,
    rank_fixV_T3J5 (ε := ε) hψ hS B₁ hH₁ hfix₁,
    rank_fixV_T3J5 (ε := ε) hψ hS B₂ hH₂ hfix₂,
    fixV_ne_T3J5 (ε := ε) hψ hS hF hn hH₁ hH₂ hfix₂ hsup,
    fixV_sup_T3J5 (ε := ε) hψ hS hH₁ hH₂ hsup⟩

end Helpers

theorem exists_two_root_groups_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H A : Subgroup (MulAut W)} {n : ℕ} (hn : 1 ≤ n) (hNat : NatSUn H ⊤ ⊥ 4 n)
    (hAH : A ≤ H) (hA : IsElemAbelian2 A) (hrk : rk ↥A = 4 * n) :
    ∃ B₁ B₂ : Subgroup (MulAut W), B₁ ≤ A ∧ B₂ ≤ A ∧ rk ↥B₁ = n ∧ rk ↥B₂ = n ∧
      rk ↥(fixV B₁) = 6 * n ∧ rk ↥(fixV B₂) = 6 * n ∧
      fixV B₁ ≠ fixV B₂ ∧ fixV B₁ ⊔ fixV B₂ = ⊤ := by
  obtain ⟨F, hFld, hFfin, hF, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  letI := hFld
  letI := hFfin
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  set σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := hσdef.symm ▸ isUnitaryInvolution_unitaryInvolution hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hS : SUid σ 4 = StatedSU 4 (2 ^ n) F := by
    rw [hσdef]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  let f : ↥A →* ↥(SUid σ 4) :=
    (coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)
  let E : Subgroup (SUid σ 4) := f.range
  have hfinj : Function.Injective f :=
    (coordsEps (ε := ε) hS).injective.comp (Subgroup.inclusion_injective hAH)
  have hEcardA : Nat.card ↥E = Nat.card ↥A :=
    (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hE2 : ∀ a ∈ E, a * a = 1 := by
    rintro x ⟨a, rfl⟩
    rw [← map_mul]
    have ha : a * a = 1 := by
      apply Subtype.ext
      show (a : MulAut W) * (a : MulAut W) = 1
      simpa [pow_two] using hA.2 a.1 a.2
    rw [ha, map_one]
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    have hab : a * b = b * a := by
      apply Subtype.ext
      exact hA.1 a.1 a.2 b.1 b.2
    rw [hab]
  have hAcard : Nat.card ↥A = 2 ^ rk ↥A := by
    have hV : ∀ v : ↥A, v ^ 2 = 1 := fun v => Subtype.ext (hA.2 v.1 v.2)
    exact card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have hcardE : Nat.card ↥E = 2 ^ (4 * n) := by rw [hEcardA, hAcard, hrk]
  obtain ⟨B₁, B₂, hB₁E, hB₂E, hB₁c, hB₂c, -, -, hfix₁, hfix₂, hsup⟩ :=
    s16_C4ModelTv_two_root_groups hσ h2 hE2 hEc hn hF hcardE
  exact exists_from_roots_T3J5 (ε := ε) hn hF hAH hψ hS hB₁c hB₂c
    (show B₁ ≤ coordsE (ε := ε) hAH hS from hB₁E)
    (show B₂ ≤ coordsE (ε := ε) hAH hS from hB₂E) hfix₁ hfix₂ hsup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
