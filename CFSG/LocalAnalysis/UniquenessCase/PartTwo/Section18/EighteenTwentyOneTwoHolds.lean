module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneTwoLe
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneTwoCoordsA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneTwoCoordsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open Subgroup CFSG.Quasithin CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Unitary (SUid)

theorem rk_le_four_mul_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H A : Subgroup (MulAut W)} {n : ℕ} (hn : 1 ≤ n) (hNat : NatSUn H ⊤ ⊥ 4 n)
    (hAH : A ≤ H) (hA : IsElemAbelian2 A) : rk ↥A ≤ 4 * n := by
  obtain ⟨F, hFld, hFfin, hF, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  letI := hFld
  letI := hFfin
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  set σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := hσdef.symm ▸ isUnitaryInvolution_unitaryInvolution hF
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
  have hle := card_le_two_pow_four hσ hE2 hEc hn hF
  rw [hEcardA, hAcard] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle

theorem k_K_18_21_i2_holds : K_18_21_i2 := by
  intro W _ _ H Y A n hn _ hNat _ hYN hA hrk
  have hAH : A ≤ H := le_of_mem_aSet_two_of_natSUn hn hNat hYN hA
  have hAel : IsElemAbelian2 A := hA.2.2.1
  refine ⟨hAH, rk_le_four_mul_of_natSUn (by omega) hNat hAH hAel,
    exists_two_transvections_of_natSUn hn hNat hAH hAel hrk, fun h4 => ?_⟩
  obtain ⟨B₁, B₂, h1, h2, h3, h4', h5, h6, h7, h8⟩ :=
    exists_two_root_groups_of_natSUn (by omega) hNat hAH hAel h4
  exact ⟨A, B₁, B₂, rfl, hAH, hAel, h4, h1, h2, h3, h4', h5, h6, h7, h8⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
