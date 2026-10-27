module

public import CFSG.RankThree.GF2n.Smith81.S81KNormMain
public import CFSG.RankThree.GF2n.Smith81.S81KInvolRed

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Normalizer

open CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.D6Spin

section Pow


theorem indW_pow {K : Type} [Field K] {x : Gp K} {y : W K ≃ₗ[K] W K} (h : IndW x y) (n : ℕ) :
    IndW (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using IndW.one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

end Pow

section Transport


theorem sylowW_holds : SylowW := by
  intro K _ _ _ _ A hAΓ hA2
  let A₀ : Subgroup (Gp K) :=
    { carrier := {x | x ∈ LamG K ∧ ∃ y ∈ A, IndW x y}
      mul_mem' := by
        rintro a b ⟨ha, y, hy, hay⟩ ⟨hb, z, hz, hbz⟩
        exact ⟨mul_mem ha hb, y * z, mul_mem hy hz, hay.mul hbz⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, IndW.one⟩
      inv_mem' := by
        rintro a ⟨ha, y, hy, hay⟩
        exact ⟨inv_mem ha, y⁻¹, inv_mem hy, hay.inv⟩ }
  have hA₀ : A₀ ≤ LamG K := fun x hx => hx.1
  have hA₀2 : IsPGroup 2 A₀ := by
    rintro ⟨x, hxL, y, hy, hxy⟩
    obtain ⟨k, hk⟩ := hA2 ⟨y, hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 : IndW (x ^ (2 ^ k)) 1 := by
      have := indW_pow hxy (2 ^ k)
      rwa [h1] at this
    exact CFSG.RankThree.GF2n.Smith81.SK.eq_one_of_indW_one (pow_mem hxL _) h2
  obtain ⟨g, hg, hgle⟩ := CFSG.RankThree.GF2n.Smith81.SK.lam_conj_into_ULG A₀ hA₀ hA₀2
  obtain ⟨g', hg'⟩ := exists_indW (K := K) hg
  refine ⟨g', mem_EAut0_iff.2 ⟨g, hg, hg'⟩, fun a ha => ?_⟩
  obtain ⟨x, hxL, hxa⟩ := mem_EAut0_iff.1 (hAΓ ha)
  have hx₀ : x ∈ A₀ := ⟨hxL, a, ha, hxa⟩
  exact ⟨g * x * g⁻¹, hgle ⟨x, hx₀, rfl⟩, (hg'.mul hxa).mul hg'.inv⟩

end Transport

end CFSG.RankThree.GF2n.Smith81.D6Normalizer
