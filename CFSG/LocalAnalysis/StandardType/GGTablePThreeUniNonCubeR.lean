module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniNonCubeCompR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniNonCubeRankR

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem uniNonCube_eight_le_cube {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) : 8 ≤ q ^ 3 := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  have h2 : 2 ≤ q := by
    by_contra h
    have h3 : q = 0 ∨ q = 1 := by omega
    rcases h3 with h3 | h3 <;> subst h3 <;> simp_all
  calc 8 = 2 * 2 * 2 := by norm_num
    _ ≤ q * q * q := Nat.mul_le_mul (Nat.mul_le_mul h2 h2) h2
    _ = q ^ 3 := by ring

theorem uniR_noncube {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {Ahat : Subgroup (GL (Fin N) K)}
    (hL : UniLift N q K Ā Ahat) {d : GL (Fin N) K} (hdA : d ∈ Ahat) {c : Kˣ}
    (hdc : d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c) (hc : c ^ (q + 1) = 1)
    (hnc : ∀ s : Kˣ, s ^ (q + 1) = 1 → s ^ 3 ≠ c) (hδ : IsConjBy d δ') :
    UniShapeConcl q N Ā J' := by
  have hcomp := uniR_noncube_comp hK hq3 hN hR (hL.iso d hdA) hdc hc hnc hδ
  rcases hcomp with ⟨hN6, F, hFF, hFFin, hFcard, hisoF⟩ |
    ⟨E, hEF, hEFin, m, hEcard, hm3, hNm, hisoE⟩
  ·
    subst hN6
    have hrank : Nat.card Ā ≤ 3 ^ 3 :=
      uniR_noncube_rank hK hq3 hR hL hdA hdc hc hnc hδ
    refine Or.inl ⟨F, hFF, hFFin, 3, Or.inr rfl, hFcard, ?_, hisoF, ?_, ?_⟩
    · rw [hFcard]
      have h8 := uniNonCube_eight_le_cube hK
      omega
    · intro h
      exact absurd h (by decide)
    · intro _
      exact ⟨rfl, hrank⟩
  ·
    refine Or.inr ⟨E, hEF, hEFin, m, 3, Or.inr rfl, hEcard, hm3, ?_, hisoE, ?_, ?_, ?_⟩
    · intro h
      have h2 : q ^ 3 = 2 := congrArg Prod.snd h
      have h8 := uniNonCube_eight_le_cube hK
      omega
    · intro h
      exact absurd h (by decide)
    · intro _
      exact hNm
    · intro _ h
      exact absurd h (by decide)

end CFSG.StandardType.TablePThreeKG

end
