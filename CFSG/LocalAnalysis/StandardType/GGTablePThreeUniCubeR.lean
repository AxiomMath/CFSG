module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeBlockR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeRankR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniPSU2

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

theorem uniR_cube {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {Ahat : Subgroup (GL (Fin N) K)}
    (hL : UniLift N q K Ā Ahat) (hcard : Nat.card Ahat = Nat.card Ā * (q + 1)) {d : GL (Fin N) K}
    (hdA : d ∈ Ahat) (hd3 : d ^ 3 = 1) (hδ : IsConjBy d δ') :
    UniShapeConcl q N Ā J' := by
  have hd := hL.iso d hdA
  obtain ⟨μ, hμ, hJ, hQS, hk2, hkN, hNle, hcenterQuot, hcent⟩ :=
    uniR_cube_block hK hq3 hN hR hd hd3 hδ
  set k : ℕ := Module.finrank K (cubeEigen d μ) with hkdef
  have hQS' : (2 ≤ k ∧ 4 ≤ q) ∨ 4 ≤ k := by
    have h := hQS
    unfold CubeBlockQS at h
    rw [← hkdef] at h
    exact h
  by_cases hk2eq : k = 2
  ·
    have hk23 : k = 2 ∨ k = 3 := Or.inl hk2eq
    have hArank : Nat.card Ā ≤ 3 ^ k :=
      uniR_cube_rank hK hq3 hN hR hL hcard hdA hd3 hδ hμ hJ hQS hk23
    have hA9 : Nat.card Ā ≤ 9 := by
      have h := hArank
      rw [hk2eq] at h
      norm_num at h
      exact h
    have hq4 : 4 ≤ q := by
      rcases hQS' with ⟨-, h4⟩ | h4
      · exact h4
      · omega
    obtain ⟨F, hFld, hFfin, hFcard, hpsu2⟩ := psu2_equiv_psl2 (K := K) (q := q) hK
    have hFcard1 : Nat.card F = q ^ 1 := by simpa using hFcard
    have hF4 : 4 ≤ Nat.card F := by rw [hFcard]; exact hq4
    have hquot : Nonempty (J' ⧸ Subgroup.center J' ≃* PSLg 2 F) := by
      obtain ⟨e1⟩ := hcenterQuot
      rw [hk2eq] at e1
      obtain ⟨e2⟩ := hpsu2
      exact ⟨e1.trans e2⟩
    refine Or.inl ⟨F, hFld, hFfin, 1, Or.inl rfl, hFcard1, hF4, hquot, ?_, ?_⟩
    · intro _
      have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
      rw [h27]
      omega
    · intro h13
      exfalso
      omega
  ·
    have hk3 : 3 ≤ k := by omega
    have hne : (k, q ^ 1) ≠ (3, 2) := by
      intro h
      have hq2 : q = 2 := by simpa using congrArg Prod.snd h
      have hk3' : k = 3 := by simpa using congrArg Prod.fst h
      have hqs := hQS'
      rw [hk3', hq2] at hqs
      rcases hqs with ⟨-, h4⟩ | h4 <;> omega
    refine Or.inr ⟨K, inferInstance, inferInstance, k, 1, Or.inl rfl, ?_, hk3, hne,
      ?_, ?_, ?_, ?_⟩
    · simpa using hK
    · have hpow : q ^ 1 = q := pow_one q
      have hEq : Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃* PSUg k K (q ^ 1)) =
          Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃* PSUg k K q) :=
        congrArg (fun t : ℕ => Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃* PSUg k K t)) hpow
      exact hEq.symm ▸ hcenterQuot
    · intro _
      exact hkN
    · intro h13
      exfalso
      omega
    · intro hm3 _
      have hArank : Nat.card Ā ≤ 3 ^ k :=
        uniR_cube_rank hK hq3 hN hR hL hcard hdA hd3 hδ hμ hJ hQS (Or.inr hm3)
      have hq4 : 4 ≤ q := by
        have h := hQS'
        rw [hm3] at h
        rcases h with ⟨-, h4⟩ | h4
        · exact h4
        · omega
      have hA27 : Nat.card Ā ≤ 27 := by
        rw [hm3] at hArank
        norm_num at hArank
        exact hArank
      refine ⟨hcent hm3, ?_, ?_⟩
      · have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
        rw [h27]
        exact hA27
      · have h := hNle hq4
        rw [hm3] at h
        omega

end CFSG.StandardType.TablePThreeKG

end
