module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoSetup
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Delta

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.StandardType.TableBUE
  CFSG.StandardType.SmallU CFSG.StandardType.IOneUDelta CFSG.StandardType.IOneUDvdR
  CFSG.StandardType.Line63.H5
open scoped commutatorElement

theorem ggStdSubTwoTorusDeltaSmall_sixTwo
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGStdSubTwoTorusDeltaSmall 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hδ a ha ha1 hEcomp hcentA hsmall
  exfalso
  classical
  have hd3 : 3 ≤ 6 := by norm_num
  have hdq : ((6 : ℕ), 2 ^ 1) ≠ (3, 2) := by norm_num
  have hcen : Subgroup.center (UnitaryR K 1 6) = ⊥ := six_center_eq_bot hK
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hcen
  have hAge : 3 ^ (6 - 2) ≤ Nat.card A :=
    card_ge_delta hK le_rfl hd3 hdq Nat.prime_three (by norm_num) hψ hker hZ hδ
  have hA3 : IsPGroup 3 A := isPGroup_three_of_isElemAbelian hA
  obtain ⟨ψb, hψbmk, hψbs, hkerb, hperfb, hoddb, hAb, hcardAb, hAIb⟩ :=
    six_package hK hψ hker hperf hA hAI
  set Ab := A.map (qAutHom L') with hAbdef
  obtain ⟨φ, hM, hdiag⟩ := exists_diagModel_odd hK hψbs hkerb hperfb hoddb hAb hAIb
    (by rw [hcardAb]; simpa using hAge)
  have hc := qAutHom_compat a
  obtain ⟨t₀, ht₀⟩ := hdiag _ (⟨a, ha, rfl⟩ : qAutHom L' a ∈ Ab)
  obtain ⟨σ, -, hσ⟩ := ActsU.of_actsDiagU ht₀
  have hEcompb := isComponentOf_layer_down qmk_surjective qmk_ker_le_center hc hEcomp
  obtain ⟨i₀, hbig'⟩ := exists_bigOK_cls hM (by norm_num) le_rfl hσ hEcompb
  have hS := cls_isCls σ i₀
  set S := cls σ i₀ with hSdef
  have hSd : ∃ k₀, k₀ ∉ S := by
    by_contra hall
    push Not at hall
    refine ha1 (qAutHom_injective hperf ?_)
    rw [map_one]
    exact hσ.eq_one_of_const hM i₀ fun i j => by
      rw [mem_cls.mp (hall i), mem_cls.mp (hall j)]
  obtain ⟨k₀, hk₀⟩ := hSd
  have hlayer : LargeEvenLayer (ggFix (qAutHom L' a)) = (blockSU S).map φ :=
    layer_eq_block hM hσ hS (isQuasisimple_block hM hbig') hEcompb
  obtain ⟨Eb, hEcard, hEdesc⟩ :=
    exists_torus hM hK Nat.prime_three (by norm_num) hk₀ id (fun k hk => hk)
  rw [Finset.image_id] at hEcard
  have hEbab : CFSG.Open.IsElemAbelian 3 Eb := isElemAbelian_torus fun e he => by
    obtain ⟨g, τ, h1, h2, h3, -⟩ := hEdesc e he
    exact ⟨g, τ, h1, h2, h3⟩
  have hEbL : Eb ≤ LargeEvenLayer (ggFix (qAutHom L' a)) := by
    rw [hlayer]
    exact torus_le_block fun e he => by
      obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2, h4⟩
  have hEbfix : ∀ a' ∈ Ab, ∀ e ∈ Eb, a' e = e := by
    intro a' ha'
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
    exact fix_of_torus hσ' fun e he => by
      obtain ⟨g, τ, h1, h2, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2⟩
  have hmap := layer_map_eq (π := qmk L') qmk_surjective qmk_ker_le_center hc
  obtain ⟨E, hEL, hE, hEmap, hEfix, hEcardE⟩ := exists_elemAbelian_lift_fixed hA3
    (layer_invariant_A hA ha) hEbab (by rw [hmap]; exact hEbL)
    (fun a' ha' x hx => hEbfix _ ⟨a', ha', rfl⟩ x hx)
  have hEconj : ∀ e ∈ E, MulAut.conj e ∈ A := fun e he =>
    hδ.1 e (hE.2 e he) (fun a' ha' => hEfix a' ha' e he)
  have hEsmall : Nat.card E < 3 ^ 3 := hsmall E hE hEL hEfix (Or.inl hEconj)
  have hS4 : 4 ≤ S.card := by
    rcases hbig' with h | ⟨h2, -⟩
    · exact h
    · omega
  have h1 : 3 ^ 3 ≤ 3 ^ (S.card - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.StandardType.USixTwo

end
