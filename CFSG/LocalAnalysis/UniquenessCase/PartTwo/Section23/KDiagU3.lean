module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagCoatom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

theorem exists_catGroup_of_isU3 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsU3 X n) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      CFSG.AGLEmbedding.IsUnitaryIndex 2 d ∧
        Nonempty (X ≃* CFSG.AGLEmbedding.CatGroup d) := by
  have hX' : CFSG.Blueprint.LieModel X .PSU 3 2 n := hX
  have ht : (CFSG.Open.StatedLieTag.PSU) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX' ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨e⟩⟩ := hmodel
  let _ : Field K := hfield
  let _ : Finite K := hfinite
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ n := hadm.2.1
  have hnq : (3, 2 ^ n) ≠ (3, 2) := hadm.2.2.2
  have hcard' : Fintype.card K = (2 ^ n) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hEven : Fintype.card K % 2 = 0 := by
    rw [hcard', ← pow_mul]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n * 2 ≠ 0))
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr hEven
  haveI : CharP K 2 := ringChar.of_eq hchar
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := n) (n := 3) hcard (by norm_num) hnq).2
  have eProj : CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) K) ≃*
      ↥(CFSG.Open.StatedSU 3 (2 ^ n) K) ⧸
        Subgroup.center ↥(CFSG.Open.StatedSU 3 (2 ^ n) K) :=
    QuotientGroup.quotientMulEquivOfEq hZ.symm
  obtain ⟨q', hv, hq'p, -, ⟨eC⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := K) (m := 3) (q := 2 ^ n) hcard' (by norm_num) hnq
  have hq'p' : q'.p = 2 := by rw [hq'p, hchar]
  refine ⟨⟨TauCeti.LieTypeIndex.twistedA 2 q', hv⟩, ⟨q', hq'p', rfl⟩, ⟨?eX⟩⟩
  exact (e.trans eProj).trans eC

theorem coatom_normalizer_sylow_of_isU3 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsU3 X n) : ∀ S : Sylow 2 X, IsCoatom (Subgroup.normalizer (S : Set X)) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_catGroup_of_isU3 hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  exact CFSG.AGLEmbedding.kFactUnitaryBorelMaximal X 2 d hd ⟨e⟩ S

theorem kDiag_of_isU3 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsU3 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P :=
  kDiag_of_sylow_normalizer_coatom (coatom_normalizer_sylow_of_isU3 hX)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
