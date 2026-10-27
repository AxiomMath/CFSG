module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddKFactSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddKFactL3Alg
import CFSG.LinearAlgebra.SpecialLinearIrreducibleConj
import CFSG.NumberTheory.TwoPowAddOneOdd
import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
import CFSG.CGT.T75N.L29Overgroup
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open Matrix

theorem kFactL2Odd_L3_even {Q : Type} [Group Q] [Finite Q] {f : ℕ} (hpf : 2 ^ f % 3 = 2)
    (hQ : LieModel Q .PSL 3 2 f) {X W T : Subgroup Q} {n r : ℕ} (c : KCfgL2Odd X W T n r) :
    W = ⊤ := by
  classical
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hQ.statedClassicalModel (by decide)
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hpf
  let e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    (eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.pslEquivSL3 hqK)
  let W' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := W.map e.toMonoidHom
  have hcardBar : Nat.card (Bar2 X) = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.card_isL2 c.isL2).2
  have hdvdBar : 2 ^ n - 1 ∣ Nat.card (Bar2 X) := by
    rw [hcardBar]
    exact dvd_mul_of_dvd_right (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2) _
  have hdvdX : Nat.card (Bar2 X) ∣ Nat.card ↥X :=
    Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X)
  have hXr : r ∣ Nat.card ↥X := c.r_dvd.trans (hdvdBar.trans hdvdX)
  let : Fact r.Prime := ⟨c.r_prime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) r hXr
  let A : Subgroup Q := (Subgroup.zpowers x).map X.subtype
  have hAX : A ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hAr : Nat.card A = r := by
    dsimp [A]
    rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hx]
  let B' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := A.map e.toMonoidHom
  have hr5 : 5 ≤ r :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S898.prime_ne_two_three_of_dvd c.r_prime c.odd c.r_dvd
  have hr2ne : r ≠ 2 := by omega
  have hN' : ∀ P' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K), IsPGroup r ↥P' →
      B' ≤ P' → normalizer (P' : Set (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ W' := by
    intro P' hP' hB'P'
    let P : Subgroup Q := P'.map e.symm.toMonoidHom
    have hPe : P.map e.toMonoidHom = P' := by
      have hP : P = P'.comap e.toMonoidHom := by
        dsimp [P]
        rw [Subgroup.map_equiv_eq_comap_symm]
        rfl
      rw [hP, Subgroup.map_comap_eq_self_of_surjective e.surjective P']
    have hP : IsPGroup r ↥P := by
      dsimp [P]
      exact hP'.of_equiv (Subgroup.equivMapOfInjective P' e.symm.toMonoidHom e.symm.injective)
    have hAP : A ≤ P := by
      intro a ha
      refine Subgroup.mem_map.mpr ⟨e a, hB'P' (Subgroup.mem_map_of_mem e.toMonoidHom ha), ?_⟩
      exact e.symm_apply_apply a
    have hNP : normalizer P ≤ W := c.Nr A hAX hAr P hP hAP
    have hNPe : (normalizer P).map e.toMonoidHom = normalizer P' := by
      rw [Subgroup.map_equiv_normalizer_eq P e, hPe]
    rw [← hNPe]
    exact Subgroup.map_mono hNP
  have hB'W' : B' ≤ W' := by
    dsimp [B', W']
    exact Subgroup.map_mono (hAX.trans c.X_le)
  have hB'r : Nat.card B' = r := by
    dsimp [B']
    rw [Subgroup.card_map_of_injective e.injective, hAr]
  have hrK : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro hdiv
    exact hr2ne ((Nat.prime_dvd_prime_iff_eq c.r_prime Nat.prime_two).mp
      (c.r_prime.dvd_of_dvd_pow hdiv))
  have hr2 : ¬ r ∣ Nat.card K + 1 := by
    rw [hK]
    exact fun h => CFSG.NumberTheory.not_dvd_two_pow_sub_one_of_dvd_two_pow_add_one c.r_prime
      hr2ne h c.odd c.r_dvd
  have hirr : ∀ Z : Submodule K (Fin 3 → K),
      (∀ s ∈ W', ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) → Z = ⊥ ∨ Z = ⊤ := by
    by_cases hr1 : r ∣ Nat.card K - 1
    · exact sl3_irreducible_of_prime_dvd c.r_prime hr5 hr1 hB'r hN'
    · intro Z hZ
      exact sl3_irreducible_of_prime_of_not_dvd c.r_prime hrK hr1 hr2 hB'r Z
        (fun s hs v hv => hZ s (hB'W' hs) v hv)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTindex : ¬ 2 ∣ T.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp c.T_sylow).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hWodd : ¬ 2 ∣ W'.index := by
    dsimp [W']
    rw [Subgroup.index_map_equiv W e]
    exact fun h => hTindex (dvd_trans h (Subgroup.index_dvd_of_le c.T_le))
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  obtain ⟨g, hg⟩ := CFSG.CGT.T75N.exists_conj_unitriangular_le_gen W' hWodd
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := W'.map (MulAut.conj g).toMonoidHom
  have hU : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 K ≤ S := by
    intro u hu
    exact Subgroup.mem_map_equiv.mpr (show (MulAut.conj g).symm u ∈ W' from hg u hu)
  have hirrS := CFSG.LinearAlgebra.specialLinear_irreducible_map_conj hirr g
  have hStop : S = ⊤ := CFSG.CGT.T75N.eq_top_of_unitriangular_le_gen S hU hirrS
  have hW'top : W' = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g) y ∈ S := by rw [hStop]; exact Subgroup.mem_top _
    change (MulAut.conj g) y ∈ W'.map (MulAut.conj g).toMonoidHom at hy
    have hy' : (MulAut.conj g).symm ((MulAut.conj g) y) ∈ W' := Subgroup.mem_map_equiv.mp hy
    simpa only [MulEquiv.symm_apply_apply] using hy'
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ W' := by
    rw [hW'top]
    exact Subgroup.mem_top _
  change e x ∈ W.map e.toMonoidHom at hx
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hx
  rw [e.injective hwe] at hw
  exact hw

theorem kFactShape92L2Odd_holds : KFactShape92L2Odd := by
  intro Q _ _ hQ hcyc X W T n r c
  rcases hQ with ⟨-, h3⟩ | hJ | ⟨p, f, hL2⟩ | ⟨p, f, hpf, hL3⟩ | ⟨p, f, -, hU3⟩
  · exact (kFactL2Odd_not_three_group h3 c).elim
  · exact (kFactL2Odd_not_J1 hJ c).elim
  · by_cases hp : p = 2
    · subst hp
      exact kFactL2Odd_L2_even hL2 hcyc c
    · exact (kFactL2Odd_L2_odd hp hL2 c).elim
  · by_cases hp : p = 2
    · subst hp
      exact kFactL2Odd_L3_even hpf hL3 c
    · exact (kFactL2Odd_L3U3_odd hp (Or.inl hL3) c).elim
  · by_cases hp : p = 2
    · subst hp
      exact kFactL2Odd_U3_even hU3 c
    · exact (kFactL2Odd_L3U3_odd hp (Or.inr hU3) c).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
