module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Frame
public import CFSG.LocalAnalysis.StandardType.GGTBRowUFrameAux
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTorusPermFrameW_fixed {p r l : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hPF : GGTorusPermFrameW p r R I)
    (hAut : GGTorusAutCardSC p R I (l + 1 - 1) (l + 1).factorial) :
    GGTorusWeylFrameW p r R I (CoxeterMatrix.A l) ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → Nat.card ↥A = p ^ l := by
  have key : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
      (A : Subgroup (MulAut L')), GGTorusTBGroup p r R I L' ψ A →
      Nat.card ↥A = p ^ l ∧ GGWeylFrame p A (CoxeterMatrix.A l) := by
    intro L' _ _ ψ A hTB
    obtain ⟨k, hk3, -, hAcard, hFrame⟩ := hPF L' ψ A hTB
    obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hTB
    have hFrame' := hFrame
    obtain ⟨n, hn, hweyl, hrefl, e, he⟩ := hFrame
    have hcardk : Nat.card (CoxeterMatrix.A k).Group = (k + 1).factorial := by
      rw [CFSG.TwoNodeSmall.pws_card_coxeterA k, CFSG.TwoNodeSmall.natFact_eq]
    have hfac : (k + 1).factorial = (l + 1).factorial := by
      rw [← hcardk, Nat.card_congr e.toEquiv,
        (hAut L' ψ hψ hker hperf A hAe hAI h3 hsc).2]
    have hk : k = l := by
      have h1 : k + 1 = l + 1 := (Nat.factorial_inj (by omega)).1 hfac
      omega
    subst hk
    exact ⟨hAcard, hFrame'⟩
  exact ⟨fun L' _ _ ψ A hTB => (key L' ψ A hTB).2,
    fun L' _ _ ψ A hTB => (key L' ψ A hTB).1⟩


theorem ggU_recipe_frameW {l n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n)
    (hl : 3 ≤ l) (hpl : ¬ p ∣ l + 1) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary (l + 1) (2 ^ n) Q) :
    LargeEvenRecipeUnitary (l + 1) (2 ^ n) fun R _ I F => Q R I F ∧ GGCenterPrime p R ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I (CoxeterMatrix.A l) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup p r R I L' ψ A → Nat.card ↥A = p ^ l := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    rintro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    omega
  have hZ := TableBUE.center_proj_eq_bot hK (by omega) hdq
  have hIp := fun φ hφ hφp =>
    InndiagSU.ggOutdiagPrime_unitary hK hn (by omega) hdq hp hpq hpl φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn (by omega) hdq hp hp2 hpl
  have hmodel := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpl
  have hPF := ggTorusPermFrameW_of_permEltSC (p := p) (r := ggUnitaryTorusRank p (l + 1))
    (d := l + 1) hp hp2 hZ hIp hcp hpl hmodel
  have hAut := ggTorusAutCardSC_of_permEltSC (p := p) (d := l + 1) hp hp2 (by omega)
    hZ hIp hcp hmodel
  have hfix := ggTorusPermFrameW_fixed (l := l) hPF hAut
  exact ⟨hcp, ggUnitaryTorusRank p (l + 1),
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq, hfix.1, hfix.2⟩

theorem ggQ2TableBI1FailOn_unitary : GGQ2TableBI1FailOn GGQ2TBULabel := by
  refine ggQ2TableBI1FailOn_of_frames ?_ ?_
  · rintro ⟨t, r, n⟩ ⟨ht, h4, -⟩
    exact Or.inl ⟨ht, h4⟩
  · rintro ⟨t, r, n⟩ hlab hq hS
    obtain ⟨ht, h4, hndvd⟩ := hS
    subst ht
    have h4' : 4 ≤ r := by simpa using h4
    have hndvd' : ¬ 3 ∣ r + 1 := by simpa using hndvd
    have hn1 : n = 1 := by
      have hnpos : 1 ≤ n := by simpa using hlab.1
      have hq2 : n < 2 := by simpa only [GGLabQTwo] using hq
      omega
    subst hn1
    refine ⟨Fin r, inferInstance, inferInstance, CoxeterMatrix.A r, CartanMatrix.A r,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [GGQ2LabelWeyl]
      exact ⟨Equiv.refl _, rfl⟩
    · exact Or.inl ⟨r, Equiv.refl _, by omega, Or.inl rfl⟩
    · exact ggIntCartan_A r
    · exact SecFiveRootRefl.entries_A r
    · exact SecFiveRootRefl.cartanTree_A r (by omega)
    · rw [CartanMatrix.A_det]
      intro hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      exact hndvd' (by exact_mod_cast hz)
    · have hAll : LargeEvenLabelAll ⟨.twA, r, 1⟩ fun R _ I _ => GGCenterPrime 3 R ∧
          ∃ r', GGTorusLift 3 r' R ∧ GGTorusWeylFrameW 3 r' R I (CoxeterMatrix.A r) ∧
            ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
              GGTorusTBGroup 3 r' R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card (Fin r) := by
        intro Q hQ
        dsimp only [LargeEvenRawDatum] at hQ ⊢
        simpa only [Fintype.card_fin] using
          ggU_recipe_frameW (l := r) (n := 1) (p := 3) Nat.prime_three (by norm_num)
            (by norm_num) (by omega) hndvd' hQ
      exact hAll.mono fun _ _ _ _ ⟨hcp, r', hl, hf, hc⟩ => ⟨hcp, r', r', Nat.le_succ r', hl, hf, hc⟩

end CFSG.StandardType

end
