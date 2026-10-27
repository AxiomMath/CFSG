module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5Stell
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.FrattiniSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.Goldschmidt75.Sig32
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (coprime_card_relPPrimeCore)

variable {G : Type} [Group G] [Finite G]

private theorem isSylowOf_two_relPPrimeCore {Q R N : Subgroup G} (hQ3 : IsPGroup 3 Q)
    (hQN : Q ≤ N) (hR2 : IsPGroup 2 R) (hQR : Q ≤ Subgroup.normalizer (R : Set G))
    (hRK : R ≤ CFSG.Open.relPPrimeCore 3 N)
    (hmax : ∀ T : Subgroup G, T ≤ N → IsPGroup 2 T → Q ≤ Subgroup.normalizer (T : Set G) →
      R ≤ Subgroup.normalizer (T : Set G) → T ≤ R) :
    CFSG.ABGLocalTools.IsSylowOf 2 R (CFSG.Open.relPPrimeCore 3 N) := by
  classical
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 N
  have hKle : K ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hKn : (K.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  have h3K : ¬ 3 ∣ Nat.card K :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_relPPrimeCore Nat.prime_three N)
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) :=
    hQN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mp hKn)
  obtain ⟨W, hW, hRW, hQW⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hQ3 h3K hQK hRK hR2 hQR
  let V : Subgroup G := W ⊓ Subgroup.normalizer (R : Set G)
  have hV2 : IsPGroup 2 V := hW.2.1.to_le inf_le_left
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_inf_of_le hQW (hQR.trans Subgroup.le_normalizer)
  have hRV : R ≤ V := le_inf hRW Subgroup.le_normalizer
  have hVN : V ≤ N := inf_le_left.trans (hW.1.trans hKle)
  have hVR : V ≤ R := hmax V hVN hV2 hQV (hRV.trans Subgroup.le_normalizer)
  have hVeq : V = R := le_antisymm hVR hRV
  have hWR : W = R := by
    by_contra hne
    have hlt : R < W := lt_of_le_of_ne hRW (Ne.symm hne)
    have hgrow : R < W ⊓ Subgroup.normalizer (R : Set G) :=
      CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 2) hW.2.1 hlt
    have hgrow' : R < V := hgrow
    rw [hVeq] at hgrow'
    exact lt_irrefl R hgrow'
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn (p := 2) hW
  exact ⟨P, hP.trans hWR⟩

theorem le_of_calCGS_le
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK : CFSG.Open.IsKProper G)
    (h3G : 3 ∣ Nat.card G) {Q R N M : Subgroup G} (hQ3 : IsPGroup 3 Q) (hQN : Q ≤ N)
    (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) (hQR : Q ≤ Subgroup.normalizer (R : Set G))
    (hRK : R ≤ CFSG.Open.relPPrimeCore 3 N) (hNc : CFSG.QuasithinUnique.CharTwo N)
    (hmax : ∀ T : Subgroup G, T ≤ N → IsPGroup 2 T → Q ≤ Subgroup.normalizer (T : Set G) →
      R ≤ Subgroup.normalizer (T : Set G) → T ≤ R)
    (hCGS : CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS R ≤ M) : N ≤ M := by
  classical
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 N
  have hKle : K ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hKn : (K.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  have h3K : ¬ 3 ∣ Nat.card K :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_relPPrimeCore Nat.prime_three N)
  obtain ⟨P, hP⟩ := isSylowOf_two_relPPrimeCore (N := N) hQ3 hQN hR2 hQR hRK hmax
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 R K := ⟨P, hP⟩
  have hKc : CFSG.QuasithinUnique.CharTwo K := CFSG.QuasithinUnique.CharTwo.of_normal hNc hKle hKn
  have hKcal : K ≤ CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS R :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F09.le_calCGS_of_kProper hKPSz hK h3G h3K hKc hRsyl hR
  have hNRcal : Subgroup.normalizer (R : Set G) ≤
      CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS R := by
    unfold CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS
    refine le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le le_rfl (le_iSup_of_le ?_ le_rfl)))
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.topCharacteristic
  have hfr := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.eq_sup_normalizer_of_sylow
    (p := 2) hKle hKn P
  rw [hP] at hfr
  calc N = K ⊔ (Subgroup.normalizer (R : Set G) ⊓ N) := hfr
    _ ≤ K ⊔ Subgroup.normalizer (R : Set G) :=
        sup_le le_sup_left (inf_le_left.trans le_sup_right)
    _ ≤ M := sup_le (hKcal.trans hCGS) (hNRcal.trans hCGS)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen
