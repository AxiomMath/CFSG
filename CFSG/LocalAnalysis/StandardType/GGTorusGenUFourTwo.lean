module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFourTwoCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFourTwoComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSC
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusGenTableB_psuFourTwo
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    GGTorusGenTableB 3 (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 4) K (2 ^ 1))) := by
  have hUA : CFSG.LocalAnalysis.GLTheoremA.T173A.UniArith 3 1 4 K :=
    ⟨Nat.prime_three, by norm_num, by norm_num, by rw [hK]; norm_num, le_rfl, by norm_num,
      by omega⟩
  have hI : ∀ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))
      (LargeEvenGUSet (Fin 4) K (2 ^ 1)), φ ^ 3 = 1 →
      φ ∈ Set.range (MulAut.conj :
        LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))) := by
    intro φ hφ hφp
    obtain ⟨r, hr⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.T173A.uni_conjImage_pPower_inner hUA hφ hφp
    refine ⟨r, MulEquiv.ext fun y => ?_⟩
    rw [MulAut.conj_apply]
    exact (hr y).symm
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) = ⊥ :=
    TableBUE.center_proj_eq_bot (n := 1) (d := 4) (K := K) (by rw [hK]; norm_num)
      (by norm_num) (by norm_num)
  have hcp : GGCenterPrime 3 (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) :=
    StdSubRestU.ggCenterPrime_unitary (n := 1) (d := 4) (p := 3) (K := K)
      (by rw [hK]; norm_num) le_rfl (by norm_num) (by norm_num) Nat.prime_three
      (by norm_num) (by norm_num)
  exact ggTorusGenTableB_of_torusSC Nat.prime_three hI hZ hcp
    (ggTorusCentSC_psuFourTwo hK) (ggTorusCompGenSC_psuFourTwo hK)

theorem largeEvenLabelAll_torusGenTableB_uFourTwo
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (htag : lab.tag = .twA ∨ lab.tag = .twD)
    (hl : lab.rank = 3) (hn : lab.n = 1) (hpn : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hn hpn ⊢
  subst hn
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by simpa using hpn
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  subst hp3
  subst hl
  intro Q hQ
  rcases htag with rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    exact ⟨K, i1, i2, hK, ⟨hQ', ggTorusGenTableB_psuFourTwo (by rw [hK]; norm_num)⟩⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by norm_num : ¬ (3 = 2)), if_pos rfl] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    exact ⟨K, i1, i2, hK, ⟨hQ', ggTorusGenTableB_psuFourTwo (by rw [hK]; norm_num)⟩⟩

end CFSG.StandardType
