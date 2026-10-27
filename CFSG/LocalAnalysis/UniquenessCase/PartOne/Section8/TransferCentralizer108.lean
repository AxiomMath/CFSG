module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarX108
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_centralizer_of_e9_le_X
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    {L L' : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf S.M L = {L, L'})
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))
    {E : Subgroup G} (hEX : E ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure S.M L)
    (hEel : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9) :
    2 ≤ CFSG.Open.pRank S.p
      (S.M ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  haveI : Fact S.p.Prime := ⟨S.hp.1.1⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  set X : Subgroup G := CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure S.M L with hXdef
  set O : Subgroup G := CFSG.Open.pCoreOf 2 X with hOdef
  set C : Subgroup (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 S.M) :=
    Subgroup.centralizer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.barImage S.M X :
        Set (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 S.M)) with hCdef
  set D : Subgroup G :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.barPreimage S.M C with hDdef
  obtain ⟨hX_le_M, hMX, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_conjClosure_isProd
      (M := S.M) (X := S.M) (K := L) le_rfl Subgroup.le_normalizer hL
  have hX_le_M' : X ≤ S.M := by simpa [hXdef] using hX_le_M
  have hMX' : S.M ≤ Subgroup.normalizer (X : Set G) := by simpa [hXdef] using hMX
  have hEX' : E ≤ X := by simpa [hXdef] using hEX
  have hXsub : CFSG.Open.IsSubnormal X S.M :=
    CFSG.Quasithin.A3.subnormal_of_normal hX_le_M'
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hX_le_M').mpr hMX')
  have hO_eq : O = X ⊓ CFSG.Open.pCoreOf 2 S.M := by
    rw [hOdef]
    exact pCoreOf_eq_inf_pCoreOf_of_subnormal hXsub
  have hO_le_M : O ≤ S.M := by
    rw [hOdef]
    exact (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) X).trans hX_le_M'
  have hO2 : IsPGroup 2 O := by
    rw [hOdef]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X
  have hSM_normalizes_O : S.M ≤ Subgroup.normalizer (O : Set G) := by
    rw [hOdef]
    exact hMX'.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) X)
  have hBN : E ≤ Subgroup.normalizer (O : Set G) := by
    rw [hOdef]
    exact hEX'.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) X)
  have hC_two : 2 ≤ CFSG.Open.pRank S.p C := by
    have h := two_le_pRank_centralizer_barX hS hU S hMS hnot hL hset hSL
    simpa [hCdef, hXdef, top_inf_eq] using h
  have hD_rank : CFSG.Open.pRank S.p D = CFSG.Open.pRank S.p C := by
    have h1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_barImage
      (p := S.p) hp hp2 (M := S.M) (P := D)
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barPreimage_le S.M C)
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_barPreimage S.M C] at h1
    exact h1.symm
  have hD_two : 2 ≤ CFSG.Open.pRank S.p D := by
    rw [hD_rank]
    exact hC_two
  have hcomm_aux : ∀ (b : ↥S.M), uc22p21cPi S.M b ∈ C →
      ∀ e ∈ E, ⁅(b : G), e⁆ ∈ O := by
    intro b hbC e he
    have heX : e ∈ X := hEX' he
    have heM : e ∈ S.M := hX_le_M' heX
    have heBar : uc22p21cPi S.M ⟨e, heM⟩ ∈ barImage S.M X := by
      rw [uc22p21c_mem_barImage]
      exact ⟨⟨e, heM⟩, heX, rfl⟩
    have hcent : uc22p21cPi S.M ⟨e, heM⟩ * uc22p21cPi S.M b =
        uc22p21cPi S.M b * uc22p21cPi S.M ⟨e, heM⟩ :=
      Subgroup.mem_centralizer_iff.mp hbC _ heBar
    have hmemM : (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ S.M :=
      S.M.mul_mem (S.M.mul_mem (S.M.mul_mem b.2 heM) (S.M.inv_mem b.2))
        (S.M.inv_mem heM)
    have hq : uc22p21cPi S.M
        ⟨(b : G) * e * (b : G)⁻¹ * e⁻¹, hmemM⟩ = 1 := by
      have hq' : uc22p21cPi S.M (⁅b, (⟨e, heM⟩ : ↥S.M)⁆) = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcent.symm
      have hsub : (⁅b, (⟨e, heM⟩ : ↥S.M)⁆ : ↥S.M) =
          ⟨(b : G) * e * (b : G)⁻¹ * e⁻¹, hmemM⟩ := by
        apply Subtype.ext
        simp [commutatorElement_def, mul_assoc]
      rwa [hsub] at hq'
    have hpcm : (⟨(b : G) * e * (b : G)⁻¹ * e⁻¹, hmemM⟩ : ↥S.M) ∈
        CFSG.pCore 2 ↥S.M := (QuotientGroup.eq_one_iff _).mp hq
    have hpc : (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ CFSG.Open.pCoreOf 2 S.M :=
      (CFSG.mem_openPCoreOf_iff (p := 2) ⟨_, hmemM⟩).mpr hpcm
    have hmemX : (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ X := by
      have hmap : X.map (MulAut.conj (b : G)).toMonoidHom = X :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMX' b.2)
      have h1 : (MulAut.conj (b : G)) e ∈ X := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ heX
      have h2 : ((MulAut.conj (b : G)) e) * e⁻¹ ∈ X := X.mul_mem h1 (X.inv_mem heX)
      simpa [MulAut.conj_apply, mul_assoc] using h2
    rw [hO_eq, commutatorElement_def]
    exact ⟨hmemX, hpc⟩
  obtain ⟨R, hRD, hR_el, hR_card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt D
  have hD_le_M : D ≤ S.M := by
    rw [hDdef]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barPreimage_le S.M C
  have hR_le_M : R ≤ S.M := hRD.trans hD_le_M
  have hcomm : ⁅R, E⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro r hr e he
    have hrD : r ∈ D := hRD hr
    obtain ⟨hrM, hrC⟩ :=
      (uc22p21c_mem_barPreimage (M := S.M) (Y := C) (x := r)).mp hrD
    have h := hcomm_aux ⟨r, hrM⟩ hrC e he
    simpa using h
  have hR_rank : CFSG.Open.pRank S.p R = CFSG.Open.pRank S.p D := by
    refine le_antisymm (CFSG.SectionRank.pRank_mono hp.one_lt hRD) ?_
    exact CFSG.SectionRank.le_pRank hp.one_lt (le_rfl : R ≤ R) hR_el hR_card
  have hR_ispg : IsPGroup S.p R := CFSG.Open.IsElemAbelian.isPGroup hR_el
  have hE_ispg : IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hEel
  have hRN : R ≤ Subgroup.normalizer (O : Set G) := hR_le_M.trans hSM_normalizes_O
  have hpN : ¬ S.p ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp
      (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2))))
  have hqN : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
  have hmain := CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
    (p := S.p) (q := 3) (M := S.M) (N := O) (R := R) (B := E)
    hR_le_M hO_le_M hRN hBN hR_ispg hE_ispg hpN hqN hcomm
  have hR_two : 2 ≤ CFSG.Open.pRank S.p R := by
    rw [hR_rank]
    exact hD_two
  exact hR_two.trans hmain

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
