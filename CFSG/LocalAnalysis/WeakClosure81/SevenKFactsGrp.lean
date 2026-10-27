module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.LargeExtraspecial.S97RZStar
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.GH74.GLS.Statements
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem isL2OrSz_of_mulEquiv {S T : Type} [Group S] [Group T] {n : ℕ} (hS : IsL2OrSz S n)
    (e : S ≃* T) : IsL2OrSz T n :=
  hS.imp (CFSG.Quasithin.IsPSL.of_mulEquiv e) (CFSG.Quasithin.IsSz.of_mulEquiv e)

theorem seven_k_grp_exists_mulEquiv_sz {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Quasithin.IsSz n X) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (X ≃* Sz a) := by
  unfold CFSG.Quasithin.IsSz CFSG.Blueprint.SuzukiModel at h
  obtain ⟨-, a, ha, K, hKfld, hKfin, hf, hKcard, ⟨eX⟩⟩ := h
  letI : Field K := hKfld
  letI : Finite K := hKfin
  have hcard : Nat.card K = Nat.card (GaloisField 2 (2 * a + 1)) := by
    rw [GaloisField.card 2 (2 * a + 1) (by omega)]
    rw [hf] at hKcard
    exact hKcard
  obtain ⟨φ⟩ := CFSG.Blueprint.EvenSource.nonempty_ringEquiv_of_card_eq K
    (GaloisField 2 (2 * a + 1)) hcard
  exact ⟨a, ha, hf, ⟨eX.trans ((CFSG.Blueprint.EvenSource.suzukiGroupMapEquiv a φ).trans
    (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup
      a).some.symm)⟩⟩

theorem seven_k_grp_fusionZStar_le_fusionOddCore {X : Type} [Group X] [Finite X]
    (hO2 : CFSG.pCore 2 X = ⊥) (hodd : fusionOddCore X ≤ Subgroup.center X) :
    fusionZStar X ≤ fusionOddCore X := by
  have hOodd : Odd (Nat.card (fusionOddCore X)) :=
    Nat.coprime_two_left.mp CFSG.LargeExtraspecial.S9.coprime_card_fusionOddCore
  have key : ∀ z : X, z ∈ fusionZStar X → ∀ b : ℕ, z ^ (2 ^ b) = 1 → z = 1 := by
    intro z hz b hzb
    have hzcenter : z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hzq : QuotientGroup.mk z ∈ Subgroup.center (X ⧸ fusionOddCore X) := by
        have hz' : QuotientGroup.mk' (fusionOddCore X) z ∈
            Subgroup.center (X ⧸ fusionOddCore X) := hz
        rwa [QuotientGroup.mk'_apply] at hz'
      have hxq : QuotientGroup.mk x * QuotientGroup.mk z =
          QuotientGroup.mk z * QuotientGroup.mk x :=
        Subgroup.mem_center_iff.mp hzq (QuotientGroup.mk x)
      have heq : QuotientGroup.mk' (fusionOddCore X) (x * z) =
          QuotientGroup.mk' (fusionOddCore X) (z * x) := by
        rw [map_mul, map_mul]
        exact hxq
      have heq' : (QuotientGroup.mk (x * z) : X ⧸ fusionOddCore X) =
          QuotientGroup.mk (z * x) := by
        simpa only [QuotientGroup.mk'_apply] using heq
      have hcO : (x * z)⁻¹ * (z * x) ∈ fusionOddCore X :=
        (QuotientGroup.eq).mp heq'
      have hc : x⁻¹ * z * x = z * ((x * z)⁻¹ * (z * x)) := by group
      have hcomm : Commute z ((x * z)⁻¹ * (z * x)) :=
        Subgroup.mem_center_iff.mp (hodd hcO) z
      have hconj : (x⁻¹ * z * x) ^ (2 ^ b) = 1 := by
        have h1 : x⁻¹ * z * x = (MulAut.conj x⁻¹) z := by
          rw [MulAut.conj_apply, inv_inv]
        rw [h1, ← map_pow, hzb, map_one]
      have hcpow : ((x * z)⁻¹ * (z * x)) ^ (2 ^ b) = 1 := by
        have h2 : (z * ((x * z)⁻¹ * (z * x))) ^ (2 ^ b) =
            z ^ (2 ^ b) * ((x * z)⁻¹ * (z * x)) ^ (2 ^ b) :=
          Commute.mul_pow hcomm (2 ^ b)
        have h3 : (z * ((x * z)⁻¹ * (z * x))) ^ (2 ^ b) = 1 := by
          rw [← hc]; exact hconj
        rw [h2, hzb, one_mul] at h3
        exact h3
      have hc1 : (x * z)⁻¹ * (z * x) = 1 := by
        have hdvd : orderOf ((x * z)⁻¹ * (z * x)) ∣ 2 ^ b :=
          orderOf_dvd_iff_pow_eq_one.mpr hcpow
        have hco : Odd (orderOf ((x * z)⁻¹ * (z * x))) :=
          hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (fusionOddCore X) hcO)
        exact orderOf_eq_one_iff.mp
          ((hco.coprime_two_right.pow_right b).eq_one_of_dvd hdvd)
      have hxz : x⁻¹ * z * x = z := by rw [hc, hc1, mul_one]
      calc x * z = x * (x⁻¹ * z * x) := by rw [hxz]
        _ = z * x := by group
    have hnorm : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center fun w hw => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (Subgroup.center X).zpow_mem hzcenter k
    have hpg : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card_dvd_pow (p := 2) (n := b) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_iff_pow_eq_one.mpr hzb)
    have hle : Subgroup.zpowers z ≤ CFSG.pCore 2 X := le_sSup ⟨hnorm, hpg⟩
    rw [hO2] at hle
    have h1 : z ∈ (⊥ : Subgroup X) := hle (Subgroup.mem_zpowers z)
    simpa using h1
  have hOddZ : Odd (Nat.card (fusionZStar X)) := by
    by_contra hoddZ
    rw [Nat.not_odd_iff_even] at hoddZ
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hoddZ)
    have hpow : (z : X) ^ (2 ^ 1) = 1 := by
      have hz2 : z ^ 2 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
      have h2 : (z : X) ^ 2 = 1 := by simpa using congrArg Subtype.val hz2
      simpa using h2
    have hz1 : (z : X) = 1 := key (z : X) z.2 1 hpow
    have hz1' : z = 1 := Subtype.ext hz1
    rw [hz1'] at hzord
    simp only [orderOf_one] at hzord
    omega
  exact le_sSup ⟨inferInstance, hOddZ⟩

theorem pRank_eq_of_isL2OrSz {S : Type} [Group S] [Finite S]
    {n : ℕ} (hn : 1 < n) (hS : IsL2OrSz S n) : CFSG.pRank 2 S = n := by
  rcases hS with hS | hS
  · rw [CFSG.GH74.GLS.pRank_two_eq_twoRank]
    exact CFSG.GH74.SmallRanks.twoRank_eq_of_statedClassicalModel_PSL_two_two hS
  · obtain ⟨a, ha, hn_eq, ⟨e⟩⟩ := seven_k_grp_exists_mulEquiv_sz hS
    rw [CFSG.GH74.GLS.pRank_two_eq_twoRank, twoRank_eq_of_mulEquiv_sz ha e]
    exact hn_eq.symm

theorem not_isPGroup_two_of_isL2OrSz {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 1 < n)
    (hS : IsL2OrSz S n) : ¬ IsPGroup 2 S := by
  unfold IsL2OrSz at hS
  intro h2
  haveI : IsSimpleGroup S := CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz hS
  have hcomm : commutator S = ⊤ := CFSG.Quasithin.E2.commutator_eq_top_of_psl_or_sz hn hS
  haveI : Group.IsNilpotent S := IsPGroup.isNilpotent h2
  have hlt := IsSolvable.commutator_lt_top_of_nontrivial S
  rw [hcomm] at hlt
  exact absurd hlt (lt_irrefl ⊤)

theorem sup_conj_eq_top_of_card_eq_two_pow
    {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 1 < n)
    (hS : IsL2OrSz S n) {A : Subgroup S} (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 2 ^ n)
    {g : S} (hg : conjSubgroup A g ≠ A) : A ⊔ conjSubgroup A g = ⊤ := by
  have hcard' : Nat.card (conjSubgroup A g) = 2 ^ n := by
    change Nat.card (A.map (MulAut.conj g⁻¹).toMonoidHom) = 2 ^ n
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hA' : IsElemAbelian 2 (conjSubgroup A g) :=
    CFSG.CGT.Timmesfeld75.isElemAbelian_map_of_hom hA (MulAut.conj g⁻¹).toMonoidHom
  rcases hS with hS | hS
  · obtain ⟨e⟩ :=
      CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField S 2 2 n hS
    have hf : n ≠ 0 := by omega
    obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow hA.isPGroup
    have hL2P : CFSG.CGT.Timmesfeld75.IsL2Pair S (P : Subgroup S) (2 ^ n) :=
      CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow hf ⟨e⟩ P
    have hPeq : (P : Subgroup S) = A :=
      (Subgroup.eq_of_le_of_card_ge hAP (by simp [hcard, hL2P.card_eq])).symm
    obtain ⟨P', hA'P'⟩ := IsPGroup.exists_le_sylow hA'.isPGroup
    have hL2P' : CFSG.CGT.Timmesfeld75.IsL2Pair S (P' : Subgroup S) (2 ^ n) :=
      CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow hf ⟨e⟩ P'
    have hP'eq : (P' : Subgroup S) = conjSubgroup A g :=
      (Subgroup.eq_of_le_of_card_ge hA'P' (by simp [hcard', hL2P'.card_eq])).symm
    have hPP' : P ≠ P' := by
      intro h
      apply hg
      rw [← hP'eq, ← congrArg (fun Q : Sylow 2 S => (Q : Subgroup S)) h, hPeq]
    have htop := hL2P.sup_sylow_eq_top hPP'
    rwa [hPeq, hP'eq] at htop
  · obtain ⟨a, ha, hn_eq, ⟨e⟩⟩ := seven_k_grp_exists_mulEquiv_sz hS
    have hcarda : Nat.card A = 2 ^ (2 * a + 1) := by rw [hcard, hn_eq]
    have hcarda' : Nat.card (conjSubgroup A g) = 2 ^ (2 * a + 1) := by rw [hcard', hn_eq]
    obtain ⟨P, hPA⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e hA hcarda
    obtain ⟨P', hPA'⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e hA' hcarda'
    have hPP' : P ≠ P' := by
      intro h
      apply hg
      rw [hPA', ← h, ← hPA]
    have htop := inf_centralizer_sup_inf_centralizer_eq_top ha e hPP'
    rwa [← hPA, ← hPA'] at htop

end CFSG.LocalAnalysis.WeakClosure81
