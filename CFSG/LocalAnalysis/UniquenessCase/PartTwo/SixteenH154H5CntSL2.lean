module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowSL4A
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H
open Matrix

private theorem s16h_statedClassicalModel_statedSL_two_of_card_eight
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 8) :
    StatedClassicalModel (StatedSL 2 K) .PSL 2 2 3 := by
  refine ⟨by norm_num [StatedLieAdmissible], K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ?_⟩
  refine ⟨?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := K))).trans
      QuotientGroup.quotientBot).symm

theorem s16h_natNorm_elemAbelian_le_sl2 {K : Type} [Field K] [Finite K] {a : ℕ}
    (ha : 2 ≤ a ∧ a ≤ 3) (hK : Nat.card K = 2 ^ a) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {A' : Subgroup (MulAut (StdMod (Fin 2) K))} (hA : A' ≤ natNorm (StatedSL 2 K))
    (hE : IsElemAbelian q A') : Nat.card ↥A' ≤ q ^ 2 := by
  rcases (by omega : a = 2 ∨ a = 3) with rfl | rfl
  · exact s16h_H5_natNorm_statedSL_two_four_elemAbelian (by rw [hK]; norm_num) hq hq2 hA hE
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  haveI : CharP K 2 := by
    have hKeven : Fintype.card K % 2 = 0 := by
      rw [Fintype.card_eq_nat_card, hK8]
    have hring : ringChar K = 2 := (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
    exact hring ▸ ringChar.charP K
  haveI : Finite (MulAut (StdMod (Fin 2) K)) := MulEquiv.finite_left
  haveI : Fact q.Prime := ⟨hq⟩
  have hΓ : HasScalarCommutant (StatedSL 2 K) :=
    hasScalarCommutant_statedSL (d := 2) (by norm_num)
  let φ : ↥A' →* (K ≃+* K) := (fieldHom hΓ).comp (Subgroup.inclusion hA)
  have hcardA : Nat.card ↥A' = Nat.card φ.ker * Nat.card φ.range :=
    (Subgroup.card_ker_mul_card_range φ).symm
  have hker : Nat.card φ.ker = Nat.card ↥(A' ⊓ linSub) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (fieldHom_eq_one_iff hΓ _).mp x.2⟩
        invFun := fun y =>
          ⟨⟨y.1, y.2.1⟩, (fieldHom_eq_one_iff hΓ ⟨y.1, hA y.2.1⟩).mpr y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hBrange : A' ⊓ linSub ≤
      (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range := by
    rintro g ⟨-, hglin⟩
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hglin
    exact ⟨A, rfl⟩
  let E₀ : Subgroup (GL (Fin 2) K) :=
    (A' ⊓ linSub).comap (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))
  have hmapE₀ : E₀.map (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) =
      A' ⊓ linSub := by
    show ((A' ⊓ linSub).comap (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))).map
      (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)) = A' ⊓ linSub
    exact Subgroup.map_comap_eq_self hBrange
  have hE₀card : Nat.card E₀ = Nat.card ↥(A' ⊓ linSub) := by
    rw [← hmapE₀]
    exact (Subgroup.card_map_of_injective (K := E₀) matHom_injective).symm
  have hB_el : IsElemAbelian q (A' ⊓ linSub) := IsElemAbelian.mono hE inf_le_left
  have hE₀el : IsElemAbelian q E₀ := IsElemAbelian.comap hB_el matHom_injective
  let δ : ↥E₀ →* Kˣ := (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).comp E₀.subtype
  have hcardE₀ : Nat.card E₀ = Nat.card δ.ker * Nat.card δ.range :=
    (Subgroup.card_ker_mul_card_range δ).symm
  have hδker : Nat.card δ.ker = Nat.card ↥(E₀ ⊓ StatedSL 2 K) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, CFSG.Open.StatedAPI.mem_statedSL_iff.mpr ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have h := congrArg (Units.val) x.2
      change (GeneralLinearGroup.det (x.1.1 : GL (Fin 2) K)).val = 1 at h
      rw [GeneralLinearGroup.val_det_apply] at h
      exact h
    · apply Units.ext
      exact CFSG.Open.StatedAPI.mem_statedSL_iff.mp y.2.2
  have hδrange_eq : δ.range =
      E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨A, hA₀, rfl⟩
      exact ⟨⟨A, hA₀⟩, rfl⟩
  have hδrange : Nat.card δ.range =
      Nat.card (E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ)) := by
    rw [hδrange_eq]
  have hE₁el : IsElemAbelian q (E₀ ⊓ StatedSL 2 K) := IsElemAbelian.mono hE₀el inf_le_left
  obtain ⟨c, hc⟩ := hE₁el.isPGroup.exists_card_eq
  have hc1 : c ≤ 1 := by
    have hle : c ≤ CFSG.Open.pRank q (StatedSL 2 K) :=
      CFSG.SectionRank.le_pRank hq.one_lt inf_le_right hE₁el hc
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (StatedSL 2 K)] at hle
    exact hle.trans
      (CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
        (s16h_statedClassicalModel_statedSL_two_of_card_eight hK8) hq hq2)
  obtain ⟨u, hu⟩ :=
    (hE₀el.isPGroup.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ)).exists_card_eq
  have hφP : IsPGroup q φ.range :=
    hE.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨v, hv⟩ := hφP.exists_card_eq
  have ht_dvd : Nat.card (E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ)) ∣ 7 := by
    have h := Subgroup.card_subgroup_dvd_card
      (E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ))
    rwa [Nat.card_units, hK8] at h
  have hr_dvd : Nat.card φ.range ∣ 3 := by
    have hAut3 : Nat.card (K ≃+* K) = 3 := by
      have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
        (p := 2) (n := 3) Nat.prime_two K (by rw [hK8]; norm_num)).1
      simpa using h
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hAut3] at h
  have huv : u + v ≤ 1 := by
    have htr : q ^ (u + v) ∣ 21 := by
      have h1 : Nat.card (E₀.map (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ)) *
          Nat.card φ.range ∣ 7 * 3 := Nat.mul_dvd_mul ht_dvd hr_dvd
      rw [hu, hv, ← pow_add] at h1
      norm_num at h1
      exact h1
    by_contra h
    have h2 : 2 ≤ u + v := by omega
    have hdvd : q ^ 2 ∣ 21 := (pow_dvd_pow q h2).trans htr
    have hq_dvd : q ∣ 21 := (dvd_pow_self q (by norm_num : (2 : ℕ) ≠ 0)).trans hdvd
    have hq_dvd' : q ∣ 3 * 7 := by simpa using hq_dvd
    rcases hq.dvd_mul.mp hq_dvd' with h3 | h7
    · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
      rw [hq3] at hdvd
      norm_num at hdvd
    · have hq7 : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp h7
      rw [hq7] at hdvd
      norm_num at hdvd
  have hA'card : Nat.card ↥A' = q ^ (c + u + v) := by
    calc Nat.card ↥A'
        = Nat.card φ.ker * Nat.card φ.range := hcardA
      _ = Nat.card ↥(A' ⊓ linSub) * Nat.card φ.range := by rw [hker]
      _ = Nat.card E₀ * Nat.card φ.range := by rw [hE₀card]
      _ = (Nat.card δ.ker * Nat.card δ.range) * Nat.card φ.range := by rw [hcardE₀]
      _ = (Nat.card ↥(E₀ ⊓ StatedSL 2 K) * Nat.card δ.range) * Nat.card φ.range := by
            rw [hδker]
      _ = (q ^ c * Nat.card δ.range) * Nat.card φ.range := by rw [hc]
      _ = (q ^ c * q ^ u) * Nat.card φ.range := by rw [hδrange, hu]
      _ = (q ^ c * q ^ u) * q ^ v := by rw [hv]
      _ = q ^ (c + u + v) := by rw [← pow_add, ← pow_add]
  have hExp : c + u + v ≤ 2 := by omega
  calc Nat.card ↥A' = q ^ (c + u + v) := hA'card
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq.one_le hExp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
