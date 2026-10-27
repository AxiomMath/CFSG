module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanCoverTools
public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySubTorus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
public import CFSG.GH74.Filter.Lie.SepWitness
public import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.RankThree.CentralCover
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def e6D4Embedding : Fin 4 → Fin Tag.E6.rank :=
  fun i => ⟨i.val + 1, by
    have hi := i.isLt
    have h6 : Tag.E6.rank = 6 := rfl
    omega⟩

theorem e6D4Embedding_injective : Function.Injective e6D4Embedding := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [e6D4Embedding] at h'
  omega

theorem cartan_E6_submatrix_e6D4Embedding :
    Tag.E6.cartan.submatrix e6D4Embedding e6D4Embedding = Tag.D4.cartan := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem isUnit_det_cartan_E6_submatrix_e6D4Embedding :
    IsUnit (((Tag.E6.cartan.submatrix e6D4Embedding e6D4Embedding).det : ℤ) : ZMod 3) := by
  have h4 : (Tag.E6.cartan.submatrix e6D4Embedding e6D4Embedding).det = 4 := by
    rw [cartan_E6_submatrix_e6D4Embedding]
    exact det_cartan_D4
  rw [h4]
  exact isUnit_natCast_of_coprime (by decide : Nat.Coprime 4 3)

private theorem chevSubTorus_comap_comm
    {τ : Tag} {F : Type} [Field F] {r d : ℕ} [NeZero r] (hr : r.Prime) (hr2 : r ≠ 2)
    (e : Fin d → Fin τ.rank) (he : Function.Injective e) {ζ : Fˣ} (hζ : ζ ^ r = 1)
    {Y : Type} [Group Y] (φ : Y →* adjointGroup τ F) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∀ x ∈ (chevSubTorus e ζ hζ).range.comap φ,
      ∀ y ∈ (chevSubTorus e ζ hζ).range.comap φ, x * y = y * x := by
  classical
  let c : Fin d → (Fin d → ZMod r) →ₗ[ZMod r] ZMod r := fun i =>
    (cartanFunctional τ r (e i)).comp (subTorusLinearMap e)
  have hc : ∀ i : Fin d, c i (Pi.single i 1) = 2 := by
    intro i
    show cartanFunctional τ r (e i) (subTorusExp e (Pi.single i 1)) = 2
    rw [subTorusExp_single e he i, cartanFunctional_single]
  have hconj : ∀ (i : Fin d) (v : Fin d → ZMod r),
      (⟨weylElt τ F (e i) 1, weylElt_mem_adjointGroup (e i) 1⟩ : adjointGroup τ F) *
          chevSubTorus e ζ hζ (.ofAdd v) *
          (⟨weylElt τ F (e i) 1, weylElt_mem_adjointGroup (e i) 1⟩ : adjointGroup τ F)⁻¹ =
        chevSubTorus e ζ hζ (.ofAdd (v - c i v • Pi.single i 1)) := by
    intro i v
    have hcv : c i v = ∑ j : Fin d, (τ.cartan (e j) (e i) : ZMod r) * v j := by
      show cartanFunctional τ r (e i) (subTorusExp e v) = _
      rw [cartanFunctional_apply, sum_mul_subTorusExp]
    rw [hcv]
    exact weylElt_conj_chevSubTorus e he ζ hζ i v
  exact reflection_comap_comm hφ hker hr hr2 (chevSubTorus e ζ hζ) c hc
    (fun i => ⟨weylElt τ F (e i) 1, weylElt_mem_adjointGroup (e i) 1⟩) hconj

theorem chevSubTorus_cartan_witness
    {τ : Tag} {F : Type} [Field F] {r d : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (e : Fin d → Fin τ.rank) (he : Function.Injective e) {ζ : Fˣ}
    (hζo : orderOf ζ = r) (hζ : ζ ^ r = 1)
    (hdet : IsUnit (((τ.cartan.submatrix e e).det : ℤ) : ZMod r)) (h4 : 4 ≤ d)
    {Y : Type} [Group Y] (φ : Y →* adjointGroup τ F) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ D : Subgroup (adjointGroup τ F),
      (∀ x ∈ D, x ^ r = 1) ∧
        (∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x) ∧
          r ^ 4 ≤ Nat.card D ∧
            D ≤ Subgroup.normalizer (((posUnipotent τ F).subgroupOf (adjointGroup τ F) :
              Subgroup (adjointGroup τ F)) : Set (adjointGroup τ F)) := by
  classical
  haveI : NeZero r := ⟨hr.ne_zero⟩
  set D : Subgroup (adjointGroup τ F) := (chevSubTorus e ζ hζ).range with hD
  have hinj : Function.Injective (chevSubTorus e ζ hζ) :=
    chevSubTorus_injective e he hζo hζ hdet
  have hcard : Nat.card D = r ^ d := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      card_multiplicative_fin_zmod]
  have hexp : ∀ x ∈ D, x ^ r = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  have hDcomm : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x :=
    chevSubTorus_comap_comm hr hr2 e he hζ φ hφ hker
  have hDnorm : D ≤ Subgroup.normalizer
      (((posUnipotent τ F).subgroupOf (adjointGroup τ F) :
        Subgroup (adjointGroup τ F)) : Set (adjointGroup τ F)) := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    have hTG : ((chevSubTorus e ζ hζ a : adjointGroup τ F) : ModGL τ F) ∈ torusGroup τ F := by
      have ha : a = Multiplicative.ofAdd (Multiplicative.toAdd a) :=
        (ofAdd_toAdd a).symm
      rw [ha, chevSubTorus_apply]
      exact (torusCoordHom τ F
        (chevTorusExp τ ζ hζ (.ofAdd (subTorusExp e (Multiplicative.toAdd a))))).2
    exact uc22pwex_mem_normalizer_subgroupOf (torusGroup_le_normalizer_posUnipotent hTG)
  refine ⟨D, hexp, hDcomm, ?_, hDnorm⟩
  rw [hcard]
  exact Nat.pow_le_pow_right hr.one_le h4

section Certificates

theorem cartanRankLarge_of_model {τ : Tag} {f : ℕ} {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] (hFcard : Nat.card F = 2 ^ f)
    (e₀ : (K ⧸ Subgroup.center K) ≃* CFSG.Blueprint.AdjointQuotient τ F)
    {r d : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ 2 ^ f - 1)
    (e : Fin d → Fin τ.rank) (he : Function.Injective e) (h4 : 4 ≤ d)
    (hdet : IsUnit (((τ.cartan.submatrix e e).det : ℤ) : ZMod r))
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    ∃ r' : ℕ, r'.Prime ∧ r' ≠ 2 ∧ r' ∣ 2 ^ f - 1 ∧
      3 < CFSG.Open.pRank r' (⊤ : Subgroup (normalizerQuotient S)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP F 2 := uc22pwex_charP_two hFcard
  let eφ : (K ⧸ Subgroup.center K) ≃* adjointGroup τ F :=
    e₀.trans (CFSG.GH74.Filter.Lie.adjointQuotientEquiv τ F)
  let φ : K →* adjointGroup τ F :=
    eφ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ :=
    eφ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : φ.ker ≤ Subgroup.center K := by
    have hker_eq : φ.ker = Subgroup.center K := by
      rw [MonoidHom.ker_comp_of_injective _ _ eφ.injective, QuotientGroup.ker_mk']
    exact le_of_eq hker_eq
  have hdvdUnits : r ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    rw [hFcard]
    exact hrdvd
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' r hdvdUnits
  have hζ : ζ ^ r = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨D, hDr, hDc, hDk, hDU⟩ :=
    chevSubTorus_cartan_witness hr hr2 e he hζo hζ hdet h4 φ hφ hker
  let U : Subgroup (adjointGroup τ F) :=
    (posUnipotent τ F).subgroupOf (adjointGroup τ F)
  have hU : IsSylowTwoOf U ⊤ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨hU2, hUidx⟩ := isPGroup_and_not_dvd_index 2
      (posUnipotent_le_adjointGroup (τ := τ) (K := F))
      (card_posUnipotent (τ := τ) (K := F))
    refine ⟨le_top, hU2, ?_⟩
    rwa [CFSG.QuasithinUnique.index_subgroupOf_top]
  have h := le_pRank_normalizerQuotient_of_comap_comm hφ hker hr hr2 hDr hDc hDk
    hU hDU S hS
  exact ⟨r, hr, hr2, hrdvd, by omega⟩

theorem k_CartanRankLarge_F4 :
    ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
      CFSG.Open.StatedLieAdmissible .F4 0 2 f → 2 < 2 ^ f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .F4 0 2 f →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .F4 0 →
                ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
                  3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ f _ hq hL _ _ S hS _
  obtain ⟨F, hFld, hFin, hFcard, ⟨e₀⟩⟩ := (hL.chevalleyExceptionalModel (by decide)).2
  letI := hFld
  letI := hFin
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at hq
  obtain ⟨r, hr, hr2, -, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  have hdet : IsUnit (((Tag.F4.cartan.submatrix id id).det : ℤ) : ZMod r) := by
    rw [Matrix.submatrix_id_id, det_cartan_F4]
    exact isUnit_natCast_of_coprime (Nat.coprime_one_left r)
  exact cartanRankLarge_of_model hFcard e₀ hr hr2 hrdvd id Function.injective_id (by decide)
    hdet S hS

theorem k_CartanRankLarge_E7 :
    ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
      CFSG.Open.StatedLieAdmissible .E7 0 2 f → 2 < 2 ^ f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 f →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .E7 0 →
                ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
                  3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ f _ hq hL _ _ S hS _
  obtain ⟨F, hFld, hFin, hFcard, ⟨e₀⟩⟩ := (hL.chevalleyExceptionalModel (by decide)).2
  letI := hFld
  letI := hFin
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at hq
  obtain ⟨r, hr, hr2, -, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  have hdet : IsUnit (((Tag.E7.cartan.submatrix id id).det : ℤ) : ZMod r) := by
    rw [Matrix.submatrix_id_id, det_cartan_E7]
    exact isUnit_natCast_of_coprime ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  exact cartanRankLarge_of_model hFcard e₀ hr hr2 hrdvd id Function.injective_id (by decide)
    hdet S hS

theorem k_CartanRankLarge_E8 :
    ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
      CFSG.Open.StatedLieAdmissible .E8 0 2 f → 2 < 2 ^ f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 f →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .E8 0 →
                ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
                  3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ f _ hq hL _ _ S hS _
  obtain ⟨F, hFld, hFin, hFcard, ⟨e₀⟩⟩ := (hL.chevalleyExceptionalModel (by decide)).2
  letI := hFld
  letI := hFin
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at hq
  obtain ⟨r, hr, hr2, -, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  have hdet : IsUnit (((Tag.E8.cartan.submatrix id id).det : ℤ) : ZMod r) := by
    rw [Matrix.submatrix_id_id, det_cartan_E8]
    exact isUnit_natCast_of_coprime (Nat.coprime_one_left r)
  exact cartanRankLarge_of_model hFcard e₀ hr hr2 hrdvd id Function.injective_id (by decide)
    hdet S hS

theorem k_CartanRankLarge_E6_of_three_le :
    ∀ (K : Type) [Group K] [Finite K] (f : ℕ), 3 ≤ f →
      CFSG.Open.StatedLieAdmissible .E6 0 2 f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 f →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .E6 0 →
                ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
                  3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ f hf _ hL _ _ S hS _
  obtain ⟨F, hFld, hFin, hFcard, ⟨e₀⟩⟩ := (hL.chevalleyExceptionalModel (by decide)).2
  letI := hFld
  letI := hFin
  obtain ⟨r, hr, hr2, hr3, hrdvd⟩ :=
    CFSG.exists_prime_ne_two_ne_three_dvd_two_pow_sub_one hf
  have hdet : IsUnit (((Tag.E6.cartan.submatrix id id).det : ℤ) : ZMod r) := by
    rw [Matrix.submatrix_id_id, det_cartan_E6]
    exact isUnit_natCast_of_coprime ((Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3))
  exact cartanRankLarge_of_model hFcard e₀ hr hr2 hrdvd id Function.injective_id (by decide)
    hdet S hS

theorem k_CartanRankLarge_E6_of_eq_two :
    ∀ (K : Type) [Group K] [Finite K],
      CFSG.Open.StatedLieAdmissible .E6 0 2 2 →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 2 →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .E6 0 →
                ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ 2 - 1 ∧
                  3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ _ hL _ _ S hS _
  obtain ⟨F, hFld, hFin, hFcard, ⟨e₀⟩⟩ := (hL.chevalleyExceptionalModel (by decide)).2
  letI := hFld
  letI := hFin
  have hdet := isUnit_det_cartan_E6_submatrix_e6D4Embedding
  exact cartanRankLarge_of_model hFcard e₀ (by norm_num) (by norm_num) (by norm_num)
    e6D4Embedding e6D4Embedding_injective (by decide) hdet S hS

theorem k_CartanRankLarge_E6 :
    ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
      CFSG.Open.StatedLieAdmissible .E6 0 2 f → 2 < 2 ^ f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 f →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .E6 0 →
                ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
                  3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ f hadm hq hL hqs hodd S hS hrank
  rcases Nat.lt_or_ge f 3 with hf | hf
  · have hf2 : f = 2 := by
      rcases f with _ | _ | _ | f
      · norm_num at hq
      · norm_num at hq
      · rfl
      · omega
    subst hf2
    exact k_CartanRankLarge_E6_of_eq_two K hadm hL hqs hodd S hS hrank
  · exact k_CartanRankLarge_E6_of_three_le K f hf hadm hL hqs hodd S hS hrank

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
