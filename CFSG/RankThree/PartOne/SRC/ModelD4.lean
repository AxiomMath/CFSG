module

public import CFSG.RankThree.PartOne.SRC.CentralizerTwo
public import CFSG.RankThree.PartOne.SRC.ThreeOne
public import CFSG.RankThree.PartTwo.Census.Exceptional.TrialityD4

public section

namespace CFSG.RankThree.PartOne.SRC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.RankThree.PartTwo.Census.Exceptional

@[expose] def negOneSL2 (F : Type*) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨-1, by simp [Matrix.det_neg]⟩

theorem negOneSL2_sq (F : Type*) [Field F] : negOneSL2 F ^ 2 = 1 := by
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
  change (-1 : Matrix (Fin 2) (Fin 2) F) * -1 = 1
  rw [neg_mul_neg, one_mul]

theorem negOneSL2_ne_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) : negOneSL2 F ≠ 1 := by
  intro h
  have h00 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => X.val 0 0) h
  change (-1 : Matrix (Fin 2) (Fin 2) F) 0 0 = (1 : Matrix (Fin 2) (Fin 2) F) 0 0 at h00
  rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  apply h2
  linear_combination -h00

theorem orderOf_negOneSL2 (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) : orderOf (negOneSL2 F) = 2 :=
  orderOf_eq_prime (negOneSL2_sq F) (negOneSL2_ne_one F h2)

theorem negOneSL2_comm (F : Type*) [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    A * negOneSL2 F = negOneSL2 F * A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (A : Matrix (Fin 2) (Fin 2) F) * (-1 : Matrix (Fin 2) (Fin 2) F) =
    (-1 : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]


theorem rankFourCover_derivedCentralQuotient_D4 {p f : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] [CharP K p] (σ : K ≃+* K) (hp2 : p ≠ 2) (hf : 2 ≤ f) (hσ : σ ^ 3 = 1)
    (hK : Nat.card K = p ^ (3 * f)) :
    RankFourCover p
      (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ.toRingHom)) := by
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2K : (2 : fixSubfield σ) ≠ 0 := by
    intro h
    have h' := congrArg (fixSubfield σ).subtype h
    rw [map_ofNat, map_zero] at h'
    exact Ring.two_ne_zero hK2 h'
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ
  obtain ⟨-, -, hH⟩ := odd_diagram_fixed_root_group_perfect .D4 K hK2 σ
  have hZ := center_graphFixedRootGroup_eq_bot (t := .D4) (K := K) (σ := σ.toRingHom)
    σ.surjective
  let e₁ : ↥(graphFixedRootGroup .D4 K σ.toRingHom) ≃*
      ↥⁅twistedFixedGroup .D4 K σ.toRingHom, twistedFixedGroup .D4 K σ.toRingHom⁆ :=
    MulEquiv.subgroupCongr hH.symm
  let π : ↥(graphFixedRootGroup .D4 K σ.toRingHom) →*
      CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ.toRingHom) :=
    (QuotientGroup.mk' _).comp e₁.toMonoidHom
  have hπ : Function.Injective π := by
    refine (injective_iff_map_eq_one π).2 fun x hx => ?_
    have h1 : e₁ x ∈ Subgroup.center
        ↥⁅twistedFixedGroup .D4 K σ.toRingHom, twistedFixedGroup .D4 K σ.toRingHom⁆ :=
      (QuotientGroup.eq_one_iff _).1 hx
    have h2 : x ∈ Subgroup.center ↥(graphFixedRootGroup .D4 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro g
      apply e₁.injective
      rw [map_mul, map_mul]
      exact h1 (e₁ g)
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hηt : orderOf ((π.comp η) (negOneSL2 (fixSubfield σ))) = 2 := by
    rw [orderOf_injective (π.comp η) (hπ.comp hη), orderOf_negOneSL2 _ h2K]
  exact rankFourCover_of_SL2 (F := K) hK hp2 (by omega) (π.comp ι) (hπ.comp hι) hηt
    fun g => by
      simp only [MonoidHom.comp_apply, ← map_mul, hcomm g]

theorem rankFourCover_derivedCentralQuotient_D4_prime {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] [CharP K p] (σ : K ≃+* K) (hp2 : p ≠ 2) (hσ : σ ^ 3 = 1)
    (hK : Nat.card K = p ^ 3) (hk : Nat.card (fixSubfield σ) = p) :
    RankFourCover p
      (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ.toRingHom)) := by
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2K : (2 : fixSubfield σ) ≠ 0 := by
    intro h
    have h' := congrArg (fixSubfield σ).subtype h
    rw [map_ofNat, map_zero] at h'
    exact Ring.two_ne_zero hK2 h'
  have hkc : CharP (fixSubfield σ) p := by
    have := Fintype.ofFinite (fixSubfield σ)
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hk, pow_one])
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ
  obtain ⟨-, -, hH⟩ := odd_diagram_fixed_root_group_perfect .D4 K hK2 σ
  have hZ := center_graphFixedRootGroup_eq_bot (t := .D4) (K := K) (σ := σ.toRingHom)
    σ.surjective
  let e₁ : ↥(graphFixedRootGroup .D4 K σ.toRingHom) ≃*
      ↥⁅twistedFixedGroup .D4 K σ.toRingHom, twistedFixedGroup .D4 K σ.toRingHom⁆ :=
    MulEquiv.subgroupCongr hH.symm
  let π : ↥(graphFixedRootGroup .D4 K σ.toRingHom) →*
      CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ.toRingHom) :=
    (QuotientGroup.mk' _).comp e₁.toMonoidHom
  have hπ : Function.Injective π := by
    refine (injective_iff_map_eq_one π).2 fun x hx => ?_
    have h1 : e₁ x ∈ Subgroup.center
        ↥⁅twistedFixedGroup .D4 K σ.toRingHom, twistedFixedGroup .D4 K σ.toRingHom⁆ :=
      (QuotientGroup.eq_one_iff _).1 hx
    have h2 : x ∈ Subgroup.center ↥(graphFixedRootGroup .D4 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro g
      apply e₁.injective
      rw [map_mul, map_mul]
      exact h1 (e₁ g)
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  refine rankFourCover_of_two_SL2_gen (Fact.out : p.Prime) hp2
    (fun _ _ _ ρ hρ hker => rank_four_of_cover_SL2_three_one (F₁ := K) (F₂ := fixSubfield σ) hK hk
      hp2 ρ hρ hker)
    (π.comp ι) (π.comp η) (hπ.comp hι) (hπ.comp hη)
    (fun A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm A B])
    (t := (π.comp η) (negOneSL2 (fixSubfield σ)))
    (by rw [orderOf_injective (π.comp η) (hπ.comp hη), orderOf_negOneSL2 _ h2K]) ?_ ?_
  · intro A
    simp only [MonoidHom.comp_apply, ← map_mul, hcomm A]
  · intro B
    simp only [MonoidHom.comp_apply, ← map_mul, negOneSL2_comm]


theorem rankFourCover_trialityD4 (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hp2 : q.p ≠ 2) (hq : 2 ≤ q.exponent) :
    RankFourCover q.p (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.trialityD4 q, hv⟩ with hd
  have hqd : d.fieldOrder = q.card := LieTypeIndex.fieldOrder_trialityD4 q
  have hcard : Nat.card (cubeField d) = q.card ^ TwistTag.D4.order := by
    rw [card_cubeField, hqd]
    rfl
  have hfinK : Finite (cubeField d) :=
    finite_frobeniusFixedSubfield _ _ _ (by have := d.fieldExponent_pos; omega)
  obtain ⟨e⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2 (cubeField d) hcard
    (cubeFrob d).toRingHom fun x => Subtype.ext (by
      change ((cubeFrob d x : cubeField d) : d.Closure) = _
      rw [coe_cubeFrob, hqd, SubmonoidClass.coe_pow])
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (cubeField d) = q.p ^ (3 * q.exponent) := by
    rw [card_cubeField, hqd, PrimePower.card_def, ← pow_mul, mul_comm]
  have : Fintype (cubeField d) := Fintype.ofFinite _
  have : CharP (cubeField d) q.p :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact rankFourCover_of_mulEquiv e.symm
    (rankFourCover_derivedCentralQuotient_D4 (cubeFrob d) hp2 hq (cubeFrob_pow_three d) hK)

theorem rankFourCover_trialityD4_prime (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hp2 : q.p ≠ 2) (hq : q.exponent = 1) :
    RankFourCover q.p (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.trialityD4 q, hv⟩ with hd
  have hqd : d.fieldOrder = q.card := LieTypeIndex.fieldOrder_trialityD4 q
  have hcard : Nat.card (cubeField d) = q.card ^ TwistTag.D4.order := by
    rw [card_cubeField, hqd]
    rfl
  have hfinK : Finite (cubeField d) :=
    finite_frobeniusFixedSubfield _ _ _ (by have := d.fieldExponent_pos; omega)
  obtain ⟨e⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2 (cubeField d) hcard
    (cubeFrob d).toRingHom fun x => Subtype.ext (by
      change ((cubeFrob d x : cubeField d) : d.Closure) = _
      rw [coe_cubeFrob, hqd, SubmonoidClass.coe_pow])
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (cubeField d) = q.p ^ 3 := by
    rw [card_cubeField, hqd, PrimePower.card_def, hq, pow_one]
  have hk : Nat.card (fixSubfield (cubeFrob d)) = q.p := by
    rw [card_fixSubfield_cubeFrob, hqd, PrimePower.card_def, hq, pow_one]
  have : Fintype (cubeField d) := Fintype.ofFinite _
  have : CharP (cubeField d) q.p :=
    charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact rankFourCover_of_mulEquiv e.symm
    (rankFourCover_derivedCentralQuotient_D4_prime (cubeFrob d) hp2 (cubeFrob_pow_three d) hK hk)

end CFSG.RankThree.PartOne.SRC
