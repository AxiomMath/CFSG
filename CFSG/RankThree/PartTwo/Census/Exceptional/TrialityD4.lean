module

public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic
public import CFSG.Adapters.TauCetiExceptional.TwistedD4Push
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

section Two

variable {G : Type} [Group G] [Finite G]

theorem add_le_localRank_of_two_commuting_SL2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K₁ K₂ : Type} [Field K₁] [Field K₂] [Fintype K₁] [Fintype K₂] {f₁ f₂ : ℕ}
    (hK₁ : Fintype.card K₁ = p ^ f₁) (hK₂ : Fintype.card K₂ = p ^ f₂)
    (φ₁ : SL(2, K₁) →* G) (φ₂ : SL(2, K₂) →* G) (h₁ : Function.Injective φ₁)
    (h₂ : Function.Injective φ₂) (hcomm : ∀ A B, φ₁ A * φ₂ B = φ₂ B * φ₁ A) :
    f₁ + f₂ ≤ localRank p G := by
  let K : Bool → Type := fun b => cond b K₁ K₂
  let iF : ∀ b, Field (K b) := fun b => match b with
    | true => (inferInstance : Field K₁)
    | false => (inferInstance : Field K₂)
  let iT : ∀ b, Fintype (K b) := fun b => match b with
    | true => (inferInstance : Fintype K₁)
    | false => (inferInstance : Fintype K₂)
  let φ : ∀ b, SL(2, K b) →* G := fun b => match b with
    | true => φ₁
    | false => φ₂
  have h := sum_le_localRank_of_commuting_SL2 hp hp2 true (K := K) (fun b => cond b f₁ f₂)
    (fun b => match b with
      | true => hK₁
      | false => hK₂) φ
    (fun b => match b with
      | true => h₁
      | false => h₂)
    (fun i j hij A B => match i, j, hij, A, B with
      | true, false, _, A, B => hcomm A B
      | false, true, _, A, B => (hcomm B A).symm)
  rw [Fintype.sum_bool] at h
  exact h

end Two

section Native

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem four_le_localRank_derivedCentralQuotient_D4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hσ : σ ^ 3 = 1) (hK : Nat.card K = p ^ (3 * f))
    (hk : Nat.card (fixSubfield σ) = p ^ f)
    [Finite (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ.toRingHom))] :
    4 ≤ localRank p
      (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ.toRingHom)) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
    rwa [ringChar.eq K p]
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
  have h := add_le_localRank_of_two_commuting_SL2 hp hp2 (K₁ := K) (K₂ := fixSubfield σ)
    (f₁ := 3 * f) (f₂ := f) (by rw [← Nat.card_eq_fintype_card, hK])
    (by rw [← Nat.card_eq_fintype_card, hk]) (π.comp ι) (π.comp η) (hπ.comp hι) (hπ.comp hη)
    fun A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm A B]
  omega

end Native

section Field

variable (d : ValidLieTypeIndex)

noncomputable abbrev cubeField : Subfield d.Closure :=
  frobeniusFixedSubfield d.Closure d.characteristic (d.fieldExponent * 3)

theorem frob_mem_cubeField (c : cubeField d) : (c : d.Closure) ^ d.fieldOrder ∈ cubeField d := by
  rw [mem_frobeniusFixedSubfield, ← pow_mul, mul_comm, pow_mul,
    mem_frobeniusFixedSubfield.1 c.2]

@[expose] noncomputable def cubeFrobHom : cubeField d →+* cubeField d :=
  ((d.frobeniusEquiv : d.Closure →+* d.Closure).comp (cubeField d).subtype).codRestrict
    (cubeField d) fun c => by
      rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, ValidLieTypeIndex.frobeniusEquiv_apply]
      exact frob_mem_cubeField d c

theorem coe_cubeFrobHom (c : cubeField d) :
    ((cubeFrobHom d c : cubeField d) : d.Closure) = (c : d.Closure) ^ d.fieldOrder :=
  ValidLieTypeIndex.frobeniusEquiv_apply d _

instance : Finite (cubeField d) :=
  finite_frobeniusFixedSubfield _ _ _ (by have := d.fieldExponent_pos; omega)

@[expose] noncomputable def cubeFrob : cubeField d ≃+* cubeField d :=
  RingEquiv.ofBijective (cubeFrobHom d)
    ⟨(cubeFrobHom d).injective, Finite.surjective_of_injective (cubeFrobHom d).injective⟩

theorem coe_cubeFrob (c : cubeField d) :
    ((cubeFrob d c : cubeField d) : d.Closure) = (c : d.Closure) ^ d.fieldOrder :=
  coe_cubeFrobHom d c

theorem cubeFrob_pow_three : cubeFrob d ^ 3 = 1 := by
  refine RingEquiv.ext fun c => Subtype.ext ?_
  change ((cubeFrob d (cubeFrob d (cubeFrob d c)) : cubeField d) : d.Closure) = c
  rw [coe_cubeFrob, coe_cubeFrob, coe_cubeFrob, ← pow_mul, ← pow_mul,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, ← pow_add, ← pow_add,
    show d.fieldExponent + (d.fieldExponent + d.fieldExponent) = d.fieldExponent * 3 by ring]
  exact mem_frobeniusFixedSubfield.1 c.2

theorem card_cubeField : Nat.card (cubeField d) = d.fieldOrder ^ 3 := by
  rw [card_frobeniusFixedSubfield _ _ _ (by have := d.fieldExponent_pos; omega),
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, ← pow_mul]

theorem card_fixSubfield_cubeFrob : Nat.card (fixSubfield (cubeFrob d)) = d.fieldOrder := by
  rw [← ValidLieTypeIndex.card_fixedField]
  refine Nat.card_congr
    { toFun := fun c => ⟨((c : cubeField d) : d.Closure), ?_⟩
      invFun := fun x => ⟨⟨x, ?_⟩, ?_⟩
      left_inv := fun c => rfl
      right_inv := fun x => rfl }
  · rw [ValidLieTypeIndex.mem_fixedField, ← coe_cubeFrob]
    exact congrArg Subtype.val (show cubeFrob d c = c from c.2)
  · have hle : d.fixedField ≤ cubeField d := by
      rw [ValidLieTypeIndex.fixedField_def]
      exact frobeniusFixedSubfield_le_of_dvd (dvd_mul_right _ 3)
    exact hle x.2
  · refine Subtype.ext ?_
    change ((cubeFrob d ⟨x, _⟩ : cubeField d) : d.Closure) = x
    rw [coe_cubeFrob]
    exact ValidLieTypeIndex.mem_fixedField.1 x.2

end Field

theorem four_le_twoLocalOddRank_trialityD4 (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hp2 : q.p ≠ 2)
    [hfin : Finite (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.trialityD4 q, hv⟩ with hd
  have hq : d.fieldOrder = q.card := LieTypeIndex.fieldOrder_trialityD4 q
  have hpc : d.characteristic = q.p := LieTypeIndex.characteristic_trialityD4 q
  have hfe : d.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_trialityD4 q
  have hcard : Nat.card (cubeField d) = q.card ^ TwistTag.D4.order := by
    rw [card_cubeField, hq]
    rfl
  have hfinK : Finite (cubeField d) :=
    finite_frobeniusFixedSubfield _ _ _ (by have := d.fieldExponent_pos; omega)
  obtain ⟨e⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2 (cubeField d) hcard
    (cubeFrob d).toRingHom fun x => Subtype.ext (by
      change ((cubeFrob d x : cubeField d) : d.Closure) = _
      rw [coe_cubeFrob, hq, SubmonoidClass.coe_pow])
  have : Finite (CFSG.Blueprint.DerivedCentralQuotient
      (twistedFixedGroup .D4 (cubeField d) (cubeFrob d).toRingHom)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hp : q.p.Prime := q.prime_p
  have h4 := four_le_localRank_derivedCentralQuotient_D4 (cubeFrob d) hp hp2 q.exponent_pos
    (cubeFrob_pow_three d) (by rw [card_cubeField, hq, PrimePower.card_def, ← pow_mul, mul_comm])
    (by rw [card_fixSubfield_cubeFrob, hq, PrimePower.card_def])
  exact four_le_twoLocalOddRank_of_localRank hp hp2
    (h4.trans (localRank_eq_of_mulEquiv e hp).le)

end CFSG.RankThree.PartTwo.Census.Exceptional
