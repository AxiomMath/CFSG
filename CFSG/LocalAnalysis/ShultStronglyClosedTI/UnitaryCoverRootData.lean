module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.BenderSuzuki.External
open scoped Matrix commutatorElement

universe u

variable {K : Type u} [Field K]

@[expose] def unitaryCoverFixedField (J : HermitianForm 3 K) : Subfield K :=
  FixedBy.subfield K J.conj

@[expose] def unitaryCoverFirstCoord (J : HermitianForm 3 K) :
    hermitianUnipotentCoord J →* Multiplicative K where
  toFun z := Multiplicative.ofAdd z.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def unitaryCoverRoot (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (hermitianUnipotentPSU J hJ).range

@[expose] def unitaryCoverRootEquiv (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hermitianUnipotentCoord J ≃* unitaryCoverRoot J hJ :=
  MulEquiv.ofBijective (hermitianUnipotentPSU J hJ).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
      (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ),
      (hermitianUnipotentPSU J hJ).rangeRestrict_surjective⟩

@[simp]
theorem unitaryCoverRootEquiv_val (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) :
    (unitaryCoverRootEquiv J hJ z : ProjectiveSpecialUnitaryMatrixGroup J) =
      hermitianUnipotentPSU J hJ z := rfl

@[expose] def unitaryCoverZeroFirstEquiv [CharP K 2] (J : HermitianForm 3 K) :
    (unitaryCoverFirstCoord J).ker ≃* Multiplicative (unitaryCoverFixedField J) where
  toFun z := Multiplicative.ofAdd ⟨z.1.1.2, by
    have hz : z.1.1.1 = 0 := z.property
    have hp : z.1.1.2 + J.conj z.1.1.2 = 0 := by
      simpa only [hz, zero_mul, add_zero] using z.1.property
    exact (CharTwo.add_eq_zero.mp hp).symm⟩
  invFun w := ⟨⟨(0, ((Multiplicative.toAdd w : unitaryCoverFixedField J) : K)), by
    have hw : J.conj ((Multiplicative.toAdd w : unitaryCoverFixedField J) : K) = ((Multiplicative.toAdd w : unitaryCoverFixedField J) : K) :=
      (Multiplicative.toAdd w).property
    simp only [hw, CharTwo.add_self_eq_zero, zero_mul]⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show z.1.1.1 = 0 from z.property).symm
    · rfl
  right_inv _ := rfl
  map_mul' z w := by
    apply Subtype.ext
    change z.1.1.2 + w.1.1.2 - z.1.1.1 * J.conj w.1.1.1 = _
    have hz : z.1.1.1 = 0 := z.property
    simp only [hz, zero_mul, sub_zero]
    rfl

theorem unitaryCoverCoord_commutator_le_ker (J : HermitianForm 3 K) :
    commutator (hermitianUnipotentCoord J) ≤ (unitaryCoverFirstCoord J).ker := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  exact CFSG.BenderSuzuki.Background.hermitianUnipotent_commutator_fst J x y

theorem unitaryCoverRoot_nativeStructure [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (unitaryCoverRoot J hJ) = q ^ 3 ∧
      commutator (unitaryCoverRoot J hJ) = Subgroup.center (unitaryCoverRoot J hJ) ∧
      Nat.card (commutator (unitaryCoverRoot J hJ)) = q := by
  rcases huppert_II_10_12 J q hcard hfixed hJ with
    ⟨_hpoints, rho, pinf, _hinj, _hnatural, _hUcard,
      ⟨R, H, _hRle, _hHle, _hN, _hinf, _hsup, _hcyc, hRcard,
        hcomm, hcommcard, _hHcard, _hreg, ⟨coord, hcoord⟩,
        _hHcoord, _hHsurj⟩, _htwo, _hGcard, _hthree⟩
  have hmatch (z : hermitianUnipotentCoord J) :
      (coord z : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    have hMeq : M = hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    simpa only [hermitianUnipotentPSU_val, hMeq] using hproj
  have hrange : unitaryCoverRoot J hJ = R := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rw [← hmatch]
      exact (coord z).property
    · intro hx
      obtain ⟨z, hz⟩ := coord.surjective ⟨x, hx⟩
      exact ⟨z, (hmatch z).symm.trans (congrArg Subtype.val hz)⟩
  rw [hrange]
  exact ⟨hRcard, hcomm, hcommcard⟩

theorem unitaryCoverCoord_commutator_eq_ker [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    commutator (hermitianUnipotentCoord J) = (unitaryCoverFirstCoord J).ker := by
  let e := unitaryCoverRootEquiv J hJ
  have hmap : (commutator (hermitianUnipotentCoord J)).map (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) =
      commutator (unitaryCoverRoot J hJ) := by
    change (⁅(⊤ : Subgroup (hermitianUnipotentCoord J)), ⊤⁆ :
      Subgroup (hermitianUnipotentCoord J)).map (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) = _
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) e.surjective]
    rfl
  have hcommcard : Nat.card (commutator (hermitianUnipotentCoord J)) = q := by
    calc
      Nat.card (commutator (hermitianUnipotentCoord J)) =
          Nat.card ((commutator (hermitianUnipotentCoord J)).map (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ)) :=
        Nat.card_congr (e.subgroupMap _).toEquiv
      _ = q := by rw [hmap]; exact (unitaryCoverRoot_nativeStructure J q hcard hfixed hJ).2.2
  have hfixcard : Nat.card (unitaryCoverFixedField J) = q := by
    let c : unitaryCoverFixedField J ≃ {x : K // J.conj x = x} :=
      { toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr c).trans hfixed
  have hkerCard : Nat.card (unitaryCoverFirstCoord J).ker = q :=
    (Nat.card_congr (unitaryCoverZeroFirstEquiv J).toEquiv).trans
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (unitaryCoverFixedField J) ≃ _)).trans hfixcard)
  exact Subgroup.eq_of_le_of_card_ge (unitaryCoverCoord_commutator_le_ker J)
    (by rw [hkerCard, hcommcard])

theorem unitaryCoverFirstCoord_surjective [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Surjective (unitaryCoverFirstCoord J) := by
  have hqpos : 0 < q := by
    have h := Nat.card_pos (α := K)
    rw [hcard] at h
    by_contra hq
    have : q = 0 := by omega
    simp only [this, zero_pow (by decide : 2 ≠ 0)] at h
    omega
  have hUcard : Nat.card (hermitianUnipotentCoord J) = q ^ 3 :=
    (Nat.card_congr (unitaryCoverRootEquiv J hJ).toEquiv).trans
      (unitaryCoverRoot_nativeStructure J q hcard hfixed hJ).1
  have hkerCard : Nat.card (unitaryCoverFirstCoord J).ker = q := by
    rw [← unitaryCoverCoord_commutator_eq_ker J q hcard hfixed hJ]
    let e := unitaryCoverRootEquiv J hJ
    have hmap : (commutator (hermitianUnipotentCoord J)).map (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) =
        commutator (unitaryCoverRoot J hJ) := by
      change (⁅(⊤ : Subgroup (hermitianUnipotentCoord J)), ⊤⁆ :
      Subgroup (hermitianUnipotentCoord J)).map (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) = _
      rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) e.surjective]
      rfl
    exact (Nat.card_congr (e.subgroupMap _).toEquiv).trans
      (by rw [hmap]; exact (unitaryCoverRoot_nativeStructure J q hcard hfixed hJ).2.2)
  have hrangeCard : Nat.card (unitaryCoverFirstCoord J).range = q ^ 2 := by
    have h := Subgroup.card_ker_mul_card_range (unitaryCoverFirstCoord J)
    rw [hkerCard, hUcard, show q ^ 3 = q * q ^ 2 by ring] at h
    exact Nat.eq_of_mul_eq_mul_left hqpos h
  exact MonoidHom.range_eq_top.mp ((unitaryCoverFirstCoord J).range.eq_top_of_card_eq (by
    exact hrangeCard.trans (hcard.symm.trans
      (Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)).symm)))

@[expose] def unitaryCoverRootFirstCoord (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    unitaryCoverRoot J hJ →* Multiplicative K :=
  (unitaryCoverFirstCoord J).comp (unitaryCoverRootEquiv J hJ).symm.toMonoidHom

@[simp]
theorem unitaryCoverRootFirstCoord_apply (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) :
    unitaryCoverRootFirstCoord J hJ (unitaryCoverRootEquiv J hJ z) =
      Multiplicative.ofAdd z.1.1 := by
  simp only [unitaryCoverRootFirstCoord, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

theorem unitaryCoverRootFirstCoord_ker [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (unitaryCoverRootFirstCoord J hJ).ker = commutator (unitaryCoverRoot J hJ) := by
  let e := unitaryCoverRootEquiv J hJ
  change ((unitaryCoverFirstCoord J).comp
    (e.symm : unitaryCoverRoot J hJ →* hermitianUnipotentCoord J)).ker = _
  rw [MonoidHom.ker_comp_mulEquiv,
    ← unitaryCoverCoord_commutator_eq_ker J q hcard hfixed hJ]
  change (commutator (hermitianUnipotentCoord J)).map
    (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) = _
  change (⁅(⊤ : Subgroup (hermitianUnipotentCoord J)), ⊤⁆ :
    Subgroup (hermitianUnipotentCoord J)).map
      (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) = _
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective
      (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) e.surjective]
  rfl

theorem unitaryCoverRootFirstCoord_surjective [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Surjective (unitaryCoverRootFirstCoord J hJ) :=
  (unitaryCoverFirstCoord_surjective J q hcard hfixed hJ).comp
    (unitaryCoverRootEquiv J hJ).symm.surjective

@[expose] def unitaryCoverDerivedEquiv [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    commutator (unitaryCoverRoot J hJ) ≃*
      Multiplicative (unitaryCoverFixedField J) := by
  let e := unitaryCoverRootEquiv J hJ
  have hmap : (commutator (hermitianUnipotentCoord J)).map
      (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) =
        commutator (unitaryCoverRoot J hJ) := by
    change (⁅(⊤ : Subgroup (hermitianUnipotentCoord J)), ⊤⁆ :
      Subgroup (hermitianUnipotentCoord J)).map
        (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) = _
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective
        (e : hermitianUnipotentCoord J →* unitaryCoverRoot J hJ) e.surjective]
    rfl
  exact ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)).symm.trans
    ((MulEquiv.subgroupCongr (unitaryCoverCoord_commutator_eq_ker J q hcard hfixed hJ)).trans
      (unitaryCoverZeroFirstEquiv J))

theorem unitaryCoverDerivedEquiv_snd [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (w : commutator (unitaryCoverRoot J hJ)) :
    ((Multiplicative.toAdd (unitaryCoverDerivedEquiv J q hcard hfixed hJ w) :
      unitaryCoverFixedField J) : K) =
        ((unitaryCoverRootEquiv J hJ).symm w.val).1.2 := rfl

@[expose] def unitaryCoverQuotientEquiv [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    unitaryCoverRoot J hJ ⧸ commutator (unitaryCoverRoot J hJ) ≃* Multiplicative K :=
  (QuotientGroup.quotientMulEquivOfEq
    (unitaryCoverRootFirstCoord_ker J q hcard hfixed hJ).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (unitaryCoverRootFirstCoord J hJ)
        (unitaryCoverRootFirstCoord_surjective J q hcard hfixed hJ))

@[simp]
theorem unitaryCoverQuotientEquiv_mk [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (r : unitaryCoverRoot J hJ) :
    unitaryCoverQuotientEquiv J q hcard hfixed hJ
        (QuotientGroup.mk' (commutator (unitaryCoverRoot J hJ)) r) =
      unitaryCoverRootFirstCoord J hJ r := by
  simp only [unitaryCoverQuotientEquiv, MulEquiv.trans_apply,
    QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem unitaryCoverRoot_layers_elementary [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    IsElementaryAbelian 2 (commutator (unitaryCoverRoot J hJ)) ∧
      IsElementaryAbelian 2 (unitaryCoverRoot J hJ ⧸ commutator (unitaryCoverRoot J hJ)) := by
  have elementary {A : Type u} [AddCommGroup A] (hA : ∀ a : A, a + a = 0)
      {B : Type u} [Group B] (e : B ≃* Multiplicative A) : IsElementaryAbelian 2 B := by
    refine
      { toIsMulCommutative := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    apply e.injective
    rw [map_pow, map_one, pow_two]
    exact congrArg Multiplicative.ofAdd (hA (Multiplicative.toAdd (e x)))
  exact ⟨elementary (fun _ => CharTwo.add_self_eq_zero _) (unitaryCoverDerivedEquiv J q hcard hfixed hJ),
    elementary (fun _ => CharTwo.add_self_eq_zero _) (unitaryCoverQuotientEquiv J q hcard hfixed hJ)⟩

theorem unitaryCover_native_card [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  rcases huppert_II_10_12 J q hcard hfixed hJ with
    ⟨_, _, _, _, _, _, _, _, hGcard, _⟩
  exact hGcard

theorem unitaryCoverRoot_index_odd [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Odd (unitaryCoverRoot J hJ).index := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective Subtype.val Subtype.coe_injective
  let q := 2 ^ f
  have hqpos : 0 < q := by positivity
  have hqeven : Even q := (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
  have hdiv : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
  have hGcard := unitaryCover_native_card J q hcard hfixed hJ
  rw [Nat.mul_div_assoc _ hdiv] at hGcard
  have hindex : (unitaryCoverRoot J hJ).index =
      (q ^ 3 + 1) * ((q ^ 2 - 1) / Nat.gcd 3 (q + 1)) := by
    have h := (unitaryCoverRoot J hJ).card_mul_index
    rw [(unitaryCoverRoot_nativeStructure J q hcard hfixed hJ).1, hGcard] at h
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hqpos 3)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  rw [hindex]
  have hoddN : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd (pow_pos hqpos 2) (hqeven.pow_of_ne_zero (by decide)) odd_one
  exact ((hqeven.pow_of_ne_zero (by decide)).add_odd odd_one).mul
    (hoddN.of_dvd_nat (Nat.div_dvd_of_dvd hdiv))

@[expose] def unitaryCoverSylow [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (IsPGroup.of_card (n := f * 3) (by
    simpa only [← pow_mul] using (unitaryCoverRoot_nativeStructure J (2 ^ f) hcard hfixed hJ).1)).toSylow
      (unitaryCoverRoot_index_odd J f hf hcard hfixed hJ).not_two_dvd_nat

@[simp]
theorem unitaryCoverSylow_coe [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (unitaryCoverSylow J f hf hcard hfixed hJ :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ := rfl

end CFSG.ShultStronglyClosedTI
