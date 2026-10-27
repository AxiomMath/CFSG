module

public import CFSG.RankThree.PartOne.F106.OddRadAt
public import CFSG.RankThree.PartOne.F106.OddRadUnitaryBlock
public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveFieldActor
import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
import CFSG.RankThree.GroupTheory.SteinbergCDCentralQuotientFixed
import CFSG.RankThree.PartOne.F106.OddRadAbs
import CFSG.RankThree.PartOne.F106.OddRadTools
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.RankThree.PartOne.F106.OddRadGen

public section

namespace CFSG.RankThree.PartOne.F106.OddRadUnitary

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial Polynomial
open scoped commutatorElement

section Transport

theorem odd_card_radical_residual_of_hom {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (φ : G →* Q) (hcomm : commutator Q ≤ φ.range) (hker : Group.IsSolvable φ.ker)
    (h : Odd (Nat.card ↥(solvableRadical ↥(perfectResidual G)))) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual Q))) := by
  have h1 := card_rad_perfectResidual_dvd_of_surjective φ.rangeRestrict
    φ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
  have h2 := card_rad_perfectResidual_eq_of_commutator_le (C := (⊤ : Subgroup Q)) (N := φ.range)
    le_top (by rwa [← commutator_def])
  have h3 := card_solvableRadical_perfectResidual_eq
    (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  rw [← h3, h2]
  exact Odd.of_dvd_nat h h1

end Transport

section Central

theorem oddRadConcl_of_central_quotient {X : Type} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (hZ : Z ≤ Subgroup.center X) (α : MulAut X) (hαZ : Z.map (α : X →* X) = Z)
    (hC : Odd (Nat.card ↥(solvableRadical
      ↥(perfectResidual ↥((α : X →* X).eqLocus (MonoidHom.id X)))))) :
    OddRadConcl (X ⧸ Z) (QuotientGroup.congr Z Z α hαZ) := by
  obtain ⟨_, δ, -, -, -, -, -, -, hcenter, hCQ, hMn, ε, -, hεker, -, -, hab, -⟩ :=
    CFSG.RankThree.GroupTheory.central_quotient_fixed_group_exact_sequence Z hZ α hαZ
  set C := (α : X →* X).eqLocus (MonoidHom.id X) with hCdef
  set Q := (QuotientGroup.congr Z Z α hαZ : X ⧸ Z →* X ⧸ Z).eqLocus (MonoidHom.id _) with hQdef
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  let φ : ↥C →* ↥Q := (π.comp C.subtype).codRestrict Q fun c => hCQ ⟨c, c.2, rfl⟩
  have hcomm : commutator ↥Q ≤ φ.range := by
    have h1 : commutator ↥Q ≤ (C.map π).subgroupOf Q := by
      rw [← hεker, commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hab (ε x) (ε y),
        mul_inv_cancel_right, mul_inv_cancel]
    refine h1.trans ?_
    intro q hq
    obtain ⟨c, hc, hcq⟩ := Subgroup.mem_subgroupOf.mp hq
    exact ⟨⟨c, hc⟩, Subtype.ext hcq⟩
  have hker : Group.IsSolvable ↥φ.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have ha : (a : ↥C) ∈ Subgroup.center ↥C := by
      apply hcenter
      have := a.2
      rw [MonoidHom.mem_ker] at this
      have h2 : π (a : ↥C) = 1 := congrArg Subtype.val this
      exact Subgroup.mem_subgroupOf.mpr ((QuotientGroup.eq_one_iff _).mp h2)
    exact Subtype.ext (Subgroup.mem_center_iff.mp ha b.1).symm
  have := Finite.of_injective _ (Subtype.val_injective (p := (· ∈ C)))
  exact odd_card_radical_residual_of_hom φ hcomm hker hC

end Central

section S1

open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

abbrev Fx {T : Type*} [Group T] (β : MulAut T) : Subgroup T :=
  (β : T →* T).eqLocus (MonoidHom.id T)

noncomputable abbrev Cfix (u : primeFormUnitary h (idGram K n)) :
    Subgroup (gramSU h (idGram K n)) :=
  Fx (primeFormConjSU h (idGram K n) u)

theorem gramSU_le_primeFormUnitary : gramSU h (idGram K n) ≤ primeFormUnitary h (idGram K n) :=
  fun _ hg => hg.1

@[expose] noncomputable def gramToLin :
    ↥(gramSU h (idGram K n)) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (toLinU h n).comp (Subgroup.inclusion (gramSU_le_primeFormUnitary h))

theorem gramToLin_injective : Function.Injective (gramToLin h (n := n)) := fun _ _ e =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective e)

theorem gramToLin_mem_unitary (g : ↥(gramSU h (idGram K n))) :
    gramToLin h g ∈ sesqUnitaryGroup (idForm h n) :=
  toLinU_mem ⟨(g : GL (Fin n) K), g.2.1⟩

theorem gramToLin_mem_special (g : ↥(gramSU h (idGram K n))) :
    gramToLin h g ∈ sesqSpecialUnitaryGroup (idForm h n) :=
  (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (g : GL (Fin n) K)).mpr g.2

theorem commute_gramToLin {u : primeFormUnitary h (idGram K n)} {g : ↥(gramSU h (idGram K n))}
    (hcomm : (u : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * u) :
    Commute
      ((gramToLin h g : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
      ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) := by
  have := congrArg (fun y : GL (Fin n) K =>
    ((Matrix.GeneralLinearGroup.toLin y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) hcomm
  simp only [map_mul, Units.val_mul] at this
  exact this.symm

theorem mem_MS {B : (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K}
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    {g : LinearMap.GeneralLinearGroup K (Fin n → K)} :
    g ∈ MS B x ↔ g ∈ unitaryCentralizer B x ∧ g ∈ sesqSpecialUnitaryGroup B :=
  Subgroup.mem_inf

theorem map_gramToLin_Cfix (u : primeFormUnitary h (idGram K n)) :
    (Cfix h u).map (gramToLin h) = MS (idForm h n) (toLinU h n u) := by
  ext m
  rw [mem_MS h]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (u : GL (Fin n) K) * (g : GL (Fin n) K) * (u : GL (Fin n) K)⁻¹ = g :=
      congrArg Subtype.val hg
    have hcomm : (u : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * u := by
      have := congrArg (· * (u : GL (Fin n) K)) hg'
      simp only [inv_mul_cancel_right] at this
      exact this
    exact ⟨mem_unitaryCentralizer.mpr ⟨gramToLin_mem_unitary h g, commute_gramToLin h hcomm⟩,
      gramToLin_mem_special h g⟩
  · rintro ⟨hm1, hm2⟩
    obtain ⟨hmU, hmC⟩ := mem_unitaryCentralizer.mp hm1
    set g : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm m with hgdef
    have hgm : Matrix.GeneralLinearGroup.toLin g = m := MulEquiv.apply_symm_apply _ _
    have hgS : g ∈ gramSU h (idGram K n) :=
      (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) g).mp (hgm ▸ hm2)
    refine ⟨⟨g, hgS⟩, ?_, ?_⟩
    · have hcomm : (u : GL (Fin n) K) * g = g * u := by
        apply Matrix.GeneralLinearGroup.toLin.injective
        apply Units.ext
        rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hgm]
        exact hmC.eq.symm
      show primeFormConjSU h (idGram K n) u ⟨g, hgS⟩ = ⟨g, hgS⟩
      apply Subtype.ext
      change (u : GL (Fin n) K) * g * (u : GL (Fin n) K)⁻¹ = g
      rw [hcomm, mul_inv_cancel_right]
    · exact hgm

theorem pow_toLinU_eq_smul {u : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hc : ((u ^ 5 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c) :
    ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) ^ 5 =
      (c : K) • (1 : Module.End K (Fin n → K)) := by
  have h2 : ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) ^ 5 = ((toLinU h n (u ^ 5) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) := by
    rw [map_pow, Units.val_pow_eq_pow_val]
  rw [h2]
  change Matrix.toLin' (((u ^ 5 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) = _
  rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext v i
  simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem squarefree_minpoly_of_pow_scalar {u : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hc : ((u ^ 5 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) := by
  have := h.finite
  have hK2 : CharP K 2 := h.charP
  have hp0 : ((5 : ℕ) : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K 2 5).mp h0
    omega
  have hsep : (X ^ 5 - C (c : K)).Separable :=
    Polynomial.separable_X_pow_sub_C (c : K) hp0 c.ne_zero
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ 5 - C (c : K)) hsep.squarefree ?_
  simp [pow_toLinU_eq_smul h hc, Algebra.algebraMap_eq_smul_one]

theorem unitaryPrimaryData_of_pow_scalar {u : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hc : ((u ^ 5 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c) :
    UnitaryPrimaryData h.bar (idForm h n) (toLinU h n u) :=
  ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, toLinU_mem _,
    squarefree_minpoly_of_pow_scalar h hc⟩

theorem odd_card_radical_Cfix {u : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hc : ((u ^ 5 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Cfix h u)))) := by
  have e : ↥(Cfix h u) ≃* ↥(MS (idForm h n) (toLinU h n u)) :=
    ((Cfix h u).equivMapOfInjective (gramToLin h) (gramToLin_injective h)).trans
      (MulEquiv.subgroupCongr (map_gramToLin_Cfix h u))
  rw [card_solvableRadical_perfectResidual_eq e]
  exact odd_card_radical_perfectResidual_MS (unitaryPrimaryData_of_pow_scalar h hc)

theorem primeFormConjHom_eq_congr (u : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) u =
      QuotientGroup.congr (normOneScalars h (gramSU h (idGram K n)) n)
        (normOneScalars h (gramSU h (idGram K n)) n) (primeFormConjSU h (idGram K n) u)
        (map_normOneScalars_conj h _ u) := rfl

theorem oddRadConcl_conj {u : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hc : ((u ^ 5 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c) :
    OddRadConcl (primeFormP h (idGram K n)) (primeFormConjHom h (idGram K n) u) := by
  have := h.finite
  have hfinX : Finite ↥(gramSU h (idGram K n)) := inferInstance
  rw [primeFormConjHom_eq_congr]
  exact oddRadConcl_of_central_quotient (normOneScalars h (gramSU h (idGram K n)) n)
    (normOneScalars_le_center h _ n) (primeFormConjSU h (idGram K n) u)
    (map_normOneScalars_conj h _ u) (odd_card_radical_Cfix h hc)

end S1

section Field

open Matrix CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCEvenUnitaryFive
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Chevalley

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem oddRadConcl_fieldHom {σ : K ≃+* K} (hσ : orderOf σ = 5) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    OddRadConcl (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  have := h.finite
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  by_cases hq₀ : n = 3 ∧ 2 ^ (f / 5) = 2
  · obtain ⟨rfl, hq2⟩ := hq₀
    have hZ : ¬ 5 ∣ Nat.card (normOneScalars h
        (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3) := by
      rw [card_normOneScalars_one h (by norm_num)]
      intro hd
      have : 5 ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
      omega
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h72⟩ :=
      prime_subfield_fixed_group_package h hp hp2 hσ 3 hn hq hZ
    obtain ⟨hcard, -⟩ := h72 ⟨rfl, hq2⟩ (by norm_num)
    have hfinQ : Finite ↥(fieldFixedPSU h 3 σ) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hsolv : Group.IsSolvable ↥(fieldFixedPSU h 3 σ) := by
      apply isSolvable_of_card_primeFactors_le_two
      rw [hcard, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide
    have hbot := radical_perfectResidual_eq_bot_of_isSolvable hsolv
    show Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(fieldFixedPSU h 3 σ))))
    rw [hbot, Subgroup.card_bot]
    exact odd_one
  · have hDR := commutator_fieldFixedPSU_eq_range h hbar n hn hq₀
    have hjinj := subfieldPSU_injective h h₀ hbar n (by omega)
    have hsimple := isSimpleGroup_primeFormP_one h₀ hn hq₀
    let eJ := MonoidHom.ofInjective hjinj
    have hsJ : IsSimpleGroup ↥(subfieldPSU h h₀ hbar n).range := eJ.symm.isSimpleGroup
    have : Group.IsPerfect (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) := isPerfect_gramSU_one h₀ hn hq₀
    have hperf0 : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hpJ : Group.IsPerfect ↥(subfieldPSU h h₀ hbar n).range :=
      Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
    have hc := card_radical_residual_of_commutator_eq (fieldFixedPSU h n σ) _ hDR hsJ hpJ
    show Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(fieldFixedPSU h n σ))))
    rw [hc]
    exact odd_one

end Field

section Main

open Matrix CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCEvenUnitaryFive
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KCUnitaryModel

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem oddRadConcl_of_mem_D (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {β : MulAut (primeFormP h (idGram K n))} (hβ : orderOf β = 5)
    (hD : β ∈ primeFormD h (idGram K n)) : OddRadConcl (primeFormP h (idGram K n)) β := by
  obtain ⟨u, rfl⟩ := hD
  have h5 : primeFormConjHom h (idGram K n) (u ^ 5) = 1 := by
    rw [map_pow]
    have := pow_orderOf_eq_one (primeFormConjHom h (idGram K n) u)
    rwa [hβ] at this
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq (u ^ 5)).mp h5
  exact oddRadConcl_conj h hc

theorem oddRadConcl_of_order_five (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {β : MulAut (primeFormP h (idGram K n))} (hβ : orderOf β = 5) :
    OddRadConcl (primeFormP h (idGram K n)) β := by
  have := h.finite
  by_cases hD : β ∈ primeFormD h (idGram K n)
  · exact oddRadConcl_of_mem_D h hn hq hβ hD
  · set σ := primeFormFieldFactor h isPrimeFormGram_one hn hq β with hσdef
    have hσ1 : σ ≠ 1 := fun h1 => hD (by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn hq]
      exact h1)
    have hβ5 : β ^ 5 = 1 := by
      have := pow_orderOf_eq_one β
      rwa [hβ] at this
    have hσ5 : σ ^ 5 = 1 := by rw [hσdef, ← map_pow, hβ5, map_one]
    have hσord : orderOf σ = 5 := by
      have hd : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ5
      rcases (Nat.dvd_prime Nat.prime_five).mp hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hσ1
      · exact h1
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq
        Nat.prime_five (by norm_num) (by norm_num) β hβ σ rfl hσord
    have hF := oddRadConcl_fieldHom h hσord hn hq
    have hcongr : MulAut.congr (primeFormConjHom h (idGram K n) M)⁻¹ β =
        primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ := by
      rw [← hM]
      ext x
      simp [MulAut.congr_apply]
    exact (oddRadConcl_congr (primeFormConjHom h (idGram K n) M)⁻¹ β).mp (hcongr ▸ hF)

end Main

end CFSG.RankThree.PartOne.F106.OddRadUnitary

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.N143
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag
  Matrix

theorem oddRadAt_psu_all : OddRadAt (fun X _ =>
    ∃ n f : ℕ, StatedLieAdmissible .PSU n 2 f ∧ LieModel X .PSU n 2 f) := by
  intro T _ _ hs ⟨n, f, hadm, hmodel⟩ β hβ
  have hC : StatedClassicalModel T .PSU n 2 f :=
    (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp hmodel
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have hU : UnitaryFieldData 2 f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  have e' : T ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact oddRadConcl_of_mulEquiv e'
    (fun β' hβ' => OddRadUnitary.oddRadConcl_of_order_five hU hn3 hq hβ') β hβ

theorem oddRadAt_smallModel_psu : OddRadAt (SmallModel .PSU) :=
  OddRadAt.mono (fun _ _ ⟨n, f, hadm, hm, _⟩ => ⟨n, f, hadm, hm⟩) oddRadAt_psu_all

end CFSG.RankThree.PartOne.F106
