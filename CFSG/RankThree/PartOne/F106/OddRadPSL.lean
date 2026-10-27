module

public import CFSG.RankThree.PartOne.F106.OddRadAt
public import CFSG.RankThree.PartOne.F106.OddRadAbs
public import CFSG.RankThree.PartOne.F106.OddRadGL
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.RankThree.PartOne.FOC
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  renaming conjAut → linConjAut, proj → linProj
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open scoped commutatorElement
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne (linearSubfieldInclusion linearSubfieldInclusion_injective
  mem_range_linearSubfieldInclusion fieldAut_linearSubfieldInclusion)

open scoped _root_.Classical in
theorem odd_card_rad_perfectResidual_commutantUnits {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x)) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(blockTheta hx).range))) := by
  let e : PiGL (Efac x) (mult x) ≃* ↥(blockTheta hx).range :=
    MonoidHom.ofInjective (blockTheta_injective hx)
  have : ∀ b : primaryFactors x, CharP (Efac x b) 2 := fun b =>
    charP_of_injective_algebraMap (algebraMap K (Efac x b)).injective 2
  rw [← card_solvableRadical_perfectResidual_eq e]
  exact odd_card_rad_perfectResidual_pi
    (fun b => odd_card_rad_perfectResidual_gl (E := Efac x b) (mult x b))


section Inner

variable {n : ℕ} {K : Type} [Field K]

noncomputable def Ct (A : GL (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (((linConjAut n K A : MulAut (projectiveSL n K)) :
    projectiveSL n K →* projectiveSL n K).eqLocus (MonoidHom.id _)).comap (linProj n K)

def Ut (A : GL (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (Subgroup.centralizer ({A} : Set (GL (Fin n) K))).comap SpecialLinearGroup.toGL

theorem mem_Ct {A : GL (Fin n) K} {s : SpecialLinearGroup (Fin n) K} :
    s ∈ Ct A ↔ linProj n K (slConjugation n K A s) = linProj n K s := by
  show linConjAut n K A (linProj n K s) = linProj n K s ↔ _
  rw [conjAut_proj]

theorem mem_Ut {A : GL (Fin n) K} {s : SpecialLinearGroup (Fin n) K} :
    s ∈ Ut A ↔ slConjugation n K A s = s := by
  show SpecialLinearGroup.toGL s ∈ Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply SpecialLinearGroup.toGL_injective
    rw [toGL_slConjugation, ← h]; group
  · intro h
    have := congrArg SpecialLinearGroup.toGL h
    rw [toGL_slConjugation] at this
    calc SpecialLinearGroup.toGL s * A = A * SpecialLinearGroup.toGL s * A⁻¹ * A := by
          rw [this]
      _ = A * SpecialLinearGroup.toGL s := by group

theorem Ut_le_Ct (A : GL (Fin n) K) : Ut A ≤ Ct A := fun s hs => by
  rw [mem_Ct, mem_Ut.mp hs]

theorem commutator_Ct_le_Ut (A : GL (Fin n) K) : ⁅Ct A, Ct A⁆ ≤ Ut A := by
  rw [Subgroup.commutator_le]
  intro s hs t ht
  rw [mem_Ut]
  have key : ∀ s ∈ Ct A, ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K),
      slConjugation n K A s = s * z := by
    intro s hs
    have h1 := proj_eq_proj_iff.mp (mem_Ct.mp hs).symm
    exact ⟨_, scalars_le_center n K h1, by group⟩
  obtain ⟨z, hz, hzs⟩ := key s hs
  obtain ⟨w, hw, hwt⟩ := key t ht
  rw [map_commutatorElement, hzs, hwt, commutatorElement_mul_central_left _ _ _ hz,
    commutatorElement_mul_central_right _ _ _ hw]

open scoped _root_.Classical in
theorem oddRadConcl_conjAut {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (A : GL (Fin n) K) (hA : orderOf (linConjAut n K A) = 5) :
    OddRadConcl (projectiveSL n K) (linConjAut n K A) := by
  have h5 : linConjAut n K (A ^ 5) = 1 := by
    rw [map_pow, ← hA]; exact pow_orderOf_eq_one _
  obtain ⟨c, hc⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff hn (A ^ 5)).mp h5
  have hpK : ((5 : ℕ) : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 5).mp h
    omega
  have hx : Squarefree (minpoly K (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K))) := by
    have hMp : (A : Matrix (Fin n) (Fin n) K) ^ 5 =
        algebraMap K (Matrix (Fin n) (Fin n) K) c := by
      have h1 : ((A ^ 5 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) ^ 5 := Units.val_pow_eq_pow_val _ _
      rw [← h1, hc, GeneralLinearGroup.coe_scalar]
      rfl
    have haeval : Polynomial.aeval (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K))
        (Polynomial.X ^ 5 - Polynomial.C (c : K)) = 0 := by
      have hX : Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) =
          Matrix.toLinAlgEquiv' (A : Matrix (Fin n) (Fin n) K) :=
        (toLinAlgEquiv'_eq_toLin' _).symm
      rw [hX]
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]
    exact squarefree_minpoly_of_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree haeval
  set T := projectiveSL n K with hT
  set C : Subgroup T := ((linConjAut n K A : MulAut T) : T →* T).eqLocus (MonoidHom.id T)
    with hC
  let f : ↥(Ct A) →* ↥C := ((linProj n K).comp (Ct A).subtype).codRestrict C (fun s => s.2)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨s, hs⟩ := proj_surjective n K (y : T)
    exact ⟨⟨s, by show linProj n K s ∈ C; rw [hs]; exact y.2⟩, Subtype.ext hs⟩
  have hker : Group.IsSolvable ↥f.ker := by
    refine Group.isSolvable_of_comm ?_
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    apply Subtype.ext
    have ha1 : linProj n K ((a : ↥(Ct A)) : SpecialLinearGroup (Fin n) K) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    have hcen := scalars_le_center n K (proj_eq_one_iff.mp ha1)
    exact (Subgroup.mem_center_iff.mp hcen _).symm
  have h1 := card_rad_perfectResidual_dvd_of_surjective f hf hker
  have h2 := card_rad_perfectResidual_eq_of_commutator_le (Ut_le_Ct A) (commutator_Ct_le_Ut A)
  set U : Subgroup (GL (Fin n) K) := Subgroup.centralizer ({A} : Set (GL (Fin n) K)) with hU
  set V : Subgroup (GL (Fin n) K) :=
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range ⊓ U
    with hV
  have hmapUt : (Ut A).map SpecialLinearGroup.toGL = V := by
    unfold Ut
    exact Subgroup.map_comap_eq _ _
  let e3 : ↥(Ut A) ≃* ↥V :=
    ((Ut A).equivMapOfInjective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr hmapUt)
  have h3 := card_solvableRadical_perfectResidual_eq e3
  have hVU : V ≤ U := inf_le_right
  have hUV : ⁅U, U⁆ ≤ V := by
    refine le_inf ?_ (CFSG.RankThree.PartOne.KCUnitary.commutator_self_le U)
    rw [Subgroup.commutator_le]
    intro u _ v _
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  have h4 := card_rad_perfectResidual_eq_of_commutator_le hVU hUV
  have hrange : (blockTheta hx).range = U := by
    rw [range_blockTheta, range_commutantUnitsToGL_eq_centralizer A rfl]
  have h5 := odd_card_rad_perfectResidual_commutantUnits hx
  have h6 : Nat.card ↥(solvableRadical ↥(perfectResidual ↥(blockTheta hx).range)) =
      Nat.card ↥(solvableRadical ↥(perfectResidual ↥U)) :=
    card_solvableRadical_perfectResidual_eq (MulEquiv.subgroupCongr hrange)
  have hodd : Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Ct A)))) := by
    rw [h2, h3, ← h4, ← h6]
    exact h5
  exact Odd.of_dvd_nat hodd h1

end Inner

section Field

theorem commutator_fixed_fieldAut_le {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K) :
    ⁅((fieldAut n K σ : MulAut (projectiveSL n K)) :
        projectiveSL n K →* projectiveSL n K).eqLocus (MonoidHom.id _),
      ((fieldAut n K σ : MulAut (projectiveSL n K)) :
        projectiveSL n K →* projectiveSL n K).eqLocus (MonoidHom.id _)⁆ ≤
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  obtain ⟨h, rfl⟩ := proj_surjective n K y
  have key : ∀ g : SpecialLinearGroup (Fin n) K,
      fieldAut n K σ (linProj n K g) = linProj n K g →
      ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K),
        SpecialLinearGroup.map σ.toRingHom g = g * z := by
    intro g hg
    obtain ⟨c, hc, hent⟩ :=
      CFSG.RankThree.PartOne.KCLinearSubfield.exists_scalar_of_fieldAut_proj_eq hg
    refine ⟨scalarElement c hc, scalars_le_center n K (scalarElement_mem_scalars c hc), ?_⟩
    apply Subtype.ext
    ext a b
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, scalar_apply, Matrix.mul_diagonal]
    exact hent a b
  obtain ⟨z, hz, hzg⟩ := key g hx
  obtain ⟨w, hw, hwh⟩ := key h hy
  have hfix : SpecialLinearGroup.map σ.toRingHom ⁅g, h⁆ = ⁅g, h⁆ := by
    rw [map_commutatorElement, hzg, hwh, commutatorElement_mul_central_left _ _ _ hz,
      commutatorElement_mul_central_right _ _ _ hw]
  refine mem_range_linearSubfieldInclusion.mpr ⟨⁅g, h⁆, fun i j => ?_, ?_⟩
  · have h1 := congrArg
      (fun m : SpecialLinearGroup (Fin n) K => (m : Matrix (Fin n) (Fin n) K) i j) hfix
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    exact RingHom.mem_eqLocusField.mpr h1
  · rw [map_commutatorElement]

theorem oddRadConcl_fieldAut {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    (σ : K ≃+* K) : OddRadConcl (projectiveSL n K) (fieldAut n K σ) := by
  set k := semilinearFixedSubfield σ with hk
  set C : Subgroup (projectiveSL n K) :=
    ((fieldAut n K σ : MulAut (projectiveSL n K)) :
      projectiveSL n K →* projectiveSL n K).eqLocus (MonoidHom.id _) with hC
  have hNC : (linearSubfieldInclusion n k).range ≤ C := by
    rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => RingHom.mem_eqLocusField.mp hc) y
  have h1 := card_rad_perfectResidual_eq_of_commutator_le hNC (commutator_fixed_fieldAut_le σ)
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  have : Finite ↥k := inferInstance
  have hs : IsSimpleGroup (projectiveSL n ↥k) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL hn
  have hnab : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have := CFSG.RankThree.PartOne.KCLinearSubfield.not_commutative_projectiveSL
      (n := n) (K := ↥k) hn
    push Not at this
    exact this
  have h2 := card_solvableRadical_perfectResidual_eq (MonoidHom.ofInjective hinj).symm
  show Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥C)))
  rw [h1, h2, radical_perfectResidual_eq_bot_of_isSimpleGroup
    (isPerfect_of_isSimpleGroup_nonabelian hnab), Subgroup.card_bot]
  exact odd_one

end Field

section Assembly

theorem charP_two_of_natCard_eq_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])

open scoped _root_.Classical in
theorem oddRadConcl_projectiveSL {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) (β : MulAut (projectiveSL n K)) (hβ : orderOf β = 5) :
    OddRadConcl (projectiveSL n K) β := by
  by_cases hD : β ∈ linearAutGroup n K
  · obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hD
    exact oddRadConcl_conjAut hn A hβ
  · have hE : β ∈ semilinearAutGroup n K :=
      CFSG.RankThree.PartOne.KCLinCommOdd.mem_semilinearAutGroup_of_pow_eq_one hn
        (by norm_num : (5 : ℕ) ≠ 2) (by norm_num : Nat.Prime 5) (j := 1)
        (by rw [pow_one, ← hβ]; exact pow_orderOf_eq_one β)
    have := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
    obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
      CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two
        f.pos hn hK
    obtain ⟨-, σ, -, ⟨h, -, hβh⟩, -⟩ := hdesc 5 (by norm_num) (by norm_num) β hE hD hβ
    have h1 := oddRadConcl_fieldAut hn σ
    rw [← oddRadConcl_congr (h⁻¹ : projectiveSL n K ≃* projectiveSL n K) β]
    have : MulAut.congr (h⁻¹ : projectiveSL n K ≃* projectiveSL n K) β = fieldAut n K σ := by
      rw [hβh]
      refine MulEquiv.ext fun x => ?_
      simp [MulAut.congr_apply]
    rw [this]
    exact h1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.N143 in
@[expose] def PslGeThree (X : Type) [Group X] : Prop :=
  ∃ n f : ℕ, 3 ≤ n ∧ StatedLieAdmissible .PSL n 2 f ∧ LieModel X .PSL n 2 f ∧
    SmallEvenParams .PSL n f

theorem oddRadAt_pslGeThree : OddRadAt PslGeThree := by
  intro T _ _ _ hP β hβ
  obtain ⟨n, f, hn3, -, hmodel, -⟩ := hP
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      hmodel
  have hchar : CharP K 2 := charP_two_of_natCard_eq_pow hK
  exact oddRadConcl_of_mulEquiv e (fun β' hβ' => oddRadConcl_projectiveSL hn3 β' hβ') β hβ

end Assembly

end CFSG.RankThree.PartOne.F106
