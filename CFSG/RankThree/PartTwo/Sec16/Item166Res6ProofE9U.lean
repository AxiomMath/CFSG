module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9L
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofNT
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Foundations
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Res6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def diagGL : Kˣ × Kˣ →* GL (Fin 3) K :=
  (Matrix.SpecialLinearGroup.toGL).comp diagSL

theorem coe_diagGL (u : Kˣ × Kˣ) :
    ((diagGL u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal (diagVec u) := rfl

theorem diagGL_injective : Function.Injective (diagGL (K := K)) :=
  Matrix.SpecialLinearGroup.toGL_injective.comp diagSL_injective

@[expose] noncomputable def permGL : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL permSL

theorem coe_permGL : ((permGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem diagGL_mem_unitarySU (h : UnitaryFieldData p f K) {u : Kˣ × Kˣ}
    (h1 : h.norm (u.1 : K) = 1) (h2 : h.norm (u.2 : K) = 1) : diagGL u ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨det_diagVec u, ?_⟩
  rw [coe_diagGL, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  have h3 : h.norm ((((u.1 * u.2)⁻¹ : Kˣ)) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_mul, norm_inv_eq, norm_mul_eq, h1, h2, mul_one,
      inv_one]
  funext i
  fin_cases i
  · simpa [diagVec, UnitaryFieldData.norm, mul_comm] using h1
  · simpa [diagVec, UnitaryFieldData.norm, mul_comm] using h2
  · simpa [diagVec, UnitaryFieldData.norm, mul_comm] using h3

theorem permGL_mem_unitarySU (h : UnitaryFieldData p f K) : permGL ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨permSL.2, ?_⟩
  rw [coe_permGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem permGL_conj_diagGL (u : Kˣ × Kˣ) :
    permGL * diagGL u * permGL⁻¹ = diagGL ((u.1 * u.2)⁻¹, u.1) := by
  change Matrix.SpecialLinearGroup.toGL permSL * Matrix.SpecialLinearGroup.toGL (diagSL u) *
    (Matrix.SpecialLinearGroup.toGL permSL)⁻¹ =
      Matrix.SpecialLinearGroup.toGL (diagSL ((u.1 * u.2)⁻¹, u.1))
  rw [← map_inv, ← map_mul, ← map_mul, permSL_conj_diagSL]

theorem permGL_not_mem_range : (permGL : GL (Fin 3) K) ∉ (diagGL (K := K)).range := by
  rintro ⟨u, hu⟩
  exact permSL_not_mem_range ⟨u, Matrix.SpecialLinearGroup.toGL_injective hu⟩

theorem permGL_pow_three : (permGL : GL (Fin 3) K) ^ 3 = 1 := by
  change (Matrix.SpecialLinearGroup.toGL permSL) ^ 3 = 1
  rw [← map_pow, permSL_pow_three, map_one]

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def diagSU (P : Subgroup Kˣ) : Subgroup ↥(unitarySU p f K 3) :=
  ((P.prod P).map diagGL).subgroupOf (unitarySU p f K 3)

theorem map_diagGL_le (P : Subgroup Kˣ) (hP : ∀ x ∈ P, h.norm (x : K) = 1) :
    (P.prod P).map diagGL ≤ unitarySU p f K 3 := by
  rintro _ ⟨u, hu, rfl⟩
  exact diagGL_mem_unitarySU h (hP _ hu.1) (hP _ hu.2)

theorem card_diagSU (P : Subgroup Kˣ) (hP : ∀ x ∈ P, h.norm (x : K) = 1) :
    Nat.card (diagSU (p := p) (f := f) P) = Nat.card P ^ 2 := by
  rw [diagSU, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (map_diagGL_le h P hP)).toEquiv,
    Subgroup.card_map_of_injective diagGL_injective,
    Nat.card_congr (Subgroup.prodEquiv P P).toEquiv, Nat.card_prod, sq]

@[expose] noncomputable def permSU : ↥(unitarySU p f K 3) := ⟨permGL, permGL_mem_unitarySU h⟩

theorem coe_mem_diagSU {P : Subgroup Kˣ} {g : ↥(unitarySU p f K 3)}
    (hg : g ∈ diagSU (p := p) (f := f) P) : ∃ u ∈ P.prod P, diagGL u = (g : GL (Fin 3) K) :=
  hg

variable [Finite K]

theorem permSU_mem_normalizer_diagSU (P : Subgroup Kˣ) :
    permSU h ∈ Subgroup.normalizer (diagSU (p := p) (f := f) P : Set ↥(unitarySU p f K 3)) := by
  refine mem_normalizer_of_conj_mem ?_
  intro g hg
  obtain ⟨u, hu, hug⟩ := coe_mem_diagSU hg
  change ((permSU h * g * (permSU h)⁻¹ : ↥(unitarySU p f K 3)) : GL (Fin 3) K) ∈
    (P.prod P).map diagGL
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hug]
  change permGL * diagGL u * permGL⁻¹ ∈ _
  rw [permGL_conj_diagGL]
  exact ⟨((u.1 * u.2)⁻¹, u.1), ⟨P.inv_mem (P.mul_mem hu.1 hu.2), hu.1⟩, rfl⟩

theorem diagSU_le_normalizer (P Q : Subgroup Kˣ) :
    diagSU (p := p) (f := f) P ≤
      Subgroup.normalizer (diagSU (p := p) (f := f) Q : Set ↥(unitarySU p f K 3)) := by
  intro x hx
  obtain ⟨u, -, hux⟩ := coe_mem_diagSU hx
  refine mem_normalizer_of_conj_mem ?_
  intro g hg
  obtain ⟨v, hv, hvg⟩ := coe_mem_diagSU hg
  change ((x * g * x⁻¹ : ↥(unitarySU p f K 3)) : GL (Fin 3) K) ∈ (Q.prod Q).map diagGL
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hux, ← hvg, ← map_mul,
    ← map_inv, ← map_mul, mul_comm u v, mul_inv_cancel_right]
  exact ⟨v, hv, rfl⟩

omit [Finite K] in
theorem norm_eq_one_of_mem_rootsOfUnity_two {x : Kˣ} (hx : x ∈ rootsOfUnity 2 K) :
    h.norm (x : K) = 1 := by
  have hxx : (x : K) * x = 1 := by
    rw [← Units.val_mul, ← sq, (mem_rootsOfUnity 2 x).mp hx, Units.val_one]
  rw [UnitaryFieldData.norm]
  rcases mul_self_eq_one_iff.mp hxx with h1 | h1 <;> rw [h1] <;> simp

@[expose] noncomputable def fourSU : Subgroup ↥(unitarySU p f K 3) :=
  diagSU (p := p) (f := f) (rootsOfUnity 2 K)

@[expose] noncomputable def fourPSU : Subgroup (unitaryPSU h 3) :=
  (fourSU (p := p) (f := f) (K := K)).map (unitaryProj h 3)

omit [Finite K] in
theorem mul_self_of_mem_fourSU {g : ↥(unitarySU p f K 3)}
    (hg : g ∈ fourSU (p := p) (f := f) (K := K)) :
    g * g = 1 := by
  obtain ⟨u, hu, hug⟩ := coe_mem_diagSU hg
  apply Subtype.ext
  rw [Subgroup.coe_mul, ← hug, ← map_mul, Subgroup.coe_one]
  have h1 : u.1 * u.1 = 1 := by rw [← sq]; exact (mem_rootsOfUnity 2 u.1).mp hu.1
  have h2 : u.2 * u.2 = 1 := by rw [← sq]; exact (mem_rootsOfUnity 2 u.2).mp hu.2
  rw [show u * u = 1 from Prod.ext h1 h2, map_one]

omit [Finite K] in
theorem isPGroup_fourSU : IsPGroup 2 (fourSU (p := p) (f := f) (K := K)) := by
  rintro ⟨g, hg⟩
  exact ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact mul_self_of_mem_fourSU hg)⟩

omit [Finite K] in
theorem isPGroup_fourPSU : IsPGroup 2 (fourPSU h) := isPGroup_fourSU.map _

omit [Finite K] in
theorem fourPSU_ne_bot (h2 : (2 : K) ≠ 0) : fourPSU h ≠ ⊥ := by
  intro hbot
  have hm : (-1 : Kˣ) ∈ rootsOfUnity 2 K := (mem_rootsOfUnity 2 _).mpr neg_one_sq
  have hmem : diagGL ((-1 : Kˣ), (-1 : Kˣ)) ∈ unitarySU p f K 3 :=
    diagGL_mem_unitarySU h (norm_eq_one_of_mem_rootsOfUnity_two h hm)
      (norm_eq_one_of_mem_rootsOfUnity_two h hm)
  have hV : unitaryProj h 3 ⟨_, hmem⟩ ∈ fourPSU h :=
    ⟨⟨_, hmem⟩, ⟨(-1, -1), ⟨hm, hm⟩, rfl⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_unitaryProj, mem_unitaryScalars] at hV
  obtain ⟨c, -, -, hc⟩ := hV
  have hc' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  simp only [coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar] at hc'
  have h0 := congrFun (congrFun hc' 0) 0
  have h22 := congrFun (congrFun hc' 2) 2
  simp [diagVec] at h0 h22
  apply h2
  rw [← h22] at h0
  linear_combination -h0

omit [Finite K] in
theorem map_conj_fourPSU {x : ↥(unitarySU p f K 3)}
    (hx : x ∈ Subgroup.normalizer
      (fourSU (p := p) (f := f) (K := K) : Set ↥(unitarySU p f K 3))) :
    (fourPSU h).map (MulAut.conj (unitaryProj h 3 x) : unitaryPSU h 3 →* unitaryPSU h 3) =
      fourPSU h := by
  have hcomp : (MulAut.conj (unitaryProj h 3 x) : unitaryPSU h 3 →* unitaryPSU h 3).comp
      (unitaryProj h 3) = (unitaryProj h 3).comp
        (MulAut.conj x : ↥(unitarySU p f K 3) →* ↥(unitarySU p f K 3)) := by
    ext g
    simp [MulAut.conj_apply]
  rw [fourPSU, Subgroup.map_map, hcomp, ← Subgroup.map_map, map_conj_eq_of_mem_normalizer hx]

@[expose] noncomputable def stabSU (P : Subgroup Kˣ) : Subgroup ↥(unitarySU p f K 3) :=
  Subgroup.normalizer (fourSU (p := p) (f := f) (K := K) : Set ↥(unitarySU p f K 3)) ⊓
    Subgroup.normalizer (diagSU (p := p) (f := f) P : Set ↥(unitarySU p f K 3))

theorem three_pow_dvd_card_stabSU (P : Subgroup Kˣ) (hP : ∀ x ∈ P, h.norm (x : K) = 1) {a : ℕ}
    (hPa : Nat.card P = 3 ^ a) :
    3 ^ (2 * a + 1) ∣ Nat.card (stabSU (p := p) (f := f) P) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := stabSU (p := p) (f := f) P with hHdef
  have hDH : diagSU (p := p) (f := f) P ≤ H :=
    le_inf (diagSU_le_normalizer P _) Subgroup.le_normalizer
  have hπH : permSU h ∈ H :=
    ⟨permSU_mem_normalizer_diagSU h _, permSU_mem_normalizer_diagSU h P⟩
  set D := (diagSU (p := p) (f := f) P).subgroupOf H with hD
  have hDn : D.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDH).mpr inf_le_right
  have hcardD : Nat.card D = 3 ^ (2 * a) := by
    rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, card_diagSU h P hP, hPa,
      ← pow_mul, mul_comm]
  set πb : H ⧸ D := QuotientGroup.mk ⟨permSU h, hπH⟩ with hπb
  have hπ3 : πb ^ 3 = 1 := by
    rw [hπb, ← QuotientGroup.mk_pow]
    have : (⟨permSU h, hπH⟩ : H) ^ 3 = 1 := Subtype.ext (Subtype.ext permGL_pow_three)
    rw [this, QuotientGroup.mk_one]
  have hπ1 : πb ≠ 1 := by
    rw [hπb, Ne, QuotientGroup.eq_one_iff, hD, Subgroup.mem_subgroupOf]
    intro hm
    obtain ⟨u, -, hu⟩ := coe_mem_diagSU hm
    exact permGL_not_mem_range ⟨u, hu⟩
  have hord : orderOf πb = 3 := orderOf_eq_prime hπ3 hπ1
  have h3 : 3 ∣ Nat.card (H ⧸ D) := by
    have h := orderOf_dvd_natCard πb
    rwa [hord] at h
  rw [D.card_eq_card_quotient_mul_card_subgroup, hcardD, pow_succ, mul_comm (3 ^ (2 * a)) 3]
  exact Nat.mul_dvd_mul h3 dvd_rfl

include h in
theorem not_three_dvd_index_stabSU (hq : p ^ f % 3 = 2)
    (hcard : Nat.card ↥(unitarySU p f K 3) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)))
    (P : Sylow 3 Kˣ) : ¬ 3 ∣ (stabSU (p := p) (f := f) (P : Subgroup Kˣ)).index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKu : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Nat.card_units, h.card, ← pow_mul, mul_comm]
  have hP : Nat.card (P : Subgroup Kˣ) = 3 ^ ((p ^ f) ^ 2 - 1).factorization 3 := by
    rw [Sylow.card_eq_multiplicity, hKu]
  have hnorm : ∀ x ∈ (P : Subgroup Kˣ), h.norm (x : K) = 1 := by
    intro x hx
    have hx3 : x ^ Nat.card (P : Subgroup Kˣ) = 1 := by
      have h1 := congrArg (fun y : ↥(P : Subgroup Kˣ) => (y : Kˣ))
        (pow_card_eq_one' (G := ↥(P : Subgroup Kˣ)) (x := ⟨x, hx⟩))
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      exact h1
    have hdvd : Nat.card (P : Subgroup Kˣ) ∣ p ^ f + 1 := by
      rw [hP, factorization_sq_sub_one_three hq]
      exact Nat.ordProj_dvd (p ^ f + 1) 3
    obtain ⟨k, hk⟩ := hdvd
    have hxq : x ^ (p ^ f + 1) = 1 := by rw [hk, pow_mul, hx3, one_pow]
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ', ← Units.val_pow_eq_pow_val,
      hxq, Units.val_one]
  obtain ⟨c, hc3, hcardc⟩ := exists_three_pow_mul_card_SU hq
  obtain ⟨k, hk⟩ := three_pow_dvd_card_stabSU h (P : Subgroup Kˣ) hnorm hP
  have hmul := (stabSU (p := p) (f := f) (P : Subgroup Kˣ)).card_mul_index
  rw [hk, hcard, hcardc, mul_assoc] at hmul
  have hck : k * (stabSU (p := p) (f := f) (P : Subgroup Kˣ)).index = c :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hmul
  exact fun h3 => hc3 (hck ▸ Dvd.dvd.mul_left h3 k)

omit [Finite K] in
theorem map_psuField_fourPSU (σ : K ≃+* K) :
    (fourPSU h).map (psuField h σ : unitaryPSU h 3 →* unitaryPSU h 3) = fourPSU h := by
  refine map_eq_self_of_forall ?_
  rintro _ ⟨g, hg, rfl⟩
  change psuField h σ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  obtain ⟨u, hu, hug⟩ := coe_mem_diagSU hg
  rw [← hug]
  apply Units.ext
  rw [UnitaryHigher.coe_glAut, coe_diagGL, diagonal_map (map_zero _)]
  congr 1
  funext i
  have hw : (u.1 * u.2)⁻¹ ∈ rootsOfUnity 2 K :=
    (rootsOfUnity 2 K).inv_mem ((rootsOfUnity 2 K).mul_mem hu.1 hu.2)
  fin_cases i
  · exact ringEquiv_apply_of_sq_eq_one σ hu.1
  · exact ringEquiv_apply_of_sq_eq_one σ hu.2
  · exact ringEquiv_apply_of_sq_eq_one σ hw

omit [Finite K] in
theorem diagFirst_mem_unitaryIsom3 {d : Kˣ} (hd : h.bar (d : K) * d = 1) :
    diagFirst d ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_diagFirst, diagonal_map (map_zero _), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [hd]

omit [Finite K] in
theorem map_psuConj_diagFirst_fourPSU {d : Kˣ} (hd : diagFirst d ∈ unitaryIsom3 h) :
    (fourPSU h).map (psuConj h ⟨diagFirst d, hd⟩ : unitaryPSU h 3 →* unitaryPSU h 3) =
      fourPSU h := by
  refine map_eq_self_of_forall ?_
  rintro _ ⟨g, hg, rfl⟩
  change psuConj h ⟨diagFirst d, hd⟩ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)
  rw [psuConj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suConj]
  obtain ⟨u, -, hug⟩ := coe_mem_diagSU hg
  rw [← hug]
  have hc : diagFirst d * diagGL u = diagGL u * diagFirst d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagFirst, coe_diagGL, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  change diagFirst d * diagGL u * (diagFirst d)⁻¹ = diagGL u
  rw [hc, mul_inv_cancel_right]

omit [Finite K] in
theorem map_psuConj_fourPSU (A : unitaryIsom3 h) :
    (fourPSU h).map (psuConj h A : unitaryPSU h 3 →* unitaryPSU h 3) ∈
      conjOrbit (unitaryProj h 3) (fourPSU h) := by
  set d := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hnd : h.bar (d : K) * d = 1 := by
    have h1 := congrArg Matrix.det (mem_unitaryIsom3.mp A.2)
    rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_one] at h1
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
    exact h1
  have hD := diagFirst_mem_unitaryIsom3 h hnd
  set X := (A : GL (Fin 3) K) * (diagFirst d)⁻¹ with hX
  have hXiso : X ∈ unitaryIsom3 h := mul_mem A.2 (inv_mem hD)
  have hdetX : (X : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hX, map_mul, map_inv]
    have hdD : Matrix.GeneralLinearGroup.det (diagFirst d) = d := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagFirst, det_diagonal,
        Fin.prod_univ_three]
      simp
    rw [hdD, hd, mul_inv_cancel, Units.val_one]
  have hXSU : X ∈ unitarySU p f K 3 := (mem_unitarySU_iff h).mpr ⟨hdetX, hXiso⟩
  have hA : A = ⟨X, hXiso⟩ * ⟨diagFirst d, hD⟩ := by
    apply Subtype.ext
    change (A : GL (Fin 3) K) = X * diagFirst d
    rw [hX, inv_mul_cancel_right]
  refine ⟨⟨X, hXSU⟩, ?_⟩
  have hconj : psuConj h ⟨X, hXiso⟩ = MulAut.conj (unitaryProj h 3 ⟨X, hXSU⟩) :=
    (conj_mk_eq_psuConj (h := h) ⟨X, hXSU⟩).symm
  rw [hA, map_mul, hconj, map_mul_aut, map_psuConj_diagFirst_fourPSU]

omit [Finite K] in
theorem map_aut_fourPSU (hq2 : 2 < p ^ f) (α : MulAut (unitaryPSU h 3)) :
    (fourPSU h).map (α : unitaryPSU h 3 →* unitaryPSU h 3) ∈
      conjOrbit (unitaryProj h 3) (fourPSU h) := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq2 α
  rw [map_mul_aut, map_psuField_fourPSU]
  exact map_psuConj_fourPSU h A

theorem exists_fixed_fourGroup_unitaryPSU (h2 : (2 : K) ≠ 0) (hq2 : 2 < p ^ f)
    (hq : p ^ f % 3 = 2)
    (hcard : Nat.card ↥(unitarySU p f K 3) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)))
    (E : Subgroup (MulAut (unitaryPSU h 3))) (hE : IsPGroup 3 E) :
    ∃ S : Subgroup (unitaryPSU h 3), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      ∀ σ ∈ E, S.map (σ : unitaryPSU h 3 →* unitaryPSU h 3) = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 Kˣ := default
  obtain ⟨x, hx⟩ := exists_fixed_conj (unitaryProj h 3) (unitaryProj_surjective h 3) (fourPSU h)
    (map_aut_fourPSU h hq2) (stabSU (p := p) (f := f) (P : Subgroup Kˣ))
    (fun y hy => map_conj_fourPSU h hy.1) (not_three_dvd_index_stabSU h hq hcard P) E hE
  refine ⟨_, ?_, (isPGroup_fourPSU h).map _, hx⟩
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj (unitaryProj h 3 x)).injective]
  exact fourPSU_ne_bot h h2

end Unitary

theorem card_unitarySU_galoisField {p f : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p f (GaloisField p (2 * f))) :
    Nat.card ↥(unitarySU p f (GaloisField p (2 * f)) 3) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  obtain ⟨ψ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  rw [(unitaryScalars h 3).card_eq_card_quotient_mul_card_subgroup,
    card_unitaryScalars h (by norm_num)]
  change Nat.card (unitaryPSU h 3) * _ = _
  rw [Nat.card_congr ψ.toEquiv]
  exact KS14.card_projSU_three_mul_gcd p f h.one_le

end CFSG.RankThree.PartTwo.Sec16.Proof166Res6
