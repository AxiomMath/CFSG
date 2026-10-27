module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofL3
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open Matrix

section Groups

variable {G : Type*} [Group G]

theorem mem_of_pow_three_mem (H : Subgroup G) {x : G} {k : ℕ} (h3 : x ^ 3 ∈ H)
    (h2 : x ^ (2 ^ k) ∈ H) : x ∈ H := by
  obtain ⟨u, v, huv⟩ : IsCoprime (3 : ℤ) ((2 : ℤ) ^ k) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num : Int.gcd 3 2 = 1)).pow_right
  have hx : x = (x ^ 3) ^ u * (x ^ (2 ^ k)) ^ v := by
    rw [← zpow_natCast x 3, ← zpow_natCast x (2 ^ k), ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_add]
    conv_lhs => rw [← zpow_one x]
    congr 1
    push_cast
    linarith
  rw [hx]
  exact H.mul_mem (H.zpow_mem h3 u) (H.zpow_mem h2 v)

theorem commutator_mem_of_forall_eq_mul (N : Subgroup G) [N.Normal] (U : Set G)
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hG : ∀ g : G, ∃ d ∈ N, ∃ u ∈ U, g = d * u)
    (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  obtain ⟨d₁, hd₁, u, hu, rfl⟩ := hG a
  obtain ⟨d₂, hd₂, v, hv, rfl⟩ := hG b
  rw [← QuotientGroup.eq_one_iff]
  have h1 : ((d₁ : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hd₁
  have h2 : ((d₂ : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hd₂
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, h2, one_mul]
  rw [← QuotientGroup.mk_mul, hU u hu v hv, QuotientGroup.mk_mul]
  group

theorem pow_three_mem_of_mem_closure (N : Subgroup G) [N.Normal]
    (hab : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N) {τ : G}
    (hτ : τ ∈ Subgroup.closure {σ : G | σ ^ 3 = 1}) : τ ^ 3 ∈ N := by
  have hcomm : ∀ x y : G ⧸ N, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := hab b⁻¹ a⁻¹
    rwa [inv_inv, inv_inv, ← _root_.mul_inv_rev, mul_assoc] at h
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  induction hτ using Subgroup.closure_induction with
  | mem x hx => rw [← QuotientGroup.mk_pow, show x ^ 3 = 1 from hx, QuotientGroup.mk_one]
  | one => rw [QuotientGroup.mk_one, one_pow]
  | mul x y _ _ hx hy =>
    rw [QuotientGroup.mk_mul, (Commute.mul_pow (hcomm _ _) 3), hx, hy, one_mul]
  | inv x _ hx => rw [QuotientGroup.mk_inv, inv_pow, hx, inv_one]

theorem mem_of_mem_closure_of_two (D : Subgroup G) [D.Normal] (U : Set G)
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hG : ∀ g : G, ∃ d ∈ D, ∃ u ∈ U, g = d * u)
    {τ : G} (hτ : τ ∈ Subgroup.closure {σ : G | σ ^ 3 = 1}) {k : ℕ} (hk : τ ^ (2 ^ k) = 1) :
    τ ∈ D :=
  mem_of_pow_three_mem D
    (pow_three_mem_of_mem_closure D (commutator_mem_of_forall_eq_mul D U hU hG) hτ)
    (by rw [hk]; exact D.one_mem)

end Groups

@[expose] def InnerOfTwoThree (Y : Type*) [Group Y] : Prop :=
  ∀ τ ∈ Subgroup.closure {σ : MulAut Y | σ ^ 3 = 1}, (∃ k : ℕ, τ ^ (2 ^ k) = 1) →
    τ ∈ (MulAut.conj : Y →* MulAut Y).range

theorem innerOfTwoThree_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : InnerOfTwoThree Y) : InnerOfTwoThree X := by
  intro τ hτ ⟨k, hk⟩
  have hτ' : MulAut.congr e τ ∈ Subgroup.closure {σ : MulAut Y | σ ^ 3 = 1} := by
    have hle : Subgroup.closure {σ : MulAut X | σ ^ 3 = 1} ≤
        (Subgroup.closure {σ : MulAut Y | σ ^ 3 = 1}).comap (MulAut.congr e).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro σ hσ
      refine Subgroup.subset_closure ?_
      change (MulAut.congr e σ) ^ 3 = 1
      rw [← map_pow, show σ ^ 3 = 1 from hσ, map_one]
    exact hle hτ
  obtain ⟨y, hy⟩ := hY _ hτ' ⟨k, by rw [← map_pow, hk, map_one]⟩
  refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
  have h1 : y * e x * y⁻¹ = e (τ x) := by
    have h2 := congrArg (fun σ : MulAut Y => σ (e x)) hy
    simpa only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] using h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem innerOfTwoThree_of_perfect {S : Type*} [Group S] [Group.IsPerfect S]
    (hP : InnerOfTwoThree (S ⧸ Subgroup.center S)) : InnerOfTwoThree S := by
  intro τ hτ ⟨k, hk⟩
  set Φ := KFacts.centerDescend S with hΦ
  have hτ' : Φ τ ∈ Subgroup.closure {σ : MulAut (S ⧸ Subgroup.center S) | σ ^ 3 = 1} := by
    have hle : Subgroup.closure {σ : MulAut S | σ ^ 3 = 1} ≤
        (Subgroup.closure {σ : MulAut (S ⧸ Subgroup.center S) | σ ^ 3 = 1}).comap Φ := by
      rw [Subgroup.closure_le]
      intro σ hσ
      refine Subgroup.subset_closure ?_
      change (Φ σ) ^ 3 = 1
      rw [← map_pow, show σ ^ 3 = 1 from hσ, map_one]
    exact hle hτ
  obtain ⟨z, hz⟩ := hP _ hτ' ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨s, (Sec4.mulAut_eq_of_inv_mul_mem_center fun x => ?_).symm⟩
  have h1 := congrArg (fun σ : MulAut (S ⧸ Subgroup.center S) =>
    σ (x : S ⧸ Subgroup.center S)) hz
  simp only [MulAut.conj_apply, hΦ, KFacts.centerDescend_mk] at h1
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at h1
  rw [MulAut.conj_apply]
  exact h1

section Linear

variable {K : Type} [Field K] [Finite K]

open LinearFlag in
theorem innerOfTwoThree_projectiveSL : InnerOfTwoThree (projectiveSL 3 K) := by
  intro τ hτ ⟨k, hk⟩
  have hgen := automorphism_generation (K := K) (n := 3) le_rfl
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  obtain ⟨-, -, hDnorm, -⟩ := standard_outer_quotients (n := 3) (K := K)
  rw [hgen.1] at hDnorm
  have hN : (linearAutGroup 3 K).Normal := ⟨fun d hd g => by
    have h1 := hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ (Subgroup.mem_subgroupOf.mpr hd)
      ⟨g, Subgroup.mem_top g⟩
    exact Subgroup.mem_subgroupOf.mp h1⟩
  have hδδ : dualAut 3 K * dualAut 3 K = 1 := htrans.2.2.2.1
  have hδf : ∀ σ : K ≃+* K, Commute (dualAut 3 K) (fieldAut 3 K σ) := by
    intro σ
    have h1 := htrans.2.2.2.2.2.1 σ
    calc dualAut 3 K * fieldAut 3 K σ = dualAut 3 K * fieldAut 3 K σ * dualAut 3 K *
        dualAut 3 K := by rw [mul_assoc _ (dualAut 3 K), hδδ, mul_one]
      _ = fieldAut 3 K σ * dualAut 3 K := by rw [h1]
  have hff : ∀ σ σ' : K ≃+* K, Commute (fieldAut 3 K σ) (fieldAut 3 K σ') := by
    intro σ σ'
    change fieldAut 3 K σ * fieldAut 3 K σ' = fieldAut 3 K σ' * fieldAut 3 K σ
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ σ']
  set U : Set (MulAut (projectiveSL 3 K)) :=
    {u | ∃ (σ : K ≃+* K) (ε : ℕ), u = fieldAut 3 K σ * dualAut 3 K ^ ε} with hUdef
  have hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := by
    rintro _ ⟨σ, ε, rfl⟩ _ ⟨σ', ε', rfl⟩
    have h1 : Commute (fieldAut 3 K σ * dualAut 3 K ^ ε) (fieldAut 3 K σ') :=
      Commute.mul_left (hff σ σ') ((hδf σ').pow_left ε)
    have h2 : Commute (fieldAut 3 K σ * dualAut 3 K ^ ε) (dualAut 3 K) :=
      Commute.mul_left (hδf σ).symm (Commute.pow_left (Commute.refl _) ε)
    exact (Commute.mul_right h1 (h2.pow_right ε')).eq
  have hG : ∀ g : MulAut (projectiveSL 3 K), ∃ d ∈ linearAutGroup 3 K, ∃ u ∈ U, g = d * u := by
    intro g
    obtain ⟨A, σ, ε, -, hg⟩ := hgen.2 g
    exact ⟨conjAut 3 K A, conjAut_mem_linearAutGroup A, _, ⟨σ, ε, rfl⟩, by rw [hg, mul_assoc]⟩
  have hτD := mem_of_mem_closure_of_two (linearAutGroup 3 K) U hU hG hτ hk
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hτD
  refine mem_of_pow_three_mem _ ?_ (by rw [hk]; exact Subgroup.one_mem _)
  set d : Kˣ := GeneralLinearGroup.det A with hd
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 3) K, B = (GeneralLinearGroup.scalar (Fin 3) d)⁻¹ * A ^ 3 :=
    ⟨_, rfl⟩
  have hdetB : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : GeneralLinearGroup.det B = 1 := by
      rw [hB, map_mul, map_inv, map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hd,
        inv_mul_cancel]
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa [GeneralLinearGroup.val_det_apply] using h2
  have hA3 : A ^ 3 = GeneralLinearGroup.scalar (Fin 3) d * B := by
    rw [hB, mul_inv_cancel_left]
  have hBSL : SpecialLinearGroup.toGL (⟨B, hdetB⟩ : SpecialLinearGroup (Fin 3) K) = B :=
    Units.ext rfl
  have hc := conjAut_toGL (K := K) (n := 3) ⟨B, hdetB⟩
  rw [hBSL] at hc
  refine ⟨proj 3 K ⟨B, hdetB⟩, ?_⟩
  rw [← hc]
  calc conjAut 3 K B = conjAut 3 K (GeneralLinearGroup.scalar (Fin 3) d) * conjAut 3 K B := by
        rw [conjAut_scalar, one_mul]
    _ = conjAut 3 K A ^ 3 := by rw [← map_mul, ← hA3, map_pow]

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

open KFacts in
theorem innerOfTwoThree_unitaryPSU (hq : 2 < p ^ f) : InnerOfTwoThree (unitaryPSU h 3) := by
  intro τ hτ ⟨k, hk⟩
  have := h.finite
  have hN : (psuConj h).range.Normal := ⟨fun d hd g => by
    obtain ⟨B, rfl⟩ := hd
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq g
    refine ⟨A * ⟨glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩ * A⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ← psuField_mul_psuConj_mul_inv]
    group⟩
  set U : Set (MulAut (unitaryPSU h 3)) := Set.range (psuField h) with hUdef
  have hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := by
    rintro _ ⟨σ, rfl⟩ _ ⟨σ', rfl⟩
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ σ']
  have hG : ∀ g : MulAut (unitaryPSU h 3), ∃ d ∈ (psuConj h).range, ∃ u ∈ U, g = d * u := by
    intro g
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq g
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, rfl⟩
  have hτD := mem_of_mem_closure_of_two (psuConj h).range U hU hG hτ hk
  obtain ⟨A, rfl⟩ := hτD
  refine mem_of_pow_three_mem _ ?_ (by rw [hk]; exact Subgroup.one_mem _)
  set d : Kˣ := GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hAu : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := A.2
  have hnorm : h.bar (d : K) * (d : K) = 1 := by
    have h1 := congrArg Matrix.det hAu
    rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_one] at h1
    rw [hd, GeneralLinearGroup.val_det_apply]
    exact h1
  have hdU : GeneralLinearGroup.scalar (Fin 3) d ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [show (fun _ : Fin 3 => h.bar (d : K) * (d : K)) = fun _ => (1 : K) from
      funext fun _ => hnorm]
    exact Matrix.diagonal_one
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 3) K,
      B = (GeneralLinearGroup.scalar (Fin 3) d)⁻¹ * (A : GL (Fin 3) K) ^ 3 := ⟨_, rfl⟩
  have hBU : B ∈ unitaryIsom3 h := by
    rw [hB]
    exact (unitaryIsom3 h).mul_mem ((unitaryIsom3 h).inv_mem hdU) ((unitaryIsom3 h).pow_mem A.2 3)
  have hdetB : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : GeneralLinearGroup.det B = 1 := by
      rw [hB, map_mul, map_inv, map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hd,
        inv_mul_cancel]
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa [GeneralLinearGroup.val_det_apply] using h2
  have hBSU : B ∈ unitarySU p f K 3 := (mem_unitarySU_iff h).mpr ⟨hdetB, hBU⟩
  have hA3 : A ^ 3 = ⟨_, hdU⟩ * ⟨B, hBU⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_pow]
    change (A : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) d * B
    rw [hB, mul_inv_cancel_left]
  have hc : MulAut.conj (((⟨B, hBSU⟩ : unitarySU p f K 3) : unitaryPSU h 3)) =
      psuConj h ⟨B, hBU⟩ := conj_mk_eq_psuConj _
  have hc2 : psuConj h ⟨B, hBU⟩ = psuConj h A ^ 3 := by
    rw [← map_pow, hA3, map_mul, psuConj_scalar, one_mul]
  exact ⟨_, hc.trans hc2⟩

end Unitary

theorem odd_card_of_pow_three {Z : Type*} [Group Z] [Finite Z] (h : ∀ z : Z, z ^ 3 = 1) :
    Odd (Nat.card Z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 Z := fun z => ⟨1, by rw [pow_one, h z]⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn]
  exact Odd.pow (by decide)

theorem pow_three_of_mem_center_SL {X : Type*} [Group X] {K : Type} [Field K]
    (e : X ≃* SpecialLinearGroup (Fin 3) K) (z : Subgroup.center X) : z ^ 3 = 1 := by
  have hz : e z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 x]
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  have h3 : (e z) ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, Matrix.SpecialLinearGroup.coe_one,
      Matrix.scalar_apply, Matrix.diagonal_pow]
    have hr' : (fun _ : Fin 3 => r) ^ 3 = fun _ => (1 : K) := funext fun _ => by
      rw [Pi.pow_apply, hr]
    rw [hr', Matrix.diagonal_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply e.injective
  rw [map_pow, map_one, h3]

theorem pow_three_of_mem_center_SU {X : Type*} [Group X] {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (e : X ≃* unitarySU p f K 3)
    (z : Subgroup.center X) : z ^ 3 = 1 := by
  have hz : e z ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 x]
  rw [KFacts.center_unitarySU_three (h := h) hq] at hz
  obtain ⟨c, -, hc3, hcz⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply e.injective
  rw [map_pow, map_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, hcz, ← map_pow, hc3, map_one, Subgroup.coe_one]

noncomputable def quotientCenterCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem l3Inner_SL {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X) {K : Type} [Field K]
    [Finite K] (e : X ≃* StatedSL 3 K) :
    Odd (Nat.card (Subgroup.center X)) ∧ InnerOfTwoThree X := by
  set e₁ := e.trans (Sec4.statedSLEquiv 3 K) with he₁
  refine ⟨odd_card_of_pow_three (pow_three_of_mem_center_SL e₁), ?_⟩
  have : Group.IsPerfect X := hX.1
  refine innerOfTwoThree_of_perfect (innerOfTwoThree_of_mulEquiv ((quotientCenterCongr e₁).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
    innerOfTwoThree_projectiveSL)

theorem l3Inner_SU {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X) {p f : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (e : X ≃* unitarySU p f K 3) :
    Odd (Nat.card (Subgroup.center X)) ∧ InnerOfTwoThree X := by
  refine ⟨odd_card_of_pow_three (pow_three_of_mem_center_SU h hq e), ?_⟩
  have : Group.IsPerfect X := hX.1
  exact innerOfTwoThree_of_perfect (innerOfTwoThree_of_mulEquiv ((quotientCenterCongr e).trans
    (KFacts.suCenterEquiv h hq)) (innerOfTwoThree_unitaryPSU h hq))

end Item211Lie2Proof

open Item211Lie2Proof
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial

theorem ks211L3Inner_holds : KS211L3Inner := by
  intro X _ _ hX hM
  obtain ⟨p, hp, hp3, e, he, hcase⟩ := hM
  have hpe : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
  rcases hcase with ⟨K, _, _, hK⟩ | hL
  · rcases hK with ⟨-, -, ⟨φ⟩⟩ | ⟨hcard, -, ⟨φ⟩⟩
    · exact l3Inner_SL hX φ
    · have h : UnitaryFieldData p e K := ⟨hp.out, he, by rw [hcard, ← pow_mul, mul_comm]⟩
      exact l3Inner_SU hX h hpe φ
  · rcases hL with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p e)) :=
        CFSG.BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
          (Or.inl (by norm_num))
      have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p e)) :=
        (Sec4.projSLEquivPSLn 3 (GaloisField p e)).isSimpleGroup
      refine ⟨?_, innerOfTwoThree_of_mulEquiv
        (φ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField p e))) innerOfTwoThree_projectiveSL⟩
      rw [Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hX φ, Subgroup.card_bot]
      exact odd_one
    · have h := Sec4.unitaryFieldData_galoisField p e he
      have : IsSimpleGroup (projSU 3 p e) :=
        Sec4.Item462AltProof.isSimpleGroup_projSU_three p e he (by omega)
      refine ⟨?_, innerOfTwoThree_of_mulEquiv (φ.trans (Sec4.projSUEquivUnitaryPSU p e h))
        (innerOfTwoThree_unitaryPSU h hpe)⟩
      rw [Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hX φ, Subgroup.card_bot]
      exact odd_one

end CFSG.RankThree.PartTwo.Sec21
