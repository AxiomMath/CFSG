module

public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitTameGU
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

private def ggK1CBu_Small (nf m : ℕ) : Prop :=
  m ≤ 1 ∨ (m = 2 ∧ nf = 1) ∨ (m = 3 ∧ nf = 1)

private theorem ggK1CBu_two_pow_lt_four {nf : ℕ} (hnf : 1 ≤ nf) : 2 ^ nf < 4 ↔ nf = 1 := by
  constructor
  · intro h
    by_contra hne
    have h2 : 2 ≤ nf := by omega
    have hle : 2 ^ 2 ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) h2
    norm_num at hle
    omega
  · rintro rfl
    norm_num

private theorem ggK1CBu_two_pow_lt_three {nf : ℕ} (hnf : 1 ≤ nf) : 2 ^ nf < 3 ↔ nf = 1 := by
  constructor
  · intro h
    by_contra hne
    have h2 : 2 ≤ nf := by omega
    have hle : 2 ^ 2 ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) h2
    norm_num at hle
    omega
  · rintro rfl
    norm_num

private theorem ggK1CBu_small_iff {nf m : ℕ} (hnf : 1 ≤ nf) :
    (m ≤ 1 ∨ ¬ ((m = 2 → 4 ≤ 2 ^ nf) ∧ (m = 3 → 3 ≤ 2 ^ nf))) ↔ ggK1CBu_Small nf m := by
  unfold ggK1CBu_Small
  constructor
  · rintro (h1 | h2)
    · exact Or.inl h1
    · by_cases hm2 : m = 2
      · subst hm2
        refine Or.inr (Or.inl ⟨rfl, ?_⟩)
        by_contra hne
        exact h2 ⟨fun _ => by
          by_contra hlt; exact hne ((ggK1CBu_two_pow_lt_four hnf).mp (by omega)),
          fun h => by omega⟩
      · by_cases hm3 : m = 3
        · subst hm3
          refine Or.inr (Or.inr ⟨rfl, ?_⟩)
          by_contra hne
          exact h2 ⟨fun h => by omega,
            fun _ => by by_contra hlt; exact hne ((ggK1CBu_two_pow_lt_three hnf).mp (by omega))⟩
        · omega
  · rintro (h1 | ⟨rfl, hnf1⟩ | ⟨rfl, hnf1⟩)
    · exact Or.inl h1
    · right
      subst hnf1
      intro h
      exact absurd (h.1 rfl) (by norm_num)
    · right
      subst hnf1
      intro h
      exact absurd (h.2 rfl) (by norm_num)

private theorem ggK1CBu_conditions_of_not_small {nf m : ℕ} (hnf : 1 ≤ nf)
    (h : ¬ ggK1CBu_Small nf m) :
    2 ≤ m ∧ (m = 2 → 4 ≤ 2 ^ nf) ∧ (m = 3 → 3 ≤ 2 ^ nf) := by
  unfold ggK1CBu_Small at h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, ?_, ?_⟩
  · intro hm
    subst hm
    by_contra h4
    exact h2 rfl ((ggK1CBu_two_pow_lt_four hnf).mp (by omega))
  · intro hm
    subst hm
    by_contra h4
    exact h3 rfl ((ggK1CBu_two_pow_lt_three hnf).mp (by omega))

private theorem ggK1CBu_qs_eq {nf m : ℕ} (hm : 1 ≤ m) :
    (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su m)).qs = true ↔ ¬ ggK1CBu_Small nf m := by
  rcases m with _ | _ | _ | m
  · exfalso; omega
  · simp [ggK1CCo_kindOrbit, ggK1CBu_Small]
  · simp [ggK1CCo_kindOrbit, ggMultBlockA, ggK1CBu_Small, decide_eq_true_eq]
  · rcases m with _ | m
    · simp [ggK1CCo_kindOrbit, ggMultBlockA, ggK1CBu_Small, decide_eq_true_eq]
    · have h1 : ¬ (m + 3 = 2) := by omega
      have h2 : ¬ (m + 4 = 2) := by omega
      have h3 : ¬ (m + 4 = 3) := by omega
      have h4 : ¬ (m + 4 ≤ 1) := by omega
      simp [ggK1CCo_kindOrbit, ggMultBlockA, ggK1CBu_Small, decide_eq_true_eq, h1, h2, h3, h4]

private theorem ggK1CBu_card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem ggK1CBu_isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (h ▸ ggK1CBu_card_primeFactors_two_three a b ha hb)

private theorem ggK1CBu_finite_generalLinearGroup {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem ggK1CBu_isSolvable_sesqUnitaryGroup_of_small {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : Module.finrank E W ≤ 1 ∨ (¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)))) : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  have hq2 : 2 ≤ ℓ ^ g := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : g ≠ 0) hE.prime.one_lt
    omega
  haveI := ggK1CBu_finite_generalLinearGroup hE (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · have hq : ¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
        (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)) := by
      rcases hsmall with h | h
      · omega
      · exact h
    obtain ⟨hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
      rfl (by omega : 1 ≤ Module.finrank E W)
    have hexc : (Module.finrank E W = 2 ∧ ℓ ^ g = 2) ∨ (Module.finrank E W = 2 ∧ ℓ ^ g = 3) ∨
        (Module.finrank E W = 3 ∧ ℓ ^ g = 2) := by
      by_contra hn
      push Not at hn
      obtain ⟨h1, h2, h3⟩ := hn
      refine hq ⟨fun h2' => ?_, fun h3' => ?_⟩
      · by_contra hlt
        rcases (show ℓ ^ g = 2 ∨ ℓ ^ g = 3 by omega) with hQ | hQ
        · exact h1 h2' hQ
        · exact h2 h2' hQ
      · by_contra hlt
        exact h3 h3' (by omega)
    rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
    · rw [hm2, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
      exact ggK1CBu_isSolvable_of_card_two_three (a := 1) (b := 2) (by norm_num) (by norm_num)
        (by rw [h18]; norm_num)
    · rw [hm2, hQ] at hcard
      have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
      exact ggK1CBu_isSolvable_of_card_two_three (a := 5) (b := 1) (by norm_num) (by norm_num)
        (by rw [h96]; norm_num)
    · rw [hm3, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
      exact ggK1CBu_isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
        (by rw [h648]; norm_num)
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

private noncomputable def ggK1CBu_commutator_equiv_self {G : Type*} [Group G] (A : Subgroup G) :
    ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
  (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))

private theorem ggK1CBu_map_commutator {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem ggK1CBu_solvable_iff {nf : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {m : ℕ}
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf)
    {E : Type} [Field E] [Fintype E]
    (hE : UnitaryFieldData 2 nf E)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (b : Module.Basis (Fin m) E V)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    (e : ↥A ≃* sesqUnitaryGroup Hf) :
    Group.IsSolvable ↥A ↔ ggK1CBu_Small nf m := by
  have hfind : Module.finrank E V = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  constructor
  · intro hsol
    by_contra hns
    obtain ⟨hm2m, hq2m, hq3m⟩ := ggK1CBu_conditions_of_not_small hnf hns
    have hm2 : 2 ≤ Module.finrank E V := by rw [hfind]; exact hm2m
    have hqq : (Module.finrank E V = 2 → 4 ≤ 2 ^ nf) ∧
        (Module.finrank E V = 3 → 3 ≤ 2 ^ nf) :=
      ⟨fun h => hq2m (hfind ▸ h), fun h => hq3m (hfind ▸ h)⟩
    have hqSU : CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
        hE hHf hHfl hm2 hqq
    haveI : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
      haveI := hsol
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    haveI : Nontrivial ↥(sesqSpecialUnitaryGroup Hf) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hqSU
    haveI : Group.IsPerfect ↥(sesqSpecialUnitaryGroup Hf) := hqSU.1
    have hnot : ¬ Group.IsSolvable ↥(sesqSpecialUnitaryGroup Hf) :=
      Group.IsPerfect.not_isSolvable ↥(sesqSpecialUnitaryGroup Hf)
    refine hnot ?_
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf))
      (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le Hf))
  · intro hSmall
    have hsmall : Module.finrank E V ≤ 1 ∨ (¬ ((Module.finrank E V = 2 → 4 ≤ 2 ^ nf) ∧
        (Module.finrank E V = 3 → 3 ≤ 2 ^ nf))) := by
      rw [hfind]
      exact (ggK1CBu_small_iff hnf).mpr hSmall
    haveI : Group.IsSolvable ↥(sesqUnitaryGroup Hf) :=
      ggK1CBu_isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl hsmall
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem ggK1CBu_commutator_eq_su {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hq : CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf)) :
    ⁅(sesqUnitaryGroup Hf), (sesqUnitaryGroup Hf)⁆ = sesqSpecialUnitaryGroup Hf := by
  have hker : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitarySpecial (h := hE) Hf =
      (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_unitarySpecial (h := hE),
      Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    exact ⟨fun h => ⟨δ.2, h⟩, fun h => h.2⟩
  have hle : ⁅(sesqUnitaryGroup Hf), (sesqUnitaryGroup Hf)⁆ ≤ sesqSpecialUnitaryGroup Hf := by
    rw [← Subgroup.map_subtype_commutator (sesqUnitaryGroup Hf)]
    refine Subgroup.map_le_iff_le_comap.2 ?_
    rw [Subgroup.comap_subtype, ← hker]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.commutator_le_unitarySpecial
      (h := hE) Hf
  refine le_antisymm hle ?_
  have hperf : ⁅(sesqSpecialUnitaryGroup Hf), (sesqSpecialUnitaryGroup Hf)⁆ =
      sesqSpecialUnitaryGroup Hf := Subgroup.isPerfect_iff.mp hq.1
  rw [← hperf]
  exact Subgroup.commutator_mono (sesqSpecialUnitaryGroup_le Hf) (sesqSpecialUnitaryGroup_le Hf)

private theorem ggK1CBu_model_nonempty {nf : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {m : ℕ}
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf)
    {E : Type} [Field E] [Fintype E]
    (hE : UnitaryFieldData 2 nf E)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (b : Module.Basis (Fin m) E V)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    (e : ↥A ≃* sesqUnitaryGroup Hf)
    (hq : CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf)) :
    Nonempty (↥⁅A, A⁆ ≃* ↥(StatedSU m (Nat.card K) E)) := by
  obtain ⟨eGram⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU
    (h := hE) b (G := (1 : Matrix (Fin m) (Fin m) E))
    (fun i j => by rw [hb i j, Matrix.one_apply])
  have hgramStated : gramSU hE (1 : Matrix (Fin m) (Fin m) E) = StatedSU m (Nat.card K) E := by
    rw [← CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU hE m, hK]
  have hss_eq := ggK1CBu_commutator_eq_su hE hHf hHfl hq
  have hmap := ggK1CBu_map_commutator e
  let eAcomm : ↥(commutator ↥A) ≃* ↥(commutator ↥(sesqUnitaryGroup Hf)) :=
    (Subgroup.equivMapOfInjective (commutator ↥A) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  let ecomm : ↥(commutator ↥(sesqUnitaryGroup Hf)) ≃*
      ↥⁅(sesqUnitaryGroup Hf), (sesqUnitaryGroup Hf)⁆ :=
    ggK1CBu_commutator_equiv_self (sesqUnitaryGroup Hf)
  refine ⟨((ggK1CBu_commutator_equiv_self A).symm.trans eAcomm).trans
    (ecomm.trans ((MulEquiv.subgroupCongr hss_eq).trans
      (eGram.trans (MulEquiv.subgroupCongr hgramStated))))⟩

theorem ggK1CBl_classical_su {nf : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {m : ℕ}
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf) (hm : 1 ≤ m)
    {E : Type} [Field E] [Fintype E]
    (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf E)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (b : Module.Basis (Fin m) E V)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    (e : ↥A ≃* CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) :
    (CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ ↔
        (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su m)).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ → ggK1CBl_Model nf K (ggK1CCo_Kind.su m) ↥⁅A, A⁆) := by
  let ρE : E ≃+* E :=
    { toFun := hE.bar
      invFun := hE.bar
      left_inv := hE.bar_bar
      right_inv := hE.bar_bar
      map_mul' := hE.bar.map_mul
      map_add' := hE.bar.map_add }
  have hρE : ∀ y, ρE (ρE y) = y := hE.bar_bar
  have hτQ : ∀ y, ρE y = y ^ Nat.card K := by
    intro y
    change hE.bar y = y ^ Nat.card K
    rw [hE.bar_apply, ← hK]
  have hEc : Nat.card E = Nat.card K ^ 2 := by
    rw [hK, hE.card, show 2 * nf = nf * 2 by omega, pow_mul]
  obtain ⟨eU⟩ := CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU
    ρE hρE Hf b hb
  let φ : ↥A ≃* heldGU m E ρE hρE := e.trans eU
  have hdisj : CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A :=
    ggNbrLSideTame_gu hK hnf hEc hτQ φ
  have hS_iff : Group.IsSolvable ↥A ↔ ggK1CBu_Small nf m :=
    ggK1CBu_solvable_iff hK hnf hE hHf hHfl b hb e
  have hQ_iff : CFSG.IsQuasisimple ↥⁅A, A⁆ ↔ ¬ ggK1CBu_Small nf m := by
    constructor
    · intro hQ hSmall
      have hS : Group.IsSolvable ↥A := hS_iff.mpr hSmall
      haveI : Nontrivial ↥⁅A, A⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hQ
      haveI : Group.IsPerfect ↥⁅A, A⁆ := hQ.1
      have hnot : ¬ Group.IsSolvable ↥⁅A, A⁆ :=
        Group.IsPerfect.not_isSolvable ↥⁅A, A⁆
      refine hnot ?_
      haveI := hS
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (Subgroup.commutator_le_self A))
        (Subgroup.inclusion_injective (Subgroup.commutator_le_self A))
    · intro hns
      rcases hdisj with h | h
      · exact h
      · exact absurd (hS_iff.mp h) hns
  have hqs : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su m)).qs = true ↔ ¬ ggK1CBu_Small nf m :=
    ggK1CBu_qs_eq hm
  refine ⟨hdisj, hQ_iff.trans hqs.symm, ?_⟩
  intro hQ
  have hns : ¬ ggK1CBu_Small nf m := hQ_iff.mp hQ
  obtain ⟨hm2m, hq2m, hq3m⟩ := ggK1CBu_conditions_of_not_small hnf hns
  have hfind : Module.finrank E V = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hm2 : 2 ≤ Module.finrank E V := by rw [hfind]; exact hm2m
  have hqq : (Module.finrank E V = 2 → 4 ≤ 2 ^ nf) ∧
      (Module.finrank E V = 3 → 3 ≤ 2 ^ nf) :=
    ⟨fun h => hq2m (hfind ▸ h), fun h => hq3m (hfind ▸ h)⟩
  have hqSU : CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hE hHf hHfl hm2 hqq
  refine ⟨E, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact hEc
  · exact ggK1CBu_model_nonempty hK hnf hE hHf hHfl b hb e hqSU

end CFSG.StandardType

end
