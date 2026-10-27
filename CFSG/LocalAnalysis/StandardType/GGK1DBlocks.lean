module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.StandardType.GGK1CBlFF
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.LocalAnalysis.StandardType.GGK1DOm4
public import CFSG.LocalAnalysis.StandardType.GGK1DTame
public import CFSG.LocalAnalysis.StandardType.GGK1DFixed

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial Matrix
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial
  supportedBlock isometryCentralizer)
open CFSG.RankThree.Classical (IsReciprocalTransversal)
open scoped Pointwise

private lemma ggK1Db_lin_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (v : ι → K) : ggK1DLin x v = (x : Matrix ι ι K) *ᵥ v := by
  rw [ggK1DLin, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin, Matrix.coe_mulVecLin]

private lemma ggK1Db_lin_mul {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (a b : GL ι K) : ggK1DLin (a * b) = ggK1DLin a * ggK1DLin b := by
  ext v
  rw [LinearEquiv.mul_apply, ggK1Db_lin_apply, ggK1Db_lin_apply, ggK1Db_lin_apply,
    Units.val_mul, Matrix.mulVec_mulVec]

private lemma ggK1Db_lin_pow {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (n : ℕ) : ggK1DLin (x ^ n) = (ggK1DLin x) ^ n := by
  induction n with
  | zero => ext v; rw [pow_zero, pow_zero, ggK1Db_lin_apply]; simp
  | succ n ih => rw [pow_succ, pow_succ, ggK1Db_lin_mul, ih]

private lemma ggK1Db_cast_ne_zero {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) : (p : K) ≠ 0 := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  intro hp0
  have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp hp0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm

private theorem ggK1Db_card_sq_eq_one {p nf : ℕ} (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) :
    (((2 ^ nf : ℕ) : ZMod p)) ^ 2 = 1 := by
  have hpos : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  rcases hdvd with h1 | h1
  · have h0 : (((2 ^ nf - 1 : ℕ) : ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    rw [Nat.cast_sub hpos, sub_eq_zero] at h0
    rw [h0]; simp
  · have h0 : (((2 ^ nf + 1 : ℕ) : ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    rw [Nat.cast_add, Nat.cast_one] at h0
    have h2 : ((2 ^ nf : ℕ) : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h0
    rw [h2]; simp

private theorem ggK1Db_natDegree_le_two {K : Type} [Field K] [Fintype K] {p nf : ℕ}
    (hp : p.Prime) (hpchar : p ≠ ringChar K) (hK : Fintype.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) {h : K[X]} (hirr : Irreducible h)
    (hmon : h.Monic) (hdvdX : h ∣ X ^ p - 1) (hne : h ≠ X - 1) : h.natDegree ≤ 2 := by
  rw [ggK1CBl_ff_degree hp hpchar hirr hmon hdvdX hne]
  have hsq : ((Fintype.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [hK]; exact ggK1Db_card_sq_eq_one hdvd
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hsq)

private lemma ggK1Db_selfDual_card {p nf : ℕ} {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf (AdjoinRoot h),
      h.natDegree = 2 ∧ Nat.card (AdjoinRoot h) = (2 ^ nf) ^ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := (mem_primaryFactors.mp hh).2.1
  have hdvdX : h ∣ X ^ p - 1 := hx.dvd_X_pow_sub_one hh
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hrc : ringChar K = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hK]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : nf ≠ 0))
  have hpchar : p ≠ ringChar K := by rw [hrc]; exact hp2
  have hcardK : Fintype.card K = 2 ^ nf := by rw [Fintype.card_eq_nat_card, hK]
  have hle2 : h.natDegree ≤ 2 :=
    ggK1Db_natDegree_le_two hp hpchar hcardK hdvd hirr hmon hdvdX hne1
  obtain ⟨d, _, hndeg, -⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry.exists_selfDual_hermitian
      hx hpodd hh hne1 hself
  have hpos : 0 < h.natDegree := hirr.natDegree_pos
  have hd1 : d = 1 := by omega
  have hndeg2 : h.natDegree = 2 := by omega
  have hcard : Nat.card (AdjoinRoot h) = (2 ^ nf) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K),
      CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot, hndeg2, hK]
  exact ⟨⟨Nat.prime_two, hnf, by rw [hcard, ← pow_mul, mul_comm]⟩, hndeg2, hcard⟩

private lemma ggK1Db_modular {G : Type*} [Group G] {B N D : Subgroup G}
    (hsup : ∀ g ∈ B ⊔ N, ∃ b ∈ B, ∃ n ∈ N, b * n = g) (h : N ≤ D) :
    (B ⊔ N) ⊓ D = (B ⊓ D) ⊔ N := by
  apply le_antisymm
  · rintro g hg
    obtain ⟨hgsup, hgD⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨b, hbB, n, hnN, hbn⟩ := hsup g hgsup
    have hbD : b ∈ D := by
      have h1 : b * n * n⁻¹ ∈ D := D.mul_mem (hbn ▸ hgD) (D.inv_mem (h hnN))
      simpa using h1
    rw [← hbn]
    exact Subgroup.mul_mem_sup ⟨hbB, hbD⟩ hnN
  · refine sup_le ?_ ?_
    · exact le_inf (le_trans inf_le_left le_sup_left) inf_le_right
    · exact le_inf le_sup_right h

private lemma ggK1Db_polarBilin_nondegenerate {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) : Q.polarBilin.Nondegenerate :=
  ⟨fun v hv => hx.regular v fun w => hv w,
    fun w hw => hx.regular w fun v => by
      rw [← QuadraticMap.polar_comm]
      exact hw v⟩

private lemma ggK1Db_exists_totallySingular_three {K V : Type*} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 8 ≤ Module.finrank K V) :
    ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨n, hn⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hn4 : 4 ≤ n := by rw [hn] at hdim; omega
  obtain ⟨-, -, -, -, -, h3pairs⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms Q hQ
  have hn' : Module.finrank K V = 2 * n := by omega
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := h3pairs n hn' hn4
  exact CFSG.ClassicalGroups.Orthogonal.exists_totallySingular_of_hypPairs h12 h13 h23

private lemma ggK1Db_supportedBlock_le_orthDerived {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1) :
    supportedBlock Q x r ≤ CFSG.RankThree.Classical2.orthDerived Q := by
  intro g hg
  exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
      ⟨(Subgroup.mem_inf.mp
        (CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock_le_isometryCentralizer r hg)).1,
        hx.even_finrank_commSpace_of_mem_supportedBlock hp2 hr hne1 hg⟩)

private lemma ggK1Db_kindOrbits_om_length (nf s : ℕ) (eps : Bool) :
    (ggK1DCo_kindOrbits nf (.om eps s)).length = if s = 2 ∧ eps = true then 2 else 1 := by
  by_cases h1 : s ≤ 1
  · have h2 : ¬ (s = 2 ∧ eps = true) := fun h => by omega
    simp [ggK1DCo_kindOrbits, h1, h2]
  · by_cases h2 : s = 2
    · subst h2
      cases eps <;> simp [ggK1DCo_kindOrbits, ggMultV0]
    · have h3 : ¬ (s = 2 ∧ eps = true) := fun h => h2 h.1
      by_cases h4 : s = 3
      · subst h4; cases eps <;> simp [ggK1DCo_kindOrbits, ggMultV0]
      · simp only [ggK1DCo_kindOrbits, if_neg h1, ggMultV0, h2, h4, if_false, if_neg h3]
        cases eps <;> simp

private lemma ggK1Db_kindOrbits_sl_length (nf s : ℕ) :
    (ggK1DCo_kindOrbits nf (.sl s)).length = 1 := by
  simp only [ggK1DCo_kindOrbits]; split_ifs <;> simp

private lemma ggK1Db_kindOrbits_su_length (nf s : ℕ) :
    (ggK1DCo_kindOrbits nf (.su s)).length = 1 := by
  simp only [ggK1DCo_kindOrbits]; split_ifs <;> simp

private theorem ggK1Db_iSupIndep_sigma {G : Type*} [Group G] {ι : Type*} {κ : ι → Type*}
    (A : ι → Subgroup G) (sub : (i : ι) → κ i → Subgroup G) (hA : iSupIndep A)
    (hAc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (hle : ∀ i k, sub i k ≤ A i) (hin : ∀ i, iSupIndep (sub i)) :
    iSupIndep (fun q : Σ i, κ i => sub q.1 q.2) := by
  rw [iSupIndep_def]
  rintro ⟨i, k⟩
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  simp only at hg
  let N : Subgroup G := ⨆ (j : ι) (_ : j ≠ i), A j
  let M : Subgroup G := ⨆ (k' : κ i) (_ : k' ≠ k), sub i k'
  have hMle : M ≤ A i := iSup_le fun k' => iSup_le fun _ => hle i k'
  have hNc : ∀ n ∈ N, ∀ a ∈ A i, n * a = a * n := by
    intro n hn a ha
    refine Subgroup.iSup_induction (fun j : ι => ⨆ (_ : j ≠ i), A j) (C := fun z => z * a = a * z)
      hn ?_ (by simp) ?_
    · intro j z hz
      refine Subgroup.iSup_induction (fun _ : j ≠ i => A j) (C := fun z => z * a = a * z)
        hz ?_ (by simp) ?_
      · intro hj y hy
        exact hAc j i hj y hy a ha
      · intro z w hz hw
        calc z * w * a = z * (w * a) := by rw [mul_assoc]
          _ = z * (a * w) := by rw [hw]
          _ = z * a * w := by rw [← mul_assoc]
          _ = a * z * w := by rw [hz]
          _ = a * (z * w) := by rw [mul_assoc]
    · intro z w hz hw
      calc z * w * a = z * (w * a) := by rw [mul_assoc]
        _ = z * (a * w) := by rw [hw]
        _ = z * a * w := by rw [← mul_assoc]
        _ = a * z * w := by rw [hz]
        _ = a * (z * w) := by rw [mul_assoc]
  have hNnorm : N ≤ Subgroup.normalizer M := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro m
    have hcn : ∀ m ∈ M, n * m = m * n := fun m hm => hNc n hn m (hMle hm)
    constructor
    · intro hm
      rw [hcn m hm]
      simpa using hm
    · intro hm
      have h4 : n⁻¹ * (n * m * n⁻¹) * n = n * m * n⁻¹ := by
        calc n⁻¹ * (n * m * n⁻¹) * n
            = n⁻¹ * ((n * m * n⁻¹) * n) := by rw [mul_assoc]
          _ = n⁻¹ * (n * (n * m * n⁻¹)) := by rw [← hcn (n * m * n⁻¹) hm]
          _ = n * m * n⁻¹ := by group
      have h5 : m = n⁻¹ * (n * m * n⁻¹) * n := by group
      rw [h5, h4]; exact hm
  have hsub : (⨆ (q' : Σ i, κ i) (_ : q' ≠ ⟨i, k⟩), sub q'.1 q'.2) ≤ N ⊔ M := by
    refine iSup_le fun q' => iSup_le fun hq' => ?_
    rcases q' with ⟨j, k'⟩
    by_cases hji : j = i
    · subst hji
      have hk' : k' ≠ k := fun h => hq' (by rw [h])
      exact le_sup_of_le_right (le_iSup₂ (f := fun (k'' : κ j) (_ : k'' ≠ k) => sub j k'') k' hk')
    · exact le_sup_of_le_left ((hle j k').trans
        (le_iSup₂ (f := fun (j' : ι) (_ : j' ≠ i) => A j') j hji))
  have hg2 : g ∈ N ⊔ M := hsub hg'
  have h1 : g ∈ (N : Set G) * (M : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNnorm]
    exact hg2
  obtain ⟨n, hn, m, hm, rfl⟩ := h1
  change n * m ∈ sub i k at hg
  change n * m = 1
  have hnA : n ∈ A i := by
    have : n = (n * m) * m⁻¹ := by group
    rw [this]
    exact mul_mem (hle i k hg) (inv_mem (hMle hm))
  have hn1 : n = 1 := by
    have hdisj := hA i
    rw [Subgroup.disjoint_def] at hdisj
    exact hdisj hnA hn
  subst hn1
  rw [one_mul] at hg ⊢
  have hdisj := hin i k
  rw [Subgroup.disjoint_def] at hdisj
  exact hdisj hg hm

open Classical in
private noncomputable def ggK1Db_om4Pair {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) :
    Subgroup (V ≃ₗ[K] V) × Subgroup (V ≃ₗ[K] V) :=
  if h : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 4 ∧
      CFSG.GroupTheory.WeirSylow.IsPlusType
        (Q.restrict (primaryComponent x.toLinearMap (X - 1))) then
    (Classical.choose (ggK1D_omega4_block hx hQ hT h.1 h.2),
      Classical.choose (Classical.choose_spec (ggK1D_omega4_block hx hQ hT h.1 h.2)))
  else (⊥, ⊥)

private theorem ggK1Db_om4Pair_spec {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hW : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.restrict (primaryComponent x.toLinearMap (X - 1)))) :
    (∀ a ∈ (ggK1Db_om4Pair hx hQ hT).1, ∀ b ∈ (ggK1Db_om4Pair hx hQ hT).2, a * b = b * a) ∧
    Disjoint (ggK1Db_om4Pair hx hQ hT).1 (ggK1Db_om4Pair hx hQ hT).2 ∧
    (ggK1Db_om4Pair hx hQ hT).1 ⊔ (ggK1Db_om4Pair hx hQ hT).2 = supportedBlock Q x (X - 1) ⊓
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
    Nonempty ((ggK1Db_om4Pair hx hQ hT).1 ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
    Nonempty ((ggK1Db_om4Pair hx hQ hT).2 ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  unfold ggK1Db_om4Pair
  rw [dif_pos ⟨hW, hplus⟩]
  exact Classical.choose_spec (Classical.choose_spec (ggK1D_omega4_block hx hQ hT hW hplus))

private lemma ggK1Db_tame_SL2 {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] {nf : ℕ} (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {S : Subgroup (V ≃ₗ[K] V)}
    (hSL : Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    CFSG.IsQuasisimple ↥⁅S, S⁆ ∨ Group.IsSolvable ↥S := by
  classical
  obtain ⟨e⟩ := hSL
  by_cases h4 : 4 ≤ Nat.card K
  · left
    haveI hqs : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (m := 2) (by norm_num) h4
    have hSqs : CFSG.IsQuasisimple ↥S := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqs
    have h2 : ⁅S, S⁆ = S := by
      haveI : Group.IsPerfect ↥S := hSqs.1
      rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [h2]
    exact hSqs
  · right
    have hnflt : nf = 1 := by
      have h2 : nf ≤ 1 := by
        by_contra h
        have h3 : 2 ≤ nf := by omega
        have h4' : 4 ≤ 2 ^ nf := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) h3
        omega
      omega
    have hK2 : Nat.card K = 2 := by rw [hK, hnflt]; norm_num
    haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
      haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
          (Or.inl hK2)
      exact Group.isSolvable_of_isSolvable_injective
        (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem ggK1D_orthBlocks_abstract {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {nf p : ℕ} {x : V ≃ₗ[K] V}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdim : 8 ≤ Module.finrank K V) (hx : OddOrderIsometry Q p x) :
    Nonempty (OrthPrimaryBlocks K Q nf p x) := by
  classical
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  let W : Submodule K V := primaryComponent x.toLinearMap (X - 1)
  let orthD : Subgroup (V ≃ₗ[K] V) :=
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  let kind : ↥Rep → ggK1DCo_Kind := fun r =>
    if (r : K[X]) = X - 1 then
      .om (if CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W) then true else false)
        (Module.finrank K W / 2)
    else if reciprocalPolynomial (r : K[X]) = (r : K[X]) then
      .su (primaryMultiplicity x.toLinearMap (r : K[X]))
    else .sl (primaryMultiplicity x.toLinearMap (r : K[X]))
  let blk : ↥Rep → List GGKacOrbit := fun r => ggK1DCo_kindOrbits nf (kind r)
  let A : ↥Rep → Subgroup (V ≃ₗ[K] V) := fun r =>
    if (r : K[X]) = X - 1 then supportedBlock Q x (X - 1) ⊓ orthD
    else supportedBlock Q x (r : K[X])
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hQ0 : Q.polarBilin.Nondegenerate := ggK1Db_polarBilin_nondegenerate hx
  have hT0 := ggK1Db_exists_totallySingular_three (K := K) (V := V) hQ0 hdim
  let pair := ggK1Db_om4Pair hx hQ0 hT0
  let sub : (r : ↥Rep) → Fin (blk r).length → Subgroup (V ≃ₗ[K] V) := fun r j =>
    if (r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W)) then
      (if (j : ℕ) = 0 then pair.1 else pair.2)
    else A r
  have hfixed_nd : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W).Nondegenerate := by
    by_cases h1 : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
    · have hleft : ∀ v : W,
          (∀ w : W, (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W) v w = 0) →
            v = 0 := by
        intro v hv
        refine Subtype.ext (hx.eq_zero_of_polar_selfdual h1
          CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one.symm v.2
          fun w hw => ?_)
        have := hv ⟨w, hw⟩
        simpa using this
      exact ⟨hleft, fun w hw => hleft w (fun v => by
        have hv := hw v
        change QuadraticMap.polar Q (v : V) (w : V) = 0 at hv
        change QuadraticMap.polar Q (w : V) (v : V) = 0
        rw [QuadraticMap.polar_comm]
        exact hv)⟩
    · rw [show W = ⊥ from CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
        CFSG.RankThree.PartOne.KCOrthogonal.irreducible_X_sub_one
        CFSG.RankThree.PartOne.KCOrthogonal.monic_X_sub_one h1]
      exact ⟨fun v _ => Subsingleton.elim v 0, fun w _ => Subsingleton.elim w 0⟩
  have hrank : ∃ s : ℕ, Module.finrank K W = 2 * s := by
    by_cases h1 : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
    · have halt : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W).IsAlt := fun v => by
        change QuadraticMap.polar Q (v : V) (v : V) = 0
        rw [QuadraticMap.polar_self]
        simp [h2K]
      obtain ⟨s, hs⟩ := LinearMap.BilinForm.IsAlt.even_finrank halt hfixed_nd
      exact ⟨s, by omega⟩
    · refine ⟨0, ?_⟩
      rw [show W = ⊥ from CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
        CFSG.RankThree.PartOne.KCOrthogonal.irreducible_X_sub_one
        CFSG.RankThree.PartOne.KCOrthogonal.monic_X_sub_one h1, finrank_bot]
  have hlen : ∀ r : ↥Rep, (blk r).length =
      if (r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
          CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W)) then 2 else 1 := by
    intro r
    by_cases hr : (r : K[X]) = X - 1
    · have hk : kind r = ggK1DCo_Kind.om
          (if CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W) then true else false)
          (Module.finrank K W / 2) := by
        dsimp only [kind]; rw [if_pos hr]
      obtain ⟨s, hs⟩ := hrank
      have hlen0 := ggK1Db_kindOrbits_om_length nf (Module.finrank K W / 2)
        (if CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W) then true else false)
      dsimp only [blk]
      rw [hk, hlen0]
      have hsd : Module.finrank K W / 2 = s := by omega
      rw [hsd]
      by_cases hp4 : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W)
      · by_cases hs2 : s = 2
        · have h4 : Module.finrank K W = 4 := by omega
          simp [hs2, h4, hp4, hr]
        · have h4 : ¬ Module.finrank K W = 4 := by omega
          simp [hs2, h4, hp4, hr]
      · simp [hp4, hr]
    · have hnc : ¬ ((r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
          CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W))) := fun h => hr h.1
      rw [if_neg hnc]
      dsimp only [blk, kind]
      rw [if_neg hr]
      split_ifs
      · exact ggK1Db_kindOrbits_su_length nf _
      · exact ggK1Db_kindOrbits_sl_length nf _
  have hsub_le' : ∀ (r : ↥Rep) (j : Fin (blk r).length), sub r j ≤ A r := by
    intro r j
    by_cases hc : (r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W))
    · have hspec := ggK1Db_om4Pair_spec hx hQ0 hT0 hc.2.1 hc.2.2
      have hAr : A r = supportedBlock Q x (X - 1) ⊓ orthD := by
        dsimp only [A]; rw [if_pos hc.1]
      have hj : sub r j = if (j : ℕ) = 0 then pair.1 else pair.2 := by
        dsimp only [sub]; rw [if_pos hc]
      rw [hj, hAr]
      have hjoin' : pair.1 ⊔ pair.2 = supportedBlock Q x (X - 1) ⊓ orthD := hspec.2.2.1
      rw [← hjoin']
      split_ifs
      · exact le_sup_left
      · exact le_sup_right
    · have hj : sub r j = A r := by dsimp only [sub]; rw [if_neg hc]
      rw [hj]
  have hsub_join' : ∀ r : ↥Rep, ⨆ j : Fin (blk r).length, sub r j = A r := by
    intro r
    apply le_antisymm (iSup_le fun j => hsub_le' r j)
    by_cases hc : (r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W))
    · have hspec := ggK1Db_om4Pair_spec hx hQ0 hT0 hc.2.1 hc.2.2
      have hlen2 : (blk r).length = 2 := by rw [hlen r, if_pos hc]
      have hAr : A r = supportedBlock Q x (X - 1) ⊓ orthD := by
        dsimp only [A]; rw [if_pos hc.1]
      rw [hAr, ← hspec.2.2.1]
      refine sup_le ?_ ?_
      · have h0 : sub r ⟨0, by omega⟩ = pair.1 := by
          dsimp only [sub]; rw [if_pos hc]; simp
        rw [← h0]; exact le_iSup (fun j : Fin (blk r).length => sub r j) _
      · have h1 : sub r ⟨1, by omega⟩ = pair.2 := by
          dsimp only [sub]; rw [if_pos hc]; simp
        rw [← h1]; exact le_iSup (fun j : Fin (blk r).length => sub r j) _
    · have hlen1 : (blk r).length = 1 := by rw [hlen r, if_neg hc]
      have h0 : sub r ⟨0, by omega⟩ = A r := by
        dsimp only [sub]; rw [if_neg hc]
      rw [← h0]; exact le_iSup (fun j : Fin (blk r).length => sub r j) _
  have hcomm_blocks : ∀ i j : ↥Rep, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b := by
    intro i j hij a ha b hb
    have hai : a ∈ supportedBlock Q x (i : K[X]) := by
      dsimp only [A] at ha
      split_ifs at ha with hi
      · rw [hi]; exact (Subgroup.mem_inf.mp ha).1
      · exact ha
    have hbi : b ∈ supportedBlock Q x (j : K[X]) := by
      dsimp only [A] at hb
      split_ifs at hb with hj
      · rw [hj]; exact (Subgroup.mem_inf.mp hb).1
      · exact hb
    exact hx.blocks_commute hRep hij a b hai hbi
  have hA_le : ∀ r : ↥Rep, A r ≤ supportedBlock Q x (r : K[X]) := by
    intro r
    dsimp only [A]
    split_ifs with hr
    · rw [hr]; exact inf_le_left
    · exact le_rfl
  refine ⟨
    { ι := ↥Rep
      fintype := inferInstance
      A := A
      kind := kind
      blk := blk
      blk_eq := fun r => rfl
      rep := ⟨Rep, Equiv.refl _, hRep, fun r => rfl⟩
      sub := sub
      hsub_le := ?_
      hcomm := ?_
      sub_join := ?_
      hcomm_sub := ?_
      hjoin := ?_
      hindep := ?_
      htame := ?_
      isInternal := ?_
      fixed_eq := ?_
      fixed_nondegenerate := hfixed_nd
      nontrivial := ?_
      rank := hrank
      paired_model := ?_
      selfDual_model := ?_
      fixed_model := ?_ }⟩
  · exact hsub_le'
  · exact hcomm_blocks
  · exact hsub_join'
  ·
    intro r j j' hjj' a ha b hb
    by_cases hc : (r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W))
    · have hspec := ggK1Db_om4Pair_spec hx hQ0 hT0 hc.2.1 hc.2.2
      have hlen2 : (blk r).length = 2 := by rw [hlen r, if_pos hc]
      have hj : ∀ jj : Fin (blk r).length,
          sub r jj = if (jj : ℕ) = 0 then pair.1 else pair.2 := by
        intro jj; dsimp only [sub]; rw [if_pos hc]
      have hjlt : (j : ℕ) < 2 := by have := j.2; omega
      have hjlt' : (j' : ℕ) < 2 := by have := j'.2; omega
      have hne : (j : ℕ) ≠ (j' : ℕ) := fun h => hjj' (Fin.ext h)
      rw [hj] at ha
      rw [hj] at hb
      by_cases h0 : (j : ℕ) = 0
      · have h1 : ¬ (j' : ℕ) = 0 := fun h => hne (by omega)
        rw [if_pos h0] at ha
        rw [if_neg h1] at hb
        exact hspec.1 a ha b hb
      · have h1 : (j' : ℕ) = 0 := by omega
        rw [if_neg h0] at ha
        rw [if_pos h1] at hb
        exact (hspec.1 b hb a ha).symm
    · have hlen1 : (blk r).length = 1 := by rw [hlen r, if_neg hc]
      exfalso
      apply hjj'
      apply Fin.ext
      have := j.2
      have := j'.2
      omega
  ·
    have hQ : Q.polarBilin.Nondegenerate := ggK1Db_polarBilin_nondegenerate hx
    have hT := ggK1Db_exists_totallySingular_three (K := K) (V := V) hQ hdim
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hsigma : (⨆ q : Σ i, Fin (blk i).length, sub q.1 q.2) = ⨆ r : ↥Rep, A r := by
      apply le_antisymm
      · exact iSup_le fun q => (hsub_le' q.1 q.2).trans (le_iSup (fun r : ↥Rep => A r) q.1)
      · refine iSup_le fun r => ?_
        rw [← hsub_join' r]
        exact iSup_le fun j => le_iSup (fun q : Σ i, Fin (blk i).length => sub q.1 q.2) ⟨r, j⟩
    rw [hsigma]
    have hAofne : ∀ (r : ↥Rep), (r : K[X]) ≠ X - 1 → A r = supportedBlock Q x r := by
      intro r hr; dsimp only [A]; rw [if_neg hr]
    by_cases hf : (X - 1 : K[X]) ∈ Rep
    · let i0 : ↥Rep := ⟨X - 1, hf⟩
      let N : Subgroup (V ≃ₗ[K] V) := ⨆ (r : ↥Rep) (_ : r ≠ i0), supportedBlock Q x r
      have hne : ∀ (r : ↥Rep), r ≠ i0 → (r : K[X]) ≠ X - 1 := fun r hr h => hr (Subtype.ext h)
      have hNle : N ≤ CFSG.RankThree.Classical2.orthDerived Q := by
        refine iSup_le fun r => iSup_le fun hr => ?_
        exact ggK1Db_supportedBlock_le_orthDerived hx hodd hQ hT (hRep.1 r.2) (hne r hr)
      have hcommN : ∀ b ∈ supportedBlock Q x (X - 1), ∀ n ∈ N, b * n = n * b := by
        intro b hb n hn
        refine Subgroup.iSup_induction (fun r : ↥Rep => ⨆ (_ : r ≠ i0), supportedBlock Q x r)
          (C := fun z => b * z = z * b) hn ?_ (by simp) ?_
        · intro r z hz
          refine Subgroup.iSup_induction (fun _ : r ≠ i0 => supportedBlock Q x r)
            (C := fun z => b * z = z * b) hz ?_ (by simp) ?_
          · intro hr y hy
            exact (hx.blocks_commute hRep (fun h : i0 = r => hr h.symm) b y hb hy).eq
          · intro z w hz hw
            calc b * (z * w) = b * z * w := by rw [mul_assoc]
              _ = z * b * w := by rw [hz]
              _ = z * (b * w) := by rw [mul_assoc]
              _ = z * (w * b) := by rw [hw]
              _ = z * w * b := by rw [← mul_assoc]
        · intro z w hz hw
          calc b * (z * w) = b * z * w := by rw [mul_assoc]
            _ = z * b * w := by rw [hz]
            _ = z * (b * w) := by rw [mul_assoc]
            _ = z * (w * b) := by rw [hw]
            _ = z * w * b := by rw [← mul_assoc]
      have hBnorm : supportedBlock Q x (X - 1) ≤ Subgroup.normalizer N := by
        intro b hb
        rw [Subgroup.mem_normalizer_iff]
        intro n
        constructor
        · intro hn
          rw [hcommN b hb n hn]
          simpa using hn
        · intro hn
          have h4 : b⁻¹ * (b * n * b⁻¹) * b = b * n * b⁻¹ := by
            calc b⁻¹ * (b * n * b⁻¹) * b
                = b⁻¹ * ((b * n * b⁻¹) * b) := by rw [mul_assoc]
              _ = b⁻¹ * (b * (b * n * b⁻¹)) := by rw [← hcommN b hb (b * n * b⁻¹) hn]
              _ = b * n * b⁻¹ := by group
          have h5 : n = b⁻¹ * (b * n * b⁻¹) * b := by group
          rw [h5, h4]; exact hn
      have hsup : ∀ g ∈ supportedBlock Q x (X - 1) ⊔ N,
          ∃ b ∈ supportedBlock Q x (X - 1), ∃ n ∈ N, b * n = g := by
        intro g hg
        have h1 : g ∈ (supportedBlock Q x (X - 1) : Set (V ≃ₗ[K] V)) *
            (N : Set (V ≃ₗ[K] V)) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBnorm]
          exact hg
        exact h1
      have hC : isometryCentralizer Q x = supportedBlock Q x (X - 1) ⊔ N := by
        rw [← hx.blocks_iSup_eq hRep,
          iSup_split_single (fun r : ↥Rep => supportedBlock Q x r) i0]
      have hjoinA : (⨆ r : ↥Rep, A r) =
          (supportedBlock Q x (X - 1) ⊓ CFSG.RankThree.Classical2.orthDerived Q) ⊔ N := by
        rw [iSup_split_single (fun r : ↥Rep => A r) i0]
        congr 1
        · dsimp only [A]; rw [if_pos rfl]
        · exact iSup_congr fun r => iSup_congr fun hr => hAofne r (hne r hr)
      have hmod := ggK1Db_modular hsup hNle
      rw [hjoinA, hC]
      exact hmod.symm
    · have hne : ∀ (r : ↥Rep), (r : K[X]) ≠ X - 1 := fun r h => hf (h ▸ r.2)
      have hjoinA : (⨆ r : ↥Rep, A r) = ⨆ r : ↥Rep, supportedBlock Q x r :=
        iSup_congr fun r => hAofne r (hne r)
      have hNle : (⨆ r : ↥Rep, supportedBlock Q x r) ≤
          CFSG.RankThree.Classical2.orthDerived Q := by
        refine iSup_le fun r => ?_
        exact ggK1Db_supportedBlock_le_orthDerived hx hodd hQ hT (hRep.1 r.2) (hne r)
      rw [hjoinA, ← hx.blocks_iSup_eq hRep, inf_eq_left.mpr hNle]
  ·
    refine ggK1Db_iSupIndep_sigma A sub ?_ (fun i j hij a ha b hb => hcomm_blocks i j hij a ha b hb)
      hsub_le' ?_
    · exact (hx.blocks_iSupIndep hRep).mono hA_le
    · intro r
      rw [iSupIndep_def]
      intro j
      rw [Subgroup.disjoint_def]
      intro g hg hg'
      by_cases hc : (r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
          CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W))
      · have hspec := ggK1Db_om4Pair_spec hx hQ0 hT0 hc.2.1 hc.2.2
        have hlen2 : (blk r).length = 2 := by rw [hlen r, if_pos hc]
        have hj' : ∀ jj : Fin (blk r).length,
            sub r jj = if (jj : ℕ) = 0 then pair.1 else pair.2 := by
          intro jj; dsimp only [sub]; rw [if_pos hc]
        have hjlt : (j : ℕ) < 2 := by have := j.2; omega
        by_cases h0 : (j : ℕ) = 0
        ·
          have hother : (⨆ (j' : Fin (blk r).length) (_ : j' ≠ j), sub r j') ≤ pair.2 := by
            refine iSup_le fun j' => iSup_le fun hj'' => ?_
            have hne : (j' : ℕ) ≠ (j : ℕ) := fun h => hj'' (Fin.ext h)
            have hj'lt : (j' : ℕ) < 2 := by have := j'.2; omega
            have h1 : ¬ (j' : ℕ) = 0 := fun h => hne (by omega)
            rw [hj' j', if_neg h1]
          rw [hj' j, if_pos h0] at hg
          have hd := hspec.2.1
          rw [Subgroup.disjoint_def] at hd
          exact hd hg (hother hg')
        · have hother : (⨆ (j' : Fin (blk r).length) (_ : j' ≠ j), sub r j') ≤ pair.1 := by
            refine iSup_le fun j' => iSup_le fun hj'' => ?_
            have hne : (j' : ℕ) ≠ (j : ℕ) := fun h => hj'' (Fin.ext h)
            have hj'lt : (j' : ℕ) < 2 := by have := j'.2; omega
            have h1 : (j' : ℕ) = 0 := by omega
            rw [hj' j', if_pos h1]
          rw [hj' j, if_neg h0] at hg
          have hd := hspec.2.1
          rw [Subgroup.disjoint_def] at hd
          exact hd (hother hg') hg
      · have hlen1 : (blk r).length = 1 := by rw [hlen r, if_neg hc]
        have hbot : (⨆ (j' : Fin (blk r).length) (_ : j' ≠ j), sub r j') = ⊥ := by
          refine le_bot_iff.mp (iSup_le fun j' => iSup_le fun hj'' => ?_)
          exfalso
          apply hj''
          apply Fin.ext
          have := j.2
          have := j'.2
          omega
        rw [hbot] at hg'
        exact (Subgroup.mem_bot.mp hg')
  ·
    rintro ⟨r, j⟩
    by_cases hc : (r : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W))
    · have hspec := ggK1Db_om4Pair_spec hx hQ0 hT0 hc.2.1 hc.2.2
      have hsub : sub r j = if (j : ℕ) = 0 then pair.1 else pair.2 := by
        dsimp only [sub]; rw [if_pos hc]
      have hSL : Nonempty (↥(sub r j) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
        rw [hsub]
        by_cases h0 : (j : ℕ) = 0
        · rw [if_pos h0]; exact hspec.2.2.2.1
        · rw [if_neg h0]; exact hspec.2.2.2.2
      exact ggK1Db_tame_SL2 hnf hK hSL
    · have hsub : sub r j = A r := by dsimp only [sub]; rw [if_neg hc]
      rw [hsub]
      by_cases hr : (r : K[X]) = X - 1
      · have hA : A r = supportedBlock Q x (X - 1) ⊓ orthD := by
          dsimp only [A]; rw [if_pos hr]
        rw [hA]
        exact ggK1D_tame_fixed hx hQ0 hT0 (fun h => hc ⟨hr, h⟩)
      · have hA : A r = supportedBlock Q x (r : K[X]) := by
          dsimp only [A]; rw [if_neg hr]
        rw [hA]
        by_cases hself : reciprocalPolynomial (r : K[X]) = (r : K[X])
        · exact ggK1D_tame_selfDual hx hp hp2 hnf hK hdvd (hRep.1 r.2) hr hself.symm
        · exact ggK1D_tame_paired hx (hRep.1 r.2) (fun h => hself h.symm)
  ·
    exact ⟨(CFSG.RankThree.Classical.isInternal_primaryComponent_of_squarefree
        hx.squarefree_minpoly).submodule_iSupIndep,
      (CFSG.RankThree.Classical.isInternal_primaryComponent_of_squarefree
        hx.squarefree_minpoly).submodule_iSup_eq_top⟩
  ·
    exact (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace_eq_primaryComponent (x := x)).symm
  ·
    intro h hh h1
    exact CFSG.RankThree.Classical.orderOf_root_of_mem hp
      (by rw [← CFSG.RankThree.PartOne.KCOrthogonal.toLinearMap_pow, hx.pow_eq_one]; rfl) hh h1
  ·
    intro i m hm
    have hi1 : (i : K[X]) ∈ primaryFactors x.toLinearMap := hRep.1 i.2
    have hnot1 : ¬ (i : K[X]) = X - 1 := by
      intro h
      have hk : kind i = ggK1DCo_Kind.om
          (if CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W) then true else false)
          (Module.finrank K W / 2) := by
        dsimp only [kind]; rw [if_pos h]
      rw [hk] at hm
      exact absurd hm (by simp)
    have hnot2 : ¬ reciprocalPolynomial (i : K[X]) = (i : K[X]) := by
      intro h
      have hk : kind i = ggK1DCo_Kind.su (primaryMultiplicity x.toLinearMap (i : K[X])) := by
        dsimp only [kind]; rw [if_neg hnot1, if_pos h]
      rw [hk] at hm
      exact absurd hm (by simp)
    have hm' : m = primaryMultiplicity x.toLinearMap (i : K[X]) := by
      have hk : kind i = ggK1DCo_Kind.sl (primaryMultiplicity x.toLinearMap (i : K[X])) := by
        dsimp only [kind]; rw [if_neg hnot1, if_neg hnot2]
      rw [hk] at hm
      cases hm
      rfl
    have hne : (i : K[X]) ≠ reciprocalPolynomial (i : K[X]) := fun h => hnot2 h.symm
    have hA : A i = supportedBlock Q x (i : K[X]) := by
      dsimp only [A]; rw [if_neg hnot1]
    haveI : Fact (Irreducible (i : K[X])) := ⟨irreducible_of_mem_primaryFactors hi1⟩
    haveI : Fintype (AdjoinRoot (i : K[X])) := Fintype.ofFinite _
    refine ⟨AdjoinRoot (i : K[X]), inferInstance, inferInstance, (i : K[X]), hi1, hne, ?_, hm',
      ?_⟩
    · rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K),
        CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot]
    · rw [hA]
      exact ⟨(CFSG.RankThree.PartOne.KCOrthogonal.pairedBlockEquiv hx hi1 hne).trans
        ((Matrix.GeneralLinearGroup.toLin' (Module.finBasis (AdjoinRoot (i : K[X]))
          (primaryComponent x.toLinearMap (i : K[X])))).symm.trans
            (Equiv.reindexGL (finCongr hm'.symm) (AdjoinRoot (i : K[X]))))⟩
  ·
    intro i m hm
    have hi1 : (i : K[X]) ∈ primaryFactors x.toLinearMap := hRep.1 i.2
    have hnot1 : ¬ (i : K[X]) = X - 1 := by
      intro h
      have hk : kind i = ggK1DCo_Kind.om
          (if CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W) then true else false)
          (Module.finrank K W / 2) := by
        dsimp only [kind]; rw [if_pos h]
      rw [hk] at hm
      exact absurd hm (by simp)
    have hself' : (i : K[X]) = reciprocalPolynomial (i : K[X]) := by
      by_contra hne
      have hk : kind i = ggK1DCo_Kind.sl (primaryMultiplicity x.toLinearMap (i : K[X])) := by
        dsimp only [kind]; rw [if_neg hnot1, if_neg (fun h => hne h.symm)]
      rw [hk] at hm
      exact absurd hm (by simp)
    have hm' : m = primaryMultiplicity x.toLinearMap (i : K[X]) := by
      have hk : kind i = ggK1DCo_Kind.su (primaryMultiplicity x.toLinearMap (i : K[X])) := by
        dsimp only [kind]; rw [if_neg hnot1, if_pos hself'.symm]
      rw [hk] at hm
      cases hm
      rfl
    have hA : A i = supportedBlock Q x (i : K[X]) := by
      dsimp only [A]; rw [if_neg hnot1]
    haveI : Fact (Irreducible (i : K[X])) := ⟨irreducible_of_mem_primaryFactors hi1⟩
    haveI : Fintype (AdjoinRoot (i : K[X])) := Fintype.ofFinite _
    obtain ⟨hU, hndeg2, hcard⟩ :=
      ggK1Db_selfDual_card hx hp hp2 hnf hK hdvd hi1 hnot1 hself'
    obtain ⟨d, H, hndeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
      CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry.exists_selfDual_hermitian
        hx (hp.odd_of_ne_two hp2) hi1 hnot1 hself'
    have hd1 : d = 1 := by omega
    have hbar' : ∀ z, CFSG.RankThree.PartOne.KCOrthogonal.frobPow K (AdjoinRoot (i : K[X])) d z =
        hU.bar z := by
      intro z
      rw [hd1, CFSG.RankThree.PartOne.KCOrthogonal.frobPow_apply, hU.bar_apply, hK, pow_one]
    let B : primaryComponent x.toLinearMap (i : K[X]) →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap (i : K[X]) →ₗ[AdjoinRoot (i : K[X])]
          AdjoinRoot (i : K[X]) :=
      LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
        (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
        (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
    have hBH : ∀ u w, B u w = H u w := fun u w => rfl
    have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
    have hBl : B.SeparatingLeft := by
      intro u hu
      refine Subtype.ext (hx.eq_zero_of_polar_selfdual hi1 hself' u.2 fun w hw => ?_)
      have h1 := hH u ⟨w, hw⟩ 1
      rw [mul_one, one_smul] at h1
      have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
      rw [h2, map_zero] at h1
      exact h1.symm
    have hrange : (CFSG.RankThree.PartOne.KCOrthogonal.blockGL Q x (i : K[X])).range =
        CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B := by
      ext γ
      rw [hx.mem_range_blockGL_selfDual_iff hi1 hnot1 hself' H hH,
        CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
      exact Iff.rfl
    exact ⟨AdjoinRoot (i : K[X]), inferInstance, inferInstance, hU,
      primaryComponent x.toLinearMap (i : K[X]), inferInstance, inferInstance, inferInstance,
      B, hBsymm, hBl, by rw [hm'], by
        rw [hA]
        exact ⟨(MonoidHom.ofInjective (hx.blockGL_injective hi1)).trans
          (MulEquiv.subgroupCongr hrange)⟩⟩
  ·
    intro i eps m hm
    have hnot1 : (i : K[X]) = X - 1 := by
      by_contra hne
      by_cases hself : reciprocalPolynomial (i : K[X]) = (i : K[X])
      · have hk2 : kind i = ggK1DCo_Kind.su (primaryMultiplicity x.toLinearMap (i : K[X])) := by
          dsimp only [kind]; rw [if_neg hne, if_pos hself]
        rw [hk2] at hm; exact absurd hm (by simp)
      · have hk2 : kind i = ggK1DCo_Kind.sl (primaryMultiplicity x.toLinearMap (i : K[X])) := by
          dsimp only [kind]; rw [if_neg hne, if_neg hself]
        rw [hk2] at hm; exact absurd hm (by simp)
    have hk3 : kind i = ggK1DCo_Kind.om
        (if CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W) then true else false)
        (Module.finrank K W / 2) := by
      dsimp only [kind]; rw [if_pos hnot1]
    rw [hk3] at hm
    injection hm with heps hm2
    obtain ⟨s, hs⟩ := hrank
    have hfin : Module.finrank K W = 2 * m := by
      have hs2 : s = m := by
        rw [hs, Nat.mul_div_cancel_left s (by norm_num : 0 < 2)] at hm2
        exact hm2
      omega
    have hA : A i = supportedBlock Q x (X - 1) ⊓ orthD := by
      dsimp only [A]; rw [if_pos hnot1]
    have hepsiff : (eps = true ↔
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W)) := by
      rw [← heps]
      by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W)
      · rw [if_pos hp]; exact ⟨fun _ => hp, fun _ => rfl⟩
      · rw [if_neg hp]; exact ⟨fun h => absurd h (by simp), fun h => absurd h hp⟩
    refine ⟨hfin, hepsiff, ?_, ?_, ?_, ?_⟩
    · intro hm3
      by_cases hp : eps = true
      · rw [if_pos hp, hA]
        exact ggK1D_fixed_omega hx hQ0 hT0 hm3 hfin (hepsiff.mp hp)
      · rw [if_neg hp, hA]
        exact ggK1D_fixed_omegaMinus hx hQ0 hT0 hm3 hfin (fun h => hp (hepsiff.mpr h))
    · intro hm2' hp j
      have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W) := hepsiff.mp hp
      have hfin4 : Module.finrank K W = 4 := by omega
      have hspec := ggK1Db_om4Pair_spec hx hQ0 hT0 hfin4 hplus
      have hc : (i : K[X]) = X - 1 ∧ (Module.finrank K W = 4 ∧
          CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict W)) := ⟨hnot1, hfin4, hplus⟩
      have hsub : sub i j = if (j : ℕ) = 0 then pair.1 else pair.2 := by
        dsimp only [sub]; rw [if_pos hc]
      rw [hsub]
      by_cases h0 : (j : ℕ) = 0
      · rw [if_pos h0]; exact hspec.2.2.2.1
      · rw [if_neg h0]; exact hspec.2.2.2.2
    · intro hm2' hp
      rw [hA]
      exact ggK1D_fixed_sl2 hx hQ0 hT0 hm2' hfin
        (fun h => Bool.false_ne_true (hp.symm.trans (hepsiff.mpr h)))
    · intro hm1
      rw [hA]
      exact ggK1D_fixed_abelian hx hQ0 hT0 hm1 hfin
theorem ggK1D_omegaLift_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1) :
    OddOrderIsometry (CFSG.StandardType.TableBOrth.qPlusForm K r) p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) := by
  have hxp : (x : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQPlus K r)) =>
      (y : GL (Fin r ⊕ Fin r) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Db_lin_apply, TableBOrth.coe_qPlusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Db_lin_pow, hxp]
    ext v; rw [ggK1Db_lin_apply]; simp
  · exact ggK1Db_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qPlusForm (K := K) r).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

theorem ggK1D_omegaLift_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1) :
    OddOrderIsometry (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c) p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
  have hxp : (x : GL (LargeEvenMinusIdx (r - 1)) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) =>
      (y : GL (LargeEvenMinusIdx (r - 1)) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Db_lin_apply, TableBOrth.coe_qMinusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Db_lin_pow, hxp]
    ext v; rw [ggK1Db_lin_apply]; simp
  · exact ggK1Db_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qMinusForm (K := K) (r - 1) hirr).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

end CFSG.StandardType

end
