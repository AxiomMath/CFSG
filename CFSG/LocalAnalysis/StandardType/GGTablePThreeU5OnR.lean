module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniLift
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU5Shape
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniSplit
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU5Par
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOutRank
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockLift
import CFSG.RankThree.PartOne.KF.UnitaryDiag
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
import CFSG.Assembly.E6FourLabelArith
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

section Uni5OnRAux

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KFU CFSG.StandardType CFSG.LinearGroups

private theorem isHermIso_iff_stdHerm {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    {A : Matrix (Fin n) (Fin n) K} :
    IsHermIsometry (2 ^ f) A ↔
      ∀ x y, stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  simp only [IsHermIsometry, stdHermForm_apply, h.bar_apply]

private theorem unitary_of_isHerm {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    {g : GL (Fin n) K} (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    g ∈ primeFormUnitary h (idGram K n) := by
  have hM := SUTB.map_bar_transpose_mul_of_isometry h ((isHermIso_iff_stdHerm h).mp hg)
  rw [mem_primeFormUnitary, idGram]
  simpa using hM

private theorem norm_det_of_isHerm {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    {g : GL (Fin n) K} (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    h.norm ((g : Matrix (Fin n) (Fin n) K).det) = 1 :=
  UnitaryHigher.norm_det_eq_one h (1 : GL (Fin n) K)
    (by simpa [idGram] using unitary_of_isHerm h hg)

private theorem isometry_normalizes_SU {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    {g : GL (Fin n) K} (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    ∀ k ∈ LargeEvenSUGroup (Fin n) K (2 ^ f), g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K (2 ^ f) := by
  have hmem := unitary_of_isHerm h hg
  intro k hk
  have hk' : k ∈ unitarySU 2 f K n := hk
  exact conj_mem_unitarySU h hmem hk'

private theorem isConjBy_mul {n q : ℕ} {K : Type} [Field K] {g g' : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q, g' * k * g'⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h1 : IsConjBy g a) (h2 : IsConjBy g' a') : IsConjBy (g * g') (a * a') := by
  intro x x' hx
  let x'' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g' * (x : GL (Fin n) K) * g'⁻¹, hnorm x x.2⟩
  have hx'' : (x'' : GL (Fin n) K) = g' * (x : GL (Fin n) K) * g'⁻¹ := rfl
  have h2' : a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'' := h2 x x'' hx''
  have h1' : a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' :=
    h1 x'' x' (by
      show (x' : GL (Fin n) K) = g * (x'' : GL (Fin n) K) * g⁻¹
      rw [hx, hx'']
      group)
  calc (a * a') (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a (a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)) := rfl
    _ = a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') := by rw [h2']
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := h1'

private theorem isConjBy_inv {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)} (h1 : IsConjBy g a) : IsConjBy g⁻¹ a⁻¹ := by
  intro x x' hx
  have hrel : (x : GL (Fin n) K) = g * (x' : GL (Fin n) K) * g⁻¹ := by rw [hx]; group
  have h := h1 x' x hrel
  calc a⁻¹ (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a⁻¹ (a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x')) := by rw [← h]
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

private theorem isConjBy_one {n q : ℕ} {K : Type} [Field K] :
    IsConjBy (1 : GL (Fin n) K) (1 : MulAut (PSUg n K q)) := by
  intro x x' hx
  have hxx : x' = x := Subtype.ext (by simpa using hx)
  subst hxx
  rw [MulAut.one_apply]

private theorem isConjBy_eq {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q, g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) (h' : IsConjBy g a') : a = a' := by
  ext y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K q)) y
  subst hx
  let x' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g * (x : GL (Fin n) K) * g⁻¹, hnorm x x.2⟩
  have hx' : (x' : GL (Fin n) K) = g * (x : GL (Fin n) K) * g⁻¹ := rfl
  rw [h x x' hx', h' x x' hx']

private theorem isConjBy_mul_central_iff {n q : ℕ} {K : Type} [Field K] {s : GL (Fin n) K}
    (hs : ∀ x : GL (Fin n) K, s * x = x * s) {A : GL (Fin n) K} {a : MulAut (PSUg n K q)} :
    IsConjBy (s * A) a ↔ IsConjBy A a := by
  have hrel_eq : ∀ x : GL (Fin n) K, (s * A) * x * (s * A)⁻¹ = A * x * A⁻¹ := by
    intro x
    rw [_root_.mul_inv_rev]
    calc (s * A) * x * (A⁻¹ * s⁻¹) = s * (A * x * A⁻¹) * s⁻¹ := by group
      _ = A * x * A⁻¹ := by rw [hs]; group
  constructor
  · intro h x x' hx
    exact h x x' (by
      show (x' : GL (Fin n) K) = (s * A) * (x : GL (Fin n) K) * (s * A)⁻¹
      rw [hx, hrel_eq x])
  · intro h x x' hx
    exact h x x' (by
      show (x' : GL (Fin n) K) = A * (x : GL (Fin n) K) * A⁻¹
      rw [hx, ← hrel_eq x])

private theorem isConjBy_scalar_one {n q : ℕ} {K : Type} [Field K] (c : Kˣ) :
    IsConjBy (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K)
      (1 : MulAut (PSUg n K q)) := by
  simpa using (isConjBy_mul_central_iff (s := GeneralLinearGroup.scalar (Fin n) c)
    (fun x => (commute_scalar c x).eq.symm) (A := (1 : GL (Fin n) K))
    (a := (1 : MulAut (PSUg n K q)))).mpr isConjBy_one

private theorem isConjBy_pow {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q, g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) (m : ℕ) : IsConjBy (g ^ m) (a ^ m) := by
  induction m with
  | zero => simpa using (isConjBy_one (n := n) (q := q) (K := K))
  | succ m ih =>
      rw [pow_succ, pow_succ]
      exact isConjBy_mul hnorm ih h

private theorem isConjBy_zpow {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q, g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) (m : ℤ) : IsConjBy (g ^ m) (a ^ m) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg m
  · rw [hm, zpow_natCast]
    exact isConjBy_pow hnorm h m
  · rw [hm]
    have h1 : (g : GL (Fin n) K) ^ (-(m : ℤ)) = ((g : GL (Fin n) K) ^ m)⁻¹ := by
      rw [_root_.zpow_neg, zpow_natCast]
    have h2 : a ^ (-(m : ℤ)) = (a ^ m)⁻¹ := by
      rw [_root_.zpow_neg, zpow_natCast]
    rw [h1, h2]
    exact isConjBy_inv (isConjBy_pow hnorm h m)

private lemma mod_three_eq_two_of_dvd_add_one {q : ℕ} (h : 3 ∣ q + 1) : q % 3 = 2 := by
  obtain ⟨k, hk⟩ := h
  omega

private lemma pow_two_pow_eq_sq_of_cube {K : Type} [Field K] {μ : K} (hμ : μ ^ 3 = 1) {f : ℕ}
    (hf : 2 ^ f % 3 = 2) : μ ^ (2 ^ f) = μ ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = 3 * m + 2 := ⟨2 ^ f / 3, by omega⟩
  rw [hm, pow_add, pow_mul, hμ, one_pow, one_mul]

private lemma eigenspace_orthogonal_of_unitary {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hKf : Nat.card K = (2 ^ f) ^ 2)
    {D : Module.End K (Fin n → K)}
    (hD : ∀ u v : Fin n → K,
      (CFSG.LieType.BorelTits.unitaryForm 2 f hKf n).β (D u) (D v) =
      (CFSG.LieType.BorelTits.unitaryForm 2 f hKf n).β u v)
    {μ ν : K} (hμ3 : μ ^ 3 = 1) (hν3 : ν ^ 3 = 1) (hμν : μ ≠ ν) (hq3 : 3 ∣ 2 ^ f + 1)
    {u v : Fin n → K} (hu : u ∈ D.eigenspace μ) (hv : v ∈ D.eigenspace ν) :
    (CFSG.LieType.BorelTits.unitaryForm 2 f hKf n).β u v = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := CFSG.LieType.BorelTits.unitaryForm 2 f hKf n with hF
  rw [Module.End.mem_eigenspace_iff] at hu hv
  have h1 : F.β (D u) (D v) = F.β u v := hD u v
  rw [hu, hv, F.smul_left, F.smul_right] at h1
  have hσ : F.σ μ = μ ^ (2 ^ f) := by
    rw [hF]
    exact CFSG.LieType.BorelTits.unitaryInvolution_apply K 2 f μ
  rw [hσ] at h1
  have hpow : μ ^ (2 ^ f) = μ ^ 2 :=
    pow_two_pow_eq_sq_of_cube hμ3 (mod_three_eq_two_of_dvd_add_one hq3)
  rw [hpow] at h1
  have hcoef : μ ^ 2 * ν ≠ 1 := by
    intro hc
    apply hμν
    have hμμ : μ * μ ^ 2 = μ ^ 3 := by
      rw [← pow_succ']
    have h2 : μ * (μ ^ 2 * ν) = μ := by rw [hc, mul_one]
    rw [← mul_assoc, hμμ, hμ3, one_mul] at h2
    exact h2.symm
  have h2 : μ ^ 2 * ν * F.β u v = F.β u v := by
    rw [mul_assoc]; exact h1
  have : (μ ^ 2 * ν - 1) * F.β u v = 0 := by
    rw [sub_mul, one_mul, h2, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hcoef)

private lemma eigenspace_disjoint_of_ne {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (D : Module.End K V) {μ ν : K} (h : μ ≠ ν) :
    Disjoint (D.eigenspace μ) (D.eigenspace ν) := by
  refine disjoint_iff_inf_le.mpr ?_
  intro x hx
  rw [Submodule.mem_bot]
  rw [Submodule.mem_inf] at hx
  obtain ⟨hμ, hν⟩ := hx
  rw [Module.End.mem_eigenspace_iff] at hμ hν
  have : (μ - ν) • x = 0 := by rw [sub_smul, ← hμ, ← hν, sub_self]
  rcases smul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) h
  · exact h0

private lemma finrank_sup_of_disjoint {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {W1 W2 : Submodule K V}
    (h : Disjoint W1 W2) :
    Module.finrank K ↥(W1 ⊔ W2) = Module.finrank K ↥W1 + Module.finrank K ↥W2 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W1 W2
  have h2 : W1 ⊓ W2 = ⊥ := le_bot_iff.mp h.le_bot
  rw [h2, finrank_bot] at h1
  omega

private lemma eigenspace_sup_disjoint_of_ne {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (D : Module.End K V)
    {μ ν κ : K} (hμν : μ ≠ ν) (hμκ : μ ≠ κ) (hνκ : ν ≠ κ) :
    Disjoint (D.eigenspace μ ⊔ D.eigenspace ν) (D.eigenspace κ) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  rw [Submodule.mem_bot]
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv1, hvκ⟩ := hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv1
  rw [Module.End.mem_eigenspace_iff] at hvκ hx hy
  have hrel : (μ - κ) • x = (κ - ν) • y := by
    have h := hvκ
    rw [map_add, hx, hy, smul_add] at h
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]
    rw [add_comm (κ • y) (κ • x)]
    exact h
  have hxμ : (μ - κ) • x ∈ D.eigenspace μ :=
    Module.End.mem_eigenspace_iff.mpr (by
      rw [map_smul, hx, smul_smul, smul_smul, mul_comm])
  have hyν : (κ - ν) • y ∈ D.eigenspace ν :=
    Module.End.mem_eigenspace_iff.mpr (by
      rw [map_smul, hy, smul_smul, smul_smul, mul_comm])
  have hx0 : x = 0 := by
    have hbot : D.eigenspace μ ⊓ D.eigenspace ν = ⊥ :=
      le_bot_iff.mp (eigenspace_disjoint_of_ne D hμν).le_bot
    have hmem : (μ - κ) • x ∈ D.eigenspace μ ⊓ D.eigenspace ν :=
      ⟨hxμ, hrel.symm ▸ hyν⟩
    rw [hbot, Submodule.mem_bot] at hmem
    rcases smul_eq_zero.mp hmem with h | h
    · exact absurd (sub_eq_zero.mp h) hμκ
    · exact h
  have hy0 : y = 0 := by
    have : (κ - ν) • y = 0 := by rw [← hrel, hx0, smul_zero]
    rcases smul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hνκ.symm
    · exact h
  rw [hx0, hy0, zero_add]

end Uni5OnRAux

section Uni5OnRMain

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KFU CFSG.StandardType CFSG.LinearGroups CFSG.Open

theorem uni5_kg7_on_R_holds :
    Uni5KG7OnR := by
  classical
  intro K _ _ _ q hK hq3 Ā δ' J' hRD hcardĀ hĀI hJ
  obtain ⟨Ahat, hL, hAhat_card⟩ := uni_lift hK (by norm_num : 4 ≤ 5) hĀI
  obtain ⟨f, hf1, hqpow⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hqpow
  have h : UnitaryFieldData 2 f K := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd f := (gffa2_three_dvd_pow_add_one_iff f).mp hq3
  have h5 : ¬ 5 ∣ 2 ^ f + 1 := by
    intro hdvd
    have hmod : f % 4 = 2 := CFSG.Assembly.e6Four_five_dvd_two_pow_add_one.mp hdvd
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcop : Nat.Coprime 5 (2 ^ f + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5
  let A : Subgroup (GL (Fin 5) K) := Ahat ⊓ LargeEvenSUGroup (Fin 5) K (2 ^ f)
  have hAleAhat : A ≤ Ahat := inf_le_left
  have hAleSU : A ≤ StatedSU 5 (2 ^ f) K := inf_le_right
  let ψ : A → Ā := fun a =>
    ⟨Classical.choose (hL.induces (a : GL (Fin 5) K) (hAleAhat a.2)),
      (Classical.choose_spec (hL.induces (a : GL (Fin 5) K) (hAleAhat a.2))).1⟩
  have hψ : ∀ a : A, IsConjBy (a : GL (Fin 5) K) (ψ a : MulAut (PSUg 5 K (2 ^ f))) := by
    intro a
    simpa using (Classical.choose_spec (hL.induces (a : GL (Fin 5) K) (hAleAhat a.2))).2
  let Z : Subgroup Kˣ := (Units.map h.normHom).ker
  have hZpow : ∀ c ∈ Z, (c : K) ^ (2 ^ f + 1) = 1 := by
    intro c hc
    have := (h.mem_ker_normUnits).mp hc
    rwa [h.norm_eq_pow] at this
  have hZtors : ∀ z ∈ Z, z ^ 5 = 1 → z = 1 := by
    intro z hz hz5
    have hzq : z ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      simpa using hZpow z hz
    have h1 : orderOf z ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hz5
    have h2 : orderOf z ∣ 2 ^ f + 1 := orderOf_dvd_iff_pow_eq_one.mpr hzq
    have h3 : orderOf z ∣ Nat.gcd 5 (2 ^ f + 1) := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have h5surj : ∀ u : Z, ∃ c : Z, c ^ 5 = u := by
    have hinj : Function.Injective (fun z : Z => z ^ 5) := by
      intro x y hxy
      have hxy' : (x : Kˣ) ^ 5 = (y : Kˣ) ^ 5 := by
        simpa using congrArg (fun z : Z => (z : Kˣ)) hxy
      have hmem : (x : Kˣ) * (y : Kˣ)⁻¹ ∈ Z := Z.mul_mem x.2 (Z.inv_mem y.2)
      have h1 : ((x : Kˣ) * (y : Kˣ)⁻¹) ^ 5 = 1 := by
        rw [mul_pow, hxy', inv_pow, mul_inv_cancel]
      have h2 : (x : Kˣ) * (y : Kˣ)⁻¹ = 1 := hZtors _ hmem h1
      exact Subtype.ext (mul_inv_eq_one.mp h2)
    exact Finite.injective_iff_surjective.mp hinj
  have hscalarAhat : ∀ c : Kˣ, c ∈ Z →
      (GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) ∈ Ahat := by
    intro c hc
    apply hL.scalars
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hZpow c hc
  have hscalarU : ∀ c : Kˣ, c ∈ Z →
      (GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) ∈ primeFormUnitary h (idGram K 5) :=
    fun c hc => SUTB.scalar_mem_primeFormUnitary_idGram h (hZpow c hc)
  have hscalar_eq_one : ∀ z : GL (Fin 5) K, z ∈ A →
      IsConjBy z (1 : MulAut (PSUg 5 K (2 ^ f))) → z = 1 := by
    intro z hz hzconj
    obtain ⟨c, hc1, hceq⟩ := hL.ker z (hAleAhat hz) hzconj
    have hdetunit : GeneralLinearGroup.det z = 1 := by
      apply Units.ext
      simpa using ((mem_unitarySU_iff h).mp (hAleSU hz)).1
    have hc5 : c ^ 5 = 1 := by
      have h1 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 5) c) = 1 := by
        rw [← hceq]; exact hdetunit
      rw [GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
      exact h1
    have hc1' : c = 1 := by
      have h1 : orderOf c ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hc5
      have h2 : orderOf c ∣ 2 ^ f + 1 := orderOf_dvd_iff_pow_eq_one.mpr hc1
      have h3 : orderOf c ∣ Nat.gcd 5 (2 ^ f + 1) := Nat.dvd_gcd h1 h2
      rw [hcop.gcd_eq_one] at h3
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    rw [hceq, hc1']; simp
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨g, hgA, hgconj⟩ := hL.onto a a.2
    have hgU : g ∈ primeFormUnitary h (idGram K 5) := unitary_of_isHerm h (hL.iso g hgA)
    have hdetZ : (GeneralLinearGroup.det g : Kˣ) ∈ Z := by
      apply (h.mem_ker_normUnits).mpr
      simpa using norm_det_of_isHerm h (hL.iso g hgA)
    obtain ⟨c, hc5⟩ := h5surj ⟨(GeneralLinearGroup.det g : Kˣ), hdetZ⟩
    have hc5' : (c : Kˣ) ^ 5 = GeneralLinearGroup.det g := by
      simpa using congrArg (fun z : Z => (z : Kˣ)) hc5
    have hsc : (GeneralLinearGroup.scalar (Fin 5) (c : Kˣ) : GL (Fin 5) K) ∈ Ahat :=
      hscalarAhat (c : Kˣ) c.2
    have hscU := hscalarU (c : Kˣ) c.2
    let g' : GL (Fin 5) K := g * (GeneralLinearGroup.scalar (Fin 5) (c : Kˣ) : GL (Fin 5) K)⁻¹
    have hg'A : g' ∈ A := by
      refine Subgroup.mem_inf.mpr ⟨Ahat.mul_mem hgA (Ahat.inv_mem hsc), ?_⟩
      have hg'U : g' ∈ primeFormUnitary h (idGram K 5) :=
        (primeFormUnitary h (idGram K 5)).mul_mem hgU
          ((primeFormUnitary h (idGram K 5)).inv_mem hscU)
      have hdetg' : (g' : Matrix (Fin 5) (Fin 5) K).det = 1 := by
        have h1 : GeneralLinearGroup.det g' = 1 := by
          rw [show GeneralLinearGroup.det g' = GeneralLinearGroup.det g *
              (GeneralLinearGroup.det
                (GeneralLinearGroup.scalar (Fin 5) (c : Kˣ) : GL (Fin 5) K))⁻¹ by
            simp only [g', map_mul, map_inv]]
          rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, hc5', mul_inv_cancel]
        simpa using congrArg (fun u : Kˣ => (u : K)) h1
      have hg'SU : g' ∈ unitarySU 2 f K 5 := by
        refine (mem_unitarySU_iff h).mpr ⟨hdetg', ?_⟩
        have := (mem_primeFormUnitary (h := h) (C := idGram K 5)).mp hg'U
        simpa [idGram] using this
      exact hg'SU
    refine ⟨⟨g', hg'A⟩, ?_⟩
    have hconj' : IsConjBy g' (a : MulAut (PSUg 5 K (2 ^ f))) := by
      have hnorm_sc : ∀ k ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f),
          (GeneralLinearGroup.scalar (Fin 5) (c : Kˣ) : GL (Fin 5) K)⁻¹ * k *
            ((GeneralLinearGroup.scalar (Fin 5) (c : Kˣ) : GL (Fin 5) K)⁻¹)⁻¹ ∈
              LargeEvenSUGroup (Fin 5) K (2 ^ f) :=
        fun k hk => conj_mem_unitarySU h ((primeFormUnitary h (idGram K 5)).inv_mem hscU) hk
      have hh := isConjBy_mul (n := 5) (q := 2 ^ f) (K := K) hnorm_sc hgconj
        (isConjBy_inv (isConjBy_scalar_one (n := 5) (q := 2 ^ f) (K := K) (c : Kˣ)))
      simpa [g'] using hh
    have hψ' : IsConjBy g' ((ψ ⟨g', hg'A⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f))) := by
      simpa using hψ ⟨g', hg'A⟩
    have hnorm_g' : ∀ k ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f),
        g' * k * g'⁻¹ ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f) :=
      isometry_normalizes_SU h (hL.iso g' (hAleAhat hg'A))
    exact Subtype.ext (isConjBy_eq hnorm_g' hψ' hconj')
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have hnorm_yinv : ∀ k ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f),
        (y : GL (Fin 5) K)⁻¹ * k * ((y : GL (Fin 5) K)⁻¹)⁻¹ ∈
          LargeEvenSUGroup (Fin 5) K (2 ^ f) :=
      isometry_normalizes_SU h (hL.iso (y : GL (Fin 5) K)⁻¹ (Ahat.inv_mem (hAleAhat y.2)))
    have h1 : IsConjBy ((x : GL (Fin 5) K) * (y : GL (Fin 5) K)⁻¹)
        ((ψ x) * (ψ y)⁻¹ : MulAut (PSUg 5 K (2 ^ f))) :=
      isConjBy_mul hnorm_yinv (hψ x) (isConjBy_inv (hψ y))
    have h3 : IsConjBy ((x : GL (Fin 5) K) * (y : GL (Fin 5) K)⁻¹)
        (1 : MulAut (PSUg 5 K (2 ^ f))) := by
      have hxy' : ((ψ x : Ā) : MulAut (PSUg 5 K (2 ^ f))) =
          ((ψ y : Ā) : MulAut (PSUg 5 K (2 ^ f))) := by rw [hxy]
      rw [hxy'] at h1
      simpa using h1
    have hmemA : (x : GL (Fin 5) K) * (y : GL (Fin 5) K)⁻¹ ∈ A :=
      A.mul_mem x.2 (A.inv_mem y.2)
    have hz1 : (x : GL (Fin 5) K) * (y : GL (Fin 5) K)⁻¹ = 1 := hscalar_eq_one _ hmemA h3
    apply Subtype.ext
    exact mul_inv_eq_one.mp hz1
  have hAcard : Nat.card A = 3 ^ 3 := by
    have hbij : Nat.card A = Nat.card Ā := Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)
    rw [hbij, hcardĀ]
  have hAe : IsElemAbelian 3 A := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro x y
      apply Subtype.ext
      have hxy : IsConjBy ((x : GL (Fin 5) K) * (y : GL (Fin 5) K))
          ((ψ x) * (ψ y) : MulAut (PSUg 5 K (2 ^ f))) :=
        isConjBy_mul (isometry_normalizes_SU h (hL.iso (y : GL (Fin 5) K) (hAleAhat y.2)))
          (hψ x) (hψ y)
      have hyx : IsConjBy ((y : GL (Fin 5) K) * (x : GL (Fin 5) K))
          ((ψ y) * (ψ x) : MulAut (PSUg 5 K (2 ^ f))) :=
        isConjBy_mul (isometry_normalizes_SU h (hL.iso (x : GL (Fin 5) K) (hAleAhat x.2)))
          (hψ y) (hψ x)
      have hcommψ : (ψ x) * (ψ y) = (ψ y) * (ψ x) := hRD.elem.1.is_comm.comm (ψ x) (ψ y)
      have hC : IsConjBy (((x : GL (Fin 5) K) * (y : GL (Fin 5) K)) *
          ((y : GL (Fin 5) K) * (x : GL (Fin 5) K))⁻¹) (1 : MulAut (PSUg 5 K (2 ^ f))) := by
        have hnorm : ∀ k ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f),
            ((y : GL (Fin 5) K) * (x : GL (Fin 5) K))⁻¹ * k *
              (((y : GL (Fin 5) K) * (x : GL (Fin 5) K))⁻¹)⁻¹ ∈
                LargeEvenSUGroup (Fin 5) K (2 ^ f) :=
          isometry_normalizes_SU h (hL.iso _ (Ahat.inv_mem
            (Ahat.mul_mem (hAleAhat y.2) (hAleAhat x.2))))
        have hh := isConjBy_mul hnorm hxy (isConjBy_inv hyx)
        have hcommψ' : ((ψ x : Ā) : MulAut (PSUg 5 K (2 ^ f))) * ((ψ y : Ā) : MulAut (PSUg 5 K (2 ^ f))) =
            ((ψ y : Ā) : MulAut (PSUg 5 K (2 ^ f))) * ((ψ x : Ā) : MulAut (PSUg 5 K (2 ^ f))) := by
          simpa using congrArg (fun z : Ā => (z : MulAut (PSUg 5 K (2 ^ f)))) hcommψ
        rw [hcommψ'] at hh
        simpa using hh
      have hmemA : (((x : GL (Fin 5) K) * (y : GL (Fin 5) K)) *
          ((y : GL (Fin 5) K) * (x : GL (Fin 5) K))⁻¹) ∈ A :=
        A.mul_mem (A.mul_mem x.2 y.2) (A.inv_mem (A.mul_mem y.2 x.2))
      exact mul_inv_eq_one.mp (hscalar_eq_one _ hmemA hC)
    · intro x hx
      have hψx : IsConjBy (x : GL (Fin 5) K)
          ((ψ ⟨x, hx⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f))) := by simpa using hψ ⟨x, hx⟩
      have hx3 : IsConjBy ((x : GL (Fin 5) K) ^ 3)
          (((ψ ⟨x, hx⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f))) ^ 3) :=
        isConjBy_pow (isometry_normalizes_SU h (hL.iso (x : GL (Fin 5) K) (hAleAhat hx))) hψx 3
      have hx3one : (((ψ ⟨x, hx⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f)))) ^ 3 = 1 :=
        hRD.elem.2 (ψ ⟨x, hx⟩) (ψ ⟨x, hx⟩).2
      have hC : IsConjBy ((x : GL (Fin 5) K) ^ 3) (1 : MulAut (PSUg 5 K (2 ^ f))) := by
        rw [← hx3one]; exact hx3
      exact hscalar_eq_one _ (A.pow_mem hx 3) hC
  obtain ⟨dA, hdAψ⟩ := hsurj ⟨δ', hRD.mem⟩
  let d : GL (Fin 5) K := dA
  have hdA : d ∈ A := dA.2
  have hdconj : IsConjBy d δ' := by
    have h1 := hψ dA
    have h2 : ((ψ dA : Ā) : MulAut (PSUg 5 K (2 ^ f))) = δ' := by rw [hdAψ]
    rwa [h2] at h1
  have hdSU : d ∈ StatedSU 5 (2 ^ f) K := hAleSU hdA
  have hd3 : d ^ 3 = 1 := by
    have hδ3 : δ' ^ 3 = 1 := hRD.elem.2 δ' hRD.mem
    have hconj : IsConjBy (d ^ 3) (δ' ^ 3) :=
      isConjBy_pow (isometry_normalizes_SU h (hL.iso d (hAleAhat hdA))) hdconj 3
    rw [hδ3] at hconj
    exact hscalar_eq_one _ (A.pow_mem hdA 3) hconj
  have hd1 : d ≠ 1 := by
    intro hd1eq
    have hconj1 : IsConjBy (1 : GL (Fin 5) K) δ' := by rw [← hd1eq]; exact hdconj
    have hh := isConjBy_eq (n := 5) (q := 2 ^ f) (K := K) (g := (1 : GL (Fin 5) K))
      (fun k hk => by simpa using hk) (isConjBy_one) hconj1
    exact hRD.ne_one hh.symm
  obtain ⟨F, hFld, hFfin, q', hFcard, hq', htw⟩ := hJ
  obtain ⟨α, hα3, hαdim, hαother, hJdesc⟩ :=
    uni5_shape hK hq3 hdSU hd3 hd1 hdconj hRD.comp hRD.uniq hFcard hq' htw
  let Ff : CFSG.LieType.BorelTits.ReflForm K (Fin 5 → K) :=
    CFSG.LieType.BorelTits.unitaryForm 2 f hK 5
  let D : Module.End K (Fin 5 → K) := Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)
  have hDapply : ∀ u : Fin 5 → K, D u = (d : Matrix (Fin 5) (Fin 5) K) *ᵥ u := fun u => rfl
  have hDiso : ∀ u v : Fin 5 → K, Ff.β (D u) (D v) = Ff.β u v := by
    intro u v
    rw [hDapply, hDapply]
    exact CFSG.LieType.BorelTits.statedSU_preserves hK hdSU u v
  let Eα : Submodule K (Fin 5 → K) := D.eigenspace α
  have hEα3 : Module.finrank K Eα = 3 := hαdim
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3card : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      simpa using this
    rw [hsq]
    exact dvd_mul_of_dvd_left hq3 _
  obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' 3 h3card
  have hω3u : ωu ^ 3 = 1 := by rw [← hωu]; exact pow_orderOf_eq_one ωu
  have hω1u : ωu ≠ 1 := by rintro rfl; rw [orderOf_one] at hωu; omega
  have hω3 : ((ωu : K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω3u, Units.val_one]
  have hω1 : (ωu : K) ≠ 1 := fun hh => hω1u (Units.ext hh)
  let β : K := α * (ωu : K)
  let γ : K := α * (ωu : K) ^ 2
  have hβ3 : β ^ 3 = 1 := by
    simp only [β, mul_pow, hα3, hω3, one_mul]
  have hγ3 : γ ^ 3 = 1 := by
    simp only [γ, mul_pow, hα3, one_mul]
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hβα : β ≠ α := by
    intro hh
    have h' : α * (ωu : K) = α := hh
    exact hω1 (mul_left_cancel₀ hα0 (by rw [h', mul_one]))
  have hγα : γ ≠ α := by
    intro hh
    have h' : α * (ωu : K) ^ 2 = α := hh
    have hω2 : (ωu : K) ^ 2 = 1 := mul_left_cancel₀ hα0 (by rw [h', mul_one])
    apply hω1
    calc (ωu : K) = (ωu : K) * (ωu : K) ^ 2 := by rw [hω2, mul_one]
      _ = (ωu : K) ^ 3 := by ring
      _ = 1 := hω3
  have hβγ : β ≠ γ := by
    intro hh
    have h' : (ωu : K) = (ωu : K) ^ 2 := mul_left_cancel₀ hα0 hh
    apply hω1
    have h1 : (ωu : K) * (1 : K) = (ωu : K) * (ωu : K) := by
      rw [mul_one, ← pow_two]
      exact h'
    exact (mul_left_cancel₀ ωu.ne_zero h1).symm
  let Eβ : Submodule K (Fin 5 → K) := D.eigenspace β
  let Eγ : Submodule K (Fin 5 → K) := D.eigenspace γ
  let Eβγ : Submodule K (Fin 5 → K) := Eβ ⊔ Eγ
  have hEβ1 : Module.finrank K Eβ = 1 := hαother β hβ3 hβα
  have hEγ1 : Module.finrank K Eγ = 1 := hαother γ hγ3 hγα
  have hsup : Eα ⊔ Eβ ⊔ Eγ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    have hd1 : Disjoint Eα Eβ := eigenspace_disjoint_of_ne D hβα.symm
    have hd2 : Disjoint (Eα ⊔ Eβ) Eγ := eigenspace_sup_disjoint_of_ne D hβα.symm hγα.symm hβγ
    rw [finrank_sup_of_disjoint hd2, finrank_sup_of_disjoint hd1, hEα3, hEβ1, hEγ1]
  have hEα_le_perp : Eα ≤ Ff.perp Eβγ := by
    intro u hu
    rw [Ff.mem_perp]
    intro w hw
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    rw [Ff.add_left,
      eigenspace_orthogonal_of_unitary hK hDiso hβ3 hα3 hβα hq3 hb hu,
      eigenspace_orthogonal_of_unitary hK hDiso hγ3 hα3 hγα hq3 hc hu, add_zero]
  have hdimperp : Module.finrank K (Ff.perp Eβγ) = 3 := by
    have h1 : Module.finrank K Eβγ = 2 := by
      rw [show Eβγ = Eβ ⊔ Eγ from rfl, finrank_sup_of_disjoint (eigenspace_disjoint_of_ne D hβγ),
        hEβ1, hEγ1]
    have hfin := Ff.finrank_perp Eβγ
    rw [h1, Module.finrank_fin_fun] at hfin
    omega
  have hEαeq : Eα = Ff.perp Eβγ :=
    Submodule.eq_of_le_of_finrank_eq hEα_le_perp (by rw [hdimperp, hEα3])
  have hker : ∀ a ∈ A,
      (∃ c : K, ∀ v ∈ Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)) α,
        (a : Matrix (Fin 5) (Fin 5) K) *ᵥ v = c • v) → a ∈ Subgroup.zpowers d := by
    intro a ha hc
    obtain ⟨c, hac⟩ := hc
    have hacE : ∀ v ∈ Eα, (a : Matrix (Fin 5) (Fin 5) K) *ᵥ v = c • v := hac
    have hcomm_ad : (a : GL (Fin 5) K) * d = d * (a : GL (Fin 5) K) := by
      simpa using congrArg (fun z : A => (z : GL (Fin 5) K))
        (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩)
    have hcomm_adM : (d : Matrix (Fin 5) (Fin 5) K) * (a : Matrix (Fin 5) (Fin 5) K) =
        (a : Matrix (Fin 5) (Fin 5) K) * (d : Matrix (Fin 5) (Fin 5) K) := by
      simpa using congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K)) hcomm_ad.symm
    have hapres : ∀ (b : GL (Fin 5) K), b ∈ A → b * d = d * b →
        ∀ (μ : K) v, v ∈ D.eigenspace μ → (b : Matrix (Fin 5) (Fin 5) K) *ᵥ v ∈ D.eigenspace μ := by
      intro b hb hbd μ v hv
      have hvd : (d : Matrix (Fin 5) (Fin 5) K) *ᵥ v = μ • v := by
        simpa [D, Matrix.toLin'_apply] using (Module.End.mem_eigenspace_iff.mp hv)
      have hbdM : (d : Matrix (Fin 5) (Fin 5) K) * (b : Matrix (Fin 5) (Fin 5) K) =
          (b : Matrix (Fin 5) (Fin 5) K) * (d : Matrix (Fin 5) (Fin 5) K) := by
        simpa using congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K)) hbd.symm
      rw [Module.End.mem_eigenspace_iff]
      have hgoal : (d : Matrix (Fin 5) (Fin 5) K) *ᵥ ((b : Matrix (Fin 5) (Fin 5) K) *ᵥ v) =
          μ • ((b : Matrix (Fin 5) (Fin 5) K) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, hbdM, ← Matrix.mulVec_mulVec, hvd, Matrix.mulVec_smul]
      simpa [D, Matrix.toLin'_apply] using hgoal
    have hapres_inv : ∀ (μ : K) v, v ∈ D.eigenspace μ →
        (((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v ∈ D.eigenspace μ := by
      have hcomm_inv : (a : GL (Fin 5) K)⁻¹ * d = d * (a : GL (Fin 5) K)⁻¹ := by
        simpa using congrArg (fun z : A => (z : GL (Fin 5) K))
          (hAe.1.is_comm.comm ⟨(a : GL (Fin 5) K)⁻¹, A.inv_mem ha⟩ ⟨d, hdA⟩)
      exact hapres _ (A.inv_mem ha) hcomm_inv
    have hc0 : c ≠ 0 := by
      intro h0
      have hbot : Eα = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro v hv
        have hv0 := hacE v hv
        rw [h0, zero_smul] at hv0
        have h1 : (((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ
            ((a : Matrix (Fin 5) (Fin 5) K) *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        rw [hv0, Matrix.mulVec_zero] at h1
        exact h1.symm
      have hfr : Module.finrank K Eα = 0 := by rw [hbot]; simp
      omega
    have ha_inv : ∀ v ∈ Eα, (((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v =
        c⁻¹ • v := by
      intro v hv
      have hw : (((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v ∈ Eα :=
        hapres_inv α v hv
      have h1 : (a : Matrix (Fin 5) (Fin 5) K) *ᵥ
          ((((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have h2 := hacE _ hw
      rw [h1] at h2
      have h3 : c⁻¹ • v =
          (((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v := by
        have h4 : c⁻¹ • v = c⁻¹ • (c • ((((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) :
            Matrix (Fin 5) (Fin 5) K) *ᵥ v)) := congrArg (fun w => c⁻¹ • w) h2
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h4
        exact h4
      exact h3.symm
    have hfix : ∀ j ∈ J', ((ψ ⟨a, ha⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f))) j = j := by
      intro j hj
      obtain ⟨g, hgproj, hgfix⟩ := hJdesc j hj
      have hgpres : ∀ v ∈ Eα, ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v ∈ Eα := by
        intro v hv
        rw [hEαeq, Ff.mem_perp]
        intro w hw
        have hwg : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w = w := by
          obtain ⟨b, hb, cc, hcc, rfl⟩ := Submodule.mem_sup.mp hw
          rw [Matrix.mulVec_add, hgfix β hβ3 hβα b hb, hgfix γ hγ3 hγα cc hcc]
        have hiso := CFSG.LieType.BorelTits.statedSU_preserves hK g.2 w v
        rw [hwg] at hiso
        rw [hiso]
        exact (Ff.mem_perp.mp (hEα_le_perp hv)) w hw
      have hag : (a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹ = (g : GL (Fin 5) K) := by
        apply Units.ext
        apply (Matrix.toLinAlgEquiv' (n := Fin 5) (R := K)).injective
        apply LinearMap.ext
        intro v
        change ((a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹ :
            Matrix (Fin 5) (Fin 5) K) *ᵥ v = ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v
        have hv : v ∈ Eα ⊔ Eβ ⊔ Eγ := by rw [hsup]; exact Submodule.mem_top
        obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx1
        have hu' : ((a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹ :
            Matrix (Fin 5) (Fin 5) K) *ᵥ u = ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ u := by
          have hgu : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ u ∈ Eα := hgpres u hu
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha_inv u hu, Matrix.mulVec_smul,
            Matrix.mulVec_smul, hacE _ hgu, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        have hw' : ((a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹ :
            Matrix (Fin 5) (Fin 5) K) *ᵥ w = ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w := by
          have hgfixw : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w = w :=
            hgfix β hβ3 hβα w hw
          have hinvw : (((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) :
              Matrix (Fin 5) (Fin 5) K) *ᵥ w ∈ Eβ := hapres_inv β w hw
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          rw [hgfix β hβ3 hβα _ hinvw]
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec]
          rw [hgfixw]
        have hx2' : ((a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹ :
            Matrix (Fin 5) (Fin 5) K) *ᵥ x2 = ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ x2 := by
          have hgfixx : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ x2 = x2 :=
            hgfix γ hγ3 hγα x2 hx2
          have hinvx : (((a : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) :
              Matrix (Fin 5) (Fin 5) K) *ᵥ x2 ∈ Eγ := hapres_inv γ x2 hx2
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          rw [hgfix γ hγ3 hγα _ hinvx]
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec]
          rw [hgfixx]
        simp only [Matrix.mulVec_add, hu', hw', hx2']
      have hfixg : ((ψ ⟨a, ha⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f)))
          (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ f)) g) =
          LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ f)) g := by
        let h' : ↥(LargeEvenSUGroup (Fin 5) K (2 ^ f)) :=
          ⟨(a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹,
            by rw [hag]; exact g.2⟩
        have hrel : (h' : GL (Fin 5) K) = (a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹ :=
          rfl
        have h1 := (hψ ⟨a, ha⟩) g h' hrel
        have h2 : h' = g := Subtype.ext hag
        rw [h1, h2]
      rw [← hgproj]
      exact hfixg
    have hmemψ : ((ψ ⟨a, ha⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f))) ∈ Ā := (ψ ⟨a, ha⟩).2
    have hzpow : ((ψ ⟨a, ha⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f))) ∈ Subgroup.zpowers δ' :=
      hRD.ker _ hmemψ hfix
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzpow
    have hnorm_d : ∀ k ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f),
        d * k * d⁻¹ ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f) :=
      isometry_normalizes_SU h (hL.iso d (hAleAhat hdA))
    have hdk : IsConjBy (d ^ k) (δ' ^ k) := isConjBy_zpow hnorm_d hdconj k
    have hnorm_dk_inv : ∀ j ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f),
        (d ^ k)⁻¹ * j * ((d ^ k)⁻¹)⁻¹ ∈ LargeEvenSUGroup (Fin 5) K (2 ^ f) :=
      isometry_normalizes_SU h (hL.iso (d ^ k)⁻¹ (Ahat.inv_mem (Ahat.zpow_mem (hAleAhat hdA) k)))
    have hconj_a : IsConjBy (a : GL (Fin 5) K) ((ψ ⟨a, ha⟩ : Ā) : MulAut (PSUg 5 K (2 ^ f))) :=
      hψ ⟨a, ha⟩
    have h1 : IsConjBy ((a : GL (Fin 5) K) * (d ^ k)⁻¹)
        (1 : MulAut (PSUg 5 K (2 ^ f))) := by
      have hh := isConjBy_mul hnorm_dk_inv hconj_a (isConjBy_inv hdk)
      rwa [hk, mul_inv_cancel] at hh
    have hmemAhat : (a : GL (Fin 5) K) * (d ^ k)⁻¹ ∈ Ahat :=
      Ahat.mul_mem (hAleAhat ha) (Ahat.inv_mem (Ahat.zpow_mem (hAleAhat hdA) k))
    have hmemA : (a : GL (Fin 5) K) * (d ^ k)⁻¹ ∈ A :=
      A.mul_mem ha (A.inv_mem (A.zpow_mem hdA k))
    have hz1 : (a : GL (Fin 5) K) * (d ^ k)⁻¹ = 1 := hscalar_eq_one _ hmemA h1
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, (mul_inv_eq_one.mp hz1).symm⟩
  let φ : K →+* K := (CFSG.LieType.BorelTits.unitaryInvolution K 2 f : K →+* K)
  have hφ : ∀ x : K, φ x = x ^ (2 ^ f) :=
    fun x => CFSG.LieType.BorelTits.unitaryInvolution_apply K 2 f x
  rintro ⟨U, hUne, hU2, hnorm⟩
  rcases uni_split hK (by norm_num : 4 ≤ 5) φ hφ hĀI hL hUne hU2 hnorm with
    ⟨W, hWne, hWiso, hWstab⟩ | ⟨B, hBiso, hBout⟩
  · refine (u5_par_impossible hK hq3 A hAleSU hAe hAcard d hdA α hα3
      ⟨hαdim, hαother⟩ hker) ?_
    exact ⟨W, hWne, hWiso, fun a ha w hw => hWstab a (hAleAhat ha) w hw⟩
  · have houterA : ∀ x ∈ A, B * Matrix.GeneralLinearGroup.map φ x * B⁻¹ = x := by
      intro x hx
      obtain ⟨c, hc1, hceq⟩ := hBout x (hAleAhat hx)
      have hdetx : (x : Matrix (Fin 5) (Fin 5) K).det = 1 :=
        ((mem_unitarySU_iff h).mp (hAleSU hx)).1
      have hdetx' : GeneralLinearGroup.det x = 1 := by
        apply Units.ext; simpa using hdetx
      have hmap : GeneralLinearGroup.det (GeneralLinearGroup.map φ x) =
          Units.map φ (GeneralLinearGroup.det x) :=
        Matrix.GeneralLinearGroup.map_det φ x
      have hc5 : c ^ 5 = 1 := by
        have hdet := congrArg (GeneralLinearGroup.det) hceq
        rw [map_mul, map_mul, map_inv, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
        rw [hmap, hdetx'] at hdet
        rw [map_one, mul_one, mul_inv_cancel] at hdet
        simpa using hdet.symm
      have hc1' : c = 1 := by
        have h1 : orderOf c ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hc5
        have h2 : orderOf c ∣ 2 ^ f + 1 := orderOf_dvd_iff_pow_eq_one.mpr hc1
        have h3 : orderOf c ∣ Nat.gcd 5 (2 ^ f + 1) := Nat.dvd_gcd h1 h2
        rw [hcop.gcd_eq_one] at h3
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
      rw [hc1'] at hceq
      simpa using hceq
    let sFun : (Fin 5 → K) →+ (Fin 5 → K) :=
      { toFun := fun v => (B : Matrix (Fin 5) (Fin 5) K) *ᵥ (φ ∘ v)
        map_zero' := by simp
        map_add' := by
          intro u v
          have h : φ ∘ (u + v) = φ ∘ u + φ ∘ v := by ext i; simp [Pi.add_apply]
          rw [h, Matrix.mulVec_add] }
    have hsBij : Function.Bijective sFun := by
      have hfrob : Function.Bijective (fun v : Fin 5 → K => φ ∘ v) := by
        have hφinj : Function.Injective φ := RingHom.injective φ
        have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
        refine ⟨?_, ?_⟩
        · intro u v huv
          ext i
          exact hφinj (by simpa using congrFun huv i)
        · intro w
          refine ⟨fun i => Classical.choose (hφsurj (w i)), ?_⟩
          ext i
          exact Classical.choose_spec (hφsurj (w i))
      have hmv : Function.Bijective (fun v : Fin 5 → K => (B : Matrix (Fin 5) (Fin 5) K) *ᵥ v) :=
        ⟨Matrix.mulVec_injective_of_isUnit (A := (B : Matrix (Fin 5) (Fin 5) K)) B.isUnit,
         fun w => ⟨(((B⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ w, by
            show (B : Matrix (Fin 5) (Fin 5) K) *ᵥ ((((B⁻¹ : GL (Fin 5) K)) :
              Matrix (Fin 5) (Fin 5) K) *ᵥ w) = w
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.one_mulVec]⟩⟩
      have heq : ⇑sFun = (fun w : Fin 5 → K => (B : Matrix (Fin 5) (Fin 5) K) *ᵥ w) ∘
          (fun v : Fin 5 → K => φ ∘ v) := rfl
      rw [heq]
      exact hmv.comp hfrob
    let s : (Fin 5 → K) ≃+ (Fin 5 → K) := AddEquiv.ofBijective sFun hsBij
    have hs : ∀ (c : K) (v : Fin 5 → K), s (c • v) = c ^ (2 ^ f) • s v := by
      intro c v
      change sFun (c • v) = c ^ (2 ^ f) • sFun v
      show (B : Matrix (Fin 5) (Fin 5) K) *ᵥ (φ ∘ (c • v)) =
        c ^ (2 ^ f) • ((B : Matrix (Fin 5) (Fin 5) K) *ᵥ (φ ∘ v))
      have h1 : φ ∘ (c • v) = φ c • (φ ∘ v) := by ext i; simp [Pi.smul_apply]
      rw [h1, Matrix.mulVec_smul, hφ c]
    have hsE : ∀ x ∈ A, ∀ v : Fin 5 → K,
        s ((x : Matrix (Fin 5) (Fin 5) K) *ᵥ v) = (x : Matrix (Fin 5) (Fin 5) K) *ᵥ s v := by
      intro x hx v
      have hxeq := houterA x hx
      have hxmat : (B : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K).map φ =
          (x : Matrix (Fin 5) (Fin 5) K) * (B : Matrix (Fin 5) (Fin 5) K) := by
        have h1 : (B : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K).map φ *
            (B : Matrix (Fin 5) (Fin 5) K)⁻¹ = (x : Matrix (Fin 5) (Fin 5) K) := by
          have := congrArg (fun y : GL (Fin 5) K => (y : Matrix (Fin 5) (Fin 5) K)) hxeq
          simpa [GeneralLinearGroup.map_apply, Matrix.map_apply] using this
        calc (B : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K).map φ
            = ((B : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K).map φ *
                (B : Matrix (Fin 5) (Fin 5) K)⁻¹) * (B : Matrix (Fin 5) (Fin 5) K) := by
              rw [mul_assoc, Matrix.nonsing_inv_mul (A := (B : Matrix (Fin 5) (Fin 5) K))
                (by simpa using (GeneralLinearGroup.det B).isUnit), mul_one]
          _ = (x : Matrix (Fin 5) (Fin 5) K) * (B : Matrix (Fin 5) (Fin 5) K) := by rw [h1]
      change sFun ((x : Matrix (Fin 5) (Fin 5) K) *ᵥ v) =
        (x : Matrix (Fin 5) (Fin 5) K) *ᵥ sFun v
      show (B : Matrix (Fin 5) (Fin 5) K) *ᵥ (φ ∘ ((x : Matrix (Fin 5) (Fin 5) K) *ᵥ v)) =
        (x : Matrix (Fin 5) (Fin 5) K) *ᵥ ((B : Matrix (Fin 5) (Fin 5) K) *ᵥ (φ ∘ v))
      have h1 : φ ∘ ((x : Matrix (Fin 5) (Fin 5) K) *ᵥ v) =
          (x : Matrix (Fin 5) (Fin 5) K).map φ *ᵥ (φ ∘ v) := by
        ext i
        simp only [Function.comp_apply, Matrix.mulVec_apply, Matrix.map_apply, dotProduct]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_mul]
        rfl
      rw [h1, Matrix.mulVec_mulVec, hxmat, Matrix.mulVec_mulVec]
    have hbound := outRank_bound hK hq3 A hAe.2
      (fun x hx y hy => by
        simpa using congrArg (fun z : A => (z : GL (Fin 5) K))
          (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) s hs hsE hAcard
    omega

end Uni5OnRMain

end CFSG.StandardType.TablePThreeKG

end
