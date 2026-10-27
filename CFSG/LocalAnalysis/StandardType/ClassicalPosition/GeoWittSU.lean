module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairOrbits
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.ClassicalPosition.Geo

open CFSG.LieType.Universal
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open Matrix

private theorem gWSU_one_le_exp {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) : 1 ≤ f := by
  by_contra h
  have hf : f = 0 := by omega
  rw [hf, pow_zero, one_pow] at hc
  have h1 := Finite.one_lt_card (α := F)
  omega

private noncomputable def gWSU_fieldData {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) : UnitaryFieldData 2 f F where
  prime := Nat.prime_two
  one_le := gWSU_one_le_exp hc
  card := by rw [hc, ← pow_mul, mul_comm]

private theorem gWSU_bar_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) :
    ⇑(gWSU_fieldData hc).bar = ⇑(CFSG.LieType.BorelTits.unitaryInvolution F 2 f) := by
  funext c
  rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]

private noncomputable abbrev gWSU_B {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) :
    (Fin n → F) →ₛₗ[(gWSU_fieldData hc).bar] (Fin n → F) →ₗ[F] F :=
  gramForm (gWSU_fieldData hc) (Unitary.antidiag n)

private theorem gWSU_B_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (x y : Fin n → F) :
    gWSU_B hc n x y =
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (x i))
        (Unitary.antidiag n) ⬝ᵥ y := by
  have hmap : (fun a => (gWSU_fieldData hc).bar (x a)) =
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (x i)) := by
    funext i
    exact congrFun (gWSU_bar_eq hc) (x i)
  change gramForm (gWSU_fieldData hc) (Unitary.antidiag n) x y = _
  rw [gramForm_apply, hmap, Matrix.dotProduct_mulVec]

private theorem gWSU_antidiag_conjTranspose {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) :
    Matrix.transpose ((Unitary.antidiag n).map (fun c => (gWSU_fieldData hc).bar c)) =
      Unitary.antidiag n := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Unitary.antidiag, Matrix.of_apply]
  by_cases hij : i = Fin.rev j
  · have hji : j = Fin.rev i := by rw [hij, Fin.rev_rev]
    rw [if_pos hij, if_pos hji]
    simp
  · have hji : ¬ j = Fin.rev i := fun h => hij (by rw [h, Fin.rev_rev])
    rw [if_neg hij, if_neg hji]
    simp

private theorem gWSU_B_isSymm {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) : (gWSU_B hc n).IsSymm := by
  change (gramForm (gWSU_fieldData hc) (Unitary.antidiag n)).IsSymm
  exact gramForm_isSymm _ (gWSU_antidiag_conjTranspose hc n)

private theorem gWSU_B_sep {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) : (gWSU_B hc n).SeparatingLeft := by
  change (gramForm (gWSU_fieldData hc) (Unitary.antidiag n)).SeparatingLeft
  exact gramForm_separatingLeft _ (Unitary.det_antidiag_ne_zero n)

private theorem gWSU_B_single {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (i j : Fin n) :
    gWSU_B hc n (Pi.single i 1) (Pi.single j 1) = if j = Fin.rev i then 1 else 0 := by
  change gramForm (gWSU_fieldData hc) (Unitary.antidiag n) (Pi.single i 1) (Pi.single j 1) = _
  rw [gramForm_single, Unitary.antidiag, Matrix.of_apply]

private theorem gWSU_B_of_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {x y : Fin n → F} {c : F}
    (h : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (x i))
      (Unitary.antidiag n) ⬝ᵥ y = c) : gWSU_B hc n x y = c := by
  rw [gWSU_B_eq hc]
  exact h

private theorem gWSU_four_le_of_distinct {n : ℕ} {a b : Fin n} (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hab : a ≠ b) (hab' : a ≠ Fin.rev b) : 4 ≤ n := by
  by_contra h
  interval_cases n <;> fin_cases a <;> fin_cases b <;> simp_all [Fin.rev]

private theorem gWSU_exists_smul_of_map_span {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] {x y : V} (hx : x ≠ 0) (g : LinearMap.GeneralLinearGroup F V)
    (h : Submodule.map (↑g : V →ₗ[F] V) (F ∙ x) = F ∙ y) :
    ∃ α : F, α ≠ 0 ∧ (↑g : V →ₗ[F] V) x = α • y := by
  have hmem : (↑g : V →ₗ[F] V) x ∈ F ∙ y := by
    rw [← h]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self x)
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨α, fun hα0 => ?_, hα.symm⟩
  have hgx : (↑g : V →ₗ[F] V) x = 0 := by rw [← hα, hα0, zero_smul]
  have hgx' : (LinearMap.GeneralLinearGroup.toLinearEquiv g) x = 0 := by
    rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv]; exact hgx
  exact hx ((LinearMap.GeneralLinearGroup.toLinearEquiv g).injective (by rw [hgx', map_zero]))

private theorem gWSU_witt_twoPairs {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p f : ℕ} (h : UnitaryFieldData p f K)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {r ε : ℕ} (hn : Module.finrank K V = 2 * (r + 1 + 1) + ε) {a₁ b₁ a₂ b₂ : V}
    (h11 : B a₁ a₁ = 0) (hb11 : B b₁ b₁ = 0) (ha₁b₁ : B a₁ b₁ = 1)
    (h22 : B a₂ a₂ = 0) (hb22 : B b₂ b₂ = 0) (ha₂b₂ : B a₂ b₂ = 1)
    (h12 : B a₁ a₂ = 0) (h1b2 : B a₁ b₂ = 0) (hb12 : B b₁ a₂ = 0) (hb1b2 : B b₁ b₂ = 0) :
    ∃ w : Module.Basis (HypIndex (r + 1 + 1) ε) K V,
      (∀ x y, B (w x) (w y) = hypGram (r + 1 + 1) ε K x y) ∧
      w (Sum.inl (0 : Fin (r + 1 + 1))) = a₁ ∧
      w (Sum.inr (Sum.inr (0 : Fin (r + 1 + 1)))) = b₁ ∧
      w (Sum.inl (1 : Fin (r + 1 + 1))) = a₂ ∧
      w (Sum.inr (Sum.inr (1 : Fin (r + 1 + 1)))) = b₂ := by
  classical
  have ha₁ : a₁ ≠ 0 := fun h0 => by
    rw [h0] at ha₁b₁
    exact (zero_ne_one : (0 : K) ≠ 1) (by simpa using ha₁b₁)
  obtain ⟨-, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha₁ h11
  obtain ⟨-, -, -, hU₁sep, hU₁dim0⟩ := hsplit b₁ ha₁b₁ hb11
  set U₁ : Submodule K V := (Submodule.span K {a₁, b₁}).orthogonalBilin B with hU₁
  have ha₂U₁ : a₂ ∈ U₁ := by
    rw [hU₁, Submodule.mem_orthogonalBilin]
    intro z hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp [h12, hb12]
  have hb₂U₁ : b₂ ∈ U₁ := by
    rw [hU₁, Submodule.mem_orthogonalBilin]
    intro z hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp [h1b2, hb1b2]
  have hU₁dim : Module.finrank K U₁ = 2 * (r + 1) + ε := by omega
  obtain ⟨w', hw', hw'a, hw'b⟩ := exists_hypBasis_of_pair h (hB.domRestrict U₁) hU₁sep
    hU₁dim (Nat.succ_pos r) (a := ⟨a₂, ha₂U₁⟩) (b := ⟨b₂, hb₂U₁⟩)
    (by rw [LinearMap.domRestrict₁₂_apply]; exact h22)
    (by rw [LinearMap.domRestrict₁₂_apply]; exact hb22)
    (by rw [LinearMap.domRestrict₁₂_apply]; exact ha₂b₂)
  have hw'' : ∀ x y, B (w' x : V) (w' y : V) = hypGram (r + 1) ε K x y := fun x y => by
    rw [← hw' x y, LinearMap.domRestrict₁₂_apply]
  have ha₁U₁ : ∀ x ∈ U₁, B a₁ x = 0 := fun x hx =>
    (Submodule.mem_orthogonalBilin.mp hx) a₁ (Submodule.subset_span (by simp))
  have hb₁U₁ : ∀ x ∈ U₁, B b₁ x = 0 := fun x hx =>
    (Submodule.mem_orthogonalBilin.mp hx) b₁ (Submodule.subset_span (by simp))
  obtain ⟨w, hw, hwa, hwb, hwa', hwb'⟩ := UnitaryHigher.prependPair h hB h11 hb11 ha₁b₁
    ha₁U₁ hb₁U₁ (r := r + 1) hn w' hw''
  refine ⟨w, hw, hwa, hwb, ?_, ?_⟩
  · rw [← Fin.succ_zero_eq_one, hwa' 0]
    exact congrArg Subtype.val hw'a
  · rw [← Fin.succ_zero_eq_one, hwb' 0]
    exact congrArg Subtype.val hw'b

private theorem gWSU_exists_matrix {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    {g : LinearMap.GeneralLinearGroup F (Fin n → F)}
    (hg : g ∈ sesqSpecialUnitaryGroup (gWSU_B hc n)) :
    ∃ A : GL (Fin n) F,
      A ∈ Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n ∧
      (g : (Fin n → F) →ₗ[F] (Fin n → F)) =
        (A : Matrix (Fin n) (Fin n) F).mulVecLin := by
  let A : GL (Fin n) F := Matrix.GeneralLinearGroup.toLin.symm g
  have hAtoLin : Matrix.GeneralLinearGroup.toLin A = g := MulEquiv.apply_symm_apply _ _
  have hAg : A ∈ gramSU (gWSU_fieldData hc) (Unitary.antidiag n) :=
    (toLin_mem_sesqSpecialUnitaryGroup_iff (gWSU_fieldData hc) (Unitary.antidiag n) A).mp (by
      rw [hAtoLin]; exact hg)
  obtain ⟨hAiso, hAdet⟩ := (mem_gramSU.mp hAg)
  have hσ : (A : Matrix (Fin n) (Fin n) F).map ⇑(gWSU_fieldData hc).bar =
      (A : Matrix (Fin n) (Fin n) F).map
        ⇑(CFSG.LieType.BorelTits.unitaryInvolution F 2 f) := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, gWSU_bar_eq hc]
  have hAbar : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
        (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (A : Matrix (Fin n) (Fin n) F) =
        Unitary.antidiag n := by
    rw [Unitary.conjTr, ← hσ]
    exact hAiso
  refine ⟨A, ⟨hAdet, hAbar⟩, ?_⟩
  have hco : (↑g : (Fin n → F) →ₗ[F] (Fin n → F)) =
      (↑(Matrix.GeneralLinearGroup.toLin A) : (Fin n → F) →ₗ[F] (Fin n → F)) := by
    rw [hAtoLin]
  rw [hco, Matrix.GeneralLinearGroup.coe_toLin]

theorem exists_su_mulVec_single_eq_smul {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {a : Fin n} (ha : a ≠ Fin.rev a) (v w : Fin n → F)
    (hv : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w i))
      (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1) :
    ∃ u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n), ∃ α β : F, α ≠ 0 ∧
      β ≠ 0 ∧ Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Pi.single a 1) =
        α • v ∧
      Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Pi.single (Fin.rev a) 1) =
        β • w := by
  classical
  have hB : (gWSU_B hc n).IsSymm := gWSU_B_isSymm hc n
  have hBl : (gWSU_B hc n).SeparatingLeft := gWSU_B_sep hc n
  have hea : gWSU_B hc n (Pi.single a 1) (Pi.single a 1) = 0 := by
    rw [gWSU_B_single hc]; simp [ha]
  have heba : gWSU_B hc n (Pi.single (Fin.rev a) 1) (Pi.single (Fin.rev a) 1) = 0 := by
    rw [gWSU_B_single hc]; simp [Fin.rev_rev, Ne.symm ha]
  have heab : gWSU_B hc n (Pi.single a 1) (Pi.single (Fin.rev a) 1) = 1 := by
    rw [gWSU_B_single hc]; simp
  have hvB : gWSU_B hc n v v = 0 := gWSU_B_of_eq hc hv
  have hwB : gWSU_B hc n w w = 0 := gWSU_B_of_eq hc hw
  have hvwB : gWSU_B hc n v w = 1 := gWSU_B_of_eq hc hvw
  obtain ⟨g, hg, hgv, hgw⟩ := UnitaryHigher.exists_sesqSpecialUnitary_of_hyperbolic
    (gWSU_fieldData hc) hB hBl hea heba heab hvB hwB hvwB
  obtain ⟨A, hAu, hgA⟩ := gWSU_exists_matrix hc hg
  obtain ⟨α, hα0, hαeq⟩ := gWSU_exists_smul_of_map_span
    (x := Pi.single a 1) (y := v) (by simp) g hgv
  obtain ⟨β, hβ0, hβeq⟩ := gWSU_exists_smul_of_map_span
    (x := Pi.single (Fin.rev a) 1) (y := w) (by simp) g hgw
  have hgva : (A : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single a 1 =
      (g : (Fin n → F) →ₗ[F] (Fin n → F)) (Pi.single a 1) := by
    rw [← Matrix.mulVecLin_apply, ← hgA]
  have hgwa : (A : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single (Fin.rev a) 1 =
      (g : (Fin n → F) →ₗ[F] (Fin n → F)) (Pi.single (Fin.rev a) 1) := by
    rw [← Matrix.mulVecLin_apply, ← hgA]
  exact ⟨⟨A, hAu⟩, α, β, hα0, hβ0, by rw [hgva, hαeq], by rw [hgwa, hβeq]⟩

theorem exists_su_mulVec_single_eq_smul_quad {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {a b : Fin n} (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hab : a ≠ b) (hab' : a ≠ Fin.rev b) (v₁ w₁ v₂ w₂ : Fin n → F)
    (h₁ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
      (Unitary.antidiag n) ⬝ᵥ w₂ = 1)
    (h₂ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
      (Unitary.antidiag n) ⬝ᵥ v₂ = 1)
    (h₀ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
      (Unitary.antidiag n) ⬝ᵥ v₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₂ i))
        (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₂ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
        (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₂ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0) :
    ∃ u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
      ∃ α₁ β₁ α₂ β₂ : F, α₁ ≠ 0 ∧ β₁ ≠ 0 ∧ α₂ ≠ 0 ∧ β₂ ≠ 0 ∧
      Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Pi.single a 1) = α₁ • v₁ ∧
      Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Pi.single (Fin.rev b) 1) =
        β₁ • w₁ ∧
      Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Pi.single b 1) = α₂ • v₂ ∧
      Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Pi.single (Fin.rev a) 1) =
        β₂ • w₂ := by
  classical
  obtain ⟨hv₁v₁, hw₁w₁, hv₂v₂, hw₂w₂, hv₁w₁, hv₁v₂, hw₁w₂, hv₂w₂⟩ := h₀
  have hB : (gWSU_B hc n).IsSymm := gWSU_B_isSymm hc n
  have hBl : (gWSU_B hc n).SeparatingLeft := gWSU_B_sep hc n
  have h4 : 4 ≤ n := gWSU_four_le_of_distinct ha hb hab hab'
  set r : ℕ := n / 2 - 2 with hr
  set ε : ℕ := n - 2 * (n / 2) with hεdef
  have hn : Module.finrank F (Fin n → F) = 2 * (r + 1 + 1) + ε := by
    have hfr : Module.finrank F (Fin n → F) = n := Module.finrank_fin_fun F
    omega
  have hε : ε ≤ 1 := by omega
  have hrε : 0 < 2 * (r + 1 + 1) + ε := by omega
  have bv₁v₁ : gWSU_B hc n v₁ v₁ = 0 := gWSU_B_of_eq hc hv₁v₁
  have bw₁w₁ : gWSU_B hc n w₁ w₁ = 0 := gWSU_B_of_eq hc hw₁w₁
  have bv₂v₂ : gWSU_B hc n v₂ v₂ = 0 := gWSU_B_of_eq hc hv₂v₂
  have bw₂w₂ : gWSU_B hc n w₂ w₂ = 0 := gWSU_B_of_eq hc hw₂w₂
  have bv₁w₁ : gWSU_B hc n v₁ w₁ = 0 := gWSU_B_of_eq hc hv₁w₁
  have bv₁v₂ : gWSU_B hc n v₁ v₂ = 0 := gWSU_B_of_eq hc hv₁v₂
  have bw₁w₂ : gWSU_B hc n w₁ w₂ = 0 := gWSU_B_of_eq hc hw₁w₂
  have bv₂w₂ : gWSU_B hc n v₂ w₂ = 0 := gWSU_B_of_eq hc hv₂w₂
  have bh₁ : gWSU_B hc n v₁ w₂ = 1 := gWSU_B_of_eq hc h₁
  have bw₁v₂ : gWSU_B hc n w₁ v₂ = 1 := gWSU_B_of_eq hc h₂
  have bv₂w₁ : gWSU_B hc n v₂ w₁ = 1 := by
    have hh := hB.eq w₁ v₂
    rw [bw₁v₂, map_one] at hh
    exact hh.symm
  have bw₂v₂ : gWSU_B hc n w₂ v₂ = 0 := by
    have hh := hB.eq v₂ w₂
    rw [bv₂w₂, map_zero] at hh
    exact hh.symm
  have bw₂w₁ : gWSU_B hc n w₂ w₁ = 0 := by
    have hh := hB.eq w₁ w₂
    rw [bw₁w₂, map_zero] at hh
    exact hh.symm
  have s11 : gWSU_B hc n (Pi.single a 1) (Pi.single a 1) = 0 := by
    rw [gWSU_B_single hc]; simp [ha]
  have sb11 : gWSU_B hc n (Pi.single (Fin.rev a) 1) (Pi.single (Fin.rev a) 1) = 0 := by
    rw [gWSU_B_single hc]; simp [Fin.rev_rev, Ne.symm ha]
  have sa1b1 : gWSU_B hc n (Pi.single a 1) (Pi.single (Fin.rev a) 1) = 1 := by
    rw [gWSU_B_single hc]; simp
  have s22 : gWSU_B hc n (Pi.single b 1) (Pi.single b 1) = 0 := by
    rw [gWSU_B_single hc]; simp [hb]
  have sb22 : gWSU_B hc n (Pi.single (Fin.rev b) 1) (Pi.single (Fin.rev b) 1) = 0 := by
    rw [gWSU_B_single hc]; simp [Fin.rev_rev, Ne.symm hb]
  have sa2b2 : gWSU_B hc n (Pi.single b 1) (Pi.single (Fin.rev b) 1) = 1 := by
    rw [gWSU_B_single hc]; simp
  have s12 : gWSU_B hc n (Pi.single a 1) (Pi.single b 1) = 0 := by
    have hba : b ≠ Fin.rev a := fun hh => hab' (by rw [hh, Fin.rev_rev])
    rw [gWSU_B_single hc]; simp [hba]
  have s1b2 : gWSU_B hc n (Pi.single a 1) (Pi.single (Fin.rev b) 1) = 0 := by
    have hrev : Fin.rev b ≠ Fin.rev a := fun hh => hab (by
      have := congrArg Fin.rev hh
      simpa [Fin.rev_rev] using this.symm)
    rw [gWSU_B_single hc]; simp [hrev]
  have sb12 : gWSU_B hc n (Pi.single (Fin.rev a) 1) (Pi.single b 1) = 0 := by
    rw [gWSU_B_single hc]; simp [Ne.symm hab]
  have sb1b2 : gWSU_B hc n (Pi.single (Fin.rev a) 1) (Pi.single (Fin.rev b) 1) = 0 := by
    rw [gWSU_B_single hc]; simp [Fin.rev_rev, Ne.symm hab']
  obtain ⟨wstd, hwstd, hwstd_a, hwstd_ra, hwstd_b, hwstd_rb⟩ :=
    gWSU_witt_twoPairs (gWSU_fieldData hc) hB hBl hn
      s11 sb11 sa1b1 s22 sb22 sa2b2 s12 s1b2 sb12 sb1b2
  obtain ⟨wgiv, hwgiv, hwgiv_v₁, hwgiv_w₂, hwgiv_v₂, hwgiv_w₁⟩ :=
    gWSU_witt_twoPairs (gWSU_fieldData hc) hB hBl hn
      bv₁v₁ bw₂w₂ bh₁ bv₂v₂ bw₁w₁ bv₂w₁ bv₁v₂ bv₁w₁ bw₂v₂ bw₂w₁
  obtain ⟨g, hg, hgw⟩ := UnitaryHigher.exists_sesqSpecialUnitary_map_lines
    (gWSU_fieldData hc) hB hBl hε hrε wstd wgiv hwstd hwgiv
  obtain ⟨A, hAu, hgA⟩ := gWSU_exists_matrix hc hg
  obtain ⟨α₁, hα₁0, hα₁eq⟩ := gWSU_exists_smul_of_map_span
    (x := wstd (.inl 0)) (y := wgiv (.inl 0)) (wstd.ne_zero _) g (hgw _)
  rw [hwstd_a, hwgiv_v₁] at hα₁eq
  obtain ⟨α₂, hα₂0, hα₂eq⟩ := gWSU_exists_smul_of_map_span
    (x := wstd (.inl 1)) (y := wgiv (.inl 1)) (wstd.ne_zero _) g (hgw _)
  rw [hwstd_b, hwgiv_v₂] at hα₂eq
  obtain ⟨β₁, hβ₁0, hβ₁eq⟩ := gWSU_exists_smul_of_map_span
    (x := wstd (.inr (.inr 1))) (y := wgiv (.inr (.inr 1))) (wstd.ne_zero _) g (hgw _)
  rw [hwstd_rb, hwgiv_w₁] at hβ₁eq
  obtain ⟨β₂, hβ₂0, hβ₂eq⟩ := gWSU_exists_smul_of_map_span
    (x := wstd (.inr (.inr 0))) (y := wgiv (.inr (.inr 0))) (wstd.ne_zero _) g (hgw _)
  rw [hwstd_ra, hwgiv_w₂] at hβ₂eq
  have hmv : ∀ x : Fin n → F, (A : Matrix (Fin n) (Fin n) F) *ᵥ x =
      (g : (Fin n → F) →ₗ[F] (Fin n → F)) x := by
    intro x
    rw [← Matrix.mulVecLin_apply, ← hgA]
  exact ⟨⟨A, hAu⟩, α₁, β₁, α₂, β₂, hα₁0, hβ₁0, hα₂0, hβ₂0,
    by rw [hmv, hα₁eq], by rw [hmv, hβ₁eq], by rw [hmv, hα₂eq], by rw [hmv, hβ₂eq]⟩

end CFSG.StandardType.ClassicalPosition.Geo
