module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitarySingular
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGPGUQuadPhase
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotMovePSU
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearTwicePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormDescent
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace UnitaryPhase

variable {K : Type} [Field K] [Finite K] {n d : ℕ}

theorem scalar_inv_mul_pow_mem_primeFormUnitary (h : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (hd : 0 < d) {y : GL (Fin d) K}
    (hy : y ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) {l : Kˣ}
    (hl : y ^ 3 = GeneralLinearGroup.scalar (Fin d) l) {ζ μ : Kˣ} (hζ : ζ ^ 3 = 1) {j : ℕ}
    (hμ : μ ^ 3 = ζ * l ^ j) :
    GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j ∈ primeFormUnitary h (idGram K d) := by
  classical
  obtain ⟨ν, hν0, hνq, hνM⟩ := hy
  have hhy : TableBUD.herm n (y : Matrix (Fin d) (Fin d) K) =
      ν • (1 : Matrix (Fin d) (Fin d) K) := hνM
  have hsmul : ∀ (c : K) (M : Matrix (Fin d) (Fin d) K),
      TableBUD.herm n (c • M) = c ^ (2 ^ n + 1) • TableBUD.herm n M := by
    intro c M
    have hmap : (c • M).map (· ^ 2 ^ n) = c ^ 2 ^ n • M.map (· ^ 2 ^ n) := by
      ext i k
      simp [mul_pow]
    rw [TableBUD.herm, TableBUD.herm, hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, pow_succ]
  have hone : TableBUD.herm n (1 : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [TableBUD.herm, TableBUD.map_pow_eq_map_bar h, Matrix.map_one _ (map_zero _) (map_one _),
      transpose_one, Matrix.mul_one]
  have hν3 : ν ^ 3 = (l : K) ^ (2 ^ n + 1) := by
    have hy3 := TableBUD.herm_pow h hhy 3
    have hy3m : (y : Matrix (Fin d) (Fin d) K) ^ 3 =
        (l : K) • (1 : Matrix (Fin d) (Fin d) K) := by
      rw [← Units.val_pow_eq_pow_val, hl, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
    rw [hy3m, hsmul, hone] at hy3
    have := congrArg (fun N : Matrix (Fin d) (Fin d) K => N ⟨0, hd⟩ ⟨0, hd⟩) hy3
    simpa using this.symm
  have hνj0 : ν ^ j ≠ 0 := pow_ne_zero _ hν0
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hζq : (ζ : K) ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, one_pow]
  have hμ3 : (μ : K) ^ 3 = (ζ : K) * (l : K) ^ j := by
    have := congrArg (fun u : Kˣ => (u : K)) hμ
    simpa using this
  have e1 : ((μ : K) ^ (2 ^ n + 1)) ^ 3 = ((l : K) ^ (2 ^ n + 1)) ^ j := by
    rw [pow_right_comm (μ : K) (2 ^ n + 1) 3, hμ3, mul_pow, hζq, one_mul,
      pow_right_comm (l : K) j (2 ^ n + 1)]
  have hω3 : ((μ : K) ^ (2 ^ n + 1) * (ν ^ j)⁻¹) ^ 3 = 1 := by
    rw [mul_pow, e1, inv_pow, pow_right_comm ν j 3, hν3,
      mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hl0))]
  have hωq : ((μ : K) ^ (2 ^ n + 1) * (ν ^ j)⁻¹) ^ 2 ^ n =
      (μ : K) ^ (2 ^ n + 1) * (ν ^ j)⁻¹ := by
    rw [mul_pow, TableBUD.norm_pow_fixed h, inv_pow, pow_right_comm ν j (2 ^ n), hνq]
  have hμν : (μ : K) ^ (2 ^ n + 1) = ν ^ j := by
    have := TableBUD.eq_one_of_fixed_of_pow h hpq hωq hω3
    rwa [mul_inv_eq_one₀ hνj0] at this
  have hgM : ((GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = ((μ⁻¹ : Kˣ) : K) • (y : Matrix (Fin d) (Fin d) K) ^ j := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul,
      Units.val_pow_eq_pow_val]
  have hg : TableBUD.herm n ((GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hgM, hsmul, TableBUD.herm_pow h hhy j, smul_smul, Units.val_inv_eq_inv_val, inv_pow, hμν,
      inv_mul_cancel₀ hνj0, one_smul]
  change (((GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (1 : GL (Fin d) K) *
    ((GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (1 : GL (Fin d) K)
  rw [Units.val_one, Matrix.mul_one, ← TableBUD.map_pow_eq_map_bar h, ← TableBUD.herm, hg]

theorem false_of_unitary_noncomm_three (h : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1) (hd3 : 3 ∣ d) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ M : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
      ∀ l : L', TableB.projConj (unitarySU 2 n K d) M (ψ l) = ψ (a l))
    {x y : GL (Fin d) K} (hx : x ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hy : y ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hxA : TableB.projConj (unitarySU 2 n K d) ⟨x, TableBUE.gu_subset_normalizer h hx⟩ ∈
      TypeA.inducedSub ψ A)
    (hyA : TableB.projConj (unitarySU 2 n K d) ⟨y, TableBUE.gu_subset_normalizer h hy⟩ ∈
      TypeA.inducedSub ψ A)
    (hxU : x ∈ primeFormUnitary h (idGram K d)) (hxp : x ^ 3 = 1) {u : Kˣ} (hu1 : u ≠ 1)
    (hup : u ^ 3 = 1) (hxy : x * y = GeneralLinearGroup.scalar (Fin d) u * (y * x))
    [Fact (Nat.Prime 3)] {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (hh : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hdiag : ∀ i, α i (hh i) = 2) (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • hh i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  obtain ⟨m, hdm⟩ := hd3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hd0 : 0 < d := by omega
  have : NeZero 3 := ⟨by norm_num⟩
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hc := QuotMove.isScalarQuot_PSU hK hd hdq hp hpq
  have hpK : 3 ∣ Nat.card K - 1 := TableBUD.dvd_card_sub_one' h hpq
  obtain ⟨ζ₀, hζ₀⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpK
  set ζ : Kˣ := (hζ₀.isUnit (by norm_num)).unit with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := by
    rw [← IsPrimitiveRoot.coe_units_iff, hζdef, IsUnit.unit_spec]
    exact hζ₀
  obtain ⟨k, -, hk⟩ := QuotMove.exists_pow_eq_units hζ hup
  have hk0 : ¬ 3 ∣ k := by
    rintro ⟨j, rfl⟩
    apply hu1
    rw [← hk, pow_mul, hζ.pow_eq_one, one_pow]
  have hxy' : x * y = GeneralLinearGroup.scalar (Fin d) (ζ ^ k) * (y * x) := by
    rw [hk]; exact hxy
  have hUN : ∀ {g : GL (Fin d) K}, g ∈ primeFormUnitary h (idGram K d) →
      g ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := fun hg =>
    TableBUE.gu_subset_normalizer h (TableBUD.mem_guSet_of_mem_primeFormUnitary h hg)
  have hSU : ∀ {g : GL (Fin d) K}, g ∈ primeFormUnitary h (idGram K d) →
      (g : Matrix (Fin d) (Fin d) K).det = 1 → g ∈ unitarySU 2 n K d := by
    intro g hg hdet
    refine (mem_unitarySU_iff (n := d) h).mpr ⟨hdet, ?_⟩
    have h1 := mem_primeFormUnitary.mp hg
    simpa [idGram] using h1
  have : Finite (LargeEvenProj (unitarySU 2 n K d)) := Finite.of_surjective ψ hψ
  have : Finite (MulAut (LargeEvenProj (unitarySU 2 n K d))) :=
    Finite.of_injective (fun f : MulAut (LargeEvenProj (unitarySU 2 n K d)) =>
      (f : LargeEvenProj (unitarySU 2 n K d) → _)) DFunLike.coe_injective
  set X := TypeA.inducedSub ψ A with hXdef
  have hXab : IsElemAbelian 3 X := TypeA.isElemAbelian_inducedSub hψ hA
  set x₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    ⟨x, TableBUE.gu_subset_normalizer h hx⟩ with hx₀
  set y₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    ⟨y, TableBUE.gu_subset_normalizer h hy⟩ with hy₀
  obtain ⟨l, hl⟩ := hc.ker (y₀ ^ 3) (by rw [map_pow]; exact hXab.2 _ hyA)
  have hl' : y ^ 3 = GeneralLinearGroup.scalar (Fin d) l := hl
  obtain ⟨Dx, hDxU, hDxdet, hDx⟩ :=
    UnitaryPhase.exists_unitary_quadPhase_three h hpq hζ hxU hxp hu1 hup hxy
  have hdm3 : d / 3 = m := by rw [hdm, Nat.mul_div_cancel_left _ (by norm_num)]
  have hDxdet' : (Dx : Matrix (Fin d) (Fin d) K).det = (ζ : K) ^ m := by
    rw [hDxdet, hdm3]
  set Dx₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := ⟨Dx, hUN hDxU⟩
    with hDx₀
  have hDxN := QuotMove.conj_mem_inducedSub_of_phase hc hp hζ hψ hA hAI (x₀ := x₀) hxA hxp Dx₀
    hDx
  obtain ⟨cx, hcx⟩ := hDx y k hxy'
  by_cases hcube : ∃ b : Kˣ, b ^ 3 = l
  ·
    obtain ⟨b, hb⟩ := hcube
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : GL (Fin d) K, y₁ = GeneralLinearGroup.scalar (Fin d) b⁻¹ * y :=
      ⟨_, rfl⟩
    have hy₁p : y₁ ^ 3 = 1 := by
      rw [hy₁, (TypeA.PGLTor.commute_scalar _ y).mul_pow, hl', ← map_pow, ← map_mul, inv_pow, hb,
        inv_mul_cancel, map_one]
    have hy₁U : y₁ ∈ primeFormUnitary h (idGram K d) := by
      refine TableBUD.mem_primeFormUnitary_of_pow_eq_one (c := ((b⁻¹ : Kˣ) : K)) h hpq hd0 hy
        ?_ hy₁p
      rw [hy₁, Units.val_mul, GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul]
    have hyx : y * x = GeneralLinearGroup.scalar (Fin d) u⁻¹ * (x * y) := by
      rw [hxy, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have hy₁x : y₁ * x = GeneralLinearGroup.scalar (Fin d) u⁻¹ * (x * y₁) := by
      rw [hy₁, mul_assoc, hyx, ← mul_assoc, ← map_mul, mul_comm b⁻¹ u⁻¹, map_mul, mul_assoc,
        ← mul_assoc (GeneralLinearGroup.scalar (Fin d) b⁻¹) x y,
        (TypeA.PGLTor.commute_scalar b⁻¹ x).eq, mul_assoc]
    obtain ⟨Dy, hDyU, hDydet, hDy⟩ := UnitaryPhase.exists_unitary_quadPhase_three h hpq hζ hy₁U
      hy₁p (inv_ne_one.mpr hu1) (by rw [inv_pow, hup, inv_one]) hy₁x
    set y₁₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := ⟨y₁, hUN hy₁U⟩
      with hy₁₀
    have hy₁A : TableB.projConj (unitarySU 2 n K d) y₁₀ ∈ X := by
      have e : y₁₀ = ⟨GeneralLinearGroup.scalar (Fin d) b⁻¹, hc.scalar_mem _⟩ * y₀ :=
        Subtype.ext hy₁
      rw [e, map_mul, hc.map_scalar, one_mul]
      exact hyA
    set Dy₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := ⟨Dy, hUN hDyU⟩
      with hDy₀
    have hDyN := QuotMove.conj_mem_inducedSub_of_phase hc hp hζ hψ hA hAI (x₀ := y₁₀) hy₁A hy₁p
      Dy₀ hDy
    obtain ⟨cy, hcy⟩ := hDy y₁ 0 (by rw [pow_zero, map_one, one_mul])
    have hdet : ((Dx * Dy⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
      have h1 : ((Dy * Dy⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
        rw [mul_inv_cancel, Units.val_one, Matrix.det_one]
      rw [Units.val_mul, Matrix.det_mul] at h1 ⊢
      rw [hDxdet]
      rw [hDydet] at h1
      exact h1
    have hEU : Dx * Dy⁻¹ ∈ unitarySU 2 n K d :=
      hSU (Subgroup.mul_mem _ hDxU (Subgroup.inv_mem _ hDyU)) hdet
    refine QuotMove.false_of_normalizing_move hc hp hpK (by norm_num) hψ hker hperf hA hAI
      (x₀ := x₀) (y₀ := y₀) hxA hyA hxy hu1 ⟨Dx * Dy⁻¹, hEU⟩ ?_ hk0 (uE := cx * cy⁻¹) ?_
      ι φ hh α hdiag hlin hgen
    · intro z hz
      have e : Subgroup.inclusion hc.le (⟨Dx * Dy⁻¹, hEU⟩ : unitarySU 2 n K d) = Dx₀ * Dy₀⁻¹ :=
        Subtype.ext rfl
      have key : ∀ {G : Type} [Group G] (a b w : G),
          a * b⁻¹ * w * (a * b⁻¹)⁻¹ = a * (b⁻¹ * w * b) * a⁻¹ := by
        intros; group
      rw [e, map_mul, map_inv, key]
      exact hDxN _ (TypeA.conj_inv_mem_of_conj_mem hDyN z hz)
    ·
      have e1 : Dy * y₁ * Dy⁻¹ = GeneralLinearGroup.scalar (Fin d) cy * y₁ := by
        simpa using hcy
      have hy₀₁ : y = GeneralLinearGroup.scalar (Fin d) b * y₁ := by
        rw [hy₁, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      have e3 : y₁ = GeneralLinearGroup.scalar (Fin d) cy * (Dy⁻¹ * y₁ * Dy) := by
        have := TypeA.conj_scalar_mul Dy⁻¹ y₁ cy
        rw [inv_inv, ← e1, show Dy⁻¹ * (Dy * y₁ * Dy⁻¹) * Dy = y₁ by group] at this
        exact this
      have e2 : Dy⁻¹ * y₁ * Dy = GeneralLinearGroup.scalar (Fin d) cy⁻¹ * y₁ := by
        calc Dy⁻¹ * y₁ * Dy = GeneralLinearGroup.scalar (Fin d) cy⁻¹ *
              (GeneralLinearGroup.scalar (Fin d) cy * (Dy⁻¹ * y₁ * Dy)) := by
              rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
          _ = GeneralLinearGroup.scalar (Fin d) cy⁻¹ * y₁ := by rw [← e3]
      have h1 : Dy⁻¹ * y * Dy = GeneralLinearGroup.scalar (Fin d) cy⁻¹ * y := by
        have e4 := TypeA.conj_scalar_mul Dy⁻¹ y₁ b
        rw [inv_inv, ← hy₀₁, e2] at e4
        rw [e4, hy₀₁, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm b cy⁻¹]
      show Dx * Dy⁻¹ * y * (Dx * Dy⁻¹)⁻¹ =
        GeneralLinearGroup.scalar (Fin d) (cx * cy⁻¹) * (y * x ^ k)
      rw [_root_.mul_inv_rev, inv_inv, show Dx * Dy⁻¹ * y * (Dy * Dx⁻¹) =
        Dx * (Dy⁻¹ * y * Dy) * Dx⁻¹ by group, h1, TypeA.conj_scalar_mul, hcx, ← mul_assoc,
        ← map_mul, mul_comm cy⁻¹ cx]
  ·
    have hdety : (y : Matrix (Fin d) (Fin d) K).det = (l : K) ^ m := by
      have := TypeA.PGLTor.det_eq_pow_of_pow_eq_scalar (p := 3) (by norm_num) hxp hu1 hup hxy hl'
      rwa [Fintype.card_fin, hdm3] at this
    obtain ⟨j, -, μ, hμ3⟩ := TypeA.exists_cube_of_not_cube hcube ζ
    have hμK : (μ : K) ^ 3 = (ζ : K) * (l : K) ^ j := by
      have := congrArg (fun u : Kˣ => (u : K)) hμ3
      simpa using this
    have hEU : Dx * (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j) ∈ unitarySU 2 n K d := by
      refine hSU (Subgroup.mul_mem _ hDxU
        (UnitaryPhase.scalar_inv_mul_pow_mem_primeFormUnitary h hpq hd0 hy hl' hζ.pow_eq_one
          hμ3)) ?_
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hDxdet',
        Units.val_pow_eq_pow_val, Matrix.det_pow, hdety, hdm]
      calc (ζ : K) ^ m * (((μ⁻¹ : Kˣ) : K) ^ (3 * m) * ((l : K) ^ m) ^ j)
          = (((μ⁻¹ : Kˣ) : K) ^ 3 * ((ζ : K) * (l : K) ^ j)) ^ m := by ring
        _ = 1 := by
          rw [← hμK, ← mul_pow, Units.val_inv_eq_inv_val, inv_mul_cancel₀ μ.ne_zero, one_pow,
            one_pow]
    set E₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      Dx₀ * (⟨GeneralLinearGroup.scalar (Fin d) μ⁻¹, hc.scalar_mem _⟩ * y₀ ^ j) with hE₀
    have e : Subgroup.inclusion hc.le
        (⟨Dx * (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j), hEU⟩ : unitarySU 2 n K d) = E₀ :=
      Subtype.ext rfl
    refine QuotMove.false_of_normalizing_move hc hp hpK (by norm_num) hψ hker hperf hA hAI
      (x₀ := x₀) (y₀ := y₀) hxA hyA hxy hu1 ⟨_, hEU⟩ ?_ hk0 (uE := cx) ?_ ι φ hh α hdiag hlin
      hgen
    · intro z hz
      have key : ∀ {G : Type} [Group G] (a b w : G),
          a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by
        intros; group
      rw [e, hE₀, map_mul, map_mul, hc.map_scalar, one_mul, map_pow, key]
      exact hDxN _ (X.mul_mem (X.mul_mem (X.pow_mem hyA _) hz) (X.inv_mem (X.pow_mem hyA _)))
    · have hY : (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j) * y *
          (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j)⁻¹ = y := by
        rw [_root_.mul_inv_rev, show GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j * y *
            ((y ^ j)⁻¹ * (GeneralLinearGroup.scalar (Fin d) μ⁻¹)⁻¹) =
            GeneralLinearGroup.scalar (Fin d) μ⁻¹ * (y ^ j * y * (y ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin d) μ⁻¹)⁻¹ by group,
          ← pow_succ, pow_succ', mul_inv_cancel_right,
          (TypeA.PGLTor.commute_scalar μ⁻¹ y).eq, mul_inv_cancel_right]
      show Dx * (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j) * y *
          (Dx * (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j))⁻¹ =
        GeneralLinearGroup.scalar (Fin d) cx * (y * x ^ k)
      rw [show Dx * (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j) * y *
          (Dx * (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j))⁻¹ =
          Dx * ((GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j) * y *
            (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * y ^ j)⁻¹) * Dx⁻¹ by group, hY, hcx]

end UnitaryPhase

theorem ggWNormConclAt_unitary_twice_prime {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hdp : d = 2 * p)
    (hperfSU : commutator (unitarySU 2 n K d) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K d), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K d) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K d) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (h3 : p ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent p A) :
    GGWNormConclAt p A := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd : 5 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have h := TableBU.unitaryFieldData_of_card hK hn
  intro _ Λ _ _ M C V _ _ ι φ hh α hM hC hpair hlin hgen s hs
  classical
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : IsElemAbelian p Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hcardAb : Nat.card Ab = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)
  have hcard : p ^ (d / p) < Nat.card Ab := by
    rw [hcardAb, hdp, Nat.mul_div_cancel _ hp.pos]
    exact (Nat.pow_lt_pow_right hp.one_lt (by norm_num)).trans_le h3
  rcases TableBUD.exists_unitary_frame_or_noncomm h hK (by omega) hdq hp hpq hAb hAbI hcard with
    ⟨P, hP, hframe⟩ | ⟨x, y, hx, hy, hxA, hyA, hxU, hxp, u, hu1, hup, hxy⟩
  · obtain ⟨π, hπs, hπker, hdiag⟩ :=
      LineU.exists_diagModel_of_frame h hd hperfSU hcov' hψ hker hperf hAI hP hframe
    have hπ : UnitTB.Model π := ⟨h, hπs, hπker⟩
    exact ggWNormConcl_of_unitary_diagonal hK hp hp2 hpq hd hπ hA h3 hsc hdiag
      hM hC ι φ hh α hpair hlin hgen hs
  · exfalso
    have hAI' : ∀ a ∈ A, ∃ M' : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
        ∀ l : L', TableB.projConj (unitarySU 2 n K d) M' (ψ l) = ψ (a l) := by
      intro a ha
      obtain ⟨z, hz, hza⟩ := hAI a ha
      obtain ⟨M', hM', rfl⟩ := TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h) hz
      exact ⟨_, hza⟩
    have hdiag : ∀ i, α i (hh i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
    rcases eq_or_ne p 3 with rfl | hp3'
    · exact UnitaryPhase.false_of_unitary_noncomm_three h hK hpq ⟨2, by omega⟩ (by omega) hdq hψ hker
        hperf hA hAI'
        hx hy hxA hyA hxU hxp hu1 hup hxy ι φ hh α hdiag hlin hgen
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by norm_num)
      omega
    have hpK : p ∣ Nat.card K - 1 := TableBUD.dvd_card_sub_one' h hpq
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨ζ₀, hζ₀⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpK
    set ζ : Kˣ := (hζ₀.isUnit hp.ne_zero).unit with hζdef
    have hζ : IsPrimitiveRoot ζ p := by
      rw [← IsPrimitiveRoot.coe_units_iff, hζdef, IsUnit.unit_spec]
      exact hζ₀
    obtain ⟨D, hDSU, hDact⟩ :=
      UnitaryPhase.exists_unitary_quadPhase h hp hp5 hpq hζ hxU hxp hu1 hup hxy
    have hc := QuotMove.isScalarQuot_PSU hK (by omega) hdq hp hpq
    set x₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      ⟨x, TableBUE.gu_subset_normalizer h hx⟩ with hx₀
    set y₀ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      ⟨y, TableBUE.gu_subset_normalizer h hy⟩ with hy₀
    obtain ⟨k, -, hk⟩ := QuotMove.exists_pow_eq_units hζ hup
    have hk0 : ¬ p ∣ k := by
      rintro ⟨j, rfl⟩
      apply hu1
      rw [← hk, pow_mul, hζ.pow_eq_one, one_pow]
    obtain ⟨cE, hcE⟩ := hDact y k (by rw [hk]; exact hxy)
    exact QuotMove.false_of_normalizing_move hc hp hpK hp2 hψ hker hperf hA hAI' (x₀ := x₀)
      (y₀ := y₀) hxA hyA hxy hu1 ⟨D, hDSU⟩
      (QuotMove.conj_mem_inducedSub_of_phase hc hp hζ hψ hA hAI' hxA hxp
        (Subgroup.inclusion hc.le ⟨D, hDSU⟩) hDact)
      hk0 hcE ι φ hh α hdiag hlin hgen


theorem ggTorusWNormSC_unitary_twice_prime {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hdp : d = 2 * p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd : 5 ≤ d := by omega
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  by_cases hd6 : (d, n) = (6, 1)
  ·
    obtain ⟨rfl, rfl⟩ : d = 6 ∧ n = 1 := Prod.mk.inj hd6
    obtain rfl : p = 3 := by omega
    have hcov := LineU.unitaryCoverOddAt_six_two K (by rw [hK]; norm_num)
    have hR := TableBUE.center_proj_eq_bot (d := 6) hK (by norm_num) (by decide)
    exact ggWNormConclAt_descent hker hR hψ hperf hA hAI h3 hsc
      fun L₁ _ _ ψ₁ hs hk hp' hodd A₁ hA₁ hAI₁ h3₁ hsc₁ =>
        ggWNormConclAt_unitary_twice_prime hK le_rfl hp hp2 hpq rfl hcov.1
          (fun ψ'' hs'' hk'' => hcov.2 L₁ ψ'' hs'' (hk'' ▸ hk) hp' (hk'' ▸ hodd)) hs hk hp' hA₁
          hAI₁ h3₁ hsc₁
  · have hcov := LineU.unitaryCoverAt hK hd hd6
    exact ggWNormConclAt_unitary_twice_prime hK hn hp hp2 hpq hdp hcov.1
      (fun ψ'' hs hk => hcov.2 L' ψ'' hs (hk ▸ hker) hperf) hψ hker hperf hA hAI h3 hsc

theorem largeEvenLabelAll_wnorm_unitary_twice_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ lab.n) (ht : lab.tag = .twA)
    (hdp : lab.rank + 1 = 2 * p) (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hn hdp hpq ⊢
  subst tag
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_unitary_twice_prime hK hn hp hp2 hpq hdp

end CFSG.StandardType
