module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoDefs
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.Representation

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Open QuadraticMap

private theorem omSevenGI_two_ne_zero {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) :
    (2 : K) ≠ 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rwa [Nat.card_eq_fintype_card] at hK
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime (R := K) (p := 3) (by norm_num) hcard
  intro h2
  have h2' : e (2 : ZMod 3) = e 0 := by
    rw [map_zero, map_ofNat]
    exact h2
  have h : (2 : ZMod 3) = 0 := e.injective h2'
  exact absurd h (by decide)

private theorem omSevenGI_three_eq_zero {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) :
    (3 : K) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rwa [Nat.card_eq_fintype_card] at hK
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime (R := K) (p := 3) (by norm_num) hcard
  have h3 : (3 : ZMod 3) = 0 := by decide
  calc (3 : K) = e (3 : ZMod 3) := (map_ofNat e 3).symm
    _ = e 0 := by rw [h3]
    _ = 0 := map_zero e

private theorem omSevenGI_sq_eq_one {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3)
    {a : K} (ha : a ≠ 0) : a ^ 2 = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rwa [Nat.card_eq_fintype_card] at hK
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [hcard] at h

private theorem omSevenGI_eq_one_or_neg_one {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3)
    {a : K} (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  have h := omSevenGI_sq_eq_one hK ha
  exact sq_eq_one_iff.mp h

private theorem omSevenGI_rep_two_zmod (a b c : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ x y : ZMod 3, a * x ^ 2 + b * y ^ 2 = c := by
  revert a b c
  decide

private theorem omSevenGI_three_zero_zmod (a b c : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ x y z : ZMod 3, (x, y, z) ≠ 0 ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  revert a b c
  decide

private theorem omSevenGI_rep_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3)
    {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ x y : K, a * x ^ 2 + b * y ^ 2 = c := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rwa [Nat.card_eq_fintype_card] at hK
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime (R := K) (p := 3) (by norm_num) hcard
  have ha' : e.symm a ≠ 0 := by
    intro h
    exact ha (by rw [← e.apply_symm_apply a, h, map_zero])
  have hb' : e.symm b ≠ 0 := by
    intro h
    exact hb (by rw [← e.apply_symm_apply b, h, map_zero])
  have hc' : e.symm c ≠ 0 := by
    intro h
    exact hc (by rw [← e.apply_symm_apply c, h, map_zero])
  obtain ⟨x, y, hxy⟩ := omSevenGI_rep_two_zmod (e.symm a) (e.symm b) (e.symm c) ha' hb' hc'
  refine ⟨e x, e y, ?_⟩
  have h : e (e.symm a * x ^ 2 + e.symm b * y ^ 2) = e (e.symm c) := by rw [hxy]
  simpa [map_add, map_mul, map_pow] using h

private theorem omSevenGI_three_zero {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3)
    {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ x y z : K, (x, y, z) ≠ 0 ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rwa [Nat.card_eq_fintype_card] at hK
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime (R := K) (p := 3) (by norm_num) hcard
  have ha' : e.symm a ≠ 0 := by
    intro h
    exact ha (by rw [← e.apply_symm_apply a, h, map_zero])
  have hb' : e.symm b ≠ 0 := by
    intro h
    exact hb (by rw [← e.apply_symm_apply b, h, map_zero])
  have hc' : e.symm c ≠ 0 := by
    intro h
    exact hc (by rw [← e.apply_symm_apply c, h, map_zero])
  obtain ⟨x, y, z, hxyz, hxyz0⟩ :=
    omSevenGI_three_zero_zmod (e.symm a) (e.symm b) (e.symm c) ha' hb' hc'
  refine ⟨e x, e y, e z, ?_, ?_⟩
  · intro h
    apply hxyz
    have h1 : e x = 0 := by simpa using congrArg (fun t : K × K × K => t.1) h
    have h2 : e y = 0 := by simpa using congrArg (fun t : K × K × K => t.2.1) h
    have h3 : e z = 0 := by simpa using congrArg (fun t : K × K × K => t.2.2) h
    have h1' : x = 0 := e.injective (by rw [h1, map_zero])
    have h2' : y = 0 := e.injective (by rw [h2, map_zero])
    have h3' : z = 0 := e.injective (by rw [h3, map_zero])
    simp [h1', h2', h3']
  · have h : e (e.symm a * x ^ 2 + e.symm b * y ^ 2 + e.symm c * z ^ 2) = e 0 := by
      rw [hxyz0, map_zero]
    simpa [map_add, map_mul, map_pow] using h

private theorem omSevenGI_exists_orthogonal_basis {K M : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {q : QuadraticForm K M} (hq : q.Nondegenerate) :
    ∃ b : Module.Basis (Fin (Module.finrank K M)) K M,
      (∀ i j, i ≠ j → q.IsOrtho (b i) (b j)) ∧ ∀ i, q (b i) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := omSevenGI_two_ne_zero hK
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  exact hq.exists_orthogonal_basis

private theorem omSevenGI_isOrtho_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {q : QuadraticForm K M} {x y : M} (h : q.IsOrtho x y) (a b : K) :
    q.IsOrtho (a • x) (b • y) := by
  rw [isOrtho_def]
  rw [QuadraticMap.map_add q]
  have hp : polar q (a • x) (b • y) = 0 := by
    rw [polar_smul_left, polar_smul_right, IsOrtho.polar_eq_zero h, smul_zero, smul_zero]
  rw [hp, add_zero]

private theorem omSevenGI_q_add_two {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {q : QuadraticForm K M} {x y : M} (h : q.IsOrtho x y) :
    q (x + y) = q x + q y := by
  rw [QuadraticMap.map_add q, IsOrtho.polar_eq_zero h, add_zero]

private theorem omSevenGI_q_add_three {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {q : QuadraticForm K M} {x y z : M} (hxy : q.IsOrtho x y) (hxz : q.IsOrtho x z)
    (hyz : q.IsOrtho y z) : q (x + y + z) = q x + q y + q z := by
  have h1 : polar q (x + y) z = 0 := by
    rw [polar_add_left, IsOrtho.polar_eq_zero hxz, IsOrtho.polar_eq_zero hyz, add_zero]
  rw [QuadraticMap.map_add q, h1, add_zero, omSevenGI_q_add_two hxy]

private theorem omSevenGI_q_two_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {q : QuadraticForm K M} {x y : M} (a b : K) (h : q.IsOrtho x y) :
    q (a • x + b • y) = a ^ 2 * q x + b ^ 2 * q y := by
  rw [QuadraticMap.map_add q, IsOrtho.polar_eq_zero (omSevenGI_isOrtho_smul h a b), add_zero,
    map_smul_eq_sq, map_smul_eq_sq]

private theorem omSevenGI_q_three_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {q : QuadraticForm K M} {x y z : M} (a b c : K)
    (hxy : q.IsOrtho x y) (hxz : q.IsOrtho x z) (hyz : q.IsOrtho y z) :
    q (a • x + b • y + c • z) = a ^ 2 * q x + b ^ 2 * q y + c ^ 2 * q z := by
  have h1 : q.IsOrtho (a • x) (b • y) := omSevenGI_isOrtho_smul hxy a b
  have h2 : q.IsOrtho (a • x) (c • z) := omSevenGI_isOrtho_smul hxz a c
  have h3 : q.IsOrtho (b • y) (c • z) := omSevenGI_isOrtho_smul hyz b c
  rw [omSevenGI_q_add_three h1 h2 h3, map_smul_eq_sq, map_smul_eq_sq, map_smul_eq_sq]

private theorem omSevenGI_exists_singular {K M : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (q : QuadraticForm K M) (hq : q.Nondegenerate) (hrank : 3 ≤ Module.finrank K M) :
    ∃ u : M, u ≠ 0 ∧ q u = 0 := by
  obtain ⟨b, hortho, haniso⟩ := omSevenGI_exists_orthogonal_basis hK hq
  let i0 : Fin (Module.finrank K M) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K M) := ⟨1, by omega⟩
  let i2 : Fin (Module.finrank K M) := ⟨2, by omega⟩
  obtain ⟨x, y, z, hxyz, hzero⟩ :=
    omSevenGI_three_zero hK (haniso i0) (haniso i1) (haniso i2)
  refine ⟨x • b i0 + y • b i1 + z • b i2, ?_, ?_⟩
  · intro hu
    have h01 : i0 ≠ i1 := by simp [i0, i1]
    have h02 : i0 ≠ i2 := by simp [i0, i2]
    have h12 : i1 ≠ i2 := by simp [i1, i2]
    let idx : Fin 3 → Fin (Module.finrank K M) := fun i => ![i0, i1, i2] i
    have hidx : Function.Injective idx := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [idx]
    have hli := b.linearIndependent.comp idx hidx
    have hsum : (∑ i : Fin 3, ![x, y, z] i • b (idx i)) = 0 := by
      simpa [idx, Fin.sum_univ_three] using hu
    have hx0 := (Fintype.linearIndependent_iff.mp hli) ![x, y, z] hsum 0
    have hy0 := (Fintype.linearIndependent_iff.mp hli) ![x, y, z] hsum 1
    have hz0 := (Fintype.linearIndependent_iff.mp hli) ![x, y, z] hsum 2
    exact hxyz (by
      have hx0' : x = 0 := by simpa using hx0
      have hy0' : y = 0 := by simpa using hy0
      have hz0' : z = 0 := by simpa using hz0
      simp [hx0', hy0', hz0'])
  · have h01 : i0 ≠ i1 := by simp [i0, i1]
    have h02 : i0 ≠ i2 := by simp [i0, i2]
    have h12 : i1 ≠ i2 := by simp [i1, i2]
    rw [omSevenGI_q_three_smul x y z (hortho i0 i1 h01) (hortho i0 i2 h02) (hortho i1 i2 h12)]
    linear_combination hzero

private theorem omSevenGI_exists_rep_one {K M : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (q : QuadraticForm K M) (hq : q.Nondegenerate) (hrank : 2 ≤ Module.finrank K M)
    {c : K} (hc : c ≠ 0) : ∃ x : M, q x = c := by
  obtain ⟨b, hortho, haniso⟩ := omSevenGI_exists_orthogonal_basis hK hq
  let i0 : Fin (Module.finrank K M) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K M) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  obtain ⟨x, y, hxy⟩ := omSevenGI_rep_two hK (haniso i0) (haniso i1) hc
  refine ⟨x • b i0 + y • b i1, ?_⟩
  rw [omSevenGI_q_two_smul x y (hortho i0 i1 h01)]
  linear_combination hxy

private theorem omSevenGI_exists_hypPair {K M : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (q : QuadraticForm K M) (hq : q.Nondegenerate) (hrank : 3 ≤ Module.finrank K M) :
    ∃ e f : M, q e = 0 ∧ q f = 0 ∧ polar q e f = 1 := by
  obtain ⟨u, hu0, huq⟩ := omSevenGI_exists_singular hK q hq hrank
  have h2 : (2 : K) ≠ 0 := omSevenGI_two_ne_zero hK
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  have hiso : ¬ q.Anisotropic := not_anisotropic_iff_exists q |>.mpr ⟨u, hu0, huq⟩
  obtain ⟨x, y, hx, hxq, hyq, hxy⟩ := hq.exists_isotropic_pair hiso
  exact ⟨x, y, hxq, hyq, hxy⟩

private noncomputable def omSevenGI_plus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) :
    Submodule K (OmegaSevenIdx → K) :=
  LinearMap.ker (A.toLinearMap - LinearMap.id)

private noncomputable def omSevenGI_minus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) :
    Submodule K (OmegaSevenIdx → K) :=
  LinearMap.ker (A.toLinearMap + LinearMap.id)

private theorem omSevenGI_mem_plus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (v : OmegaSevenIdx → K) :
    v ∈ omSevenGI_plus A ↔ A v = v := by
  simp [omSevenGI_plus, LinearMap.mem_ker, sub_eq_zero]

private theorem omSevenGI_mem_minus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (v : OmegaSevenIdx → K) :
    v ∈ omSevenGI_minus A ↔ A v = -v := by
  simp [omSevenGI_minus, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

private theorem omSevenGI_A_sq {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (v : OmegaSevenIdx → K) : A (A v) = v := by
  have := congrArg (fun e : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K) => e v) hA2
  simpa using this

private theorem omSevenGI_mem_plus_decomp {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) (x : OmegaSevenIdx → K) :
    (2 : K)⁻¹ • (x + A x) ∈ omSevenGI_plus A := by
  rw [omSevenGI_mem_plus, map_smul, map_add, omSevenGI_A_sq A hA2]
  exact congrArg (fun y => (2 : K)⁻¹ • y) (add_comm (A x) x)

private theorem omSevenGI_mem_minus_decomp {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) (x : OmegaSevenIdx → K) :
    (2 : K)⁻¹ • (x - A x) ∈ omSevenGI_minus A := by
  rw [omSevenGI_mem_minus, map_smul, map_sub, omSevenGI_A_sq A hA2, ← smul_neg, neg_sub]

private theorem omSevenGI_decomp {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) (x : OmegaSevenIdx → K) :
    (2 : K)⁻¹ • (x + A x) + (2 : K)⁻¹ • (x - A x) = x := by
  rw [← smul_add]
  have hsum : (x + A x) + (x - A x) = (2 : K) • x := by
    rw [two_smul]
    abel
  rw [hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]

private theorem omSevenGI_sup_plus_minus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) : omSevenGI_plus A ⊔ omSevenGI_minus A = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← omSevenGI_decomp A hA2 h2 x]
  exact Submodule.mem_sup.mpr ⟨_, omSevenGI_mem_plus_decomp A hA2 h2 x, _,
    omSevenGI_mem_minus_decomp A hA2 h2 x, rfl⟩

private theorem omSevenGI_inf_plus_minus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) : omSevenGI_plus A ⊓ omSevenGI_minus A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  have hp := (omSevenGI_mem_plus A x).mp hx.1
  have hm := (omSevenGI_mem_minus A x).mp hx.2
  rw [hp] at hm
  have hxx : x + x = 0 := eq_neg_iff_add_eq_zero.mp hm
  have h2x : (2 : K) • x = 0 := by rw [two_smul, hxx]
  rcases smul_eq_zero.mp h2x with h | h
  · exact absurd h h2
  · exact h

private theorem omSevenGI_isCompl {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) : IsCompl (omSevenGI_plus A) (omSevenGI_minus A) :=
  ⟨disjoint_iff.mpr (omSevenGI_inf_plus_minus A hA2 h2),
    codisjoint_iff.mpr (omSevenGI_sup_plus_minus A hA2 h2)⟩

private theorem omSevenGI_polar_plus_minus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) {u w : OmegaSevenIdx → K} (hu : u ∈ omSevenGI_plus A)
    (hw : w ∈ omSevenGI_minus A) : polar (quadOdd 3 K) u w = 0 := by
  have hu' := (omSevenGI_mem_plus A u).mp hu
  have hw' := (omSevenGI_mem_minus A w).mp hw
  have hp : polar (quadOdd 3 K) u w = -polar (quadOdd 3 K) u w := by
    have h := polar_map_of_mem hA u w
    rw [hu', hw', polar_neg_right] at h
    exact h.symm
  have h2p : polar (quadOdd 3 K) u w + polar (quadOdd 3 K) u w = 0 := by
    nth_rewrite 2 [hp]
    rw [add_neg_cancel]
  have : (2 : K) * polar (quadOdd 3 K) u w = 0 := by rw [two_mul, h2p]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2
  · exact h

private theorem omSevenGI_polarNondegOn_plus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) : PolarNondegOn (quadOdd 3 K) (omSevenGI_plus A) := by
  intro x hx hxorth
  apply eq_zero_of_polar_eq_zero (nondegenerate_polarBilin_quadOdd (K := K) (n := 3) h2)
  intro z
  have hz : z ∈ omSevenGI_plus A ⊔ omSevenGI_minus A := by
    rw [omSevenGI_sup_plus_minus A hA2 h2]
    exact Submodule.mem_top
  obtain ⟨zp, hzp, zm, hzm, hsum⟩ := Submodule.mem_sup.mp hz
  rw [← hsum, polar_add_right, hxorth zp hzp,
    omSevenGI_polar_plus_minus A hA hA2 h2 hx hzm, add_zero]

private theorem omSevenGI_polarNondegOn_minus {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) : PolarNondegOn (quadOdd 3 K) (omSevenGI_minus A) := by
  intro x hx hxorth
  apply eq_zero_of_polar_eq_zero (nondegenerate_polarBilin_quadOdd (K := K) (n := 3) h2)
  intro z
  have hz : z ∈ omSevenGI_plus A ⊔ omSevenGI_minus A := by
    rw [omSevenGI_sup_plus_minus A hA2 h2]
    exact Submodule.mem_top
  obtain ⟨zp, hzp, zm, hzm, hsum⟩ := Submodule.mem_sup.mp hz
  rw [← hsum, polar_add_right, polar_comm (quadOdd 3 K) x zp,
    omSevenGI_polar_plus_minus A hA hA2 h2 hzp hx, hxorth zm hzm, add_zero]

private theorem omSevenGI_restrict_plus_nondegenerate {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) :
    ((quadOdd 3 K).restrict (omSevenGI_plus A)).Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  exact (QuadraticMap.nondegenerate_polar_iff).mp
    (nondegenerate_polarBilin_restrict (omSevenGI_polarNondegOn_plus A hA hA2 h2))

private theorem omSevenGI_restrict_minus_nondegenerate {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) :
    ((quadOdd 3 K).restrict (omSevenGI_minus A)).Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  exact (QuadraticMap.nondegenerate_polar_iff).mp
    (nondegenerate_polarBilin_restrict (omSevenGI_polarNondegOn_minus A hA hA2 h2))

private theorem omSevenGI_plus_ne_bot {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) (hA1' : A ≠ LinearEquiv.neg K) : omSevenGI_plus A ≠ ⊥ := by
  intro h
  apply hA1'
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ omSevenGI_minus A := by
    have htop : omSevenGI_plus A ⊔ omSevenGI_minus A = ⊤ :=
      omSevenGI_sup_plus_minus A hA2 h2
    rw [h, bot_sup_eq] at htop
    rw [htop]
    exact Submodule.mem_top
  simpa [LinearEquiv.neg_apply] using (omSevenGI_mem_minus A x).mp hx

private theorem omSevenGI_minus_ne_bot {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) (hA1 : A ≠ 1) : omSevenGI_minus A ≠ ⊥ := by
  intro h
  apply hA1
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ omSevenGI_plus A := by
    have htop : omSevenGI_plus A ⊔ omSevenGI_minus A = ⊤ :=
      omSevenGI_sup_plus_minus A hA2 h2
    rw [h, sup_bot_eq] at htop
    rw [htop]
    exact Submodule.mem_top
  simpa using (omSevenGI_mem_plus A x).mp hx

private theorem omSevenGI_finrank_V (K : Type*) [Field K] :
    Module.finrank K (OmegaSevenIdx → K) = 7 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [OmegaSevenIdx]

private theorem omSevenGI_finrank_sum {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) :
    Module.finrank K (omSevenGI_plus A) + Module.finrank K (omSevenGI_minus A) =
      Module.finrank K (OmegaSevenIdx → K) :=
  Submodule.finrank_add_eq_of_isCompl (omSevenGI_isCompl A hA2 h2)


private theorem omSevenGI_finrank_plus_pos {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) (hA1' : A ≠ LinearEquiv.neg K) :
    0 < Module.finrank K (omSevenGI_plus A) := by
  rw [Module.finrank_pos_iff]
  exact Submodule.nontrivial_iff_ne_bot.mpr (omSevenGI_plus_ne_bot A hA2 h2 hA1')

private theorem omSevenGI_finrank_minus_pos {K : Type*} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) (hA1 : A ≠ 1) :
    0 < Module.finrank K (omSevenGI_minus A) := by
  rw [Module.finrank_pos_iff]
  exact Submodule.nontrivial_iff_ne_bot.mpr (omSevenGI_minus_ne_bot A hA2 h2 hA1)

private theorem omSevenGI_polarNondegOn_orthogonal_line {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (v : OmegaSevenIdx → K) (hQv : quadOdd 3 K v ≠ 0) :
    PolarNondegOn (quadOdd 3 K)
      (LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) (K ∙ v)) := by
  intro x hx hxorth
  apply eq_zero_of_polar_eq_zero (nondegenerate_polarBilin_quadOdd (K := K) (n := 3) h2)
  intro z
  have hBvv : polarBilin (quadOdd 3 K) v v ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQv
  have hcompl := LinearMap.BilinForm.isCompl_span_singleton_orthogonal
    (B := polarBilin (quadOdd 3 K)) hBvv
  have hz : z ∈ (K ∙ v) ⊔ LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) (K ∙ v) := by
    rw [codisjoint_iff.mp hcompl.2]
    exact Submodule.mem_top
  obtain ⟨a, ha, y, hy, hsum⟩ := Submodule.mem_sup.mp hz
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hxv : polar (quadOdd 3 K) x v = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) v
      (Submodule.mem_span_singleton_self v)
    rw [polar_comm]
    simpa [polarBilin_apply_apply] using h
  rw [← hsum, polar_add_right, polar_smul_right, hxv, hxorth y hy]
  simp

private theorem omSevenGI_finrank_orthogonal_line {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (v : OmegaSevenIdx → K) (hv0 : v ≠ 0) :
    Module.finrank K (LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) (K ∙ v)) = 6 := by
  rw [LinearMap.BilinForm.finrank_orthogonal
      (nondegenerate_polarBilin_quadOdd (K := K) (n := 3) h2),
    finrank_span_singleton hv0, omSevenGI_finrank_V K]

private theorem omSevenGI_restrict_orthogonal_line_nondegenerate {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (v : OmegaSevenIdx → K) (hQv : quadOdd 3 K v ≠ 0) :
    ((quadOdd 3 K).restrict
      (LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) (K ∙ v))).Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  exact (QuadraticMap.nondegenerate_polar_iff).mp
    (nondegenerate_polarBilin_restrict (omSevenGI_polarNondegOn_orthogonal_line h2 v hQv))

private theorem omSevenGI_eichler_pair_apply {K : Type*} [Field K]
    {q : QuadraticForm K (OmegaSevenIdx → K)} {v e f : OmegaSevenIdx → K}
    (hQe : q e = 0) (hQf : q f = 0) (hev : polar q e v = 0) (hfv : polar q f v = 0)
    (hef : polar q e f = 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) = 0)
    (hqv : q v = 1 ∨ q v = -1) :
    eichler q f ((2 * q v) • v) (eichler q e v v) = q v • e + f := by
  have hve : polar q v e = 0 := by rw [polar_comm]; exact hev
  have hvf : polar q v f = 0 := by rw [polar_comm]; exact hfv
  have hvv : polar q v v = 2 * q v := polar_self_eq_two_mul q v
  have hf2 : polar q f ((2 * q v) • v) = 0 := by
    rw [polar_smul_right_eq, hfv, mul_zero]
  rw [eichler_apply hQe hev]
  rw [eichler_apply hQf hf2]
  rcases hqv with hqv | hqv
  · rw [hqv] at hvv ⊢
    simp only [mul_one, one_mul, neg_mul, mul_neg, neg_neg] at hvv ⊢
    simp only [polar_add_right, polar_add_left, polar_sub_right, polar_sub_left,
      polar_smul_right_eq, polar_smul_left_eq, hve, hev, hvf, hvv, hqv, hQe, hQf, hef,
      map_smul_eq_sq]
    ring_nf
    have h2eq : (2 : K) = -1 := by linear_combination h3
    have h4eq : (4 : K) = 1 := by linear_combination h3
    simp only [h2eq, h4eq, h3]
    module
  · rw [hqv] at hvv ⊢
    simp only [mul_one, one_mul, neg_mul, mul_neg, neg_neg] at hvv ⊢
    simp only [polar_add_right, polar_add_left, polar_sub_right, polar_sub_left,
      polar_smul_right_eq, polar_smul_left_eq, hve, hev, hvf, hvv, hqv, hQe, hQf, hef,
      map_smul_eq_sq]
    ring_nf
    have h2eq : (2 : K) = -1 := by linear_combination h3
    have h4eq : (4 : K) = 1 := by linear_combination h3
    simp only [h2eq, h4eq, h3]
    module


private theorem omSevenGI_first_disjunct_of_ranks {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0)
    (h : (3 ≤ Module.finrank K (omSevenGI_plus A) ∧
        2 ≤ Module.finrank K (omSevenGI_minus A)) ∨
      (2 ≤ Module.finrank K (omSevenGI_plus A) ∧
        3 ≤ Module.finrank K (omSevenGI_minus A))) :
    ∃ u w : OmegaSevenIdx → K, OmegaSevenShortPair u w ∧
      ((A u = u ∧ A w = -w) ∨ (A u = -u ∧ A w = w)) := by
  rcases h with ⟨hp, hm⟩ | ⟨hp, hm⟩
  · obtain ⟨u, hu0, huq⟩ := omSevenGI_exists_singular hK
      ((quadOdd 3 K).restrict (omSevenGI_plus A))
      (omSevenGI_restrict_plus_nondegenerate A hA hA2 h2) hp
    obtain ⟨w, hwq⟩ := omSevenGI_exists_rep_one hK
      ((quadOdd 3 K).restrict (omSevenGI_minus A))
      (omSevenGI_restrict_minus_nondegenerate A hA hA2 h2) hm (c := 1) one_ne_zero
    refine ⟨(u : OmegaSevenIdx → K), (w : OmegaSevenIdx → K),
      ⟨huq, ?_, omSevenGI_polar_plus_minus A hA hA2 h2 u.2 w.2, hwq⟩, Or.inl ⟨?_, ?_⟩⟩
    · intro h0
      exact hu0 (Subtype.ext h0)
    · exact (omSevenGI_mem_plus A (u : OmegaSevenIdx → K)).mp u.2
    · exact (omSevenGI_mem_minus A (w : OmegaSevenIdx → K)).mp w.2
  · obtain ⟨u, hu0, huq⟩ := omSevenGI_exists_singular hK
      ((quadOdd 3 K).restrict (omSevenGI_minus A))
      (omSevenGI_restrict_minus_nondegenerate A hA hA2 h2) hm
    obtain ⟨w, hwq⟩ := omSevenGI_exists_rep_one hK
      ((quadOdd 3 K).restrict (omSevenGI_plus A))
      (omSevenGI_restrict_plus_nondegenerate A hA hA2 h2) hp (c := 1) one_ne_zero
    refine ⟨(u : OmegaSevenIdx → K), (w : OmegaSevenIdx → K),
      ⟨huq, ?_, ?_, hwq⟩, Or.inr ⟨?_, ?_⟩⟩
    · intro h0
      exact hu0 (Subtype.ext h0)
    · rw [polar_comm]
      exact omSevenGI_polar_plus_minus A hA hA2 h2 w.2 u.2
    · exact (omSevenGI_mem_minus A (u : OmegaSevenIdx → K)).mp u.2
    · exact (omSevenGI_mem_plus A (w : OmegaSevenIdx → K)).mp w.2


private theorem omSevenGI_line_case {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    {ε : K} (hε : ε = 1 ∨ ε = -1) {v : OmegaSevenIdx → K} (hv0 : v ≠ 0)
    (hAv : A v = ε • v)
    (hperp : ∀ x : OmegaSevenIdx → K, polar (quadOdd 3 K) x v = 0 ↔ A x = -ε • x)
    (hQv : quadOdd 3 K v ≠ 0) :
    (∃ u w : OmegaSevenIdx → K, OmegaSevenShortPair u w ∧
        ((A u = u ∧ A w = -w) ∨ (A u = -u ∧ A w = w))) ∨
    (∃ g ∈ elementaryGroup (quadOdd 3 K),
      A * (g * A * g⁻¹) = (g * A * g⁻¹) * A ∧
      (∃ u w : OmegaSevenIdx → K, OmegaSevenShortPair u w ∧
        (((A * (g * A * g⁻¹)) u = u ∧ (A * (g * A * g⁻¹)) w = -w) ∨
          ((A * (g * A * g⁻¹)) u = -u ∧ (A * (g * A * g⁻¹)) w = w))) ∧
      ∃ u w : OmegaSevenIdx → K, quadOdd 3 K u = 0 ∧ u ≠ 0 ∧ polar (quadOdd 3 K) u w = 0 ∧
        quadOdd 3 K w ≠ 0 ∧ ((A u = -u ∧ A w = w) ∨ (A u = u ∧ A w = -w)) ∧
        (g * A * g⁻¹) u = A u ∧ (g * A * g⁻¹) w = -(A w)) := by
  have h2 : (2 : K) ≠ 0 := omSevenGI_two_ne_zero hK
  have h3 : (3 : K) = 0 := omSevenGI_three_eq_zero hK
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε2neg : -ε * ε = -1 := by rw [neg_mul, hε2]
  have hε2neg' : ε * -ε = -1 := by rw [mul_neg, hε2]
  have hε2negneg : -ε * -ε = 1 := by rw [neg_mul_neg, hε2]
  let W : Submodule K (OmegaSevenIdx → K) :=
    LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) (K ∙ v)
  have hWnondeg : ((quadOdd 3 K).restrict W).Nondegenerate :=
    omSevenGI_restrict_orthogonal_line_nondegenerate h2 v hQv
  have hWfin : 3 ≤ Module.finrank K W := by
    have h := omSevenGI_finrank_orthogonal_line h2 v hv0
    dsimp only [W] at h ⊢
    rw [h]
    norm_num
  by_cases hq1 : quadOdd 3 K v = 1
  · obtain ⟨u, hu0, huq⟩ :=
      omSevenGI_exists_singular hK ((quadOdd 3 K).restrict W) hWnondeg hWfin
    have hperpu : polar (quadOdd 3 K) (u : OmegaSevenIdx → K) v = 0 := by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp u.2) v
        (Submodule.mem_span_singleton_self v)
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using h
    have huA : A (u : OmegaSevenIdx → K) = -ε • (u : OmegaSevenIdx → K) :=
      (hperp (u : OmegaSevenIdx → K)).mp hperpu
    refine Or.inl ⟨(u : OmegaSevenIdx → K), v, ⟨huq, ?_, hperpu, hq1⟩, ?_⟩
    · intro h0
      exact hu0 (Subtype.ext h0)
    · rcases hε with rfl | rfl
      · right
        exact ⟨by simpa using huA, by simpa using hAv⟩
      · left
        exact ⟨by simpa using huA, by simpa using hAv⟩
  · have hqneg : quadOdd 3 K v = -1 := by
      rcases omSevenGI_eq_one_or_neg_one hK hQv with h | h
      · exact absurd h hq1
      · exact h
    obtain ⟨e, f, heQ, hfQ, hef⟩ :=
      omSevenGI_exists_hypPair hK ((quadOdd 3 K).restrict W) hWnondeg hWfin
    have hev : polar (quadOdd 3 K) (e : OmegaSevenIdx → K) v = 0 := by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp e.2) v
        (Submodule.mem_span_singleton_self v)
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using h
    have hfv : polar (quadOdd 3 K) (f : OmegaSevenIdx → K) v = 0 := by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp f.2) v
        (Submodule.mem_span_singleton_self v)
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using h
    let g : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K) :=
      eichler (quadOdd 3 K) (f : OmegaSevenIdx → K) ((2 * quadOdd 3 K v) • v) *
        eichler (quadOdd 3 K) (e : OmegaSevenIdx → K) v
    have hgmem : g ∈ elementaryGroup (quadOdd 3 K) :=
      mul_mem (eichler_mem_elementaryGroup _ _ _) (eichler_mem_elementaryGroup _ _ _)
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
      elementaryGroup_le_orthogonalGroup _ hgmem
    have hgv : g v = quadOdd 3 K v • (e : OmegaSevenIdx → K) + (f : OmegaSevenIdx → K) :=
      omSevenGI_eichler_pair_apply heQ hfQ hev hfv hef h2 h3 (Or.inr hqneg)
    have hve : polar (quadOdd 3 K) v (e : OmegaSevenIdx → K) = 0 := by
      rw [polar_comm]; exact hev
    have hvf : polar (quadOdd 3 K) v (f : OmegaSevenIdx → K) = 0 := by
      rw [polar_comm]; exact hfv
    have hgv_perp : polar (quadOdd 3 K) v (g v) = 0 := by
      rw [hgv, polar_add_right, polar_smul_right, hve, hvf]
      simp
    have heQ' : quadOdd 3 K (e : OmegaSevenIdx → K) = 0 := heQ
    have hfQ' : quadOdd 3 K (f : OmegaSevenIdx → K) = 0 := hfQ
    have hef' : polar (quadOdd 3 K) (e : OmegaSevenIdx → K) (f : OmegaSevenIdx → K) = 1 := hef
    have hQgv : quadOdd 3 K (g v) = quadOdd 3 K v := by
      rw [hgv, hqneg]
      rw [QuadraticMap.map_add (quadOdd 3 K)]
      rw [QuadraticMap.map_smul, heQ', hfQ']
      rw [polar_smul_left, hef']
      simp
    let A' : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K) := g * A * g⁻¹
    have hA'gv : A' (g v) = ε • (g v) := by
      simp only [A', LinearEquiv.mul_apply, LinearEquiv.inv_apply_apply', hAv, map_smul]
    have hA'perp : ∀ y : OmegaSevenIdx → K, polar (quadOdd 3 K) y (g v) = 0 →
        A' y = -ε • y := by
      intro y hy
      have hy' : polar (quadOdd 3 K) (g⁻¹ y) v = 0 := by
        have h := polar_map_of_mem hgO (g⁻¹ y) v
        rw [LinearEquiv.apply_inv_apply'] at h
        rw [← h]
        exact hy
      have hx := (hperp (g⁻¹ y)).mp hy'
      calc A' y = g (A (g⁻¹ y)) := by simp [A', LinearEquiv.mul_apply]
        _ = g (-ε • g⁻¹ y) := by rw [hx]
        _ = -ε • g (g⁻¹ y) := by rw [map_smul]
        _ = -ε • y := by rw [LinearEquiv.apply_inv_apply']
    have hA'v : A' v = -ε • v := hA'perp v hgv_perp
    have hAgv : A (g v) = -ε • g v := by
      apply (hperp (g v)).mp
      rwa [polar_comm]
    let P : Submodule K (OmegaSevenIdx → K) := Submodule.span K {v, g v}
    have hPpolar : PolarNondegOn (quadOdd 3 K) P := by
      intro x hx hxorth
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
      have hvP : v ∈ P := Submodule.subset_span (by simp)
      have hgvP : g v ∈ P := Submodule.subset_span (by simp)
      have hxv : polar (quadOdd 3 K) x v = 0 := hxorth v hvP
      have hxgv : polar (quadOdd 3 K) x (g v) = 0 := hxorth (g v) hgvP
      rw [← hab] at hxv hxgv
      have hvv : polar (quadOdd 3 K) v v = 2 * quadOdd 3 K v := polar_self_eq_two_mul _ _
      have hgvgv : polar (quadOdd 3 K) (g v) (g v) = 2 * quadOdd 3 K (g v) :=
        polar_self_eq_two_mul _ _
      have hgvv : polar (quadOdd 3 K) (g v) v = 0 := by rw [polar_comm]; exact hgv_perp
      rw [polar_add_left, polar_smul_left, polar_smul_left, hvv, hgvv, smul_zero,
        add_zero] at hxv
      have ha : a = 0 := (mul_eq_zero.mp hxv).resolve_right (mul_ne_zero h2 hQv)
      rw [polar_add_left, polar_smul_left, polar_smul_left, hgvgv, hgv_perp, hQgv, smul_zero,
        zero_add] at hxgv
      have hb : b = 0 := (mul_eq_zero.mp hxgv).resolve_right (mul_ne_zero h2 hQv)
      simpa [ha, hb] using hab.symm
    have hPnondeg : ((quadOdd 3 K).restrict P).Nondegenerate := by
      exact (QuadraticMap.nondegenerate_polar_iff).mp
        (nondegenerate_polarBilin_restrict hPpolar)
    have hPcompl : IsCompl P (LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P) :=
      hPnondeg.isCompl_orthogonal
    have hQnondeg : (quadOdd 3 K).Nondegenerate :=
      (QuadraticMap.nondegenerate_polar_iff).mp
        (nondegenerate_polarBilin_quadOdd (K := K) (n := 3) h2)
    have hPorthNondeg : ((quadOdd 3 K).restrict
        (LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P)).Nondegenerate :=
      hQnondeg.nondegenerate_restrict_orthogonal hPnondeg
    have hvgv : v ≠ g v := by
      intro h
      have hp : polar (quadOdd 3 K) v (g v) = 2 * quadOdd 3 K v := by
        rw [← h, polar_self_eq_two_mul]
      rw [hgv_perp] at hp
      exact (mul_ne_zero h2 hQv) hp.symm
    have hPfin : Module.finrank K P ≤ 2 := by
      haveI : Fintype ({v, g v} : Set (OmegaSevenIdx → K)) :=
        (Set.toFinite _).fintype
      calc Module.finrank K P ≤ ({v, g v} : Set (OmegaSevenIdx → K)).toFinset.card :=
            finrank_span_le_card _
        _ = 2 := by
          rw [← Set.ncard_eq_toFinset_card']
          exact Set.ncard_pair hvgv
    have hPorthfin : 3 ≤ Module.finrank K
        (LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P) := by
      rw [LinearMap.BilinForm.finrank_orthogonal
        (nondegenerate_polarBilin_quadOdd (K := K) (n := 3) h2)]
      rw [omSevenGI_finrank_V K]
      dsimp only [P] at hPfin ⊢
      calc 3 ≤ 7 - 2 := by norm_num
        _ ≤ 7 - Module.finrank K ↥(Submodule.span K {v, g v}) := Nat.sub_le_sub_left hPfin 7
    obtain ⟨u, hu0, huq⟩ := omSevenGI_exists_singular hK
      ((quadOdd 3 K).restrict
        (LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P)) hPorthNondeg hPorthfin
    have hu_orth : (u : OmegaSevenIdx → K) ∈
        LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P := u.2
    have hu_v : polar (quadOdd 3 K) (u : OmegaSevenIdx → K) v = 0 := by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp u.2) v (Submodule.subset_span (by simp))
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using h
    have hu_gv : polar (quadOdd 3 K) (u : OmegaSevenIdx → K) (g v) = 0 := by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp u.2) (g v)
        (Submodule.subset_span (by simp))
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using h
    have huA : A (u : OmegaSevenIdx → K) = -ε • (u : OmegaSevenIdx → K) :=
      (hperp (u : OmegaSevenIdx → K)).mp hu_v
    have huA' : A' (u : OmegaSevenIdx → K) = -ε • (u : OmegaSevenIdx → K) :=
      hA'perp (u : OmegaSevenIdx → K) hu_gv
    have hAA'_p : ∀ p : OmegaSevenIdx → K, p ∈ P → (A * A') p = -p := by
      intro p hp
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
      simp only [LinearEquiv.mul_apply, map_add, map_smul, map_neg, hA'v, hA'gv, hAv, hAgv,
        smul_smul, hε2, hε2neg, hε2neg', hε2negneg, neg_mul, neg_mul_neg, one_mul, mul_one,
        neg_smul, one_smul, neg_add, neg_neg, mul_assoc, mul_neg, smul_neg]
    have hA'Ap : ∀ p : OmegaSevenIdx → K, p ∈ P → (A' * A) p = -p := by
      intro p hp
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
      simp only [LinearEquiv.mul_apply, map_add, map_smul, map_neg, hA'v, hA'gv, hAv, hAgv,
        smul_smul, hε2, hε2neg, hε2neg', hε2negneg, neg_mul, neg_mul_neg, one_mul, mul_one,
        neg_smul, one_smul, neg_add, neg_neg, mul_assoc, mul_neg, smul_neg]
    have hAA'_y : ∀ y : OmegaSevenIdx → K,
        y ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P → (A * A') y = y := by
      intro y hy
      have hyv : polar (quadOdd 3 K) y v = 0 := by
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) v
          (Submodule.subset_span (by simp))
        rw [polar_comm]
        simpa [polarBilin_apply_apply] using h
      have hygv : polar (quadOdd 3 K) y (g v) = 0 := by
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) (g v)
          (Submodule.subset_span (by simp))
        rw [polar_comm]
        simpa [polarBilin_apply_apply] using h
      have hyA : A y = -ε • y := (hperp y).mp hyv
      have hyA' : A' y = -ε • y := hA'perp y hygv
      rw [LinearEquiv.mul_apply, hyA', map_smul, hyA]
      simp only [smul_smul, hε2negneg, one_smul]
    have hA'Ay : ∀ y : OmegaSevenIdx → K,
        y ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P → (A' * A) y = y := by
      intro y hy
      have hyv : polar (quadOdd 3 K) y v = 0 := by
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) v
          (Submodule.subset_span (by simp))
        rw [polar_comm]
        simpa [polarBilin_apply_apply] using h
      have hygv : polar (quadOdd 3 K) y (g v) = 0 := by
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) (g v)
          (Submodule.subset_span (by simp))
        rw [polar_comm]
        simpa [polarBilin_apply_apply] using h
      have hyA : A y = -ε • y := (hperp y).mp hyv
      have hyA' : A' y = -ε • y := hA'perp y hygv
      rw [LinearEquiv.mul_apply, hyA, map_smul, hyA']
      simp only [smul_smul, hε2negneg, one_smul]
    have hcomm : A * A' = A' * A := by
      refine LinearEquiv.ext fun z => ?_
      have hz : z ∈ P ⊔ LinearMap.BilinForm.orthogonal (polarBilin (quadOdd 3 K)) P := by
        rw [codisjoint_iff.mp hPcompl.2]
        exact Submodule.mem_top
      obtain ⟨p, hp, y, hy, hsum⟩ := Submodule.mem_sup.mp hz
      rw [← hsum, map_add, map_add, hAA'_p p hp, hA'Ap p hp, hAA'_y y hy, hA'Ay y hy]
    have hAA'_u : (A * A') (u : OmegaSevenIdx → K) = (u : OmegaSevenIdx → K) :=
      hAA'_y _ hu_orth
    have hQw : quadOdd 3 K (v + g v) = 1 := by
      rw [QuadraticMap.map_add (quadOdd 3 K), hQgv, hgv_perp, hqneg]
      norm_num
      linear_combination -h3
    have hAA'_w : (A * A') (v + g v) = -(v + g v) := by
      simp only [LinearEquiv.mul_apply, map_add, map_smul, map_neg, hA'v, hA'gv, hAv, hAgv,
        smul_smul, hε2, hε2neg, hε2neg', hε2negneg, neg_mul, neg_mul_neg, one_mul, mul_one,
        neg_smul, one_smul, neg_add, neg_neg, mul_assoc, mul_neg, smul_neg]
    have huw : polar (quadOdd 3 K) (u : OmegaSevenIdx → K) (v + g v) = 0 := by
      rw [polar_add_right, hu_v, hu_gv, add_zero]
    have hA'u_eq : A' (u : OmegaSevenIdx → K) = A (u : OmegaSevenIdx → K) := by
      rw [huA', huA]
    have hA'v_eq : A' v = -(A v) := by
      rw [hA'v, hAv, neg_smul]
    refine Or.inr ⟨g, hgmem, ?_, ?_, ?_⟩
    · simpa only [A'] using hcomm
    · refine ⟨(u : OmegaSevenIdx → K), v + g v, ⟨huq, ?_, huw, hQw⟩, Or.inl ⟨hAA'_u, hAA'_w⟩⟩
      intro h0
      exact hu0 (Subtype.ext h0)
    · refine ⟨(u : OmegaSevenIdx → K), v, ⟨huq, ?_, hu_v, ?_, ?_, hA'u_eq, hA'v_eq⟩⟩
      · intro h0
        exact hu0 (Subtype.ext h0)
      · rw [hqneg]; norm_num
      · rcases hε with rfl | rfl
        · left
          exact ⟨by simpa using huA, by simpa using hAv⟩
        · right
          exact ⟨by simpa using huA, by simpa using hAv⟩


private theorem omSevenGI_perp_of_span_plus {K : Type} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) {v : OmegaSevenIdx → K} (hv : v ∈ omSevenGI_plus A)
    (hQv : quadOdd 3 K v ≠ 0) (hspan : omSevenGI_plus A = K ∙ v) :
    ∀ x : OmegaSevenIdx → K, polar (quadOdd 3 K) x v = 0 ↔ A x = -(1 : K) • x := by
  intro x
  constructor
  · intro hx
    have hxmem : x ∈ omSevenGI_minus A := by
      have hz : x ∈ omSevenGI_plus A ⊔ omSevenGI_minus A := by
        rw [omSevenGI_sup_plus_minus A hA2 h2]
        exact Submodule.mem_top
      obtain ⟨p, hp, y, hy, hsum⟩ := Submodule.mem_sup.mp hz
      have hpv : polar (quadOdd 3 K) p v = 0 := by
        have hthis : polar (quadOdd 3 K) x v =
            polar (quadOdd 3 K) p v + polar (quadOdd 3 K) y v := by
          rw [← hsum, polar_add_left]
        rw [hx, polar_comm (quadOdd 3 K) y v,
          omSevenGI_polar_plus_minus A hA hA2 h2 hv hy, add_zero] at hthis
        exact hthis.symm
      have hpk : p ∈ K ∙ v := by rwa [← hspan]
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hpk
      have hcv : c * (2 * quadOdd 3 K v) = 0 := by
        rw [polar_smul_left, polar_self_eq_two_mul] at hpv
        simpa [mul_assoc] using hpv
      have hc : c = 0 := (mul_eq_zero.mp hcv).resolve_right (mul_ne_zero h2 hQv)
      rw [hc, zero_smul, zero_add] at hsum
      rwa [← hsum]
    simpa using (omSevenGI_mem_minus A x).mp hxmem
  · intro hx
    have hxmem : x ∈ omSevenGI_minus A :=
      (omSevenGI_mem_minus A x).mpr (by simpa using hx)
    rw [polar_comm]
    exact omSevenGI_polar_plus_minus A hA hA2 h2 hv hxmem

private theorem omSevenGI_perp_of_span_minus {K : Type} [Field K]
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (h2 : (2 : K) ≠ 0) {v : OmegaSevenIdx → K} (hv : v ∈ omSevenGI_minus A)
    (hQv : quadOdd 3 K v ≠ 0) (hspan : omSevenGI_minus A = K ∙ v) :
    ∀ x : OmegaSevenIdx → K, polar (quadOdd 3 K) x v = 0 ↔ A x = -(-(1 : K)) • x := by
  intro x
  constructor
  · intro hx
    have hxmem : x ∈ omSevenGI_plus A := by
      have hz : x ∈ omSevenGI_plus A ⊔ omSevenGI_minus A := by
        rw [omSevenGI_sup_plus_minus A hA2 h2]
        exact Submodule.mem_top
      obtain ⟨p, hp, y, hy, hsum⟩ := Submodule.mem_sup.mp hz
      have hyv : polar (quadOdd 3 K) y v = 0 := by
        have hthis : polar (quadOdd 3 K) x v =
            polar (quadOdd 3 K) p v + polar (quadOdd 3 K) y v := by
          rw [← hsum, polar_add_left]
        rw [hx, omSevenGI_polar_plus_minus A hA hA2 h2 hp hv, zero_add] at hthis
        exact hthis.symm
      have hyk : y ∈ K ∙ v := by rwa [← hspan]
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyk
      have hcv : c * (2 * quadOdd 3 K v) = 0 := by
        rw [polar_smul_left, polar_self_eq_two_mul] at hyv
        simpa [mul_assoc] using hyv
      have hc : c = 0 := (mul_eq_zero.mp hcv).resolve_right (mul_ne_zero h2 hQv)
      rw [hc, zero_smul, add_zero] at hsum
      rwa [← hsum]
    simpa using (omSevenGI_mem_plus A x).mp hxmem
  · intro hx
    have hxmem : x ∈ omSevenGI_plus A :=
      (omSevenGI_mem_plus A x).mpr (by simpa using hx)
    exact omSevenGI_polar_plus_minus A hA hA2 h2 hxmem hv

theorem involution_geometry {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (A : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K))
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (hA2 : A * A = 1)
    (hA1 : A ≠ 1) (hA1' : A ≠ LinearEquiv.neg K) :
    (∃ u w : OmegaSevenIdx → K, OmegaSevenShortPair u w ∧
        ((A u = u ∧ A w = -w) ∨ (A u = -u ∧ A w = w))) ∨
    (∃ g ∈ elementaryGroup (quadOdd 3 K),
      A * (g * A * g⁻¹) = (g * A * g⁻¹) * A ∧
      (∃ u w : OmegaSevenIdx → K, OmegaSevenShortPair u w ∧
        (((A * (g * A * g⁻¹)) u = u ∧ (A * (g * A * g⁻¹)) w = -w) ∨
          ((A * (g * A * g⁻¹)) u = -u ∧ (A * (g * A * g⁻¹)) w = w))) ∧
      ∃ u w : OmegaSevenIdx → K, quadOdd 3 K u = 0 ∧ u ≠ 0 ∧ polar (quadOdd 3 K) u w = 0 ∧
        quadOdd 3 K w ≠ 0 ∧ ((A u = -u ∧ A w = w) ∨ (A u = u ∧ A w = -w)) ∧
        (g * A * g⁻¹) u = A u ∧ (g * A * g⁻¹) w = -(A w)) := by
  have h2 : (2 : K) ≠ 0 := omSevenGI_two_ne_zero hK
  by_cases hp1 : Module.finrank K (omSevenGI_plus A) = 1
  ·
    obtain ⟨v, hv, hv0⟩ :=
      (Submodule.ne_bot_iff (omSevenGI_plus A)).mp (omSevenGI_plus_ne_bot A hA2 h2 hA1')
    have hspan : omSevenGI_plus A = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hp1 hv hv0
    have hQv : quadOdd 3 K v ≠ 0 := by
      by_contra h0
      have hperp : PolarNondegOn (quadOdd 3 K) (omSevenGI_plus A) :=
        omSevenGI_polarNondegOn_plus A hA hA2 h2
      have hvorth : ∀ y ∈ omSevenGI_plus A, polar (quadOdd 3 K) v y = 0 := by
        intro y hy
        have hyk : y ∈ K ∙ v := by rwa [← hspan]
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyk
        simp [polar_smul_right, polar_self_eq_two_mul, h0]
      exact hv0 (hperp v hv hvorth)
    have hAv : A v = (1 : K) • v := by
      rw [one_smul]
      exact (omSevenGI_mem_plus A v).mp hv
    have hperp := omSevenGI_perp_of_span_plus A hA hA2 h2 hv hQv hspan
    exact omSevenGI_line_case hK A hA hA2 (Or.inl rfl) hv0 hAv hperp hQv
  by_cases hm1 : Module.finrank K (omSevenGI_minus A) = 1
  ·
    obtain ⟨v, hv, hv0⟩ :=
      (Submodule.ne_bot_iff (omSevenGI_minus A)).mp (omSevenGI_minus_ne_bot A hA2 h2 hA1)
    have hspan : omSevenGI_minus A = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hm1 hv hv0
    have hQv : quadOdd 3 K v ≠ 0 := by
      by_contra h0
      have hperp : PolarNondegOn (quadOdd 3 K) (omSevenGI_minus A) :=
        omSevenGI_polarNondegOn_minus A hA hA2 h2
      have hvorth : ∀ y ∈ omSevenGI_minus A, polar (quadOdd 3 K) v y = 0 := by
        intro y hy
        have hyk : y ∈ K ∙ v := by rwa [← hspan]
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyk
        simp [polar_smul_right, polar_self_eq_two_mul, h0]
      exact hv0 (hperp v hv hvorth)
    have hAv : A v = (-1 : K) • v := by
      simpa using (omSevenGI_mem_minus A v).mp hv
    have hperp := omSevenGI_perp_of_span_minus A hA hA2 h2 hv hQv hspan
    exact omSevenGI_line_case hK A hA hA2 (Or.inr rfl) hv0 hAv hperp hQv
  ·
    have hp2 : 2 ≤ Module.finrank K (omSevenGI_plus A) := by
      have hpos := omSevenGI_finrank_plus_pos A hA2 h2 hA1'
      omega
    have hm2 : 2 ≤ Module.finrank K (omSevenGI_minus A) := by
      have hpos := omSevenGI_finrank_minus_pos A hA2 h2 hA1
      omega
    by_cases hp3 : 3 ≤ Module.finrank K (omSevenGI_plus A)
    · exact Or.inl (omSevenGI_first_disjunct_of_ranks hK A hA hA2 h2
        (Or.inl ⟨hp3, hm2⟩))
    · have hm3 : 3 ≤ Module.finrank K (omSevenGI_minus A) := by
        have hsum := omSevenGI_finrank_sum A hA2 h2
        have hV := omSevenGI_finrank_V K
        omega
      exact Or.inl (omSevenGI_first_disjunct_of_ranks hK A hA hA2 h2
        (Or.inr ⟨hp2, hm3⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
