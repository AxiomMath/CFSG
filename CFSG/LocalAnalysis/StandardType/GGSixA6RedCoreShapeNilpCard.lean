module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresComm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresProd
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Basis

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores

open scoped commutatorElement

private def ggA6cs_matE {r : ℕ} (D : Fin r → Type) (d : Fin r → ℕ) [∀ i, Field (D i)]
    [∀ i, NeZero (d i)] (b : Fin r) : PiMat D d :=
  Pi.single b (Matrix.single (0 : Fin (d b)) 0 (1 : D b))

private theorem matE_mul_self {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] (b : Fin r) :
    ggA6cs_matE D d b * ggA6cs_matE D d b = ggA6cs_matE D d b := by
  rw [ggA6cs_matE, single_mul_eq, Pi.single_eq_same, Matrix.single_mul_single_same, mul_one]

private theorem matE_ne_zero {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] (b : Fin r) :
    ggA6cs_matE D d b ≠ 0 := by
  intro h
  have h1 : (Matrix.single (0 : Fin (d b)) (0 : Fin (d b)) (1 : D b) :
      Matrix (Fin (d b)) (Fin (d b)) (D b)) = 0 := by
    simpa [ggA6cs_matE] using congrFun h b
  have h2 : (1 : D b) = 0 := by
    simpa using congrFun (congrFun h1 (0 : Fin (d b))) (0 : Fin (d b))
  exact one_ne_zero h2

private theorem eq_smul_matE_of_corner {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] (b : Fin r) {y : PiMat D d}
    (hy : ggA6cs_matE D d b * y * ggA6cs_matE D d b = y) :
    y = (Pi.single b (Matrix.single (0 : Fin (d b)) 0 (y b 0 0)) : PiMat D d) := by
  have hmain : ggA6cs_matE D d b * y * ggA6cs_matE D d b =
      (Pi.single b (Matrix.single (0 : Fin (d b)) 0 (y b 0 0)) : PiMat D d) := by
    rw [ggA6cs_matE, single_mul_eq, mul_single_eq, Pi.single_eq_same]
    simp only [Pi.single_eq_same, Matrix.single_mul_mul_single, one_mul, mul_one]
  conv_lhs => rw [← hy]
  exact hmain

private theorem eq_zero_or_one_of_nat_card_eq_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  classical
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have h := (Nat.card_eq_two_iff' (0 : F)).mp hF
    obtain ⟨d, hd, huniq⟩ := h
    exact (huniq c hc).trans (huniq 1 one_ne_zero).symm


private theorem nat_card_field_eq_two_of_char_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F < 4) : Nat.card F = 2 := by
  classical
  letI := Fintype.ofFinite F
  obtain ⟨n, _hnprime, hncard⟩ := FiniteField.card F 2
  have hcard : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hnle : (n : ℕ) ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ (n : ℕ) := by omega
    have h4 : 4 ≤ 2 ^ (n : ℕ) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hn1 : (n : ℕ) = 1 := by
    have := n.pos
    omega
  rw [hcard, hncard, hn1]
  norm_num

private theorem nat_card_le_of_algebraMap_injective {K F : Type} [Field K] [Field F]
    [Finite F] [Algebra K F] : Nat.card K ≤ Nat.card F :=
  Nat.card_le_card_of_injective (algebraMap K F) (RingHom.injective _)


private theorem ggA6cs_endomorphism_scalar
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Subgroup (GL ι K)}
    {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Finite (D i)] [∀ i, Algebra K (D i)]
    {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    (Φ : PiMat D d →ₐ[K] Matrix ι ι K)
    (hΦ : Function.Injective Φ)
    (hR : ∀ X : Matrix ι ι K, X ∈ Set.range Φ ↔
      ∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X)
    (b : Fin r) (hD2 : Nat.card (D b) = 2) (z : ↥A)
    (hcomm : ∀ g ∈ A, ∀ s : ι → K,
      (∃ v : ι → K, Φ (ggA6cs_matE D d b) *ᵥ v = s) →
      ((z : GL ι K) : Matrix ι ι K) *ᵥ (((g : GL ι K) : Matrix ι ι K) *ᵥ s) =
      (((g : GL ι K) : Matrix ι ι K) *ᵥ (((z : GL ι K) : Matrix ι ι K) *ᵥ s))) :
    ∀ s : ι → K, (∃ v : ι → K, Φ (ggA6cs_matE D d b) *ᵥ v = s) →
      ((z : GL ι K) : Matrix ι ι K) *ᵥ s = 0 ∨
      ((z : GL ι K) : Matrix ι ι K) *ᵥ s = s := by
  classical
  let e : PiMat D d := ggA6cs_matE D d b
  let f : Matrix ι ι K := Φ e
  let Z : Matrix ι ι K := (z : GL ι K)
  have hf_mem : f ∈ Set.range Φ := ⟨e, rfl⟩
  have hf_comm : ∀ g ∈ A, f * (g : Matrix ι ι K) = (g : Matrix ι ι K) * f :=
    (hR f).mp hf_mem
  have hfid : f * f = f := by
    have : Φ (e * e) = Φ e := by rw [matE_mul_self]
    simpa [f] using this
  have hZf : Z * f = f * Z := by
    have h := hf_comm z z.2
    simpa [Z] using h.symm
  let X : Matrix ι ι K := Z * f
  have hX_comm : ∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X := by
    intro g hg
    have hfg : f * (g : Matrix ι ι K) = (g : Matrix ι ι K) * f := hf_comm g hg
    have hlin : Matrix.toLin' (X * (g : Matrix ι ι K)) =
        Matrix.toLin' ((g : Matrix ι ι K) * X) := by
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply]
      simp only [X, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      rw [hfg]
      have hc := hcomm g hg (f *ᵥ v) ⟨v, rfl⟩
      simpa [Z, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hc
    have hinj : Function.Injective (Matrix.toLin' (R := K) (m := ι) (n := ι)) := by
      intro M N h
      calc M = LinearMap.toMatrix' (Matrix.toLin' M) := (LinearMap.toMatrix'_toLin' M).symm
        _ = LinearMap.toMatrix' (Matrix.toLin' N) := by rw [h]
        _ = N := LinearMap.toMatrix'_toLin' N
    exact hinj hlin
  obtain ⟨y, hyX⟩ := (hR X).mpr hX_comm
  have hfy : f * X * f = X := by
    have hXeq : X = Z * f := rfl
    rw [hXeq]
    calc f * (Z * f) * f = (f * Z) * (f * f) := by noncomm_ring
      _ = (f * Z) * f := by rw [hfid]
      _ = (Z * f) * f := by rw [← hZf]
      _ = Z * (f * f) := by noncomm_ring
      _ = Z * f := by rw [hfid]
  have hmap : Φ (e * y * e) = f * X * f := by
    rw [map_mul, map_mul, hyX]
  have hye : e * y * e = y := by
    apply hΦ
    rw [hmap, hfy]
    exact hyX.symm
  let c : D b := y b 0 0
  have hc : y = Pi.single b (Matrix.single (0 : Fin (d b)) 0 c) :=
    eq_smul_matE_of_corner b hye
  rcases eq_zero_or_one_of_nat_card_eq_two hD2 c with hc0 | hc1
  · intro s hs
    left
    have hy0 : y = 0 := by
      rw [hc, hc0]
      simp
    have hX0 : X = 0 := by
      rw [← hyX, hy0, map_zero]
    have hfs : f *ᵥ s = s := by
      obtain ⟨v, rfl⟩ := hs
      change f *ᵥ (f *ᵥ v) = f *ᵥ v
      simp only [Matrix.mulVec_mulVec, hfid]
    have hXs : X *ᵥ s = Z *ᵥ s := by
      change (Z * f) *ᵥ s = Z *ᵥ s
      rw [← Matrix.mulVec_mulVec]
      rw [hfs]
    rw [← hXs, hX0, Matrix.zero_mulVec]
  · intro s hs
    right
    have hye' : y = e := by
      rw [hc, hc1]
      rfl
    have hXf : X = f := by
      rw [← hyX, hye']
    have hfs : f *ᵥ s = s := by
      obtain ⟨v, rfl⟩ := hs
      change f *ᵥ (f *ᵥ v) = f *ᵥ v
      simp only [Matrix.mulVec_mulVec, hfid]
    have hXs : X *ᵥ s = Z *ᵥ s := by
      change (Z * f) *ᵥ s = Z *ᵥ s
      rw [← Matrix.mulVec_mulVec]
      rw [hfs]
    rw [← hXs, hXf, hfs]


private theorem mulVec_mulVec_of_comm {K : Type} [Field K] {ι : Type} [Fintype ι]
    {f G : Matrix ι ι K} (h : G * f = f * G) (v : ι → K) :
    G *ᵥ (f *ᵥ v) = f *ᵥ (G *ᵥ v) := by
  simpa only [Matrix.mulVec_mulVec] using congrArg (fun M : Matrix ι ι K => M *ᵥ v) h

private theorem ggA6cs_coe_inv_mul_self {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : GL ι K) : (((u⁻¹ : GL ι K) : Matrix ι ι K)) * (u : Matrix ι ι K) = 1 := by
  simpa [Matrix.GeneralLinearGroup.coe_inv] using congrArg Units.val (inv_mul_cancel u)


private theorem ggA6cs_exists_mulVec_ne_zero {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι K} (hM : M ≠ 0) :
    ∃ v : ι → K, M *ᵥ v ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hM
  ext i j
  have h0 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h0

theorem card_ge_four_of_nilpotent_free {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : Subgroup (GL ι K)) (hnil : Group.IsNilpotent ↥A)
    (hfree : ∀ v : ι → K, (∀ g ∈ A, (g : Matrix ι ι K).mulVec v = v) → v = 0)
    {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Finite (D i)] [∀ i, Algebra K (D i)]
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] (Φ : PiMat D d →ₐ[K] Matrix ι ι K)
    (hΦ : Function.Injective Φ)
    (hR : ∀ X : Matrix ι ι K, X ∈ Set.range Φ ↔
      ∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) (b : Fin r) :
    4 ≤ Nat.card (D b) := by
  classical
  by_contra hnot
  have hDlt : Nat.card (D b) < 4 := by omega
  by_cases hKbig : 4 ≤ Nat.card K
  · have hle : Nat.card K ≤ Nat.card (D b) := nat_card_le_of_algebraMap_injective
    omega
  · have hKlt : Nat.card K < 4 := by omega
    haveI : CharP (D b) 2 :=
      charP_of_injective_algebraMap (RingHom.injective (algebraMap K (D b))) 2
    have hD2 : Nat.card (D b) = 2 := nat_card_field_eq_two_of_char_two hDlt
    let e : PiMat D d := ggA6cs_matE D d b
    let f : Matrix ι ι K := Φ e
    let S : Set (ι → K) := Set.range (fun v => f *ᵥ v)
    have hf_ne : f ≠ 0 := by
      intro hf0
      refine matE_ne_zero (D := D) (d := d) b ?_
      apply hΦ
      change f = Φ 0
      rw [hf0, map_zero]
    have hf_mem : f ∈ Set.range Φ := ⟨e, rfl⟩
    have hf_comm : ∀ g ∈ A, f * (g : Matrix ι ι K) = (g : Matrix ι ι K) * f :=
      (hR f).mp hf_mem
    have hfid : f * f = f := by
      have : Φ (e * e) = Φ e := by rw [matE_mul_self]
      simpa [f] using this
    have hS_smul : ∀ g ∈ A, ∀ t : ι → K, t ∈ S →
        (g : Matrix ι ι K) *ᵥ t ∈ S := by
      intro g hg t ht
      obtain ⟨v, rfl⟩ := ht
      refine ⟨(g : Matrix ι ι K) *ᵥ v, ?_⟩
      change f *ᵥ ((g : Matrix ι ι K) *ᵥ v) = (g : Matrix ι ι K) *ᵥ (f *ᵥ v)
      exact mulVec_mulVec_of_comm (hf_comm g hg) v
    obtain ⟨n, hn⟩ := hnil.nilpotent'
    have hP : ∀ k : ℕ, ∀ z ∈ Subgroup.upperCentralSeries ↥A k, ∀ s : ι → K, s ∈ S →
        ((z : GL ι K) : Matrix ι ι K) *ᵥ s = s := by
      intro k
      induction k with
      | zero =>
        intro z hz s hs
        have hz1 : z = 1 := by
          rw [Subgroup.upperCentralSeries_zero] at hz
          exact Subgroup.mem_bot.mp hz
        subst z
        simp
      | succ k ih =>
        intro z hz s hs
        have hcomm : ∀ g ∈ A, ∀ t : ι → K, t ∈ S →
            ((z : GL ι K) : Matrix ι ι K) *ᵥ (((g : GL ι K) : Matrix ι ι K) *ᵥ t) =
            (((g : GL ι K) : Matrix ι ι K) *ᵥ (((z : GL ι K) : Matrix ι ι K) *ᵥ t)) := by
          intro g hg t ht
          let gA : ↥A := ⟨g, hg⟩
          let G : Matrix ι ι K := (g : GL ι K)
          let Z : Matrix ι ι K := (z : GL ι K)
          let Zinv : Matrix ι ι K := ((z : GL ι K)⁻¹ : GL ι K)
          let Ginv : Matrix ι ι K := ((g : GL ι K)⁻¹ : GL ι K)
          change Z *ᵥ (G *ᵥ t) = G *ᵥ (Z *ᵥ t)
          have hCm : (⁅z, gA⁆ : ↥A) ∈ Subgroup.upperCentralSeries ↥A k :=
            (Subgroup.mem_upperCentralSeries_succ_iff).mp hz gA
          have htZ : Z *ᵥ t ∈ S := hS_smul z z.2 t ht
          have htGZ : G *ᵥ (Z *ᵥ t) ∈ S := hS_smul g hg _ htZ
          have hC := ih (⁅z, gA⁆) hCm _ htGZ
          have hcommMat : (((⁅z, gA⁆ : ↥A) : GL ι K) : Matrix ι ι K) =
              Z * G * Zinv * Ginv := by
            change (((⁅z, gA⁆ : ↥A) : GL ι K) : Matrix ι ι K) =
              ((z : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K) *
                (((z : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K) *
                (((g : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K)
            rw [commutatorElement_def]
            rfl
          have hzi : Zinv * Z = 1 := ggA6cs_coe_inv_mul_self (z : GL ι K)
          have hgi : Ginv * G = 1 := ggA6cs_coe_inv_mul_self (g : GL ι K)
          rw [hcommMat] at hC
          simp only [Matrix.mulVec_mulVec] at hC
          simp only [← Matrix.mul_assoc] at hC
          change (Z * G * Zinv * Ginv * G * Z) *ᵥ t = (G * Z) *ᵥ t at hC
          have hmat : Z * G * Zinv * Ginv * G * Z = Z * G := by
            calc
              Z * G * Zinv * Ginv * G * Z
                  = Z * G * Zinv * (Ginv * G) * Z := by
                    rw [mul_assoc (Z * G * Zinv) Ginv G]
              _ = Z * G * Zinv * 1 * Z := by rw [hgi]
              _ = Z * G * Zinv * Z := by rw [mul_one]
              _ = Z * G * (Zinv * Z) := by
                    rw [mul_assoc (Z * G) Zinv Z]
              _ = Z * G * 1 := by rw [hzi]
              _ = Z * G := by rw [mul_one]
          rw [hmat] at hC
          simpa only [Matrix.mulVec_mulVec] using hC
        rcases ggA6cs_endomorphism_scalar Φ hΦ hR b hD2 z hcomm s hs with h0 | hid
        · have hs0 : s = 0 := by
            have hzi : (((z : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K) *
                ((z : GL ι K) : Matrix ι ι K) = 1 := ggA6cs_coe_inv_mul_self (z : GL ι K)
            have h := congrArg (fun w : ι → K =>
              (((z : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) h0
            rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, hzi, Matrix.one_mulVec] at h
            exact h
          rw [h0, hs0]
        · exact hid
    have htriv : ∀ g ∈ A, ∀ s : ι → K, s ∈ S → (g : Matrix ι ι K) *ᵥ s = s := by
      intro g hg s hs
      have htop : (⟨g, hg⟩ : ↥A) ∈ Subgroup.upperCentralSeries ↥A n := by
        rw [hn]
        exact Subgroup.mem_top _
      exact hP n ⟨g, hg⟩ htop s hs
    obtain ⟨v, hv⟩ := ggA6cs_exists_mulVec_ne_zero hf_ne
    have hvS : f *ᵥ v ∈ S := ⟨v, rfl⟩
    have hzero : f *ᵥ v = 0 :=
      hfree (f *ᵥ v) (fun g hg => htriv g hg (f *ᵥ v) hvS)
    exact hv hzero

end CFSG.StandardType.A6Red.CoreShape
