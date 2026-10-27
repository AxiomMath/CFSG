module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtEta
public import TauCeti.LinearAlgebra.Matrix.BlockSucc
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K] {n : ℕ}

theorem diagSignMat_eq_one_sub_vecMulVec (i : Fin n) :
    (diagSignMat i : Matrix (Fin n) (Fin n) K) =
      1 - Matrix.vecMulVec (Pi.single i 1) (Pi.single i 2) := by
  ext r c
  simp only [diagSignMat, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Matrix.diagonal_apply, Pi.single_apply]
  split_ifs <;> (simp_all; try ring)

theorem pijMat_eq_one_sub_vecMulVec {i j : Fin n} (hij : i ≠ j) {s : K} (hs : s ≠ 0) :
    pijMat i j s = 1 - Matrix.vecMulVec (Pi.single i 1 - s⁻¹ • Pi.single j 1)
      (Pi.single i 1 - s • Pi.single j 1) := by
  ext r c
  simp only [pijMat, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Pi.single_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> (simp_all; try ring)

theorem blockSucc_diagSignMat (i : Fin n) :
    Matrix.blockSucc (diagSignMat i : Matrix (Fin n) (Fin n) K) = diagSignMat i.castSucc := by
  ext r c
  induction r using Fin.lastCases with
  | last =>
      induction c using Fin.lastCases with
      | last => simp [eq_comm, Fin.castSucc_ne_last, diagSignMat]
      | cast c => simp [eq_comm, Fin.castSucc_ne_last, diagSignMat]
  | cast r =>
      induction c using Fin.lastCases with
      | last => simp [eq_comm, Fin.castSucc_ne_last, diagSignMat]
      | cast c => simp [eq_comm, diagSignMat, Matrix.diagonal_apply,
        Fin.castSucc_inj]

theorem blockSucc_pijMat (i j : Fin n) (s : K) :
    Matrix.blockSucc (pijMat i j s) = pijMat i.castSucc j.castSucc s := by
  ext r c
  induction r using Fin.lastCases with
  | last =>
      induction c using Fin.lastCases with
      | last => simp [eq_comm, Fin.castSucc_ne_last, pijMat]
      | cast c => simp [eq_comm, Fin.castSucc_ne_last, pijMat]
  | cast r =>
      induction c using Fin.lastCases with
      | last => simp [eq_comm, Fin.castSucc_ne_last, pijMat]
      | cast c => simp [eq_comm, pijMat, Fin.castSucc_inj]

end Matrices

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

section Sums

private lemma sum_psi_single {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (ψ : Module.Dual (ZMod p) U) (i : Fin m) :
    (∑ k, ψ (f k) * (Pi.single i 1 : Fin m → ZMod p) k) = ψ (f i) := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki; simp [hki]
  · intro hi; simp at hi

private lemma sum_single_repr {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U) (w : U)
    (i : Fin m) :
    (∑ k, (Pi.single i 1 : Fin m → ZMod p) k * f.repr w k) = f.repr w i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki; simp [hki]
  · intro hi; simp at hi

private lemma sum_single_mul_repr {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U) (w : U)
    (i : Fin m) (c : ZMod p) :
    (∑ k, (Pi.single i c : Fin m → ZMod p) k * f.repr w k) = c * f.repr w i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki; simp [hki]
  · intro hi; simp at hi

private def rhoVec {m : ℕ} (i j : Fin m) (s : ZMod p) : Fin m → ZMod p :=
  Pi.single i 1 - s⁻¹ • Pi.single j 1

private def kappaVec {m : ℕ} (i j : Fin m) (s : ZMod p) : Fin m → ZMod p :=
  Pi.single i 1 - s • Pi.single j 1

private lemma sum_kappa_rho {m : ℕ} {i j : Fin m} (hij : i ≠ j) {s : ZMod p} (hs : s ≠ 0) :
    (∑ k, kappaVec i j s k * rhoVec i j s k) = 2 := by
  have h1 : ∀ k, kappaVec i j s k * rhoVec i j s k
      = (if k = i then 1 else 0) + (if k = j then s * s⁻¹ else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [kappaVec, rhoVec, Pi.sub_apply, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [kappaVec, rhoVec, Pi.sub_apply, hki, mul_inv_cancel₀ hs]
      · simp [kappaVec, rhoVec, Pi.sub_apply, hki, hkj]
  simp_rw [h1]
  rw [Finset.sum_add_distrib]
  simp
  rw [mul_inv_cancel₀ hs]
  norm_num

private lemma sum_psi_rho {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (ψ : Module.Dual (ZMod p) U) {i j : Fin m} {s : ZMod p} :
    (∑ k, ψ (f k) * rhoVec i j s k) = ψ (f i) - s⁻¹ * ψ (f j) := by
  have hsub : (∑ k, ψ (f k) * rhoVec i j s k)
      = (∑ k, ψ (f k) * (Pi.single i 1 : Fin m → ZMod p) k)
        - s⁻¹ * (∑ k, ψ (f k) * (Pi.single j 1 : Fin m → ZMod p) k) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [rhoVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub, sum_psi_single f ψ i, sum_psi_single f ψ j]

private lemma sum_kappa_repr {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U) (w : U)
    {i j : Fin m} {s : ZMod p} :
    (∑ k, kappaVec i j s k * f.repr w k) = f.repr w i - s * f.repr w j := by
  have hsub : (∑ k, kappaVec i j s k * f.repr w k)
      = (∑ k, (Pi.single i 1 : Fin m → ZMod p) k * f.repr w k)
        - s * (∑ k, (Pi.single j 1 : Fin m → ZMod p) k * f.repr w k) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [kappaVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub, sum_single_repr f w i, sum_single_repr f w j]

private lemma etaOK_four_pij (hp4 : 4 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hc : Module.reflection hψ ∈ G) {i j : Fin m} (hij : i ≠ j) {s : ZMod p}
    (hs : s = 1 ∨ s = -1)
    (hπ : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat i j s) :
    EtaOK 4 (ψ (f i) - s⁻¹ * ψ (f j)) (f.repr w i - s * f.repr w j) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g, hgG, hgne, hgmat⟩ := hπ
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have h := etaOK_of_toMatrix (G := G) (d := 4) hG (by norm_num) hp4 hp2
    (f := f) (c := Module.reflection hψ) (r := g) hc hgG
    (fun h => hgne h.symm) hψ rfl (ρ := rhoVec i j s) (κ := kappaVec i j s)
    (by rw [hgmat, pijMat_eq_one_sub_vecMulVec hij hs0]; rfl) (sum_kappa_rho hij hs0)
  rwa [sum_psi_rho f ψ, sum_kappa_repr f w] at h

private lemma bond_diag_of_dMax_four (hp4 : 4 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hc : Module.reflection hψ ∈ G) {j : Fin m}
    (hd : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat j) :
    EtaOK 4 (ψ (f j)) (2 * f.repr w j) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g, hgG, hgne, hgmat⟩ := hd
  have hκρ : ∑ k, (Pi.single j 2 : Fin m → ZMod p) k *
      (Pi.single j 1 : Fin m → ZMod p) k = 2 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [hbj]
    · intro hj; simp at hj
  have h := etaOK_of_toMatrix (G := G) (d := 4) hG (by norm_num) hp4 hp2
    (f := f) (c := Module.reflection hψ) (r := g) hc hgG
    (fun h => hgne h.symm) hψ rfl (ρ := Pi.single j 1) (κ := Pi.single j 2)
    (by rw [hgmat, diagSignMat_eq_one_sub_vecMulVec]) hκρ
  rwa [sum_psi_single f ψ j, sum_single_mul_repr f w j 2] at h

private lemma bond_pi_of_dMax_four (hp4 : 4 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hc : Module.reflection hψ ∈ G) {i j : Fin m} (hij : i ≠ j) (hwi : f.repr w i = 0)
    (hψi : ψ (f i) = 0)
    (hπ : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat i j 1) :
    EtaOK 4 (-(ψ (f j))) (-(f.repr w j)) := by
  have h := etaOK_four_pij hp4 hG f hψ hc hij (Or.inl rfl) hπ
  simpa [hψi, hwi] using h

private lemma factor_of_etaOK_four (hp4 : 4 < p) {s t : ZMod p}
    (hJ : EtaOK 4 s (2 * t)) (ht : s * t = 0 ∨ s * t = 1 ∨ s * t = 2) :
    (s = 0 ∧ t = 0) ∨ s * t = 1 := by
  have hp2 : p ≠ 2 := by omega
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rcases ht with h0 | h1 | h2
  · rcases hJ with ⟨hs, h2w⟩ | ⟨-, h2t1⟩ | ⟨-, h2t2⟩ | ⟨h54, -⟩
    · left; refine ⟨hs, ?_⟩
      exact (mul_eq_zero.mp h2w).resolve_left h2ne
    · have hc1 : (2 : ZMod p) * (s * t) = 1 := by linear_combination h2t1
      rw [h0, mul_zero] at hc1
      exfalso; exact one_ne_zero hc1.symm
    · have hc2 : (2 : ZMod p) * (s * t) = 2 := by linear_combination h2t2
      rw [h0, mul_zero] at hc2
      exfalso; exact h2ne hc2.symm
    · omega
  · right; exact h1
  · rcases hJ with ⟨-, h2w⟩ | ⟨-, h2t1⟩ | ⟨-, h2t2⟩ | ⟨h54, -⟩
    · have hwj : t = 0 := (mul_eq_zero.mp h2w).resolve_left h2ne
      rw [hwj, mul_zero] at h2
      exfalso; exact h2ne h2.symm
    · have hc1 : (2 : ZMod p) * (s * t) = 1 := by linear_combination h2t1
      rw [h2] at hc1
      have h3z : (3 : ZMod p) = 0 := by linear_combination hc1
      exfalso; exact h3ne h3z
    · have hc2 : (2 : ZMod p) * (s * t) = 2 := by linear_combination h2t2
      rw [h2] at hc2
      have h2z : (2 : ZMod p) = 0 := by linear_combination hc2
      exfalso; exact h2ne h2z
    · omega

private lemma eq_zero_or_mul_eq_one_of_etaOK_four (hp4 : 4 < p) {s t : ZMod p}
    (hJ : EtaOK 4 s (2 * t)) (hPi : EtaOK 4 (-s) (-t)) :
    (s = 0 ∧ t = 0) ∨ s * t = 1 := by
  have ht : s * t = 0 ∨ s * t = 1 ∨ s * t = 2 := by
    rcases hPi with ⟨h1, h2⟩ | ⟨-, h1⟩ | ⟨-, h2⟩ | ⟨h54, -⟩
    · left
      rw [neg_eq_zero.mp h1, neg_eq_zero.mp h2]
      exact zero_mul 0
    · right; left
      rw [← h1]
      exact (neg_mul_neg s t).symm
    · right; right
      rw [← h2]
      exact (neg_mul_neg s t).symm
    · omega
  exact factor_of_etaOK_four hp4 hJ ht

end Sums

theorem apply_eq_zero_of_commute_diagSignMat (hp : p ≠ 2) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {i : Fin m} {d : U ≃ₗ[ZMod p] U}
    (hd : LinearMap.toMatrix f f (d : U →ₗ[ZMod p] U) = diagSignMat i) {w : U}
    {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hcomm : Module.reflection hψ * d = d * Module.reflection hψ)
    (hne : Module.reflection hψ ≠ d) : ψ (f i) = 0 ∧ f.repr w i = 0 := by
  let φi : Module.Dual (ZMod p) U := (2 : ZMod p) • f.coord i
  have hφi : φi (f i) = 2 := by
    simp only [φi]
    norm_num
  have hd_eq : d = Module.reflection hφi := by
    have hlin : (d : U →ₗ[ZMod p] U) = (Module.reflection hφi : U →ₗ[ZMod p] U) := by
      apply (LinearMap.toMatrix f f).injective
      rw [hd, toMatrix_reflection f hφi, diagSignMat_eq_one_sub_vecMulVec]
      have hρ : (fun j => f.repr (f i) j) = Pi.single i 1 := by
        funext j
        have h := congrArg (fun g : Fin m →₀ ZMod p => g j) (Module.Basis.repr_self f i)
        simpa only [Finsupp.single_apply, Pi.single_apply, eq_comm] using h
      have hκ : (fun j => φi (f j)) = Pi.single i 2 := by
        funext j
        simp only [φi, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji]
      rw [hρ, hκ]
    exact LinearEquiv.ext (fun v => congrFun (congrArg (fun f : U →ₗ[ZMod p] U => (f : U → U))
      hlin) v)
  have hcomm' : Commute (Module.reflection hψ) (Module.reflection hφi) := by
    rw [← hd_eq]; exact hcomm
  have hne' : Module.reflection hψ ≠ Module.reflection hφi := by
    rw [← hd_eq]; exact hne
  have hψfi : ψ (f i) = 0 :=
    apply_eq_zero_of_commute (a := w) (b := f i) (φ := ψ) (ψ := φi) hp hψ hφi
      hcomm' hne' 
  have hφiw : φi w = 0 :=
    apply_eq_zero_of_commute (a := f i) (b := w) (φ := φi) (ψ := ψ) hp hφi hψ
      hcomm'.symm (fun h => hne' h.symm)
  have hwi : f.repr w i = 0 := by
    have h2 : (2 : ZMod p) * f.repr w i = 0 := by
      have h : φi w = 2 * f.repr w i := by
        simp only [φi, LinearMap.smul_apply, Module.Basis.coord_apply]
        exact smul_eq_mul 2 (f.repr w i)
      simpa [h] using hφiw
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  exact ⟨hψfi, hwi⟩

theorem two_mul_apply_mul_eq_one_of_diagSignMat (hp : p ≠ 2) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {i : Fin m} {d : U ≃ₗ[ZMod p] U}
    (hd : LinearMap.toMatrix f f (d : U →ₗ[ZMod p] U) = diagSignMat i) {w : U}
    {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (h : orderOf (Module.reflection hψ * d) = 3) :
    2 * (ψ (f i) * f.repr w i) = 1 := by
  let φi : Module.Dual (ZMod p) U := (2 : ZMod p) • f.coord i
  have hφi : φi (f i) = 2 := by
    simp only [φi]
    norm_num
  have hd_eq : d = Module.reflection hφi := by
    have hlin : (d : U →ₗ[ZMod p] U) = (Module.reflection hφi : U →ₗ[ZMod p] U) := by
      apply (LinearMap.toMatrix f f).injective
      rw [hd, toMatrix_reflection f hφi, diagSignMat_eq_one_sub_vecMulVec]
      have hρ : (fun j => f.repr (f i) j) = Pi.single i 1 := by
        funext j
        have h := congrArg (fun g : Fin m →₀ ZMod p => g j) (Module.Basis.repr_self f i)
        simpa only [Finsupp.single_apply, Pi.single_apply, eq_comm] using h
      have hκ : (fun j => φi (f j)) = Pi.single i 2 := by
        funext j
        simp only [φi, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji]
      rw [hρ, hκ]
    exact LinearEquiv.ext (fun v => congrFun (congrArg (fun f : U →ₗ[ZMod p] U => (f : U → U))
      hlin) v)
  have h3 : orderOf (Module.reflection hψ * Module.reflection hφi) = 3 := by
    rwa [hd_eq] at h
  have hbond : ψ (f i) * φi w = 1 :=
    apply_mul_apply_eq_one_of_orderOf_eq_three hp hψ hφi h3
  have hφiw : φi w = 2 * f.repr w i := by
    simp only [φi, LinearMap.smul_apply, Module.Basis.coord_apply]
    exact smul_eq_mul 2 (f.repr w i)
  rw [hφiw] at hbond
  linear_combination hbond

theorem repr_eq_zero_or_mul_eq_one_of_dMax_four (hp4 : 4 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hc : Module.reflection hψ ∈ G) {i j : Fin m} (hij : i ≠ j) (hwi : f.repr w i = 0)
    (hψi : ψ (f i) = 0)
    (hd : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat j)
    (hπ : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat i j 1) :
    (ψ (f j) = 0 ∧ f.repr w j = 0) ∨ ψ (f j) * f.repr w j = 1 := by
  exact eq_zero_or_mul_eq_one_of_etaOK_four hp4
    (bond_diag_of_dMax_four hp4 hG f hψ hc hd)
    (bond_pi_of_dMax_four hp4 hG f hψ hc hij hwi hψi hπ)

private lemma etaOK_four_mul {s t : ZMod p} (h : EtaOK 4 s t) :
    (s * t) * (s * t - 1) * (s * t - 2) = 0 := by
  rcases h with ⟨hs, ht⟩ | ⟨-, h1⟩ | ⟨-, h2⟩ | ⟨h54, -⟩
  · rw [hs, ht, mul_zero]; ring
  · rw [h1]; ring
  · rw [h2]; ring
  · omega

private lemma cross_eq_zero_of_etaOK_four (hp4 : 4 < p) {a b c d : ZMod p}
    (hi : a * c = 1) (hj : b * d = 1)
    (h1 : EtaOK 4 (a - 1⁻¹ * b) (c - 1 * d))
    (h2 : EtaOK 4 (a - (-1)⁻¹ * b) (c - (-1) * d)) :
    a * d + b * c = 0 := by
  have hP1 : (a - 1⁻¹ * b) * (c - 1 * d) = 2 - (a * d + b * c) := by
    rw [inv_one, one_mul]
    linear_combination hi + hj
  have hP2 : (a - (-1)⁻¹ * b) * (c - (-1) * d) = 2 + (a * d + b * c) := by
    have h1' : (-1 : ZMod p)⁻¹ = -1 := by rw [inv_neg, inv_one]
    rw [h1']
    linear_combination hi + hj
  have hA := etaOK_four_mul h1
  rw [hP1] at hA
  have hB := etaOK_four_mul h2
  rw [hP2] at hB
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp hz
    have hpprime : p.Prime := Fact.out
    have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p
    · norm_num at hdvd
    · norm_num at hpprime
  have hsum : (6 : ZMod p) * (a * d + b * c) ^ 2 = 0 := by
    linear_combination hA + hB
  have hX2 : (a * d + b * c) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h h6ne
    · exact h
  rw [pow_two] at hX2
  exact mul_self_eq_zero.mp hX2

theorem cross_eq_zero_of_dMax_four (hp4 : 4 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) {m : ℕ}
    (f : Module.Basis (Fin m) (ZMod p) U) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hc : Module.reflection hψ ∈ G) {i j : Fin m} (hij : i ≠ j)
    (hti : (ψ (f i) = 0 ∧ f.repr w i = 0) ∨ ψ (f i) * f.repr w i = 1)
    (htj : (ψ (f j) = 0 ∧ f.repr w j = 0) ∨ ψ (f j) * f.repr w j = 1)
    (hπ : ∀ s : ZMod p, (s = 1 ∨ s = -1) → ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat i j s) :
    ψ (f i) * f.repr w j + ψ (f j) * f.repr w i = 0 := by
  rcases hti with ⟨hψi, hwi⟩ | hti'
  · rw [hψi, hwi]; ring
  rcases htj with ⟨hψj, hwj⟩ | htj'
  · rw [hψj, hwj]; ring
  have hbond : ∀ s : ZMod p, (s = 1 ∨ s = -1) →
      EtaOK 4 (ψ (f i) - s⁻¹ * ψ (f j)) (f.repr w i - s * f.repr w j) :=
    fun s hs => etaOK_four_pij hp4 hG f hψ hc hij hs (hπ s hs)
  exact cross_eq_zero_of_etaOK_four hp4 hti' htj'
    (hbond 1 (Or.inl rfl)) (hbond (-1) (Or.inr rfl))

end CFSG.StandardType.ZS

end
