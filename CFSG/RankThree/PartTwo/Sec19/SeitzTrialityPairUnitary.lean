module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairSub
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.RankThree.PartTwo.Sec19.NF5Pair
open Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem exists_omega [Finite F] (h3 : 3 ∣ Nat.card F - 1) : ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvd
  refine ⟨(x : F), ?_⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  have h3' : (x : F) ^ 3 = 1 := by
    have := congrArg Units.val hx3
    simpa using this
  have h1' : (x : F) ≠ 1 := fun h => hx1 (Units.ext h)
  have : ((x : F) - 1) * ((x : F) ^ 2 + (x : F) + 1) = 0 := by linear_combination h3'
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1')

theorem pow_cube_root {ω : F} (hω3 : ω ^ 3 = 1) (q : ℕ) : ω ^ q = ω ^ (q % 3) := by
  conv_lhs => rw [← Nat.div_add_mod q 3, pow_add, pow_mul, hω3, one_pow, one_mul]

theorem two_pow_mod_three_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

section Unitary

variable {p f : ℕ} (h : UnitaryFieldData p f F)

theorem homMat_mem_gu {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) (hbω : h.bar ω * ω = 1) :
    ∃ d ∈ Sec4.glPi false 3 (p ^ f) F, (d : Matrix (Fin 3) (Fin 3) F) = homMat ω := by
  obtain ⟨-, hU, -⟩ := homMat_spec hω1 hω3
  refine ⟨hU.unit, ?_, IsUnit.unit_spec _⟩
  rw [Sec4.mem_glPi_false h, IsUnit.unit_spec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, hbω]

theorem heisMat_mem_gu {l : F} (hl : ∀ θ : F, θ ^ 3 ≠ l) (hbl : h.bar l * l = 1) :
    ∃ c ∈ Sec4.glPi false 3 (p ^ f) F, (c : Matrix (Fin 3) (Fin 3) F) = heisMat l := by
  obtain ⟨-, hU, -⟩ := heisMat_spec hl
  refine ⟨hU.unit, ?_, IsUnit.unit_spec _⟩
  rw [Sec4.mem_glPi_false h, IsUnit.unit_spec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three, hbl]

theorem phi_mem_gu (hF2 : (2 : F) = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hbar : h.bar ω = ω ^ 2) :
    ∃ P ∈ Sec4.glPi false 3 (p ^ f) F, (P : Matrix (Fin 3) (Fin 3) F) = Phi ω := by
  obtain ⟨-, hF4, -⟩ := fourier_identities hF2 hω
  have hPhiU : IsUnit (Phi ω) :=
    ⟨⟨Phi ω, Phi ω * Phi ω * Phi ω, by simpa [mul_assoc] using hF4, hF4⟩, rfl⟩
  refine ⟨hPhiU.unit, ?_, IsUnit.unit_spec _⟩
  rw [Sec4.mem_glPi_false h, IsUnit.unit_spec]
  have h3 : (3 : F) = 1 := by linear_combination hF2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hb2 : h.bar (ω ^ 2) = ω := by
    rw [map_pow, hbar]
    linear_combination ω * hω3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phi, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hbar, hb2] <;> grind

@[expose] def cj (b : F →+* F) (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (M.map b)ᵀ

theorem cj_mul (b : F →+* F) (M N : Matrix (Fin 3) (Fin 3) F) :
    cj b (M * N) = cj b N * cj b M := by
  simp [cj, Matrix.map_mul, Matrix.transpose_mul]

theorem cj_diagonal (b : F →+* F) (d : Fin 3 → F) :
    cj b (Matrix.diagonal d) = Matrix.diagonal (fun i => b (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [cj]
  · simp [cj, Matrix.diagonal_apply, hij, Ne.symm hij]

theorem off_diag_zero (hF2 : (2 : F) = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hbar : h.bar ω = ω ^ 2) {ν : F} (hν : h.bar ν = ν) {c : F} (k : ℕ) (hk : ¬ 3 ∣ k)
    (hc : c * (ν * ω ^ k) = c) : c = 0 := by
  by_contra hc0
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    have h3 : (3 : F) = 0 := by rw [h1] at hω; linear_combination hω
    have h4 : (1 : F) = 0 := by linear_combination h3 - hF2
    exact one_ne_zero h4
  have h1 : ν * ω ^ k = 1 := by
    have : c * (ν * ω ^ k) = c * 1 := by rw [hc, mul_one]
    exact mul_left_cancel₀ hc0 this
  have h2 : ν * (ω ^ 2) ^ k = 1 := by
    have := congrArg h.bar h1
    rwa [map_mul, hν, map_pow, hbar, map_one] at this
  have h3 : ω ^ k = 1 := by
    have hν0 : ν ≠ 0 := by
      rintro rfl
      simp at h1
    have : ν * (ω ^ k) * (ω ^ k - 1) = 0 := by
      have e : (ω ^ 2) ^ k = (ω ^ k) ^ 2 := by ring
      rw [e] at h2
      linear_combination h2 - h1
    have h4 := (mul_eq_zero.1 this).resolve_left (by rw [h1]; exact one_ne_zero)
    exact sub_eq_zero.1 h4
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  exact hk (hord ▸ (orderOf_dvd_iff_pow_eq_one.2 h3))

theorem exists_unitary_eigenbasis (hF2 : (2 : F) = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hbar : h.bar ω = ω ^ 2) {g : GL (Fin 3) F} (hg : g ∈ Sec4.glPi false 3 (p ^ f) F)
    (hR : IsReg ω (g : Matrix (Fin 3) (Fin 3) F)) :
    ∃ A ∈ Sec4.glPi false 3 (p ^ f) F, ∃ μ : F,
      (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * (μ • Dm ω) := by
  classical
  obtain ⟨a, μ, ha, hga⟩ := hR
  have hgu : cj h.bar (g : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) = 1 :=
    (Sec4.mem_glPi_false h).1 hg
  obtain ⟨lam, hlamdef⟩ : ∃ lam : Fin 3 → F, lam = fun i : Fin 3 => μ * ω ^ (i : ℕ) := ⟨_, rfl⟩
  have hlam : μ • Dm ω = Matrix.diagonal lam := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dm, hlamdef, Matrix.diagonal_apply]
  rw [hlam] at hga
  obtain ⟨Gm, hGm⟩ : ∃ Gm : Matrix (Fin 3) (Fin 3) F, Gm = cj h.bar a * a := ⟨_, rfl⟩
  have hG : cj h.bar (Matrix.diagonal lam) * Gm * Matrix.diagonal lam = Gm := by
    calc cj h.bar (Matrix.diagonal lam) * Gm * Matrix.diagonal lam
        = cj h.bar (a * Matrix.diagonal lam) * (a * Matrix.diagonal lam) := by
          rw [hGm, cj_mul]; simp only [Matrix.mul_assoc]
      _ = cj h.bar ((g : Matrix (Fin 3) (Fin 3) F) * a) * ((g : Matrix (Fin 3) (Fin 3) F) * a) := by
          rw [hga]
      _ = cj h.bar a * (cj h.bar (g : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) *
            a := by rw [cj_mul]; simp only [Matrix.mul_assoc]
      _ = Gm := by rw [hgu, Matrix.mul_one, hGm]
  have hGij : ∀ i j, h.bar (lam i) * Gm i j * lam j = Gm i j := by
    intro i j
    have := congrFun (congrFun hG i) j
    rw [cj_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this
  have hν : h.bar (h.bar μ * μ) = h.bar μ * μ := by rw [map_mul, h.bar_bar, mul_comm]
  have hoff : ∀ i j, i ≠ j → Gm i j = 0 := by
    intro i j hij
    refine off_diag_zero h hF2 hω hbar hν (c := Gm i j) (2 * (i : ℕ) + (j : ℕ)) ?_ ?_
    · have hi := i.isLt
      have hj := j.isLt
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
      omega
    · have e := hGij i j
      rw [hlamdef] at e
      simp only [map_mul, map_pow, hbar] at e
      calc Gm i j * (h.bar μ * μ * ω ^ (2 * (i : ℕ) + (j : ℕ)))
          = h.bar μ * (ω ^ 2) ^ (i : ℕ) * Gm i j * (μ * ω ^ (j : ℕ)) := by ring
        _ = Gm i j := e
  obtain ⟨d, hd⟩ : ∃ d : Fin 3 → F, d = fun i => Gm i i := ⟨_, rfl⟩
  have hGd : Gm = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hd]
    · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdbar : ∀ i, h.bar (d i) = d i := by
    intro i
    have : d i = ∑ k, h.bar (a k i) * a k i := by
      rw [hd]; simp only [hGm, cj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, h.bar_bar, mul_comm]
  have hdet : Gm.det ≠ 0 := by
    have hdeta : a.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det a).1 ha).ne_zero
    have hmap : (a.map h.bar).det = h.bar a.det := by
      rw [RingHom.map_det]; rfl
    have : Gm.det = h.bar a.det * a.det := by
      rw [hGm, Matrix.det_mul, cj, Matrix.det_transpose, hmap]
    rw [this]
    exact mul_ne_zero (by simpa using hdeta) hdeta
  have hdne : ∀ i, d i ≠ 0 := by
    intro i hi0
    apply hdet
    rw [hGd, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi0
  have hfix : ∀ i, (d i)⁻¹ ∈ h.fixedField := fun i => by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, hdbar]
  choose c hc using fun i => h.normHom_surjective ⟨(d i)⁻¹, hfix i⟩
  have hc' : ∀ i, c i * h.bar (c i) = (d i)⁻¹ := fun i => by
    have := congrArg Subtype.val (hc i)
    simpa [UnitaryFieldData.norm] using this
  have hcne : ∀ i, c i ≠ 0 := fun i h0 => by
    have := hc' i
    rw [h0, zero_mul] at this
    exact inv_ne_zero (hdne i) this.symm
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin 3) (Fin 3) F, A' = a * Matrix.diagonal c := ⟨_, rfl⟩
  have hA'unit : IsUnit A' := by
    rw [hA']
    refine ha.mul ?_
    rw [Matrix.isUnit_diagonal]
    exact Pi.isUnit_iff.2 fun i => (hcne i).isUnit
  have hA'uni : cj h.bar A' * A' = 1 := by
    rw [hA', cj_mul, cj_diagonal]
    calc Matrix.diagonal (fun i => h.bar (c i)) * cj h.bar a * (a * Matrix.diagonal c)
        = Matrix.diagonal (fun i => h.bar (c i)) * (cj h.bar a * a) * Matrix.diagonal c := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => h.bar (c i)) * Matrix.diagonal d * Matrix.diagonal c := by
          rw [← hGm, hGd]
      _ = 1 := by
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext i
          calc h.bar (c i) * d i * c i = (c i * h.bar (c i)) * d i := by ring
            _ = (d i)⁻¹ * d i := by rw [hc' i]
            _ = 1 := inv_mul_cancel₀ (hdne i)
  have hgA : (g : Matrix (Fin 3) (Fin 3) F) * A' = A' * Matrix.diagonal lam := by
    rw [hA', ← Matrix.mul_assoc, hga, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _
  refine ⟨hA'unit.unit, ?_, μ, ?_⟩
  · rw [Sec4.mem_glPi_false h, IsUnit.unit_spec]
    exact hA'uni
  · rw [IsUnit.unit_spec, hlam]
    exact hgA

theorem noncube_pow {ν : F} (hν0 : ν ≠ 0) (hν : ∀ θ : F, θ ^ 3 ≠ ν) {m : ℕ} (hm : ¬ 3 ∣ m) :
    ∀ θ : F, θ ^ 3 ≠ ν ^ m := by
  intro θ hθ
  obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 1 ∨ m = 3 * k + 2 := ⟨m / 3, by omega⟩
  have hk0 : ν ^ k ≠ 0 := pow_ne_zero _ hν0
  rcases hk with rfl | rfl
  · apply hν (θ / ν ^ k)
    rw [div_pow, hθ]
    field_simp
    ring
  · have hρ : (θ / ν ^ k) ^ 3 = ν ^ 2 := by
      rw [div_pow, hθ]
      field_simp
      ring
    have hρ0 : θ / ν ^ k ≠ 0 := by
      intro h0
      rw [h0] at hρ
      simp at hρ
      exact hν0 ((pow_eq_zero_iff two_ne_zero).1 hρ.symm)
    apply hν (ν / (θ / ν ^ k))
    rw [div_pow, hρ]
    field_simp

theorem exists_noncube_norm_one {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hq3 : ¬ 3 ∣ p ^ f - 1) :
    ∃ l : F, (∀ θ : F, θ ^ 3 ≠ l) ∧ h.bar l * l = 1 := by
  classical
  haveI := h.finite
  obtain ⟨ν, hν⟩ := exists_noncube hω1 hω3
  have hν0 : ν ≠ 0 := fun h0 => hν 0 (by simp [h0])
  refine ⟨ν ^ (p ^ f - 1), noncube_pow hν0 hν hq3, ?_⟩
  have hfin : ν ^ (Nat.card F - 1) = 1 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one ν hν0
  rw [h.card_eq_sq] at hfin
  rw [h.bar_apply, ← pow_mul, ← pow_add]
  convert hfin using 2
  obtain ⟨R, hR⟩ : ∃ R, p ^ f = R + 1 := ⟨p ^ f - 1, by have := h.one_lt_pow; omega⟩
  rw [hR, Nat.add_sub_cancel]
  have : (R + 1) ^ 2 = R * (R + 1) + R + 1 := by ring
  generalize R * (R + 1) = T at this ⊢
  omega

theorem pairPropIn_gu (h : UnitaryFieldData p f F) (hp : p = 2) (hq : p ^ f % 3 = 2) :
    PairPropIn ((Sec4.glPi false 3 (p ^ f) F).map
      (ProjGenLinGroup.mk : GL (Fin 3) F →* PGL(3, F))) := by
  classical
  haveI := h.finite
  have hF2 : (2 : F) = 0 := by
    have : CharP F 2 := hp ▸ h.charP
    simpa using CharP.cast_eq_zero F 2
  have hsq : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  obtain ⟨ω, hω⟩ := exists_omega (F := F) (by
    rw [h.card_eq_sq]
    generalize (p ^ f) ^ 2 = Q at hsq ⊢
    omega)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    have h3 : (3 : F) = 0 := by rw [h1] at hω; linear_combination hω
    have h4 : (1 : F) = 0 := by linear_combination h3 - hF2
    exact one_ne_zero h4
  have hbar : h.bar ω = ω ^ 2 := by rw [h.bar_apply, pow_cube_root hω3, hq]
  have hbω : h.bar ω * ω = 1 := by rw [hbar]; linear_combination hω3
  have hq3 : ¬ 3 ∣ p ^ f - 1 := by omega
  obtain ⟨l, hl, hbl⟩ := exists_noncube_norm_one h hω1 hω3 hq3
  exact pairPropIn_of_data _ hF2 hω (homMat_mem_gu h hω1 hω3 hbω)
    ⟨l, hl, heisMat_mem_gu h hl hbl⟩ (phi_mem_gu h hF2 hω hbar)
    (fun g hg hR => exists_unitary_eigenbasis h hF2 hω hbar hg hR)

end Unitary

section Final

open CFSG.PGLModel (projImage)

theorem _root_.CFSG.RankThree.PartTwo.Sec19.NF5Pair.PairProp.of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    (h : PairProp N) : PairProp M := by
  intro z hz3 hz1
  obtain ⟨m, hc, hn⟩ := h (e z) (by rw [← map_pow, hz3, map_one])
    (fun h1 => hz1 (e.injective (by rw [h1, map_one])))
  refine ⟨e.symm m, ?_, ?_⟩
  · apply e.injective
    simpa using hc
  · intro hmem
    apply hn
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, by simpa using congrArg e hk⟩

theorem _root_.CFSG.RankThree.PartTwo.Sec19.NF5Pair.PairProp.subgroup {G : Type*} [Group G] {M : Subgroup G}
    (h : PairProp M) {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ m ∈ M, (m * z * m⁻¹) * z = z * (m * z * m⁻¹) ∧ m * z * m⁻¹ ∉ Subgroup.zpowers z := by
  obtain ⟨m, hc, hn⟩ := h ⟨z, hzM⟩ (Subtype.ext (by simpa using hz3))
    (fun h1 => hz1 (congrArg Subtype.val h1))
  refine ⟨m, m.2, congrArg Subtype.val hc, ?_⟩
  intro hmem
  apply hn
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem pair_projImage_glPi_false (n : ℕ) (hn : Odd n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    PairProp (projImage (Sec4.glPi false 3 (2 ^ n) F)) := by
  have h : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, by obtain ⟨k, rfl⟩ := hn; omega, by rw [hF, ← pow_mul, mul_comm]⟩
  exact (pairPropIn_gu h rfl (two_pow_mod_three_odd hn)).pairProp

theorem pair_projImage_glPi_true (n : ℕ) (hn : Even n) (hn1 : 1 ≤ n) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) :
    PairProp (projImage (Sec4.glPi true 3 (2 ^ n) F)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : (2 : F) = 0 := by
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    simpa using CharP.cast_eq_zero F 2
  have hmod := two_pow_mod_three_even hn
  obtain ⟨ω, hω⟩ := exists_omega (F := F) (by
    rw [hF]
    generalize 2 ^ n = Q at hmod ⊢
    omega)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    have h3 : (3 : F) = 0 := by rw [h1] at hω; linear_combination hω
    have h4 : (1 : F) = 0 := by linear_combination h3 - hF2
    exact one_ne_zero h4
  obtain ⟨l, hl⟩ := exists_noncube hω1 hω3
  obtain ⟨-, hF4, -⟩ := fourier_identities hF2 hω
  have hPhiU : IsUnit (Phi ω) :=
    ⟨⟨Phi ω, Phi ω * Phi ω * Phi ω, by simpa [mul_assoc] using hF4, hF4⟩, rfl⟩
  refine (pairPropIn_of_data (Sec4.glPi true 3 (2 ^ n) F) hF2 hω ?_ ?_ ?_ ?_).pairProp
  · exact ⟨(homMat_spec hω1 hω3).2.1.unit, Sec4.mem_glPi_true _ _, IsUnit.unit_spec _⟩
  · exact ⟨l, hl, (heisMat_spec hl).2.1.unit, Sec4.mem_glPi_true _ _, IsUnit.unit_spec _⟩
  · exact ⟨hPhiU.unit, Sec4.mem_glPi_true _ _, IsUnit.unit_spec _⟩
  · rintro g - ⟨a, μ, ha, hga⟩
    exact ⟨ha.unit, Sec4.mem_glPi_true _ _, μ, by rw [IsUnit.unit_spec]; exact hga⟩

end Final

end CFSG.RankThree.PartTwo.Sec19.NF5Pair