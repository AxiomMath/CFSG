module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.Open.LocalVocabulary
import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix CFSG.Open CFSG.AGLEmbedding

private lemma eigenspace_eq_bot_of_cube_ne_one {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (D : Module.End K V) (hD : D ^ 3 = 1) {μ : K}
    (hμ : μ ^ 3 ≠ 1) : D.eigenspace μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv
  have h3 : D (D (D v)) = v := by
    have h := congrArg (fun f : Module.End K V => f v) hD
    simp only [Module.End.one_apply] at h
    rw [show D ^ 3 = D * D * D by rw [pow_succ, pow_succ, pow_one],
      Module.End.mul_apply, Module.End.mul_apply] at h
    exact h
  simp only [hv, map_smul, smul_smul] at h3
  have hm : μ * μ * μ = μ ^ 3 := by ring
  rw [hm] at h3
  have : (μ ^ 3 - 1) • v = 0 := by rw [sub_smul, one_smul, h3, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hμ
  · exact h

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

private lemma two_eq_zero_of_char_two {K : Type} [Field K] [CharP K 2] : (2 : K) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CharP.cast_eq_zero K 2

private lemma three_eq_one_of_char_two {K : Type} [Field K] [CharP K 2] : (3 : K) = 1 := by
  have : (3 : K) = (2 : K) + 1 := by norm_num
  rw [this, two_eq_zero_of_char_two, zero_add]

private lemma matrix_eq_smul_one_of_cube_eq_one {K : Type} [Field K] [CharP K 2] (M : Matrix (Fin 3) (Fin 3) K)
    (hM3 : M ^ 3 = 1) (h11 : M 1 1 = M 0 0) (h22 : M 2 2 = M 0 0)
    (htri : ∀ i j : Fin 3, j < i → M i j = 0) (hc0 : M 0 0 ≠ 0) :
    M = M 0 0 • 1 := by
  have h10 : M 1 0 = 0 := htri 1 0 (by decide)
  have h20 : M 2 0 = 0 := htri 2 0 (by decide)
  have h21 : M 2 1 = 0 := htri 2 1 (by decide)
  have h01 : M 0 1 = 0 := by
    have h := congrFun (congrFun hM3 0) 1
    rw [show (1 : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 from by simp [Matrix.one_apply]] at h
    rw [show M ^ 3 = M * M * M by rw [pow_succ, pow_two]] at h
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h11, h22, zero_mul, mul_zero,
      add_zero, zero_add] at h
    ring_nf at h
    rw [three_eq_one_of_char_two, mul_one] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hc0)
  have h02 : M 0 2 = 0 := by
    have h := congrFun (congrFun hM3 0) 2
    rw [show (1 : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 from by simp [Matrix.one_apply]] at h
    rw [show M ^ 3 = M * M * M by rw [pow_succ, pow_two]] at h
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h11, h22, h01, zero_mul,
      mul_zero, add_zero, zero_add] at h
    ring_nf at h
    rw [three_eq_one_of_char_two, mul_one] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hc0)
  have h12 : M 1 2 = 0 := by
    have h := congrFun (congrFun hM3 1) 2
    rw [show (1 : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 from by simp [Matrix.one_apply]] at h
    rw [show M ^ 3 = M * M * M by rw [pow_succ, pow_two]] at h
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h11, h22, h01, h02, zero_mul,
      mul_zero, add_zero, zero_add] at h
    ring_nf at h
    rw [three_eq_one_of_char_two, mul_one] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hc0)
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [Matrix.smul_apply, h11, h22]
  · have hz : M i j = 0 := by
      by_cases hlt : j < i
      · exact htri i j hlt
      · fin_cases i <;> fin_cases j <;> simp_all
    rw [hz]
    simp [Matrix.smul_apply, Matrix.one_apply, hij]

theorem u5_par_impossible {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    (A : Subgroup (GL (Fin 5) K)) (hA : A ≤ StatedSU 5 q K)
    (hAe : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 3)
    (d : GL (Fin 5) K) (hdA : d ∈ A) (α : K) (hα3 : α ^ 3 = 1)
    (hshape : Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)) α) = 3 ∧
      ∀ β : K, β ^ 3 = 1 → β ≠ α →
        Module.finrank K
          (Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)) β) = 1)
    (hker : ∀ a ∈ A,
      (∃ c : K, ∀ v ∈ Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)) α,
        (a : Matrix (Fin 5) (Fin 5) K) *ᵥ v = c • v) → a ∈ Subgroup.zpowers d) :
    ¬ ∃ W : Submodule K (Fin 5 → K), W ≠ ⊥ ∧ IsTotallyIsotropicSU q W ∧
      ∀ a ∈ A, ∀ w ∈ W, (a : Matrix (Fin 5) (Fin 5) K) *ᵥ w ∈ W := by
  classical
  obtain ⟨f, hf1, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have hKf : Nat.card K = (2 ^ f) ^ 2 := by rw [hq] at hK; exact hK
  rw [hq] at hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Module.End K (Fin 5 → K) := Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)
  have hd3M : (d : Matrix (Fin 5) (Fin 5) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hAe.2 d hdA, Units.val_one]
  have hD3 : D ^ 3 = 1 := by
    dsimp only [D]
    rw [← Matrix.toLin'_pow, hd3M, Matrix.toLin'_one]
    rfl
  have hDapply : ∀ u : Fin 5 → K, D u = (d : Matrix (Fin 5) (Fin 5) K) *ᵥ u := fun u => rfl
  let F : CFSG.LieType.BorelTits.ReflForm K (Fin 5 → K) :=
    CFSG.LieType.BorelTits.unitaryForm 2 f hKf 5
  have hq3' : 3 ∣ 2 ^ f + 1 := by rw [← hq]; exact hq3
  have hDiso : ∀ u v : Fin 5 → K, F.β (D u) (D v) = F.β u v := by
    intro u v
    rw [hDapply, hDapply]
    exact CFSG.LieType.BorelTits.statedSU_preserves hKf (hA hdA) u v
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα3
  have h3card : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have hqmod : q % 3 = 2 := mod_three_eq_two_of_dvd_add_one hq3
    have h1 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hqmod]
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' 3 h3card
  have hω3u : ωu ^ 3 = 1 := by rw [← hωu]; exact pow_orderOf_eq_one ωu
  have hω1u : ωu ≠ 1 := by rintro rfl; rw [orderOf_one] at hωu; omega
  have hω3 : ((ωu : K)) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3u, Units.val_one]
  have hω1 : (ωu : K) ≠ 1 := fun h => hω1u (Units.ext h)
  let β : K := α * (ωu : K)
  let γ : K := α * (ωu : K) ^ 2
  have hβ3 : β ^ 3 = 1 := by
    simp only [β, mul_pow, hα3, hω3, one_mul]
  have hγ3 : γ ^ 3 = 1 := by
    simp only [γ, mul_pow, hα3, one_mul]
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hβα : β ≠ α := by
    intro h
    have h' : α * (ωu : K) = α := h
    exact hω1 (mul_left_cancel₀ hα0 (by rw [h', mul_one]))
  have hγα : γ ≠ α := by
    intro h
    have h' : α * (ωu : K) ^ 2 = α := h
    have hω2 : (ωu : K) ^ 2 = 1 := mul_left_cancel₀ hα0 (by rw [h', mul_one])
    apply hω1
    calc (ωu : K) = (ωu : K) * (ωu : K) ^ 2 := by rw [hω2, mul_one]
      _ = (ωu : K) ^ 3 := by ring
      _ = 1 := hω3
  have hβγ : β ≠ γ := by
    intro h
    have h' : (ωu : K) = (ωu : K) ^ 2 := mul_left_cancel₀ hα0 h
    apply hω1
    have h1 : (ωu : K) * (1 : K) = (ωu : K) * (ωu : K) := by
      rw [mul_one, ← pow_two]
      exact h'
    exact (mul_left_cancel₀ ωu.ne_zero h1).symm
  have hαβ : α ≠ β := hβα.symm
  have hαγ : α ≠ γ := hγα.symm
  have hγβ : γ ≠ β := hβγ.symm
  let Eα : Submodule K (Fin 5 → K) := D.eigenspace α
  let Eβ : Submodule K (Fin 5 → K) := D.eigenspace β
  let Eγ : Submodule K (Fin 5 → K) := D.eigenspace γ
  have hEα3 : Module.finrank K Eα = 3 := hshape.1
  have hEβ1 : Module.finrank K Eβ = 1 := hshape.2 β hβ3 hβα
  have hEγ1 : Module.finrank K Eγ = 1 := hshape.2 γ hγ3 hγα
  have hsup : Eα ⊔ Eβ ⊔ Eγ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    have hd1 : Disjoint Eα Eβ := eigenspace_disjoint_of_ne D hαβ
    have hd2 : Disjoint (Eα ⊔ Eβ) Eγ := eigenspace_sup_disjoint_of_ne D hαβ hαγ hβγ
    rw [finrank_sup_of_disjoint hd2, finrank_sup_of_disjoint hd1, hEα3, hEβ1, hEγ1]
  have horthαβ : ∀ u ∈ Eα, ∀ v ∈ Eβ, F.β u v = 0 := by
    intro u hu v hv
    exact eigenspace_orthogonal_of_unitary hKf hDiso hα3 hβ3 hαβ hq3' hu hv
  have horthαγ : ∀ u ∈ Eα, ∀ v ∈ Eγ, F.β u v = 0 := by
    intro u hu v hv
    exact eigenspace_orthogonal_of_unitary hKf hDiso hα3 hγ3 hαγ hq3' hu hv
  have horthβα : ∀ u ∈ Eβ, ∀ v ∈ Eα, F.β u v = 0 := by
    intro u hu v hv
    exact eigenspace_orthogonal_of_unitary hKf hDiso hβ3 hα3 hβα hq3' hu hv
  have horthγα : ∀ u ∈ Eγ, ∀ v ∈ Eα, F.β u v = 0 := by
    intro u hu v hv
    exact eigenspace_orthogonal_of_unitary hKf hDiso hγ3 hα3 hγα hq3' hu hv
  have hEα_nd : Eα ⊓ F.perp Eα = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvα, hvperp⟩ := hv
    apply F.nondeg
    intro w
    have hw : w ∈ Eα ⊔ Eβ ⊔ Eγ := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    have h1 : F.β v a = 0 := F.refl a v (hvperp a ha)
    have h2 : F.β v b = 0 := F.refl b v (horthβα b hb v hvα)
    have h3 : F.β v c = 0 := F.refl c v (horthγα c hc v hvα)
    rw [F.add_right, F.add_right, h1, h2, h3]
    simp
  have hEβ_nd : Eβ ⊓ F.perp Eβ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvβ, hvperp⟩ := hv
    apply F.nondeg
    intro w
    have hw : w ∈ Eα ⊔ Eβ ⊔ Eγ := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    have h1 : F.β v a = 0 := F.refl a v (horthαβ a ha v hvβ)
    have h2 : F.β v b = 0 := F.refl b v (hvperp b hb)
    have h3 : F.β v c = 0 := F.refl c v
      (eigenspace_orthogonal_of_unitary hKf hDiso hγ3 hβ3 hγβ hq3' hc hvβ)
    rw [F.add_right, F.add_right, h1, h2, h3]
    simp
  have hEμ_anis : ∀ μ : K, μ ^ 3 = 1 → μ ≠ α →
      ∀ v : Fin 5 → K, v ∈ D.eigenspace μ → v ≠ 0 → F.β v v ≠ 0 := by
    intro μ hμ3 hμα v hv hv0
    intro hvβ0
    have hμ1 : Module.finrank K (D.eigenspace μ) = 1 := hshape.2 μ hμ3 hμα
    have hnd : D.eigenspace μ ⊓ F.perp (D.eigenspace μ) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [Submodule.mem_inf] at hy
      obtain ⟨hyμ, hyperp⟩ := hy
      apply F.nondeg
      intro z
      have hz : z ∈ Eα ⊔ Eβ ⊔ Eγ := by rw [hsup]; exact Submodule.mem_top
      obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have ha' : F.β y a = 0 := by
        by_cases h : μ = α
        · subst h; exact F.refl a y (hyperp a ha)
        · exact eigenspace_orthogonal_of_unitary hKf hDiso hμ3 hα3 h hq3' hyμ ha
      have hb' : F.β y b = 0 := by
        by_cases h : μ = β
        · subst h; exact F.refl b y (hyperp b hb)
        · exact eigenspace_orthogonal_of_unitary hKf hDiso hμ3 hβ3 h hq3' hyμ hb
      have hc' : F.β y c = 0 := by
        by_cases h : μ = γ
        · subst h; exact F.refl c y (hyperp c hc)
        · exact eigenspace_orthogonal_of_unitary hKf hDiso hμ3 hγ3 h hq3' hyμ hc
      rw [F.add_right, F.add_right, ha', hb', hc']
      simp
    have hvperp : v ∈ F.perp (D.eigenspace μ) := by
      intro w hw
      have hspan : D.eigenspace μ = K ∙ v := by
        symm
        apply Submodule.eq_of_le_of_finrank_eq
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
        · rw [hμ1, finrank_span_singleton hv0]
      rw [hspan] at hw
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [F.smul_left, hvβ0, mul_zero]
    have hmem : v ∈ D.eigenspace μ ⊓ F.perp (D.eigenspace μ) := ⟨hv, hvperp⟩
    rw [hnd, Submodule.mem_bot] at hmem
    exact hv0 hmem
  rintro ⟨W, hW0, hWtot, hWstab⟩
  have hWtot' : F.IsTotallyIsotropic W := by
    intro v hv w hw
    have h := hWtot v hv w hw
    have hvw : F.β v w = 0 := by
      simpa [F, CFSG.LieType.BorelTits.unitaryForm_β,
        CFSG.LieType.BorelTits.unitaryInvolution,
        CFSG.LieType.BorelTits.unitaryInvolution_apply,
        iterateFrobeniusEquiv_apply, iterateFrobenius_def, hq] using h
    exact F.refl v w hvw
  have hWD : ∀ x ∈ W, D x ∈ W := by
    intro x hx
    rw [hDapply]
    exact hWstab d hdA x hx
  have hgenE : ∀ μ : K, (D.genEigenspace μ) 1 = D.eigenspace μ := by
    intro μ
    rw [Module.End.genEigenspace_one]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero, Module.End.mem_eigenspace_iff]
  have hsup_gen : ⨆ μ : K, (D.genEigenspace μ) 1 = ⊤ := by
    apply top_le_iff.mp
    rw [← hsup]
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [show Eα = (D.genEigenspace α) 1 from (hgenE α).symm]
        exact le_iSup (fun μ => (D.genEigenspace μ) 1) α
      · rw [show Eβ = (D.genEigenspace β) 1 from (hgenE β).symm]
        exact le_iSup (fun μ => (D.genEigenspace μ) 1) β
    · rw [show Eγ = (D.genEigenspace γ) 1 from (hgenE γ).symm]
      exact le_iSup (fun μ => (D.genEigenspace μ) 1) γ
  have hWle : W ≤ Eα := by
    rw [Submodule.eq_iSup_inf_genEigenspace (p := W) (f := D) 1 hWD hsup_gen]
    apply iSup_le
    intro μ
    by_cases hμ : μ = α
    · subst hμ; exact inf_le_right
    · have hbot : W ⊓ (D.genEigenspace μ) 1 = ⊥ := by
        rw [hgenE μ, Submodule.eq_bot_iff]
        intro x hx
        rw [Submodule.mem_inf] at hx
        obtain ⟨hxW, hxμ⟩ := hx
        by_cases hμ3 : μ ^ 3 = 1
        · by_contra hx0
          exact hEμ_anis μ hμ3 hμ x hxμ hx0 (hWtot' hxW x hxW)
        · rw [eigenspace_eq_bot_of_cube_ne_one D hD3 hμ3, Submodule.mem_bot] at hxμ
          exact hxμ
      rw [hbot]; exact bot_le
  have hWline : Module.finrank K W = 1 := by
    have hdisj : Disjoint (F.perp Eα) W := by
      rw [disjoint_iff_inf_le]
      intro x hx
      rw [Submodule.mem_bot]
      rw [Submodule.mem_inf] at hx
      obtain ⟨hxp, hxW⟩ := hx
      have hmem : x ∈ Eα ⊓ F.perp Eα := ⟨hWle hxW, hxp⟩
      rw [hEα_nd, Submodule.mem_bot] at hmem
      exact hmem
    have hle : F.perp Eα ⊔ W ≤ F.perp W := by
      apply sup_le
      · exact F.perp_antitone hWle
      · intro x hx w hw
        exact hWtot' hx w hw
    have hdimEαperp : Module.finrank K (F.perp Eα) = 2 := by
      have := F.finrank_perp Eα
      rw [hEα3, Module.finrank_fin_fun] at this
      omega
    have hmono : Module.finrank K ↥(F.perp Eα ⊔ W) ≤ Module.finrank K ↥(F.perp W) :=
      Submodule.finrank_mono hle
    rw [finrank_sup_of_disjoint hdisj, hdimEαperp] at hmono
    have hfin := F.finrank_perp W
    rw [Module.finrank_fin_fun] at hfin
    have hpos : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
    omega
  obtain ⟨e, heW, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have heEα : e ∈ Eα := hWle heW
  have heiso : F.β e e = 0 := hWtot' heW e heW
  have hW_eq : W = K ∙ e := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heW)
    · rw [hWline, finrank_span_singleton he0]
  let L : Submodule K (Fin 5 → K) := K ∙ e
  have heL : e ∈ L := Submodule.mem_span_singleton_self e
  let E : Submodule K (Fin 5 → K) := Eα ⊓ F.perp L
  let ρ : A →* Module.End K (Fin 5 → K) :=
    { toFun := fun a => Matrix.toLin' ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
      map_one' := by
        ext x
        simp [Matrix.toLin'_one]
      map_mul' := by
        intro a b
        ext x
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_mul, LinearMap.comp_apply,
          Module.End.mul_apply] }
  have hρiso : ∀ a : A, ∀ u v : Fin 5 → K, F.β (ρ a u) (ρ a v) = F.β u v := by
    intro a u v
    have := CFSG.LieType.BorelTits.statedSU_preserves hKf (hA a.2) u v
    change (CFSG.LieType.BorelTits.unitaryForm 2 f hKf 5).β
        (((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ u)
        (((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) =
      (CFSG.LieType.BorelTits.unitaryForm 2 f hKf 5).β u v
    exact this
  have he_stab : ∀ a : A, ∃ c : K, ρ a e = c • e := by
    intro a
    have hmem : ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e ∈ W :=
      hWstab (a : GL (Fin 5) K) a.2 e heW
    rw [hW_eq, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  have hAe_line : ∀ a : A, ∃ c : K, ρ a e = c • e ∧ c ≠ 0 := by
    intro a
    obtain ⟨c, hc⟩ := he_stab a
    refine ⟨c, hc, ?_⟩
    intro h0
    have hz : ρ a e = 0 := by rw [hc, h0, zero_smul]
    have hx : ρ a⁻¹ (ρ a e) = e := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hz, map_zero] at hx
    exact he0 hx.symm
  have hρD : ∀ a : A, ρ a * D = D * ρ a := by
    intro a
    have hcommA : a * ⟨d, hdA⟩ = ⟨d, hdA⟩ * a :=
      hAe.1.is_comm.comm a ⟨d, hdA⟩
    have h2 : ρ (a * ⟨d, hdA⟩) = ρ (⟨d, hdA⟩ * a) := by rw [hcommA]
    rw [map_mul, map_mul] at h2
    change ρ a * D = D * ρ a
    exact h2
  have hρEα : ∀ a : A, ∀ x ∈ Eα, ρ a x ∈ Eα := by
    intro a x hx
    have hx' : D x = α • x := Module.End.mem_eigenspace_iff.mp hx
    have h : D (ρ a x) = α • (ρ a x) := by
      calc D (ρ a x) = (D * ρ a) x := (Module.End.mul_apply D (ρ a) x).symm
        _ = (ρ a * D) x := by rw [← hρD a]
        _ = ρ a (D x) := Module.End.mul_apply (ρ a) D x
        _ = ρ a (α • x) := by rw [hx']
        _ = α • (ρ a x) := map_smul (ρ a) α x
    exact Module.End.mem_eigenspace_iff.mpr h
  have hρE : ∀ a : A, ∀ x ∈ E, ρ a x ∈ E := by
    intro a x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxα, hxp⟩ := hx
    refine Submodule.mem_inf.mpr ⟨hρEα a x hxα, ?_⟩
    rw [F.mem_perp_span_singleton]
    obtain ⟨c, hc, hc0⟩ := hAe_line a
    have hiso := hρiso a e x
    rw [hc, F.smul_left, hxp e heL] at hiso
    rcases mul_eq_zero.mp hiso with h | h
    · exact absurd h (fun hh => hc0 ((F.σ).map_eq_zero_iff.mp hh))
    · exact h
  let rEα : A →* Module.End K Eα :=
    { toFun := fun a => (ρ a).restrict (hρEα a)
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp [map_mul, Module.End.mul_apply] }
  have heE : e ∈ E := by
    refine Submodule.mem_inf.mpr ⟨heEα, ?_⟩
    rw [F.mem_perp_span_singleton]
    exact heiso
  have hLE : L ≤ E := by
    change K ∙ e ≤ E
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heE)
  have hL1 : Module.finrank K L = 1 := by
    change Module.finrank K (K ∙ e) = 1
    exact finrank_span_singleton he0
  have hperpL : Module.finrank K (F.perp L) = 4 := by
    have := F.finrank_perp L
    rw [hL1, Module.finrank_fin_fun] at this
    omega
  have hperpEα : Module.finrank K (F.perp Eα) = 2 := by
    have := F.finrank_perp Eα
    rw [hEα3, Module.finrank_fin_fun] at this
    omega
  have hVdecomp : Eα ⊔ F.perp Eα = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    have hd : Disjoint Eα (F.perp Eα) := disjoint_iff_inf_le.mpr (by rw [hEα_nd])
    rw [finrank_sup_of_disjoint hd, hEα3, hperpEα]
  have hE2 : Module.finrank K E = 2 := by
    have hperpEα_le : F.perp Eα ≤ F.perp L :=
      F.perp_antitone (by change K ∙ e ≤ Eα; exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heEα))
    have hsupEL : E ⊔ F.perp Eα = F.perp L := by
      apply le_antisymm
      · apply sup_le
        · exact inf_le_right
        · exact hperpEα_le
      · intro x hx
        have hx' : x ∈ Eα ⊔ F.perp Eα := by rw [hVdecomp]; exact Submodule.mem_top
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx'
        refine Submodule.mem_sup.mpr ⟨a, ?_, b, hb, rfl⟩
        refine Submodule.mem_inf.mpr ⟨ha, ?_⟩
        have hb' : b ∈ F.perp L := hperpEα_le hb
        have hab : a + b ∈ F.perp L := hx
        have : a = (a + b) - b := by abel
        rw [this]
        exact (F.perp L).sub_mem hab hb'
    have hd : Disjoint E (F.perp Eα) := by
      rw [disjoint_iff_inf_le]
      intro x hx
      rw [Submodule.mem_bot]
      rw [Submodule.mem_inf] at hx
      obtain ⟨hxE, hxperp⟩ := hx
      rw [Submodule.mem_inf] at hxE
      have : x ∈ Eα ⊓ F.perp Eα := ⟨hxE.1, hxperp⟩
      rwa [hEα_nd, Submodule.mem_bot] at this
    have hsd := finrank_sup_of_disjoint hd
    rw [hsupEL, hperpL, hperpEα] at hsd
    omega
  have hLtE : L < E := Submodule.lt_of_le_of_finrank_lt_finrank hLE (by rw [hL1, hE2]; norm_num)
  obtain ⟨fv, hfE, hfL⟩ := IsConcreteLE.exists_of_lt hLtE
  have hEtEα : E < Eα :=
    Submodule.lt_of_le_of_finrank_lt_finrank inf_le_left (by rw [hE2, hEα3]; norm_num)
  obtain ⟨z, hzEα, hzE⟩ := IsConcreteLE.exists_of_lt hEtEα
  let vE : Fin 3 → Eα := ![⟨e, heEα⟩, ⟨fv, hfE.1⟩, ⟨z, hzEα⟩]
  have hli : LinearIndependent K vE := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • e + g 1 • fv + g 2 • z = 0 := by
      have := congrArg (fun y : Eα => (y : Fin 5 → K)) hg
      simp only [Fin.sum_univ_three, vE, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at this
      simpa using this
    have h2 : g 2 = 0 := by
      by_contra h2
      apply hzE
      have hrel : g 2 • z = -(g 0 • e + g 1 • fv) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hg'
      have hz : z = -((g 2)⁻¹ • (g 0 • e + g 1 • fv)) := by
        rw [← inv_smul_smul₀ h2 z, hrel, smul_neg]
      rw [hz]
      exact E.neg_mem (E.smul_mem _ (E.add_mem (E.smul_mem _ heE) (E.smul_mem _ hfE)))
    have h1 : g 1 = 0 := by
      by_contra h1
      apply hfL
      have hsum : g 0 • e + g 1 • fv = 0 := by simpa [h2] using hg'
      have hrel : g 1 • fv = -(g 0 • e) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
      have hf : fv = -((g 1)⁻¹ • (g 0 • e)) := by
        rw [← inv_smul_smul₀ h1 fv, hrel, smul_neg]
      rw [hf]
      change -((g 1)⁻¹ • (g 0 • e)) ∈ K ∙ e
      rw [smul_smul]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    have h0 : g 0 = 0 := by
      have : g 0 • e = 0 := by simpa [h1, h2] using hg'
      rcases smul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h he0
    intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 3) K Eα, ∀ i, b i = ![⟨e, heEα⟩, ⟨fv, hfE.1⟩, ⟨z, hzEα⟩] i :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hEα3]),
      fun i => by simp [vE, coe_basisOfLinearIndependentOfCardEqFinrank]⟩
  have hb0 : b 0 = (⟨e, heEα⟩ : Eα) := by simpa using hb 0
  have hb1 : b 1 = (⟨fv, hfE.1⟩ : Eα) := by simpa using hb 1
  have hb2 : b 2 = (⟨z, hzEα⟩ : Eα) := by simpa using hb 2
  have hrepr2 : ∀ y : Eα, (y : Fin 5 → K) ∈ E → b.repr y 2 = 0 := by
    intro y hy
    by_contra hc
    apply hzE
    have hz_decomp : b.repr y 2 • z =
        (y : Fin 5 → K) - (b.repr y 0 • e + b.repr y 1 • fv) := by
      have h := congrArg (fun t : Eα => (t : Fin 5 → K)) (b.sum_repr y)
      rw [Fin.sum_univ_three] at h
      simp only [Submodule.coe_add, Submodule.coe_smul, hb0, hb1, hb2] at h
      rw [← h]; abel
    have hz_eq : z = (b.repr y 2)⁻¹ •
        ((y : Fin 5 → K) - (b.repr y 0 • e + b.repr y 1 • fv)) := by
      rw [← hz_decomp, inv_smul_smul₀ hc]
    rw [hz_eq]
    exact E.smul_mem _ (E.sub_mem hy (E.add_mem (E.smul_mem _ heE) (E.smul_mem _ hfE)))
  let Mhm : A →* Matrix (Fin 3) (Fin 3) K :=
    { toFun := fun a => LinearMap.toMatrix b b (rEα a)
      map_one' := by rw [map_one, LinearMap.toMatrix_one]
      map_mul' := by intro a b; rw [map_mul, LinearMap.toMatrix_mul] }
  have hcol0 : ∀ a : A, Mhm a 1 0 = 0 ∧ Mhm a 2 0 = 0 := by
    intro a
    obtain ⟨c, hc, -⟩ := hAe_line a
    have hE0 : rEα a (b 0) = c • b 0 := by
      rw [hb0]; apply Subtype.ext
      change ρ a e = c • e
      exact hc
    constructor
    · rw [show Mhm a 1 0 = b.repr (rEα a (b 0)) 1 from LinearMap.toMatrix_apply b b (rEα a) 1 0]
      rw [hE0, map_smul, Module.Basis.repr_self]
      simp [Finsupp.smul_apply]
    · rw [show Mhm a 2 0 = b.repr (rEα a (b 0)) 2 from LinearMap.toMatrix_apply b b (rEα a) 2 0]
      rw [hE0, map_smul, Module.Basis.repr_self]
      simp [Finsupp.smul_apply]
  have hcol1 : ∀ a : A, Mhm a 2 1 = 0 := by
    intro a
    rw [show Mhm a 2 1 = b.repr (rEα a (b 1)) 2 from LinearMap.toMatrix_apply b b (rEα a) 2 1]
    apply hrepr2
    have : ((rEα a (b 1)) : Fin 5 → K) = ρ a fv := by rw [hb1]; rfl
    rw [this]
    exact hρE a fv hfE
  have htri : ∀ a : A, ∀ i j : Fin 3, j < i → Mhm a i j = 0 := by
    intro a i j hij
    fin_cases i
    · exact absurd hij (by simp)
    · fin_cases j
      · exact (hcol0 a).1
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
    · fin_cases j
      · exact (hcol0 a).2
      · exact hcol1 a
      · exact absurd hij (by simp)
  have hunit : ∀ a : A, IsUnit (Mhm a) := fun a => (Group.isUnit a).map Mhm
  have hunitE : ∀ a : A, IsUnit (rEα a) := fun a => (Group.isUnit a).map rEα
  have hdet : ∀ a : A, (Mhm a).det = Mhm a 0 0 * Mhm a 1 1 * Mhm a 2 2 := by
    intro a
    rw [Matrix.det_fin_three]
    simp only [htri a 1 0 (by decide), htri a 2 0 (by decide), htri a 2 1 (by decide)]
    ring
  have hdetne : ∀ a : A, (Mhm a).det ≠ 0 := by
    intro a
    have h : (Mhm a).det = LinearMap.det (rEα a) := LinearMap.det_toMatrix b (rEα a)
    rw [h]
    exact isUnit_iff_ne_zero.mp (LinearMap.isUnit_det (rEα a) (hunitE a))
  have h00 : ∀ a : A, Mhm a 0 0 ≠ 0 := by
    intro a h0
    exact hdetne a (by rw [hdet a, h0, zero_mul, zero_mul])
  have h11 : ∀ a : A, Mhm a 1 1 ≠ 0 := by
    intro a h1
    exact hdetne a (by rw [hdet a, h1, mul_zero, zero_mul])
  have hmul00 : ∀ a b : A, Mhm (a * b) 0 0 = Mhm a 0 0 * Mhm b 0 0 := by
    intro a b
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three,
      htri b 1 0 (by decide), htri b 2 0 (by decide)]
    ring
  have hmul11 : ∀ a b : A, Mhm (a * b) 1 1 = Mhm a 1 1 * Mhm b 1 1 := by
    intro a b
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three,
      htri a 1 0 (by decide), htri b 2 1 (by decide)]
    ring
  let m00 : A →* Kˣ :=
    { toFun := fun a => Units.mk0 (Mhm a 0 0) (h00 a)
      map_one' := Units.ext (by rw [Units.val_mk0, map_one]; rfl)
      map_mul' := by intro a b; apply Units.ext; exact hmul00 a b }
  let m11 : A →* Kˣ :=
    { toFun := fun a => Units.mk0 (Mhm a 1 1) (h11 a)
      map_one' := Units.ext (by rw [Units.val_mk0, map_one]; rfl)
      map_mul' := by intro a b; apply Units.ext; exact hmul11 a b }
  let g : A →* Kˣ := m11 * m00⁻¹
  have hg_cube : ∀ a : A, g a ^ 3 = 1 := by
    intro a
    have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 (a : GL (Fin 5) K) a.2)
    have h0 : m00 a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have h1 : m11 a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    change (m11 a * (m00 a)⁻¹) ^ 3 = 1
    rw [mul_pow, inv_pow, h0, h1, inv_one, mul_one]
  have hker_le : ∀ a : A, g a = 1 → (a : GL (Fin 5) K) ∈ Subgroup.zpowers d := by
    intro a hga
    obtain ⟨c₀, hc₀e, hc₀ne⟩ := hAe_line a
    have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 (a : GL (Fin 5) K) a.2)
    have hc₀3 : c₀ ^ 3 = 1 := by
      have h1 : ((ρ a) ^ 3) e = c₀ ^ 3 • e := by
        rw [show (ρ a : Module.End K (Fin 5 → K)) ^ 3 = ρ a * ρ a * ρ a by
          rw [pow_succ, pow_two]]
        simp only [Module.End.mul_apply, hc₀e, map_smul, smul_smul]
        rw [show c₀ * (c₀ * c₀) = c₀ ^ 3 by ring]
      have h2 : (ρ (a ^ 3)) e = c₀ ^ 3 • e := by rw [map_pow]; exact h1
      rw [ha3, map_one, Module.End.one_apply] at h2
      have : (c₀ ^ 3 - 1) • e = 0 := by rw [sub_smul, one_smul, h2.symm, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h he0
    have hσc₀ : F.σ c₀ = c₀⁻¹ := by
      have hσ : F.σ c₀ = c₀ ^ (2 ^ f) := by
        dsimp only [F]
        exact CFSG.LieType.BorelTits.unitaryInvolution_apply K 2 f c₀
      rw [hσ, pow_two_pow_eq_sq_of_cube hc₀3 (mod_three_eq_two_of_dvd_add_one hq3')]
      have : c₀ * c₀ ^ 2 = 1 := by rw [mul_comm, ← pow_succ, hc₀3]
      exact eq_inv_of_mul_eq_one_right this
    have hβe : ∀ x : Eα, F.β e (ρ a (x : Fin 5 → K)) = c₀ * F.β e (x : Fin 5 → K) := by
      intro x
      have hiso := hρiso a e (x : Fin 5 → K)
      rw [hc₀e, F.smul_left, hσc₀] at hiso
      have := congrArg (fun t : K => c₀ * t) hiso
      rwa [← mul_assoc, mul_inv_cancel₀ hc₀ne, one_mul] at this
    have hc₀_eq : c₀ = Mhm a 0 0 := by
      have hb0_scalar : rEα a (b 0) = c₀ • b 0 := by
        apply Subtype.ext
        change ρ a ((b 0 : Eα) : Fin 5 → K) = c₀ • ((b 0 : Eα) : Fin 5 → K)
        rw [hb0]
        exact hc₀e
      have h := congrArg (fun u : Eα => b.repr u 0) hb0_scalar
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one] at h
      rw [← LinearMap.toMatrix_apply b b (rEα a) 0 0] at h
      exact h.symm
    have h22 : Mhm a 2 2 = Mhm a 0 0 := by
      have hy : (((rEα a (b 2) - c₀ • b 2 : Eα)) : Fin 5 → K) ∈ E := by
        refine ⟨(rEα a (b 2) - c₀ • b 2).2, ?_⟩
        have hL : L = K ∙ e := rfl
        rw [hL]
        refine (F.mem_perp_span_singleton (u := e)
          (v := ((rEα a (b 2) - c₀ • b 2 : Eα) : Fin 5 → K))).mpr ?_
        change F.β e (ρ a ((b 2 : Eα) : Fin 5 → K) - c₀ • ((b 2 : Eα) : Fin 5 → K)) = 0
        rw [F.β_sub_right, F.smul_right, hβe (b 2), sub_self]
      have hrepr : b.repr (rEα a (b 2) - c₀ • b 2) =
          b.repr (rEα a (b 2)) - c₀ • b.repr (b 2) := by
        rw [map_sub, map_smul]
      have h0 := hrepr2 (rEα a (b 2) - c₀ • b 2) hy
      rw [hrepr, Module.Basis.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
        smul_eq_mul, Finsupp.single_eq_same, mul_one] at h0
      have hX : b.repr (rEα a (b 2)) 2 = Mhm a 2 2 :=
        (LinearMap.toMatrix_apply b b (rEα a) 2 2).symm
      rw [hX, sub_eq_zero] at h0
      rw [h0, hc₀_eq]
    have h11 : Mhm a 1 1 = Mhm a 0 0 := by
      have h := congrArg (fun u : Kˣ => (u : K)) hga
      have h2 : (m11 a : K) * (m00 a : K)⁻¹ = 1 := by
        simpa [g, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
          Units.val_inv_eq_inv_val] using h
      have hm11 : (m11 a : K) = Mhm a 1 1 := rfl
      have hm00 : (m00 a : K) = Mhm a 0 0 := rfl
      rw [hm11, hm00] at h2
      have h3 := congrArg (fun x : K => x * Mhm a 0 0) h2
      rwa [mul_assoc, inv_mul_cancel₀ (h00 a), mul_one, one_mul] at h3
    have hM3 : Mhm a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have hrE : rEα a = (Mhm a 0 0) • 1 := by
      have hMscalar : Mhm a = (Mhm a 0 0) • 1 :=
        matrix_eq_smul_one_of_cube_eq_one (Mhm a) hM3 h11 h22 (htri a) (h00 a)
      apply (LinearMap.toMatrix b b).injective
      rw [map_smul, LinearMap.toMatrix_one]
      exact hMscalar
    refine hker (a : GL (Fin 5) K) a.2 ⟨Mhm a 0 0, ?_⟩
    intro v hv
    have h := congrArg (fun f : Module.End K Eα => f ⟨v, hv⟩) hrE
    have h2 := congrArg (fun x : Eα => (x : Fin 5 → K)) h
    have hL : ((rEα a ⟨v, hv⟩ : Eα) : Fin 5 → K) =
        ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v := by
      change Matrix.toLin' ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) v =
        ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v
      exact Matrix.toLin'_apply _ _
    rw [hL] at h2
    simpa using h2
  have hd3 : d ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hd3M, Units.val_one]
  have hker3 : Nat.card g.ker ≤ 3 := by
    have hinj : Function.Injective
        (fun x : g.ker =>
          (⟨((x : A) : GL (Fin 5) K), hker_le (x : A) x.2⟩ : Subgroup.zpowers d)) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Subgroup.zpowers d => (z : GL (Fin 5) K)) hxy
    have h1 : Nat.card g.ker ≤ Nat.card (Subgroup.zpowers d) :=
      Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card (Subgroup.zpowers d) = orderOf d := Nat.card_zpowers d
    have h3 : orderOf d ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
    omega
  have hrange3 : Nat.card g.range ≤ 3 := by
    haveI : IsCyclic Kˣ := instIsCyclicUnitsOfFinite
    haveI : IsCyclic g.range := Subgroup.isCyclic g.range
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := g.range)
    have hγ3 : γ ^ 3 = 1 := by
      obtain ⟨a, ha⟩ := γ.2
      have h : (γ : Kˣ) ^ 3 = 1 := by
        rw [show (γ : Kˣ) = g a from ha.symm]
        exact hg_cube a
      exact Subtype.ext h
    have hdvd : Nat.card g.range ∣ 3 := by
      rw [← hγ]
      exact orderOf_dvd_of_pow_eq_one hγ3
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hcard := Subgroup.card_ker_mul_card_range g
  have hle : Nat.card A ≤ 9 := by
    rw [← hcard]
    calc Nat.card g.ker * Nat.card g.range ≤ 3 * 3 := Nat.mul_le_mul hker3 hrange3
      _ = 9 := by norm_num
  have h27 : Nat.card A = 27 := by rw [hAc]; norm_num
  omega

end CFSG.StandardType.TablePThreeKG

end
