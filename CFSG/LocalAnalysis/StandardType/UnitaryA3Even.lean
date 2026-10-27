module

public import CFSG.LocalAnalysis.StandardType.UnitaryMatrixBridge
public import CFSG.LocalAnalysis.StandardType.UnitaryRepEven
public import CFSG.LocalAnalysis.StandardType.UnitaryCubeRoots
public import CFSG.LocalAnalysis.StandardType.UnitaryPairs
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders
public import CFSG.LocalAnalysis.StandardType.A8LiftBlocks

public section

namespace CFSG.StandardType

namespace UnitaryA3

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits InnerDiagSU UFusion

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} {G : Type} [Group G]

theorem exists_pair_pow_three_eq_one (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfe : Even f)
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {b : G}
    {A : GL (Fin n) F} (h : (b, A) ∈ suInducedPairs ψ) (hb3 : b ^ 3 = 1) :
    ∃ A' : GL (Fin n) F, (b, A') ∈ suInducedPairs ψ ∧ A' ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := UnitaryPairs.exists_scalar_pow_of_mem_suInducedPairs hF hf hn hnq hker h hb3
  have hmem : ((1 : G), Matrix.GeneralLinearGroup.scalar (Fin n) c) ∈ suInducedPairs ψ := by
    have h' := (suInducedPairs ψ).pow_mem h 3
    simpa only [Prod.pow_mk, hb3, hc, one_pow] using h'
  obtain ⟨hJ, -⟩ := hmem
  have hcN : c ^ (2 ^ f + 1) = 1 :=
    UnitaryPairs.norm_eq_one_of_isJUnitary_scalar (by omega : 1 ≤ n) hJ
  obtain ⟨d, hd3, hdN⟩ := UnitaryPairs.exists_cube_root_norm_one hfe hcN
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin n) d⁻¹ * A, ?_, ?_⟩
  · have hmemd : ((1 : G), Matrix.GeneralLinearGroup.scalar (Fin n) d⁻¹) ∈ suInducedPairs ψ :=
      UnitaryPairs.one_scalar_mem_suInducedPairs ψ (by rw [inv_pow, hdN, inv_one])
    have h' := (suInducedPairs ψ).mul_mem hmemd h
    simpa only [Prod.mk_mul_mk, one_mul] using h'
  · have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin n) d⁻¹) A :=
      Matrix.GeneralLinearGroup.scalar_commute d⁻¹ A
    calc (Matrix.GeneralLinearGroup.scalar (Fin n) d⁻¹ * A) ^ 3
        = (Matrix.GeneralLinearGroup.scalar (Fin n) d⁻¹) ^ 3 * A ^ 3 := hcomm.mul_pow 3
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) ((d⁻¹) ^ 3) *
            Matrix.GeneralLinearGroup.scalar (Fin n) c := by rw [map_pow, hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) ((d⁻¹) ^ 3 * c) :=
            (map_mul (Matrix.GeneralLinearGroup.scalar (Fin n)) ((d⁻¹) ^ 3) c).symm
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by rw [inv_pow, hd3, inv_mul_cancel]
      _ = 1 := map_one _

theorem commute_of_pow_three_eq_one (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfe : Even f)
    (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {b₁ b₂ : G}
    {A₁ A₂ : GL (Fin n) F} (h₁ : (b₁, A₁) ∈ suInducedPairs ψ) (h₂ : (b₂, A₂) ∈ suInducedPairs ψ)
    (hb : b₁ * b₂ = b₂ * b₁) (hA₁ : A₁ ^ 3 = 1) : A₁ * A₂ = A₂ * A₁ := by
  obtain ⟨c, hcdef⟩ :=
    UnitaryPairs.exists_scalar_commutator_of_mem_suInducedPairs hF hf hn hnq hker h₁ h₂ hb
  have hmem : ((1 : G), Matrix.GeneralLinearGroup.scalar (Fin n) c) ∈ suInducedPairs ψ := by
    have h' := (suInducedPairs ψ).mul_mem
      ((suInducedPairs ψ).mul_mem ((suInducedPairs ψ).mul_mem h₁ h₂)
        ((suInducedPairs ψ).inv_mem h₁)) ((suInducedPairs ψ).inv_mem h₂)
    have h1comp : b₁ * b₂ * b₁⁻¹ * b₂⁻¹ = 1 := by
      rw [hb, mul_inv_cancel_right, mul_inv_cancel]
    simpa only [Prod.mk_mul_mk, Prod.inv_mk, h1comp, hcdef] using h'
  obtain ⟨hJ, -⟩ := hmem
  have hcN : c ^ (2 ^ f + 1) = 1 :=
    UnitaryPairs.norm_eq_one_of_isJUnitary_scalar (by omega : 1 ≤ n) hJ
  set z : GL (Fin n) F := Matrix.GeneralLinearGroup.scalar (Fin n) c with hzdef
  have hz : ∀ g : GL (Fin n) F, z * g = g * z := fun g => by
    rw [hzdef]; exact Matrix.GeneralLinearGroup.scalar_commute c g
  have h1 : A₁ * A₂ = z * (A₂ * A₁) := by
    calc A₁ * A₂ = (A₁ * A₂ * A₁⁻¹ * A₂⁻¹) * (A₂ * A₁) := by group
      _ = z * (A₂ * A₁) := by rw [hcdef, hzdef]
  have hzpow : ∀ k : ℕ, A₁ ^ k * A₂ = z ^ k * (A₂ * A₁ ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hAz : A₁ * z ^ k = z ^ k * A₁ :=
        (show Commute A₁ (z ^ k) from (show Commute z A₁ from hz A₁).symm.pow_right k)
      rw [pow_succ', mul_assoc, ih, pow_succ, ← mul_assoc A₁ (z ^ k) (A₂ * A₁ ^ k),
        hAz, mul_assoc, ← mul_assoc A₁ A₂ (A₁ ^ k), h1]
      group
  have hz3 : z ^ 3 = 1 := by
    have h := hzpow 3
    rw [hA₁, mul_one, one_mul] at h
    exact mul_right_cancel (h.symm.trans (one_mul A₂).symm)
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hz3c : (Matrix.GeneralLinearGroup.scalar (Fin n) c) ^ 3 = 1 := by
    simpa only [hzdef] using hz3
  have hc3 : c ^ 3 = 1 := by
    have hsc : Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ 3) =
        Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by
      rw [map_pow, hz3c, map_one]
    exact UnitaryCenter.scalar_injective hsc
  have hcop : Nat.Coprime 3 (2 ^ f + 1) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr
      (UnitaryCenter.not_three_dvd_two_pow_add_one_of_even hfe)
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hc3, hcN⟩
  have hz1 : z = 1 := by rw [hzdef, hc1, map_one]
  rw [hz1, one_mul] at h1
  exact h1

theorem not_scalar_pow_mul_pow [Finite G] {ψ : SU (unitaryInvolution F 2 f) n →* G} {b₁ b₂ : G}
    {A₁ A₂ : GL (Fin n) F} (h₁ : (b₁, A₁) ∈ suInducedPairs ψ) (h₂ : (b₂, A₂) ∈ suInducedPairs ψ)
    (hb : b₁ * b₂ = b₂ * b₁) (hb₁3 : b₁ ^ 3 = 1) (hb₂3 : b₂ ^ 3 = 1)
    (hbasis : ∀ i j : ℕ, ¬ (3 ∣ i ∧ 3 ∣ j) → b₁ ^ i * b₂ ^ j ≠ 1)
    (hcen : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (ψ.range : Set G))) (i j : ℕ)
    (hij : ¬ (3 ∣ i ∧ 3 ∣ j)) :
    ∀ c : Fˣ, A₁ ^ i * A₂ ^ j ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  intro c hc
  have hmem : (b₁ ^ i * b₂ ^ j, A₁ ^ i * A₂ ^ j) ∈ suInducedPairs ψ := by
    have h' := (suInducedPairs ψ).mul_mem ((suInducedPairs ψ).pow_mem h₁ i)
      ((suInducedPairs ψ).pow_mem h₂ j)
    simpa only [Prod.pow_mk, Prod.mk_mul_mk] using h'
  rw [hc] at hmem
  have hcentral := UnitaryPairs.mem_centralizer_of_mem_suInducedPairs_scalar hmem
  have hpow : (b₁ ^ i * b₂ ^ j) ^ 3 = 1 := by
    have hcomm : Commute (b₁ ^ i) (b₂ ^ j) := (show Commute b₁ b₂ from hb).pow_pow i j
    have h1' : (b₁ ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm i 3, pow_mul, hb₁3, one_pow]
    have h2' : (b₂ ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm j 3, pow_mul, hb₂3, one_pow]
    rw [hcomm.mul_pow 3, h1', h2', one_mul]
  exact hcen (UnitaryMatrix.three_dvd_card_centralizer_of_mem hcentral hpow (hbasis i j hij))

theorem eq_one_of_even (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfe : Even f) (hn6 : 6 ≤ n)
    (hn9 : n ≤ 9) [Finite G] {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    {Γ : Subgroup (SU (unitaryInvolution F 2 f) n)} (hperf : commutator ↥Γ = ⊤)
    (h5 : HasOrderFiveData ↥Γ) (h7 : HasOrderSevenData ↥Γ) {b₁ b₂ : G} {A₁ A₂ : GL (Fin n) F}
    (h₁ : (b₁, A₁) ∈ suInducedPairs ψ) (h₂ : (b₂, A₂) ∈ suInducedPairs ψ) (hb : b₁ * b₂ = b₂ * b₁)
    (hb₁3 : b₁ ^ 3 = 1) (hb₂3 : b₂ ^ 3 = 1)
    (hbasis : ∀ i j : ℕ, ¬ (3 ∣ i ∧ 3 ∣ j) → b₁ ^ i * b₂ ^ j ≠ 1)
    (hcen : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (ψ.range : Set G)))
    (hb₁Γ : ∀ γ ∈ Γ, b₁ * ψ γ = ψ γ * b₁) (hb₂Γ : ∀ γ ∈ Γ, b₂ * ψ γ = ψ γ * b₂) (γ : ↥Γ) :
    γ = 1 := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hn3 : 3 ≤ n := by omega
  obtain ⟨A₁', h₁', hA₁'⟩ := exists_pair_pow_three_eq_one hF hf hfe hn3 hnq hker h₁ hb₁3
  obtain ⟨A₂', h₂', hA₂'⟩ := exists_pair_pow_three_eq_one hF hf hfe hn3 hnq hker h₂ hb₂3
  have hcomm : A₁' * A₂' = A₂' * A₁' :=
    commute_of_pow_three_eq_one hF hf hfe hn3 hnq hker h₁' h₂' hb hA₁'
  have hnc := not_scalar_pow_mul_pow h₁' h₂' hb hb₁3 hb₂3 hbasis hcen
  have hc₁ := UnitaryPairs.commute_of_mem_suInducedPairs_of_perfect hker hperf h₁' hb₁Γ
  have hc₂ := UnitaryPairs.commute_of_mem_suInducedPairs_of_perfect hker hperf h₂' hb₂Γ
  obtain ⟨ζ, hζ1, hζ3, hσζ⟩ := UnitaryCubeRoots.exists_cubeRoot_fixed_of_even hF hf hfe
  obtain ⟨hAJ₁, -⟩ := h₁'
  obtain ⟨hAJ₂, -⟩ := h₂'
  refine UnitaryMatrix.eq_one_of_repHom_eq_one _ Γ ?_
  refine UnitaryRep.eq_one_of_commute_even (unitaryInvolution F 2 f) hζ1 hζ3 hσζ h5 h7
    (by simpa using hn9) UnitaryAlg.isUnit_antidiag (UnitaryMatrix.repHom _ n Γ)
    (UnitaryMatrix.repHom_form _ Γ) (A := (A₁' : Matrix (Fin n) (Fin n) F))
    (B := (A₂' : Matrix (Fin n) (Fin n) F)) ?_ ?_ ?_
    (UnitaryMatrix.transpose_form_of_isJUnitary hAJ₁)
    (UnitaryMatrix.transpose_form_of_isJUnitary hAJ₂) ?_ ?_ ?_ γ
  · have h := congrArg Units.val hA₁'
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  · have h := congrArg Units.val hA₂'
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  · have h := congrArg Units.val hcomm
    simpa only [Units.val_mul] using h
  · intro g
    have h := congrArg Units.val (hc₁ g g.2)
    simp only [Units.val_mul] at h
    exact h.symm
  · intro g
    have h := congrArg Units.val (hc₂ g g.2)
    simp only [Units.val_mul] at h
    exact h.symm
  · intro i j hij e
    have h := UnitaryMatrix.coe_ne_smul_one (hnc i j hij) e
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using h

end UnitaryA3

end CFSG.StandardType
