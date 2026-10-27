module

public import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldFour

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

section Matrices

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem inv_mul_mul_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {g s : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hs : s ∈ slPi π 3 (p ^ f) K) :
    g⁻¹ * s * g ∈ slPi π 3 (p ^ f) K := by
  rw [mem_slPi_iff hπ] at hs ⊢
  refine ⟨mul_mem (mul_mem (inv_mem hg) hs.1) hg, ?_⟩
  have h1 : ((g⁻¹ * s * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((g⁻¹ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det *
        (s : Matrix (Fin 3) (Fin 3) K).det := by
    simp only [Units.val_mul, det_mul]
    ring
  rw [h1, hs.2, inv_mul_cancel, Units.val_one, det_one, mul_one]

theorem mul_mul_inv_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {g s : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hs : s ∈ slPi π 3 (p ^ f) K) :
    g * s * g⁻¹ ∈ slPi π 3 (p ^ f) K := by
  have h := inv_mul_mul_mem_slPi hπ (inv_mem hg) hs
  rwa [inv_inv] at h

theorem diagUnits_pow (a b c : Kˣ) (n : ℕ) :
    diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero =>
    apply Units.ext
    rw [pow_zero, pow_zero, pow_zero, pow_zero, Units.val_one, coe_diagUnits, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, pow_succ, pow_succ, pow_succ]

theorem diagUnits_commute (a b c a' b' c' : Kˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem diagUnits_self_eq_scalar (ζ : Kˣ) :
    diagUnits ζ ζ ζ = GeneralLinearGroup.scalar (Fin 3) ζ := by
  apply Units.ext
  rw [coe_diagUnits, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem det_diagUnits (a b c : Kˣ) :
    ((diagUnits a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (a : K) * b * c := by
  rw [coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  rfl

theorem diagUnits_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (a b c : Kˣ) :
    diagUnits a b c * diagTau hτ = diagTau hτ * diagUnits a b c := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  rw [diagTau_eq_diagUnits hτ hτ0, diagUnits_commute]

theorem exists_diagUnits_of_commute (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {D : GL (Fin 3) K} (hD : D ∈ glPi π 3 (p ^ f) K)
    (hc : D * diagTau hτ = diagTau hτ * D) :
    ∃ a b c : Kˣ, a ∈ rootsOfUnity (qSubPi π (p ^ f)) K ∧
      b ∈ rootsOfUnity (qSubPi π (p ^ f)) K ∧ c ∈ rootsOfUnity (qSubPi π (p ^ f)) K ∧
      D = diagUnits a b c := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set l := GeneralLinearGroup.det D with hl
  have hlμ : l ∈ rootsOfUnity (qSubPi π (p ^ f)) K := det_mem_rootsOfUnity hK hD
  have h1μ : (1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := one_mem _
  set D₁ := D * diagUnits l⁻¹ 1 1 with hD₁
  have hD₁H : D₁ ∈ glPi π 3 (p ^ f) K :=
    mul_mem hD (diagUnits_mem_glPi hK (inv_mem hlμ) h1μ h1μ)
  have hD₁det : (D₁ : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hD₁, Units.val_mul, det_mul, det_diagUnits]
    have : (D : Matrix (Fin 3) (Fin 3) K).det = (l : K) := by
      rw [hl, GeneralLinearGroup.val_det_apply]
    rw [this, Units.val_one, mul_one, mul_one, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ l.ne_zero]
  have hD₁L : D₁ ∈ slPi π 3 (p ^ f) K := (mem_slPi_iff hπ).mpr ⟨hD₁H, hD₁det⟩
  have hD₁C : D₁ ∈ Subgroup.centralizer {diagTau hτ} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hD₁, mul_assoc, diagUnits_commute_diagTau hτ, ← mul_assoc, hc, mul_assoc]
  have hmem : D₁ ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} := ⟨hD₁L, hD₁C⟩
  rw [centralizer_diagTau_eq hK hq hτ hτ1] at hmem
  obtain ⟨⟨a, b⟩, hab⟩ := hmem
  simp only [MonoidHom.comp_apply, MonoidHom.coe_prodMap, Prod.map, Subgroup.coe_subtype] at hab
  refine ⟨(a : Kˣ) * l, b, ((a : Kˣ) * b)⁻¹, mul_mem a.2 hlμ, b.2, inv_mem (mul_mem a.2 b.2), ?_⟩
  have hD : D = D₁ * diagUnits l 1 1 := by
    rw [hD₁, mul_assoc, diagUnits_mul, inv_mul_cancel, mul_one]
    have : diagUnits (1 : Kˣ) 1 1 = 1 := by
      have := diagUnits_self_eq_scalar (1 : Kˣ)
      rw [this, map_one]
    rw [this, mul_one]
  rw [hD, ← hab]
  change diagUnits (a : Kˣ) b ((a : Kˣ) * b)⁻¹ * diagUnits l 1 1 = _
  rw [diagUnits_mul, mul_one, mul_one]

theorem exists_slPi_conj_diagTau (hK : PiField π p f K) {τ : K} (hτ : τ ^ 3 = 1)
    {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) :
    ∃ l ∈ slPi π 3 (p ^ f) K, l * diagTau hτ * l⁻¹ = h * diagTau hτ * h⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set δ := GeneralLinearGroup.det h with hδ
  have hδμ : δ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := det_mem_rootsOfUnity hK hh
  have h1μ : (1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := one_mem _
  refine ⟨h * diagUnits δ⁻¹ 1 1, (mem_slPi_iff hπ).mpr
    ⟨mul_mem hh (diagUnits_mem_glPi hK (inv_mem hδμ) h1μ h1μ), ?_⟩, ?_⟩
  · rw [Units.val_mul, det_mul, det_diagUnits]
    have : (h : Matrix (Fin 3) (Fin 3) K).det = (δ : K) := by
      rw [hδ, GeneralLinearGroup.val_det_apply]
    rw [this, Units.val_one, mul_one, mul_one, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ δ.ne_zero]
  · have hc := diagUnits_commute_diagTau hτ δ⁻¹ 1 1
    calc h * diagUnits δ⁻¹ 1 1 * diagTau hτ * (h * diagUnits δ⁻¹ 1 1)⁻¹ =
        h * (diagUnits δ⁻¹ 1 1 * diagTau hτ) * (diagUnits δ⁻¹ 1 1)⁻¹ * h⁻¹ := by group
      _ = h * (diagTau hτ * diagUnits δ⁻¹ 1 1) * (diagUnits δ⁻¹ 1 1)⁻¹ * h⁻¹ := by rw [hc]
      _ = h * diagTau hτ * h⁻¹ := by group

end Matrices

theorem exists_mul_pow_eq_cube {M : Type*} [CommGroup M] [IsCyclic M] {l : M}
    (hl : ∀ m : M, m ^ 3 ≠ l) (t : M) : ∃ k < 3, ∃ ν : M, ν ^ 3 = t * l ^ k := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := M)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hγ l)
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hγ t)
  have hm3 : ¬ (3 : ℤ) ∣ m := by
    rintro ⟨j, rfl⟩
    apply hl (γ ^ j)
    rw [← hm, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
    rfl
  have hk : ∃ k : ℕ, k < 3 ∧ (3 : ℤ) ∣ r + k * m := by
    have hm' : m % 3 = 1 ∨ m % 3 = 2 := by omega
    have hr' : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases hr' with h0 | h1 | h2
    · exact ⟨0, by norm_num, by omega⟩
    · rcases hm' with hm1 | hm2
      · exact ⟨2, by norm_num, by push_cast; omega⟩
      · exact ⟨1, by norm_num, by push_cast; omega⟩
    · rcases hm' with hm1 | hm2
      · exact ⟨1, by norm_num, by push_cast; omega⟩
      · exact ⟨2, by norm_num, by push_cast; omega⟩
  obtain ⟨k, hk3, s, hs⟩ := hk
  refine ⟨k, hk3, γ ^ s, ?_⟩
  rw [← hm, ← hr, ← zpow_natCast (γ ^ m), ← _root_.zpow_mul, ← _root_.zpow_add,
    ← zpow_natCast (γ ^ s), ← _root_.zpow_mul]
  congr 1
  push_cast
  linarith

section CubeRoot

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem det_inv_mul_mul (g y : GL (Fin 3) K) :
    ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (y : Matrix (Fin 3) (Fin 3) K).det := by
  have h1 : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((g⁻¹ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det *
        (y : Matrix (Fin 3) (Fin 3) K).det := by
    simp only [Units.val_mul, det_mul]
    ring
  rw [h1, inv_mul_cancel, Units.val_one, det_one, one_mul]

theorem three_ne_zero_of_tau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : (3 : K) ≠ 0 := by
  intro h3
  apply hτ1
  have h : (τ - 1) ^ 3 = 0 := by linear_combination hτ + (τ - τ ^ 2) * h3
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)

theorem diagTau_not_mem_statedScalars {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    diagTau hτ ∉ StatedScalars (Fin 3) K :=
  CFSG.RankThree.PartTwo.Sec4.diagTau_not_mem_statedScalars hτ hτ1

theorem diagUnits_cube_identity {d₀ d₁ d₂ ξ ζ ν : Kˣ} {k : ℕ} (hk : k < 3)
    (hζ : ζ ^ 3 = 1) (hν : ν ^ 3 = ζ * ξ ^ k) :
    diagUnits (ν * d₀⁻¹ ^ k * ζ⁻¹) (ν * d₁⁻¹ ^ k) (ν * d₂⁻¹ ^ k) ^ 3 *
        (diagUnits d₀ d₁ d₂ ^ 3 * (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹) ^ k =
      GeneralLinearGroup.scalar (Fin 3) ζ := by
  rw [← diagUnits_self_eq_scalar ξ, ← diagUnits_self_eq_scalar ζ]
  have hinv : (diagUnits ξ ξ ξ)⁻¹ = diagUnits ξ⁻¹ ξ⁻¹ ξ⁻¹ := by
    rw [inv_eq_iff_mul_eq_one, diagUnits_mul, mul_inv_cancel, diagUnits_self_eq_scalar, map_one]
  rw [hinv, diagUnits_pow, diagUnits_pow, diagUnits_mul, diagUnits_pow, diagUnits_mul]
  have hν' : (ν : K) ^ 3 = ζ * ξ ^ k := by
    have := congrArg (fun u : Kˣ => (u : K)) hν
    simpa using this
  have hζ' : (ζ : K) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hζ
    simpa using this
  have hξ0 : (ξ : K) ≠ 0 := ξ.ne_zero
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have key : ∀ d : Kˣ, (ν * d⁻¹ ^ k) ^ 3 * (d ^ 3 * ξ⁻¹) ^ k = ζ := by
    intro d
    have hd0 : (d : K) ≠ 0 := d.ne_zero
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    interval_cases k
    · field_simp
      linear_combination hν'
    · field_simp
      linear_combination hν'
    · field_simp
      linear_combination hν'
  have key0 : (ν * d₀⁻¹ ^ k * ζ⁻¹) ^ 3 * (d₀ ^ 3 * ξ⁻¹) ^ k = ζ := by
    have hd0 : (d₀ : K) ≠ 0 := d₀.ne_zero
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    interval_cases k
    · field_simp
      linear_combination hν' - (ζ : K) * hζ'
    · field_simp
      linear_combination hν' - (ζ : K) * (ξ : K) * hζ'
    · field_simp
      linear_combination hν' - (ζ : K) * (ξ : K) ^ 2 * hζ'
  congr 1
  all_goals first | exact key0 | exact key _

theorem sLTwoData_exists_cube_root {X : Type} [Group X] (D : SLTwoData X π p f K) {z : X}
    (hz : z ∈ D.L₀) (hz3 : z ^ 3 = 1) (hzC : z ∉ Subgroup.centralizer (D.L₀ : Set X)) {c₀ : X}
    (hc₀ : c₀ ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X)) :
    ∃ x : X, x * z = z * x ∧ x ^ 3 = c₀ := by
  have hK := D.piField
  have hq := D.modThree
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := three_ne_zero_of_tau hτ hτ1
  set zL : D.L₀ := ⟨z, hz⟩ with hzL
  have hεL : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := (D.e zL).2
  have hzL3 : zL ^ 3 = 1 := Subtype.ext (by simp [hzL, hz3])
  have hε3 : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hzL3, map_one, Subgroup.coe_one]
  have hεZ : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro hεZ
    apply hzC
    have hS := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hεZ
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : D.e ⟨w, hw⟩ * D.e zL = D.e zL * D.e ⟨w, hw⟩ :=
      Subtype.ext (commute_of_mem_statedScalars hS _)
    have h2 : (⟨w, hw⟩ : D.L₀) * zL = zL * ⟨w, hw⟩ :=
      D.e.injective (by rw [map_mul, map_mul, h1])
    exact congrArg Subtype.val h2
  have hε1 : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ≠ 1 :=
    fun h => hεZ (h ▸ one_mem _)
  obtain ⟨g, hgH, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 hεL hεZ (orderOf_eq_prime hε3 hε1)
  set Φ : D.L₀ →* GL (Fin 3) K := (MulAut.conj g⁻¹).toMonoidHom.comp
    ((slPi π 3 (p ^ f) K).subtype.comp D.e.toMonoidHom) with hΦdef
  have hΦ : ∀ w : D.L₀, Φ w = g⁻¹ * (D.e w : GL (Fin 3) K) * g := fun w => by
    simp [hΦdef]
  have hΦinj : Function.Injective Φ := by
    intro w w' h
    rw [hΦ, hΦ] at h
    have h1 : ((D.e w : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = D.e w' := by
      have := congrArg (fun m => g * m * g⁻¹) h
      simpa [mul_assoc] using this
    exact D.e.injective (Subtype.ext h1)
  have hΦL : ∀ w : D.L₀, Φ w ∈ slPi π 3 (p ^ f) K := fun w => by
    rw [hΦ]
    exact inv_mul_mul_mem_slPi hπ hgH (D.e w).2
  have hΦz : Φ zL = diagTau hτ := by rw [hΦ]; exact hgD
  have hΦsurj : ∀ s ∈ slPi π 3 (p ^ f) K, ∃ w : D.L₀, Φ w = s := by
    intro s hs
    refine ⟨D.e.symm ⟨g * s * g⁻¹, mul_mul_inv_mem_slPi hπ hgH hs⟩, ?_⟩
    rw [hΦ, MulEquiv.apply_symm_apply]
    group
  set y' := g⁻¹ * D.y * g with hy'
  have hy'H : y' ∈ glPi π 3 (p ^ f) K := mul_mem (mul_mem (inv_mem hgH) D.y_mem) hgH
  have hact : ∀ w : D.L₀,
      Φ ⟨D.a * w * D.a⁻¹, D.normal.conj_mem w w.2 D.a⟩ = y' * Φ w * y'⁻¹ := by
    intro w
    rw [hΦ, hΦ, D.act w, hy']
    group
  set azL : D.L₀ := ⟨D.a * z * D.a⁻¹, D.normal.conj_mem z hz D.a⟩ with hazL
  have hε' : Φ azL = y' * diagTau hτ * y'⁻¹ := by rw [hazL, hact zL, hΦz]
  have hε'3 : Φ azL ^ 3 = 1 := by rw [hε', conj_pow, diagTau_pow_three hτ, mul_one, mul_inv_cancel]
  have hε'Z : Φ azL ∉ zPi π 3 (p ^ f) K := by
    intro hZ
    apply diagTau_not_mem_statedScalars hτ hτ1
    have hS := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hZ
    have e1 : diagTau hτ = y'⁻¹ * Φ azL * y' := by rw [hε']; group
    rw [e1, mul_assoc, ← commute_of_mem_statedScalars hS y', ← mul_assoc, inv_mul_cancel,
      one_mul]
    exact hS
  have hε'1 : Φ azL ≠ 1 := fun h => hε'Z (h ▸ one_mem _)
  obtain ⟨h, hhH, hhD⟩ := rank3II_4_10_three hK hq hτ hτ1 (hΦL azL) hε'Z
    (orderOf_eq_prime hε'3 hε'1)
  obtain ⟨ℓ₀, hℓ₀L, hℓ₀⟩ := exists_slPi_conj_diagTau hK hτ hhH
  have hℓ₀ε : ℓ₀ * diagTau hτ * ℓ₀⁻¹ = y' * diagTau hτ * y'⁻¹ := by
    rw [hℓ₀, ← hε', ← hhD]
    group
  set D' := ℓ₀⁻¹ * y' with hD'
  have hD'H : D' ∈ glPi π 3 (p ^ f) K := mul_mem (inv_mem (slPi_le_glPi hπ hℓ₀L)) hy'H
  have hD'c : D' * diagTau hτ = diagTau hτ * D' := by
    calc D' * diagTau hτ = ℓ₀⁻¹ * (y' * diagTau hτ * y'⁻¹) * y' := by rw [hD']; group
      _ = ℓ₀⁻¹ * (ℓ₀ * diagTau hτ * ℓ₀⁻¹) * y' := by rw [hℓ₀ε]
      _ = diagTau hτ * D' := by rw [hD']; group
  obtain ⟨d₀, d₁, d₂, hd₀, hd₁, hd₂, hD'eq⟩ :=
    exists_diagUnits_of_commute hK hq hτ hτ1 hD'H hD'c
  obtain ⟨-, hy3Z, hirr⟩ := D.type3
  obtain ⟨ξ, hξμ, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hy3Z
  have hyM : ((D.y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ξ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hξ, coe_scalar_eq_smul]
  have hnc : ∀ μ : K, μ ^ 3 ≠ (ξ : K) :=
    Sec12.KS128NotHJTC.not_cube_of_irreducible hτ hτ1 h3K hyM hirr
  have hdety : ((D.y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = ξ :=
    det_eq_of_cube hnc hyM
  have hy'3 : y' ^ 3 = GeneralLinearGroup.scalar (Fin 3) ξ := by
    rw [hy', show g⁻¹ * D.y * g = g⁻¹ * D.y * g⁻¹⁻¹ by rw [inv_inv], conj_pow, ← hξ, inv_inv,
      mul_assoc, ← commute_of_mem_statedScalars ⟨ξ, rfl⟩ g, ← mul_assoc, inv_mul_cancel, one_mul]
  have hdetD' : d₀ * d₁ * d₂ = ξ := by
    have h1 : (D' : Matrix (Fin 3) (Fin 3) K).det = ξ := by
      rw [hD', Units.val_mul, det_mul, hy', det_inv_mul_mul, hdety,
        ((mem_slPi_iff hπ).mp (inv_mem hℓ₀L)).2, one_mul]
    rw [hD'eq, det_diagUnits] at h1
    exact Units.ext (by simpa using h1)
  set cL : D.L₀ := ⟨c₀, hc₀.1⟩ with hcL
  have hcS : ((D.e cL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs => ?_
    obtain ⟨w, hw⟩ : ∃ w : D.L₀, D.e w = ⟨s, hs⟩ := ⟨D.e.symm ⟨s, hs⟩, by simp⟩
    have hwc : cL * w = w * cL :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hc₀.2 w w.2).symm
    have h1 := congrArg (fun v => ((D.e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hwc
    simp only [map_mul, Subgroup.coe_mul, hw] at h1
    exact h1
  obtain ⟨ζ, hζ⟩ := hcS
  have hζ3 : ζ ^ 3 = 1 := pow_three_eq_one_of_scalar_mem_slPi hπ (hζ ▸ (D.e cL).2)
  have hζμ : ζ ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
    cube_root_mem_qSubPi hq ((mem_rootsOfUnity _ _).mpr hζ3)
  have hΦc : Φ cL = GeneralLinearGroup.scalar (Fin 3) ζ := by
    rw [hΦ, ← hζ, mul_assoc, ← commute_of_mem_statedScalars ⟨ζ, rfl⟩ g, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  have hnc' : ∀ m : rootsOfUnity (qSubPi π (p ^ f)) K, m ^ 3 ≠ ⟨ξ, hξμ⟩ := by
    intro m hm
    apply hnc ((m : Kˣ) : K)
    have := congrArg (fun t : rootsOfUnity (qSubPi π (p ^ f)) K => ((t : Kˣ) : K)) hm
    simpa using this
  obtain ⟨k, hk3, ν, hν⟩ := exists_mul_pow_eq_cube hnc' ⟨ζ, hζμ⟩
  have hνU : (ν : Kˣ) ^ 3 = ζ * ξ ^ k := by
    have := congrArg (fun t : rootsOfUnity (qSubPi π (p ^ f)) K => (t : Kˣ)) hν
    simpa using this
  set s := diagUnits ((ν : Kˣ) * d₀⁻¹ ^ k * ζ⁻¹) ((ν : Kˣ) * d₁⁻¹ ^ k) ((ν : Kˣ) * d₂⁻¹ ^ k)
    with hs
  have hsH : s ∈ glPi π 3 (p ^ f) K :=
    diagUnits_mem_glPi hK (mul_mem (mul_mem ν.2 (pow_mem (inv_mem hd₀) k)) (inv_mem hζμ))
      (mul_mem ν.2 (pow_mem (inv_mem hd₁) k)) (mul_mem ν.2 (pow_mem (inv_mem hd₂) k))
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hs, det_diagUnits]
    have hνK : ((ν : Kˣ) : K) ^ 3 = (ζ : K) * ((d₀ : K) * d₁ * d₂) ^ k := by
      have h1 := congrArg (fun u : Kˣ => (u : K)) hνU
      have h2 := congrArg (fun u : Kˣ => (u : K)) hdetD'
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h1 h2
      rw [h1, ← h2]
    have h0 : (d₀ : K) ≠ 0 := d₀.ne_zero
    have h1 : (d₁ : K) ≠ 0 := d₁.ne_zero
    have h2 : (d₂ : K) ≠ 0 := d₂.ne_zero
    have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    interval_cases k
    · field_simp
      linear_combination hνK
    · field_simp
      linear_combination hνK
    · field_simp
      linear_combination hνK
  have hsL : s ∈ slPi π 3 (p ^ f) K := (mem_slPi_iff hπ).mpr ⟨hsH, hsdet⟩
  obtain ⟨σ, hσ⟩ := hΦsurj s hsL
  obtain ⟨l, hl⟩ := hΦsurj ℓ₀⁻¹ (inv_mem hℓ₀L)
  set g₁ : X := (l : X) * D.a with hg₁
  have hg₁L : ∀ w : D.L₀, g₁ * w * g₁⁻¹ ∈ D.L₀ := fun w => D.normal.conj_mem w w.2 g₁
  have hg₁act : ∀ w : D.L₀, Φ ⟨g₁ * w * g₁⁻¹, hg₁L w⟩ = D' * Φ w * D'⁻¹ := by
    intro w
    have e1 : (⟨g₁ * w * g₁⁻¹, hg₁L w⟩ : D.L₀) =
        l * ⟨D.a * w * D.a⁻¹, D.normal.conj_mem w w.2 D.a⟩ * l⁻¹ :=
      Subtype.ext (by simp only [hg₁, Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e1, map_mul, map_mul, map_inv, hact, hl, hD']
    group
  have hg₁z : g₁ * z = z * g₁ := by
    have h1 := hg₁act zL
    rw [hΦz, hD'c, mul_inv_cancel_right, ← hΦz] at h1
    have h2 : g₁ * z * g₁⁻¹ = z := congrArg Subtype.val (hΦinj h1)
    calc g₁ * z = g₁ * z * g₁⁻¹ * g₁ := by group
      _ = z * g₁ := by rw [h2]
  have hσz : (σ : X) * z = z * σ := by
    have h1 : Φ (σ * zL) = Φ (zL * σ) := by
      rw [map_mul, map_mul, hσ, hΦz, hs, diagUnits_commute_diagTau]
    exact congrArg Subtype.val (hΦinj h1)
  have hD's : D' * s = s * D' := by rw [hD'eq, hs]; exact diagUnits_commute _ _ _ _ _ _
  have hg₁σ : g₁ * σ = σ * g₁ := by
    have h1 := hg₁act σ
    rw [hσ, hD's, mul_inv_cancel_right, ← hσ] at h1
    have h2 : g₁ * σ * g₁⁻¹ = σ := congrArg Subtype.val (hΦinj h1)
    calc g₁ * σ = g₁ * σ * g₁⁻¹ * g₁ := by group
      _ = σ * g₁ := by rw [h2]
  have hl₁ : D.a * (l : X) * D.a⁻¹ ∈ D.L₀ := D.normal.conj_mem l l.2 D.a
  have hl₂ : D.a * (D.a * (l : X) * D.a⁻¹) * D.a⁻¹ ∈ D.L₀ := D.normal.conj_mem _ hl₁ D.a
  have hg₁3 : g₁ ^ 3 = ((l * ⟨D.a * (l : X) * D.a⁻¹, hl₁⟩ *
      ⟨D.a * (D.a * (l : X) * D.a⁻¹) * D.a⁻¹, hl₂⟩ : D.L₀) : X) := by
    have ha3 := D.a_pow
    simp only [Subgroup.coe_mul]
    calc g₁ ^ 3 = (l : X) * (D.a * l * D.a⁻¹) * (D.a * (D.a * l * D.a⁻¹) * D.a⁻¹) * D.a ^ 3 := by
          rw [hg₁]; simp only [pow_three]; group
      _ = _ := by rw [ha3, mul_one]
  have hΦg₁3 : Φ (l * ⟨D.a * (l : X) * D.a⁻¹, hl₁⟩ *
      ⟨D.a * (D.a * (l : X) * D.a⁻¹) * D.a⁻¹, hl₂⟩) =
        D' ^ 3 * (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ := by
    have e1 : Φ ⟨D.a * (l : X) * D.a⁻¹, hl₁⟩ = y' * ℓ₀⁻¹ * y'⁻¹ := by
      rw [hact l, hl]
    have e2 : Φ ⟨D.a * (D.a * (l : X) * D.a⁻¹) * D.a⁻¹, hl₂⟩ =
        y' * (y' * ℓ₀⁻¹ * y'⁻¹) * y'⁻¹ := by
      rw [← e1]
      exact hact ⟨D.a * (l : X) * D.a⁻¹, hl₁⟩
    rw [map_mul, map_mul, hl, e1, e2, ← hy'3, hD']
    simp only [pow_three]
    group
  refine ⟨(σ : X) * g₁ ^ k, ?_, ?_⟩
  · have hk : g₁ ^ k * z = z * g₁ ^ k := (Commute.pow_left hg₁z k).eq
    calc (σ : X) * g₁ ^ k * z = σ * (g₁ ^ k * z) := by group
      _ = σ * (z * g₁ ^ k) := by rw [hk]
      _ = (σ * z) * g₁ ^ k := by group
      _ = z * σ * g₁ ^ k := by rw [hσz]
      _ = z * (σ * g₁ ^ k) := by group
  · have hc : Commute (σ : X) (g₁ ^ k) := (Commute.pow_right (Commute.symm hg₁σ) k)
    rw [hc.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hg₁3]
    have h1 : Φ (σ ^ 3 * (l * ⟨D.a * (l : X) * D.a⁻¹, hl₁⟩ *
        ⟨D.a * (D.a * (l : X) * D.a⁻¹) * D.a⁻¹, hl₂⟩) ^ k) = Φ cL := by
      rw [map_mul, map_pow, map_pow, hσ, hΦg₁3, hΦc, hD'eq, hs]
      exact diagUnits_cube_identity hk3 hζ3 hνU
    have h2 := congrArg Subtype.val (hΦinj h1)
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using h2

end CubeRoot

end CFSG.RankThree.PartTwo.Sec13.Res2Proof
