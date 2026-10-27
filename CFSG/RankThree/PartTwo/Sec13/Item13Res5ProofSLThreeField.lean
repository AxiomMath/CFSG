module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.Sec4.LThreePiFixed
import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix

namespace Res5Proof

theorem three_dvd_of_pow_mul_pow_eq_one {G : Type*} [Group G] {a b : G} (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hb : b ∉ Subgroup.zpowers a) {i j : ℕ}
    (h : a ^ i * b ^ j = 1) : 3 ∣ i ∧ 3 ∣ j := by
  have hbj : b ^ j = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hmem : b ^ j ∈ Subgroup.zpowers a := hbj ▸ inv_mem (pow_mem (Subgroup.mem_zpowers a) i)
  have hj : 3 ∣ j := by
    have hbj' : b ^ j = b ^ (j % 3) := by
      conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hb3, one_pow, one_mul]
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
    · exact Nat.dvd_of_mod_eq_zero h0
    · rw [hbj', h1, pow_one] at hmem
      exact absurd hmem hb
    · rw [hbj', h2] at hmem
      exfalso
      apply hb
      have : b = (b ^ 2) ^ 2 := by
        rw [← pow_mul]
        calc b = b ^ 3 * b := by rw [hb3, one_mul]
          _ = b ^ (2 * 2) := by rw [← pow_succ]
      rw [this]
      exact pow_mem hmem 2
  refine ⟨?_, hj⟩
  obtain ⟨k, rfl⟩ := hj
  rw [pow_mul, hb3, one_pow, mul_one] at h
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one h

section Model

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem semiActIn_mul (hK : PiField π p f K) {ζ ζ' : MulAut (slPi π 3 (p ^ f) K)}
    {τ τ' : K ≃+* K} (h : ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct ζ τ g)
    (h' : ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct ζ' τ' g) :
    ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct (ζ * ζ') (τ * τ') g := by
  obtain ⟨g, hg, hζ⟩ := h
  obtain ⟨g', hg', hζ'⟩ := h'
  exact ⟨g * frobGL τ g', mul_mem hg (frobGL_mem_glPi hK τ hg'), hζ.mul hζ'⟩

theorem semiActIn_pow (hK : PiField π p f K) {ζ : MulAut (slPi π 3 (p ^ f) K)} {τ : K ≃+* K}
    (h : ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct ζ τ g) (k : ℕ) :
    ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct (ζ ^ k) (τ ^ k) g := by
  induction k with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero]; exact KFacts.semiAct_one⟩
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact semiActIn_mul hK ih h

theorem semiAct_one_pow {ζ : MulAut (slPi π 3 (p ^ f) K)} {g : GL (Fin 3) K}
    (h : KFacts.SemiAct ζ 1 g) (k : ℕ) : KFacts.SemiAct (ζ ^ k) 1 (g ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact KFacts.semiAct_one
  | succ k ih =>
    have := ih.mul h
    rw [KFacts.frobGL_one_apply, one_mul, ← pow_succ, ← pow_succ] at this
    exact this

theorem semiActIn_of_pow_three (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    {ζ : MulAut (slPi π 3 (p ^ f) K)} (hζ : ζ ^ 3 = 1) :
    (∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct ζ 1 g) ∨
      ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct ζ σ g := by
  rcases KFacts.exists_conj_or_field_of_pow_three_eq_one hK hq2 hζ with h | ⟨σ, hσ, H, hH, hζH⟩
  · exact Or.inl h
  · exact Or.inr ⟨σ, hσ, H * frobGL σ H⁻¹, mul_mem hH (frobGL_mem_glPi hK σ (inv_mem hH)),
      KFacts.semiAct_of_conj_frob hζH⟩

theorem mem_range_conj_of_det (hK : PiField π p f K) {ζ : MulAut (slPi π 3 (p ^ f) K)}
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) (hζ : KFacts.SemiAct ζ 1 g) {μ : Kˣ}
    (hμ : μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K)
    (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = (μ : K) ^ 3) :
    ζ ∈ (MulAut.conj : slPi π 3 (p ^ f) K →* MulAut (slPi π 3 (p ^ f) K)).range := by
  obtain ⟨l, hl, -, hlm⟩ := exists_inner_of_det_eq_cube hK hg ((scalar_mem_glPi_iff hK μ).mpr hμ)
    hdet
  refine ⟨⟨l, hl⟩, MulEquiv.ext fun s => Subtype.ext ?_⟩
  rw [KFacts.semiAct_one_iff] at hζ
  rw [hζ s, hlm]
  rfl

theorem false_of_conj_pair (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {β₁ β₂ : MulAut (slPi π 3 (p ^ f) K)} {g₁ g₂ : GL (Fin 3) K}
    (hg₁ : g₁ ∈ glPi π 3 (p ^ f) K) (hg₂ : g₂ ∈ glPi π 3 (p ^ f) K)
    (h₁ : KFacts.SemiAct β₁ 1 g₁) (h₂ : KFacts.SemiAct β₂ 1 g₂)
    (hI : ∀ a b : ℕ, β₁ ^ a * β₂ ^ b ∈
      (MulAut.conj : slPi π 3 (p ^ f) K →* MulAut (slPi π 3 (p ^ f) K)).range →
        3 ∣ a ∧ 3 ∣ b) : False := by
  have := hK.finite
  have hN0 : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hK hq
  have : NeZero (qSubPi π (p ^ f)) := ⟨hN0⟩
  have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := rootsOfUnity (qSubPi π (p ^ f)) K)
  have hfin : IsOfFinOrder ω := isOfFinOrder_of_finite ω
  obtain ⟨m₁, hm₁⟩ : ∃ m : ℕ, ω ^ m = ⟨_, det_mem_rootsOfUnity hK hg₁⟩ :=
    (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr (hω _))
  obtain ⟨m₂, hm₂⟩ : ∃ m : ℕ, ω ^ m = ⟨_, det_mem_rootsOfUnity hK hg₂⟩ :=
    (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr (hω _))
  obtain ⟨a, b, hab, hM⟩ : ∃ a b : ℕ, ¬ (3 ∣ a ∧ 3 ∣ b) ∧ 3 ∣ a * m₁ + b * m₂ := by
    have h1 := Nat.mod_lt m₁ (show 3 > 0 by norm_num)
    have h2 := Nat.mod_lt m₂ (show 3 > 0 by norm_num)
    interval_cases hm1 : m₁ % 3 <;> interval_cases hm2 : m₂ % 3
    · exact ⟨1, 0, by omega, by omega⟩
    · exact ⟨1, 0, by omega, by omega⟩
    · exact ⟨1, 0, by omega, by omega⟩
    · exact ⟨0, 1, by omega, by omega⟩
    · exact ⟨1, 2, by omega, by omega⟩
    · exact ⟨1, 1, by omega, by omega⟩
    · exact ⟨0, 1, by omega, by omega⟩
    · exact ⟨1, 1, by omega, by omega⟩
    · exact ⟨1, 2, by omega, by omega⟩
  set μ : rootsOfUnity (qSubPi π (p ^ f)) K := ω ^ ((a * m₁ + b * m₂) / 3) with hμ
  have hμ3 : μ ^ 3 = (⟨_, det_mem_rootsOfUnity hK hg₁⟩ : rootsOfUnity (qSubPi π (p ^ f)) K) ^ a *
      (⟨_, det_mem_rootsOfUnity hK hg₂⟩ : rootsOfUnity (qSubPi π (p ^ f)) K) ^ b := by
    rw [hμ, ← pow_mul, Nat.div_mul_cancel hM, pow_add, ← hm₁, ← hm₂, ← pow_mul, ← pow_mul,
      mul_comm a, mul_comm b]
  have hdet : ((g₁ ^ a * g₂ ^ b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (((μ : Kˣ) : K)) ^ 3 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_pow, map_pow]
    have h := congrArg (fun x : rootsOfUnity (qSubPi π (p ^ f)) K => ((x : Kˣ) : K)) hμ3
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Units.val_pow_eq_pow_val, Units.val_mul]
      at h
    rw [h]
    rfl
  have hs := (semiAct_one_pow h₁ a).mul (semiAct_one_pow h₂ b)
  rw [KFacts.frobGL_one_apply, one_mul] at hs
  exact hab (hI a b (mem_range_conj_of_det hK (mul_mem (pow_mem hg₁ a) (pow_mem hg₂ b)) hs
    μ.2 hdet))

theorem three_dvd_of_orderOf (hK : PiField π p f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    3 ∣ f := by
  have := hK.finite
  obtain ⟨n, hn, hnf⟩ : ∃ n : ℕ, Nat.card K = p ^ n ∧ n ∣ 2 * f ∧ (π = true → n = f) := by
    cases π
    · refine ⟨2 * f, ?_, dvd_rfl, fun h => absurd h (by decide)⟩
      rw [hK.card]
      change (p ^ f) ^ 2 = p ^ (2 * f)
      ring
    · exact ⟨f, hK.card, Dvd.intro_left 2 rfl, fun _ => rfl⟩
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hK.prime K hn).1
  have h3 : 3 ∣ n := by
    rw [← hσ, ← hcard]
    exact orderOf_dvd_natCard σ
  cases π
  · have : 3 ∣ 2 * f := h3.trans hnf.1
    omega
  · rw [hnf.2 rfl] at h3
    exact h3

theorem eq_or_eq_sq_of_orderOf {φ σ : K ≃+* K} [Finite K] (hφ3 : orderOf φ = 3)
    (hσ : orderOf σ = 3) : σ = φ ∨ σ = φ ^ 2 := by
  obtain ⟨i, hi⟩ := KFacts.exists_pow_mul_eq_one_of_orderOf_eq_three hφ3 hσ
  have hσi : σ = φ ^ (2 * i) := by
    rw [eq_inv_of_mul_eq_one_right hi, inv_eq_iff_mul_eq_one, ← pow_add,
      show i + 2 * i = 3 * i by ring, pow_mul, ← hφ3, pow_orderOf_eq_one, one_pow]
  rw [← pow_mod_orderOf, hφ3] at hσi
  rcases (by omega : 2 * i % 3 = 0 ∨ 2 * i % 3 = 1 ∨ 2 * i % 3 = 2) with h | h | h
  · rw [h, pow_zero] at hσi
    rw [hσi, orderOf_one] at hσ
    norm_num at hσ
  · rw [h, pow_one] at hσi
    exact Or.inl hσi
  · rw [h] at hσi
    exact Or.inr hσi

theorem mem_range_conj_of_commute_field (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {β γ : MulAut (slPi π 3 (p ^ f) K)} (hβ3 : β ^ 3 = 1)
    {g₁ : GL (Fin 3) K} (hg₁ : g₁ ∈ glPi π 3 (p ^ f) K) (hβ : KFacts.SemiAct β φ g₁)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) (hγ : KFacts.SemiAct γ 1 g)
    (hcomm : β * γ = γ * β) :
    γ ∈ (MulAut.conj : slPi π 3 (p ^ f) K →* MulAut (slPi π 3 (p ^ f) K)).range := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  rw [KFacts.semiAct_one_iff] at hγ
  set σM : GL (Fin 3) K →* GL (Fin 3) K := (MulAut.conj g₁).toMonoidHom.comp (frobGL φ)
    with hσMdef
  have hσM : ∀ A, σM A = g₁ * frobGL φ A * g₁⁻¹ := fun A => rfl
  have hβσ : ∀ s : slPi π 3 (p ^ f) K, ((β s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      σM s := fun s => by rw [hβ s, hσM]
  have hσ3L : ∀ A ∈ slPi π 3 (p ^ f) K, σM (σM (σM A)) = A := by
    intro A hA
    have h := congrArg (fun α : MulAut (slPi π 3 (p ^ f) K) =>
      ((α ⟨A, hA⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hβ3
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
    rwa [hβσ, hβσ, hβσ] at h
  set c : GL (Fin 3) K := g₁ * frobGL φ g₁ * frobGL φ (frobGL φ g₁) with hcdef
  have hσ3c : ∀ A, σM (σM (σM A)) = c * A * c⁻¹ := by
    intro A
    rw [hσM, hσM, hσM, hcdef]
    simp only [map_mul, map_inv, frobGL_three hφ3]
    group
  have hcS : c ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
    have h := hσ3L x hx
    rw [hσ3c] at h
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [h]
  have hσ3 : ∀ A, σM (σM (σM A)) = A := by
    intro A
    rw [hσ3c]
    obtain ⟨u, hu⟩ := hcS
    rw [← hu, ← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq, mul_inv_cancel_right]
  have hφL : ∀ t ∈ slPi π 3 (p ^ f) K, ∃ u ∈ slPi π 3 (p ^ f) K, frobGL φ u = t := by
    intro t ht
    exact ⟨frobGL φ (frobGL φ t), frobGL_mem_slPi hK φ (frobGL_mem_slPi hK φ ht),
      frobGL_three hφ3 t⟩
  set M : GL (Fin 3) K := (g₁ * frobGL φ g)⁻¹ * (g * g₁) with hMdef
  have hMcomm : ∀ x ∈ slPi π 3 (p ^ f) K, M * x = x * M := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hφL x hx
    have h := congrArg (fun α : MulAut (slPi π 3 (p ^ f) K) =>
      ((α ⟨u, hu⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hcomm
    simp only [MulAut.mul_apply] at h
    rw [hβσ, hγ, hγ, hβσ, hσM, hσM] at h
    change g₁ * frobGL φ (g * u * g⁻¹) * g₁⁻¹ = g * (g₁ * frobGL φ u * g₁⁻¹) * g⁻¹ at h
    rw [map_mul, map_mul, map_inv] at h
    rw [hMdef]
    calc (g₁ * frobGL φ g)⁻¹ * (g * g₁) * frobGL φ u =
        (g₁ * frobGL φ g)⁻¹ * (g * (g₁ * frobGL φ u * g₁⁻¹) * g⁻¹) * (g * g₁) := by group
      _ = (g₁ * frobGL φ g)⁻¹ * (g₁ * (frobGL φ g * frobGL φ u * (frobGL φ g)⁻¹) * g₁⁻¹) *
          (g * g₁) := by rw [← h]
      _ = frobGL φ u * ((g₁ * frobGL φ g)⁻¹ * (g * g₁)) := by group
  have hMH : M ∈ glPi π 3 (p ^ f) K :=
    mul_mem (inv_mem (mul_mem hg₁ (frobGL_mem_glPi hK φ hg))) (mul_mem hg hg₁)
  obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_commute hπ hq' hτ hτ1 hMcomm
  have hℓT : ℓ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    rw [← scalar_mem_glPi_iff hK, hℓ]
    exact hMH
  have hgg : g * g₁ = g₁ * frobGL φ g * GeneralLinearGroup.scalar (Fin 3) ℓ := by
    rw [hℓ, hMdef]
    group
  have hσs : ∀ ν : Kˣ, σM (GeneralLinearGroup.scalar (Fin 3) ν) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : K →* K) ν) := by
    intro ν
    rw [hσM, frobGL_scalar, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ g₁).eq,
      mul_inv_cancel_right]
  have hσg : σM g = g * GeneralLinearGroup.scalar (Fin 3) ℓ⁻¹ := by
    rw [hσM]
    calc g₁ * frobGL φ g * g₁⁻¹ =
        (g₁ * frobGL φ g * GeneralLinearGroup.scalar (Fin 3) ℓ) *
          (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ * g₁⁻¹ := by group
      _ = g * g₁ * (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ * g₁⁻¹ := by rw [← hgg]
      _ = g * (g₁ * GeneralLinearGroup.scalar (Fin 3) ℓ⁻¹) * g₁⁻¹ := by rw [map_inv]; group
      _ = g * (GeneralLinearGroup.scalar (Fin 3) ℓ⁻¹ * g₁) * g₁⁻¹ := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ⁻¹ g₁).eq]
      _ = g * GeneralLinearGroup.scalar (Fin 3) ℓ⁻¹ := by group
  have hN : ((ℓ⁻¹ : Kˣ) : K) * φ ((ℓ⁻¹ : Kˣ) : K) * φ (φ ((ℓ⁻¹ : Kˣ) : K)) = 1 := by
    have h := hσ3 g
    have e1 : σM (σM g) = g * GeneralLinearGroup.scalar (Fin 3) ℓ⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : K →* K) ℓ⁻¹) := by
      rw [hσg, map_mul, hσg, hσs]
    have e2 : σM (σM (σM g)) = g * (GeneralLinearGroup.scalar (Fin 3) ℓ⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : K →* K) ℓ⁻¹) *
        GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : K →* K)
          (Units.map (φ : K →* K) ℓ⁻¹))) := by
      rw [e1, map_mul, map_mul, hσg, hσs, hσs]
      group
    rw [e2] at h
    have h' := mul_eq_left.mp h
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h'
    simp only [Units.val_mul, ← map_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq, Units.coe_map,
      MonoidHom.coe_ofClass] at h2
    exact h2
  obtain ⟨μ, hμT, hμ⟩ := exists_frob_mul_eq hK hq hf hφ hφ3 (Or.inl rfl) (inv_mem hℓT) hN
  have hgμ : σM (g * GeneralLinearGroup.scalar (Fin 3) μ) =
      g * GeneralLinearGroup.scalar (Fin 3) μ := by
    rw [map_mul, hσg, hσs, mul_assoc, ← map_mul]
    congr 2
    apply Units.ext
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, mul_comm]
    exact hμ
  have hgμH : g * GeneralLinearGroup.scalar (Fin 3) μ ∈ glPi π 3 (p ^ f) K :=
    mul_mem hg ((scalar_mem_glPi_iff hK μ).mpr hμT)
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  have : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨K₀, _, hK₀⟩ : ∃ (K₀ : Type) (_ : Field K₀), PiField π p f₀ K₀ := by
    cases π
    · refine ⟨GaloisField p (2 * f₀), inferInstance, ⟨hK.prime, hf₀, ?_⟩⟩
      rw [GaloisField.card p (2 * f₀) (by omega)]
      change p ^ (2 * f₀) = (p ^ f₀) ^ 2
      ring
    · exact ⟨GaloisField p f₀, inferInstance, ⟨hK.prime, hf₀, GaloisField.card p f₀ (by omega)⟩⟩
  have hσform : ∀ A : GL (Fin 3) K, (σM A : Matrix (Fin 3) (Fin 3) K) =
      g₁ * (A : Matrix (Fin 3) (Fin 3) K).map (· ^ piCard π (p ^ f₀)) *
        (g₁⁻¹ : GL (Fin 3) K) := by
    intro A
    rw [hσM, Units.val_mul, Units.val_mul, coe_frobGL]
    congr 2
    ext i k
    exact hφ _
  obtain ⟨-, hinner, -⟩ := rank3II_4_10_four hK hq hf hg₁ σM hσform
    (fun A _ => hσ3 A) K₀ hK₀
  obtain ⟨l, hl, hlm⟩ := hinner _ (mem_fixedIn.mpr ⟨hgμH, hgμ⟩)
  refine ⟨⟨l, hl⟩, MulEquiv.ext fun s => Subtype.ext ?_⟩
  change l * s * l⁻¹ = ((γ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K)
  rw [hγ s, ← hlm _ s.2]
  have hcμ := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ (s : GL (Fin 3) K)).eq
  calc g * GeneralLinearGroup.scalar (Fin 3) μ * s *
        (g * GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ =
      g * (GeneralLinearGroup.scalar (Fin 3) μ * s) *
        (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * g⁻¹ := by group
    _ = g * (s * GeneralLinearGroup.scalar (Fin 3) μ) *
        (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * g⁻¹ := by rw [hcμ]
    _ = g * s * g⁻¹ := by group

theorem false_of_field (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {B : Subgroup (MulAut (slPi π 3 (p ^ f) K))} (hB3 : ∀ β ∈ B, β ^ 3 = 1)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hI : ∀ β ∈ B, β ∈
      (MulAut.conj : slPi π 3 (p ^ f) K →* MulAut (slPi π 3 (p ^ f) K)).range → β = 1)
    {β₁ β₂ : MulAut (slPi π 3 (p ^ f) K)} (hβ₁B : β₁ ∈ B) (hβ₂B : β₂ ∈ B)
    (hβ₂ : β₂ ∉ Subgroup.zpowers β₁) {σ₁ : K ≃+* K} (hσ₁ : orderOf σ₁ = 3)
    (h₁ : ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct β₁ σ₁ g) : False := by
  have := hK.finite
  obtain ⟨f₀, hf⟩ := three_dvd_of_orderOf hK hσ₁
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hφ3' : φ ^ 3 = 1 := by rw [← hφ3, pow_orderOf_eq_one]
  have hφφ : φ * φ ^ 2 = 1 := by rw [← pow_succ']; exact hφ3'
  have hφφ' : φ ^ 2 * φ = 1 := by rw [← pow_succ]; exact hφ3'
  have hφ4 : (φ ^ 2) ^ 2 = φ := by
    rw [← pow_mul]
    calc φ ^ (2 * 2) = φ ^ 3 * φ := by rw [← pow_succ]
      _ = φ := by rw [← hφ3, pow_orderOf_eq_one, one_mul]
  obtain ⟨β₁', hβ₁'B, hz, h₁'⟩ : ∃ β ∈ B, Subgroup.zpowers β = Subgroup.zpowers β₁ ∧
      ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct β φ g := by
    rcases eq_or_eq_sq_of_orderOf hφ3 hσ₁ with h | h
    · exact ⟨β₁, hβ₁B, rfl, h ▸ h₁⟩
    · refine ⟨β₁ ^ 2, pow_mem hβ₁B 2, le_antisymm ?_ ?_, ?_⟩
      · exact Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers β₁) 2)
      · rw [Subgroup.zpowers_le]
        have h4 : β₁ ^ 2 * β₁ ^ 2 = β₁ := by
          rw [← pow_add]
          calc β₁ ^ (2 + 2) = β₁ ^ 3 * β₁ := by rw [← pow_succ]
            _ = β₁ := by rw [hB3 β₁ hβ₁B, one_mul]
        have hm : β₁ ^ 2 * β₁ ^ 2 ∈ Subgroup.zpowers (β₁ ^ 2) :=
          mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
        rwa [h4] at hm
      · obtain ⟨g, hg, hg'⟩ := semiActIn_pow hK h₁ 2
        rw [h, hφ4] at hg'
        exact ⟨g, hg, hg'⟩
  have hβ₂' : β₂ ∉ Subgroup.zpowers β₁' := hz ▸ hβ₂
  have hpow : ∀ k : ℕ, β₁' ^ k ∈ Subgroup.zpowers β₁' := fun k =>
    pow_mem (Subgroup.mem_zpowers β₁') k
  obtain ⟨γ, hγB, hγ, g, hg, hγg⟩ : ∃ γ ∈ B, γ ∉ Subgroup.zpowers β₁' ∧
      ∃ g ∈ glPi π 3 (p ^ f) K, KFacts.SemiAct γ 1 g := by
    rcases semiActIn_of_pow_three hK hq2 (hB3 β₂ hβ₂B) with h₂ | ⟨σ₂, hσ₂, h₂⟩
    · exact ⟨β₂, hβ₂B, hβ₂', h₂⟩
    · have hnot : ∀ k : ℕ, β₂ * β₁' ^ k ∉ Subgroup.zpowers β₁' := by
        intro k hmem
        apply hβ₂'
        have : β₂ = β₂ * β₁' ^ k * (β₁' ^ k)⁻¹ := by group
        rw [this]
        exact mul_mem hmem (inv_mem (hpow k))
      rcases eq_or_eq_sq_of_orderOf hφ3 hσ₂ with h | h
      · refine ⟨β₂ * β₁' ^ 2, mul_mem hβ₂B (pow_mem hβ₁'B 2), hnot 2, ?_⟩
        obtain ⟨g', hg', h'⟩ := semiActIn_mul hK h₂ (semiActIn_pow hK h₁' 2)
        rw [h, hφφ] at h'
        exact ⟨g', hg', h'⟩
      · refine ⟨β₂ * β₁', mul_mem hβ₂B hβ₁'B, by simpa using hnot 1, ?_⟩
        obtain ⟨g', hg', h'⟩ := semiActIn_mul hK h₂ h₁'
        rw [h, hφφ'] at h'
        exact ⟨g', hg', h'⟩
  obtain ⟨g₁, hg₁, hβ₁g⟩ := h₁'
  have hγr := mem_range_conj_of_commute_field hK hq hf hφ hφ3 (hB3 _ hβ₁'B) hg₁ hβ₁g hg hγg
    (hBc _ hβ₁'B _ hγB)
  have h1 := hI γ hγB hγr
  exact hγ (h1 ▸ one_mem _)

theorem false_of_inner_trivial (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {B : Subgroup (MulAut (slPi π 3 (p ^ f) K))}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hI : ∀ β ∈ B, β ∈
      (MulAut.conj : slPi π 3 (p ^ f) K →* MulAut (slPi π 3 (p ^ f) K)).range → β = 1) :
    False := by
  have := hK.finite
  have hB3 := hB.2
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
    have := hB.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : B) ⟨b, hb⟩)
  obtain ⟨β₁, hβ₁B, hβ₁1⟩ : ∃ β ∈ B, β ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : B = ⊥ := eq_bot_iff.mpr fun β hβ => h β hβ
    rw [hbot, Subgroup.card_bot] at hB9
    norm_num at hB9
  obtain ⟨β₂, hβ₂B, hβ₂⟩ : ∃ β ∈ B, β ∉ Subgroup.zpowers β₁ := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers β₁ from h)
    rw [hB9, Nat.card_zpowers, orderOf_eq_prime (hB3 β₁ hβ₁B) hβ₁1] at h1
    norm_num at h1
  have hindep : ∀ a b : ℕ, β₁ ^ a * β₂ ^ b ∈
      (MulAut.conj : slPi π 3 (p ^ f) K →* MulAut (slPi π 3 (p ^ f) K)).range →
        3 ∣ a ∧ 3 ∣ b := fun a b hab =>
    three_dvd_of_pow_mul_pow_eq_one (hB3 β₁ hβ₁B) hβ₁1 (hB3 β₂ hβ₂B) hβ₂
      (hI _ (mul_mem (pow_mem hβ₁B a) (pow_mem hβ₂B b)) hab)
  rcases semiActIn_of_pow_three hK hq2 (hB3 β₁ hβ₁B) with ⟨g₁, hg₁, h₁⟩ | ⟨σ₁, hσ₁, h₁⟩
  · rcases semiActIn_of_pow_three hK hq2 (hB3 β₂ hβ₂B) with ⟨g₂, hg₂, h₂⟩ | ⟨σ₂, hσ₂, h₂⟩
    · exact false_of_conj_pair hK hq hg₁ hg₂ h₁ h₂ hindep
    · have hβ₁' : β₁ ∉ Subgroup.zpowers β₂ := by
        intro hmem
        apply hβ₂
        have hβ₂1 : β₂ ≠ 1 := fun h1 => hβ₂ (h1 ▸ one_mem _)
        have hz : Subgroup.zpowers β₁ = Subgroup.zpowers β₂ := by
          refine le_antisymm (Subgroup.zpowers_le.mpr hmem) ?_
          refine le_of_eq_of_le ?_ le_rfl
          rw [eq_comm]
          apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hB3 β₁ hβ₁B) hβ₁1,
            orderOf_eq_prime (hB3 β₂ hβ₂B) hβ₂1]
        rw [hz]
        exact Subgroup.mem_zpowers β₂
      exact false_of_field hK hq hq2 hB3 hBc hI hβ₂B hβ₁B hβ₁' hσ₂ h₂
  · exact false_of_field hK hq hq2 hB3 hBc hI hβ₁B hβ₂B hβ₂ hσ₁ h₁

end Model

end Res5Proof

end CFSG.RankThree.PartTwo.Sec13
