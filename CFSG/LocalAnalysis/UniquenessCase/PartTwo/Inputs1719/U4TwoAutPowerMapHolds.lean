module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TwoAutLie
public import CFSG.Milestones.ASVolI.F431.BCoreU4
public import CFSG.Milestones.ASVolI.F411.aSwL3BField
public import CFSG.Quasithin.H13.A5W1622c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

section U4

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ASVolI (burnsideF4m_U4_fieldAut burnsideF4m_U4_normalForm)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem coe_burnsideF4m_U4_fieldAut (σ : K ≃+* K) (y : hypSU h 2 0) :
    (((burnsideF4m_U4_fieldAut h σ y : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      ((y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map σ :=
  rfl

theorem burnsideF4m_U4_fieldAut_mem_hypBorel (σ : K ≃+* K) {y : hypSU h 2 0}
    (hy : y ∈ hypBorel h 2 0) : burnsideF4m_U4_fieldAut h σ y ∈ hypBorel h 2 0 := by
  rw [mem_hypBorel_iff_blockTriangular h (by norm_num)] at hy ⊢
  rw [coe_burnsideF4m_U4_fieldAut]
  intro i j hij
  rw [Matrix.map_apply, hy hij, map_zero]

theorem burnsideF4m_U4_fieldAut_mem_hypUnitriangular (σ : K ≃+* K) {y : hypSU h 2 0}
    (hy : y ∈ hypUnitriangular h 2 0) :
    burnsideF4m_U4_fieldAut h σ y ∈ hypUnitriangular h 2 0 := by
  rw [mem_hypUnitriangular] at hy ⊢
  rw [coe_burnsideF4m_U4_fieldAut]
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · rw [Matrix.map_apply, hy.1 hij, map_zero]
  · rw [Matrix.map_apply, hy.2 a, map_one]

theorem hypDiagHom_burnsideF4m_U4_fieldAut (σ : K ≃+* K) {k : ℕ}
    (hk : ∀ x : K, σ x = x ^ 2 ^ k) {y : hypSU h 2 0} (hy : y ∈ hypBorel h 2 0) :
    hypDiagHom h 2 0 (Nat.zero_le 1)
        ⟨burnsideF4m_U4_fieldAut h σ y, burnsideF4m_U4_fieldAut_mem_hypBorel h σ hy⟩ =
      hypDiagHom h 2 0 (Nat.zero_le 1) ⟨y, hy⟩ ^ 2 ^ k := by
  funext i
  apply Units.ext
  rw [Pi.pow_apply, Units.val_pow_eq_pow_val, coe_hypDiagHom, coe_hypDiagHom]
  change ((((burnsideF4m_U4_fieldAut h σ y : hypSU h 2 0) : GL (HypIndex 2 0) K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K)) (.inl i) (.inl i) = _
  rw [coe_burnsideF4m_U4_fieldAut, Matrix.map_apply, hk]

theorem burnsideF4m_U4_conj_fieldAut_pow_inv_mem_hypUnitriangular (σ : K ≃+* K) {k : ℕ}
    (hk : ∀ x : K, σ x = x ^ 2 ^ k) {b y : hypSU h 2 0} (hb : b ∈ hypBorel h 2 0)
    (hy : y ∈ hypBorel h 2 0) :
    b * burnsideF4m_U4_fieldAut h σ y * b⁻¹ * (y ^ 2 ^ k)⁻¹ ∈ hypUnitriangular h 2 0 := by
  let A : hypBorel h 2 0 := ⟨b, hb⟩
  let Y₀ : hypBorel h 2 0 := ⟨y, hy⟩
  let FY : hypBorel h 2 0 :=
    ⟨burnsideF4m_U4_fieldAut h σ y, burnsideF4m_U4_fieldAut_mem_hypBorel h σ hy⟩
  have hdF : hypDiagHom h 2 0 (Nat.zero_le 1) FY =
      hypDiagHom h 2 0 (Nat.zero_le 1) Y₀ ^ 2 ^ k :=
    hypDiagHom_burnsideF4m_U4_fieldAut h σ hk hy
  have hd1 : hypDiagHom h 2 0 (Nat.zero_le 1) (A * FY * A⁻¹ * (Y₀ ^ 2 ^ k)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hdF,
      mul_comm (hypDiagHom h 2 0 (Nat.zero_le 1) A), mul_inv_cancel_right, mul_inv_cancel]
  have hker : A * FY * A⁻¹ * (Y₀ ^ 2 ^ k)⁻¹ ∈
      (hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0) := by
    rw [← ker_hypDiagHom (Nat.zero_le 1)]
    exact hd1
  exact Subgroup.mem_subgroupOf.mp hker

theorem mem_hypBorel_of_burnsideF4m_U4_conj_fieldAut (σ : K ≃+* K) {b : hypSU h 2 0}
    (hb : ∀ u ∈ hypUnitriangular h 2 0,
      b * burnsideF4m_U4_fieldAut h σ u * b⁻¹ ∈ hypUnitriangular h 2 0) :
    b ∈ hypBorel h 2 0 := by
  have : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hBN : normalizer ((hypUnitriangular h 2 0 : Subgroup (hypSU h 2 0)) :
      Set (hypSU h 2 0)) = hypBorel h 2 0 :=
    UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)
  rw [← hBN]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨u, hu, rfl⟩
    have hFu : burnsideF4m_U4_fieldAut h σ (burnsideF4m_U4_fieldAut h σ⁻¹ u) = u := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have h1 := hb _ (burnsideF4m_U4_fieldAut_mem_hypUnitriangular h σ⁻¹ hu)
    rw [hFu] at h1
    exact h1
  · rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]

theorem hypSU_four_powerMap (θ : MulAut (hypSU h 2 0)) {S : Subgroup (hypSU h 2 0)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hθS : S.map θ.toMonoidHom = S) :
    ∃ j : ℕ, ∀ x ∈ normalizer (S : Set (hypSU h 2 0)), θ x * (x ^ 2 ^ j)⁻¹ ∈ S := by
  classical
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.A5.exists_conj_of_isSylowTwoOf_top
    (CFSG.Quasithin.H13.U4Par.isSylowTwoOf_hypUnitriangular h) hS
  obtain ⟨a, σ, hθ⟩ := burnsideF4m_U4_normalForm h θ
  obtain ⟨k, hk⟩ := CFSG.ASVolI.burnsideF411a_ringEquiv_pow (p := 2) σ
  have hmemS : ∀ y, g * y * g⁻¹ ∈ S ↔ y ∈ hypUnitriangular h 2 0 := by
    intro y
    rw [← hg]
    constructor
    · rintro ⟨u, hu, hu'⟩
      have hu'' : g * u * g⁻¹ = g * y * g⁻¹ := hu'
      rw [mul_left_inj, mul_right_inj] at hu''
      rw [← hu'']
      exact hu
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hBN : normalizer ((hypUnitriangular h 2 0 : Subgroup (hypSU h 2 0)) :
      Set (hypSU h 2 0)) = hypBorel h 2 0 :=
    UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)
  set a' := g⁻¹ * a * burnsideF4m_U4_fieldAut h σ g with ha'
  have hθx : ∀ x, θ x = a * burnsideF4m_U4_fieldAut h σ x * a⁻¹ := fun x => by
    rw [hθ]; rfl
  have hconj : ∀ y, θ (g * y * g⁻¹) =
      g * (a' * burnsideF4m_U4_fieldAut h σ y * a'⁻¹) * g⁻¹ := fun y => by
    rw [hθx, map_mul, map_mul, map_inv, ha']
    group
  have ha'B : a' ∈ hypBorel h 2 0 := by
    refine mem_hypBorel_of_burnsideF4m_U4_conj_fieldAut h σ fun u hu => ?_
    have h2 : θ (g * u * g⁻¹) ∈ S := by
      rw [← hθS]
      exact ⟨_, (hmemS u).mpr hu, rfl⟩
    rw [hconj] at h2
    exact (hmemS _).mp h2
  refine ⟨k, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = g * y * g⁻¹ := ⟨g⁻¹ * x * g, by group⟩
  have hyB : y ∈ hypBorel h 2 0 := by
    rw [← hBN, Subgroup.mem_normalizer_iff]
    intro u
    rw [← hmemS u, ← hmemS (y * u * y⁻¹)]
    have h1 := Subgroup.mem_normalizer_iff.mp hx (g * u * g⁻¹)
    rw [show g * y * g⁻¹ * (g * u * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * u * y⁻¹) * g⁻¹ by
      group] at h1
    exact h1
  have h2 : (g * y * g⁻¹) ^ 2 ^ k = g * y ^ 2 ^ k * g⁻¹ := conj_pow
  have h3 : g * (a' * burnsideF4m_U4_fieldAut h σ y * a'⁻¹) * g⁻¹ * (g * y ^ 2 ^ k * g⁻¹)⁻¹ =
      g * (a' * burnsideF4m_U4_fieldAut h σ y * a'⁻¹ * (y ^ 2 ^ k)⁻¹) * g⁻¹ := by
    group
  rw [hconj, h2, h3]
  exact (hmemS _).mpr
    (burnsideF4m_U4_conj_fieldAut_pow_inv_mem_hypUnitriangular h σ hk ha'B hyB)

omit h in
theorem k_U4TwoAutPowerMap_holds : K_U4TwoAutPowerMap := by
  intro Y _ _ n hU4 _ S hS α _ hαS
  obtain ⟨F, _, hF, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU4
  have : Finite (hypSU hF 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU hF
  set θ : MulAut (hypSU hF 2 0) := (MulAut.congr e).symm α with hθdef
  set S' : Subgroup (hypSU hF 2 0) := S.map e.symm.toMonoidHom with hS'def
  have hθ : ∀ x, θ x = e.symm (α (e x)) := fun x => rfl
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S' ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e.symm.toMonoidHom e.symm.surjective hS
  have hmem : ∀ y : Y, e.symm y ∈ S' ↔ y ∈ S := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := e.symm.injective hzy
      rw [← hzy']
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hθS' : S'.map θ.toMonoidHom = S' := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      change θ (e.symm y) ∈ S'
      rw [hθ, MulEquiv.apply_symm_apply, hmem, ← hαS]
      exact ⟨y, hy, rfl⟩
    · rw [Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
  obtain ⟨j, hj⟩ := hypSU_four_powerMap hF θ hS' hθS'
  refine ⟨j, fun x hx => ?_⟩
  have hx' : e.symm x ∈ normalizer (S' : Set (hypSU hF 2 0)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.symm.surjective z
    rw [hmem, ← map_inv e.symm x, ← map_mul e.symm x w, ← map_mul e.symm (x * w) x⁻¹, hmem]
    exact Subgroup.mem_normalizer_iff.mp hx w
  have hfin := hj _ hx'
  rw [hθ, MulEquiv.apply_symm_apply, ← map_pow e.symm x (2 ^ j), ← map_inv e.symm (x ^ 2 ^ j),
    ← map_mul e.symm (α x) (x ^ 2 ^ j)⁻¹, hmem] at hfin
  exact hfin

end U4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
