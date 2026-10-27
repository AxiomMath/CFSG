module

public import CFSG.Timmesfeld.Transvection.ModelSUPerp
public import CFSG.Timmesfeld.Transvection.ModelSURadical

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

@[expose] def lineSL (σ : F ≃+* F) (a d : Fin m → F) : Subgroup (SU σ m) where
  carrier := {g | (∀ u ∈ perpPair σ a d, suMat σ m g *ᵥ u = u) ∧
    ∃ α β γ δ : F, σ α = α ∧ σ β = β ∧ σ γ = γ ∧ σ δ = δ ∧ α * δ - β * γ = 1 ∧
      suMat σ m g *ᵥ a = α • a + β • d ∧ suMat σ m g *ᵥ d = γ • a + δ • d}
  mul_mem' := by
    rintro g h ⟨hgP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hga, hgd⟩
      ⟨hhP, α', β', γ', δ', hα', hβ', hγ', hδ', hdet', hha, hhd⟩
    refine ⟨fun u hu => ?_, α' * α + β' * γ, α' * β + β' * δ, γ' * α + δ' * γ,
      γ' * β + δ' * δ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, ← mulVec_mulVec, hhP u hu, hgP u hu]
    · rw [map_add, map_mul, map_mul, hα', hα, hβ', hγ]
    · rw [map_add, map_mul, map_mul, hα', hβ, hβ', hδ]
    · rw [map_add, map_mul, map_mul, hγ', hα, hδ', hγ]
    · rw [map_add, map_mul, map_mul, hγ', hβ, hδ', hδ]
    · have h : (α' * α + β' * γ) * (γ' * β + δ' * δ) -
          (α' * β + β' * δ) * (γ' * α + δ' * γ) =
          (α' * δ' - β' * γ') * (α * δ - β * γ) := by ring
      rw [h, hdet, hdet', mul_one]
    · rw [map_mul, ← mulVec_mulVec, hha, mulVec_add, mulVec_smul, mulVec_smul, hga, hgd]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [map_mul, ← mulVec_mulVec, hhd, mulVec_add, mulVec_smul, mulVec_smul, hga, hgd]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  one_mem' := ⟨fun u _ => by rw [map_one, one_mulVec], 1, 0, 0, 1, map_one σ, map_zero σ,
    map_zero σ, map_one σ, by norm_num, by rw [map_one, one_mulVec]; simp,
    by rw [map_one, one_mulVec]; simp⟩
  inv_mem' := by
    rintro g ⟨hgP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hga, hgd⟩
    have hdet' : δ * α - β * γ = 1 := by linear_combination hdet
    refine ⟨fun u hu => ?_, δ, -β, -γ, α, hδ, ?_, ?_, hα, ?_, ?_, ?_⟩
    · calc suMat σ m g⁻¹ *ᵥ u = suMat σ m g⁻¹ *ᵥ (suMat σ m g *ᵥ u) := by rw [hgP u hu]
        _ = u := suMat_inv_mulVec_suMat_mulVec g u
    · rw [map_neg, hβ]
    · rw [map_neg, hγ]
    · have h : δ * α - (-β) * (-γ) = δ * α - β * γ := by ring
      rw [h, hdet']
    · have hcomp : suMat σ m g *ᵥ (δ • a - β • d) = a := by
        rw [mulVec_sub, mulVec_smul, mulVec_smul, hga, hgd, sub_eq_add_neg, ← neg_smul]
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (a i) * hdet'
      have h := suMat_inv_mulVec_suMat_mulVec g (δ • a - β • d)
      rw [hcomp] at h
      simpa only [sub_eq_add_neg, neg_smul] using h
    · have hcomp : suMat σ m g *ᵥ (-γ • a + α • d) = d := by
        rw [mulVec_add, mulVec_smul, mulVec_smul, hga, hgd]
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (d i) * hdet
      have h := suMat_inv_mulVec_suMat_mulVec g (-γ • a + α • d)
      rw [hcomp] at h
      simpa only [sub_eq_add_neg, neg_smul] using h

theorem mem_lineSL {a d : Fin m → F} {g : SU σ m} :
    g ∈ lineSL σ a d ↔ (∀ u ∈ perpPair σ a d, suMat σ m g *ᵥ u = u) ∧
      ∃ α β γ δ : F, σ α = α ∧ σ β = β ∧ σ γ = γ ∧ σ δ = δ ∧ α * δ - β * γ = 1 ∧
        suMat σ m g *ᵥ a = α • a + β • d ∧ suMat σ m g *ᵥ d = γ • a + δ • d := Iff.rfl

theorem eq_projPair_add (a d x : Fin m → F) :
    x = projPair σ a d x + uForm σ d x • a + uForm σ a x • d := by
  rw [projPair]
  abel

theorem le_lineSL_of_isUTransGroup_left [CharP F 2] {a d : Fin m → F}
    (haa : uForm σ a a = 0) (had : uForm σ a d = 1) {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ a T) : T ≤ lineSL σ a d := by
  intro t ht
  obtain ⟨c, hc, htc⟩ := (hT.1 t).1 ht
  have hcfix : σ c = c := by
    have h : σ c = -c := by linear_combination hc
    rw [h, CharTwo.neg_eq]
  refine ⟨fun u hu => ?_, 1, 0, c, 1, map_one σ, map_zero σ, hcfix, map_one σ, by norm_num,
    ?_, ?_⟩
  · rw [htc, uTrans_mulVec, hu.1, mul_zero, zero_smul, add_zero]
  · rw [htc, uTrans_mulVec, haa, mul_zero, zero_smul, add_zero]
    simp
  · rw [htc, uTrans_mulVec, had, mul_one, one_smul, add_comm]

theorem le_lineSL_of_isUTransGroup_right [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ d T) : T ≤ lineSL σ a d := by
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  intro t ht
  obtain ⟨c, hc, htc⟩ := (hT.1 t).1 ht
  have hcfix : σ c = c := by
    have h : σ c = -c := by linear_combination hc
    rw [h, CharTwo.neg_eq]
  refine ⟨fun u hu => ?_, 1, c, 0, 1, map_one σ, hcfix, map_zero σ, map_one σ, by norm_num,
    ?_, ?_⟩
  · rw [htc, uTrans_mulVec, hu.2, mul_zero, zero_smul, add_zero]
  · rw [htc, uTrans_mulVec, hda, mul_one, one_smul, add_comm]
  · rw [htc, uTrans_mulVec, hdd, mul_zero, zero_smul, add_zero]
    simp

theorem eq_one_of_mulVec_eq (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    {M : Matrix (Fin m) (Fin m) F} (ha : M *ᵥ a = a) (hd : M *ᵥ d = d)
    (hP : ∀ u ∈ perpPair σ a d, M *ᵥ u = u) : M = 1 := by
  have hlin : ∀ x, M *ᵥ x = x := by
    intro x
    calc M *ᵥ x
        = M *ᵥ (projPair σ a d x + uForm σ d x • a + uForm σ a x • d) := by
            conv_lhs => rw [eq_projPair_add (σ := σ) a d x]
      _ = M *ᵥ projPair σ a d x + uForm σ d x • (M *ᵥ a) +
            uForm σ a x • (M *ᵥ d) := by
            rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul]
      _ = projPair σ a d x + uForm σ d x • a + uForm σ a x • d := by
            rw [hP _ (projPair_mem hσ haa hdd had x), ha, hd]
      _ = x := by conv_rhs => rw [eq_projPair_add (σ := σ) a d x]
  exact Matrix.ext_iff_mulVec.2 fun v => by rw [hlin v, Matrix.one_mulVec]

theorem mul_self_eq_one_of_add_eq_zero [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {g : SU σ m}
    (hP : ∀ u ∈ perpPair σ a d, suMat σ m g *ᵥ u = u) {α β γ δ : F}
    (hdet : α * δ - β * γ = 1) (hga : suMat σ m g *ᵥ a = α • a + β • d)
    (hgd : suMat σ m g *ᵥ d = γ • a + δ • d) (hαδ : α + δ = 0) : g * g = 1 := by
  have hδα : δ = α := by
    have h : δ = -α := by linear_combination hαδ
    rwa [CharTwo.neg_eq] at h
  have hdet' : α * α - β * γ = 1 := by rwa [hδα] at hdet
  have hcoef : α * α + β * γ = 1 := by
    linear_combination hdet' + (β * γ) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have h2a : suMat σ m (g * g) *ᵥ a = a := by
    rw [map_mul, ← mulVec_mulVec, hga, mulVec_add, mulVec_smul, mulVec_smul, hga, hgd]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hδα]
    linear_combination (a i) * hcoef +
      (d i * β * α) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have h2d : suMat σ m (g * g) *ᵥ d = d := by
    rw [map_mul, ← mulVec_mulVec, hgd, mulVec_add, mulVec_smul, mulVec_smul, hga, hgd]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hδα]
    linear_combination (d i) * hcoef +
      (a i * γ * α) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have hP2 : ∀ u ∈ perpPair σ a d, suMat σ m (g * g) *ᵥ u = u := by
    intro u hu
    rw [map_mul, ← mulVec_mulVec, hP u hu, hP u hu]
  have hM := eq_one_of_mulVec_eq hσ haa hdd had h2a h2d hP2
  apply suMat_injective σ
  rwa [map_mul, map_one]

theorem mul_self_eq_one_of_mem_lineSL [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {g : SU σ m}
    (hg : g ∈ lineSL σ a d) {u : Fin m → F} (hgu : suMat σ m g *ᵥ u = u)
    (hu : u ∉ perpPair σ a d) : g * g = 1 := by
  obtain ⟨hP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hga, hgd⟩ := hg
  have hnot : uForm σ d u ≠ 0 ∨ uForm σ a u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (by rw [mem_perpPair]; exact ⟨h.2, h.1⟩)
  have h1 : γ * uForm σ a u + δ * uForm σ d u = uForm σ d u := by
    have h := uForm_mulVec σ g d u
    rw [hgu, hgd] at h
    simpa only [uForm_add_left, uForm_smul_left, hγ, hδ] using h
  have h2 : α * uForm σ a u + β * uForm σ d u = uForm σ a u := by
    have h := uForm_mulVec σ g a u
    rw [hgu, hga] at h
    simpa only [uForm_add_left, uForm_smul_left, hα, hβ] using h
  have hcy : ((α - 1) * (δ - 1) - β * γ) * uForm σ a u = 0 := by
    linear_combination (δ - 1) * h2 - β * h1
  have hcx : ((α - 1) * (δ - 1) - β * γ) * uForm σ d u = 0 := by
    linear_combination (α - 1) * h1 - γ * h2
  have hceq : (α - 1) * (δ - 1) - β * γ = α + δ := by
    linear_combination hdet + (1 - α - δ) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have hc0 : (α - 1) * (δ - 1) - β * γ = 0 := by
    rcases hnot with hx0 | hy0
    · exact (mul_eq_zero.mp hcx).resolve_right hx0
    · exact (mul_eq_zero.mp hcy).resolve_right hy0
  have hαδ : α + δ = 0 := by rw [← hceq, hc0]
  exact mul_self_eq_one_of_add_eq_zero hσ haa hdd had hP hdet hga hgd hαδ

private theorem sub_mul_sigma_eq_zero [CharP F 2] {x y l α β γ δ : F}
    (hα : σ α = α) (hβ : σ β = β) (hγ : σ γ = γ) (hδ : σ δ = δ)
    (hxe : α * x + γ * y = l * x) (hye : β * x + δ * y = l * y)
    (hxy : x * σ y + y * σ x = 0) :
    (l - σ l) * x * σ x = 0 ∧ (l - σ l) * y * σ y = 0 := by
  have hxeσ : α * σ x + γ * σ y = σ l * σ x := by
    have h := congrArg σ hxe
    simpa only [map_add, map_mul, hα, hγ] using h
  have hyeσ : β * σ x + δ * σ y = σ l * σ y := by
    have h := congrArg σ hye
    simpa only [map_add, map_mul, hβ, hδ] using h
  have hxy' : y * σ x = x * σ y := by
    linear_combination hxy - (x * σ y) * (CharTwo.two_eq_zero : (2 : F) = 0)
  constructor
  · have hT : (l - σ l) * x * σ x = γ * (y * σ x - x * σ y) := by
      calc (l - σ l) * x * σ x
          = σ x * (α * x + γ * y) - x * (α * σ x + γ * σ y) := by
              rw [hxe, hxeσ]; ring
        _ = γ * (y * σ x - x * σ y) := by ring
    have hzero : y * σ x - x * σ y = 0 := sub_eq_zero.mpr hxy'
    rw [hT, hzero, mul_zero]
  · have hT : (l - σ l) * y * σ y = β * (x * σ y - y * σ x) := by
      calc (l - σ l) * y * σ y
          = σ y * (β * x + δ * y) - y * (β * σ x + δ * σ y) := by
              rw [hye, hyeσ]; ring
        _ = β * (x * σ y - y * σ x) := by ring
    have hzero : x * σ y - y * σ x = 0 := sub_eq_zero.mpr hxy'.symm
    rw [hT, hzero, mul_zero]

private theorem sigma_eq_of_mem_lineSL_of_projPair_eq_zero [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {g : SU σ m}
    (hg : g ∈ lineSL σ a d) {u : Fin m → F} {l : F} (hgu : suMat σ m g *ᵥ u = l • u)
    (huu : uForm σ u u = 0) (hu : u ∉ perpPair σ a d)
    (hp0 : projPair σ a d u = 0) : σ l = l := by
  obtain ⟨hP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hga, hgd⟩ := hg
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  have hu0 : u ≠ 0 := fun h => hu (by rw [h]; exact (perpPair σ a d).zero_mem)
  have hu_eq : u = uForm σ d u • a + uForm σ a u • d := by
    have h := eq_projPair_add (σ := σ) a d u
    rw [hp0] at h
    simpa using h
  have hnot : uForm σ d u ≠ 0 ∨ uForm σ a u ≠ 0 := by
    by_contra h
    push Not at h
    apply hu0
    rw [hu_eq, h.1, h.2, zero_smul, zero_smul, add_zero]
  have hgu_decomp : suMat σ m g *ᵥ u =
      uForm σ d u • (α • a + β • d) + uForm σ a u • (γ • a + δ • d) := by
    conv_lhs => rw [hu_eq]
    rw [mulVec_add, mulVec_smul, mulVec_smul, hga, hgd]
  have hxe : α * uForm σ d u + γ * uForm σ a u = l * uForm σ d u := by
    have h := congrArg (uForm σ d) (hgu_decomp.symm.trans hgu)
    simp only [uForm_add_right, uForm_smul_right, hdd, hda, mul_one, mul_zero, add_zero] at h
    linear_combination h
  have hye : β * uForm σ d u + δ * uForm σ a u = l * uForm σ a u := by
    have h := congrArg (uForm σ a) (hgu_decomp.symm.trans hgu)
    simp only [uForm_add_right, uForm_smul_right, haa, had, mul_one, mul_zero, zero_add] at h
    linear_combination h
  have hxy : uForm σ d u * σ (uForm σ a u) +
      uForm σ a u * σ (uForm σ d u) = 0 := by
    have h := huu
    rw [hu_eq] at h
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right,
      haa, hdd, had, hda, mul_zero, mul_one, zero_mul, add_zero, zero_add] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  obtain ⟨hx_eq, hy_eq⟩ := sub_mul_sigma_eq_zero hα hβ hγ hδ hxe hye hxy
  rcases hnot with hx0 | hy0
  · have hxσ : uForm σ d u * σ (uForm σ d u) ≠ 0 :=
      mul_ne_zero hx0 ((map_ne_zero σ).2 hx0)
    have h := hx_eq
    rw [mul_assoc] at h
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hxσ)).symm
  · have hyσ : uForm σ a u * σ (uForm σ a u) ≠ 0 :=
      mul_ne_zero hy0 ((map_ne_zero σ).2 hy0)
    have h := hy_eq
    rw [mul_assoc] at h
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hyσ)).symm

private theorem sigma_eq_of_mem_lineSL_of_projPair_ne_zero [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {g : SU σ m}
    (hg : g ∈ lineSL σ a d) {u : Fin m → F} {l : F} (hgu : suMat σ m g *ᵥ u = l • u)
    (hp0 : projPair σ a d u ≠ 0) : σ l = l := by
  obtain ⟨hP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hga, hgd⟩ := hg
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  have hmem : projPair σ a d u ∈ perpPair σ a d := projPair_mem hσ haa hdd had u
  have hgu_decomp : suMat σ m g *ᵥ u =
      projPair σ a d u + uForm σ d u • (α • a + β • d) +
        uForm σ a u • (γ • a + δ • d) := by
    conv_lhs => rw [eq_projPair_add (σ := σ) a d u]
    rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hP _ hmem, hga, hgd]
  have hpa : projPair σ a d (α • a + β • d) = 0 := by
    rw [projPair_add, projPair_smul, projPair_smul, projPair_a hσ haa had,
      projPair_d hdd had, smul_zero, smul_zero, add_zero]
  have hpd : projPair σ a d (γ • a + δ • d) = 0 := by
    rw [projPair_add, projPair_smul, projPair_smul, projPair_a hσ haa had,
      projPair_d hdd had, smul_zero, smul_zero, add_zero]
  have hproj_g : projPair σ a d (suMat σ m g *ᵥ u) = projPair σ a d u := by
    rw [hgu_decomp, projPair_add, projPair_add, projPair_smul, projPair_smul,
      projPair_of_mem hmem, hpa, hpd, smul_zero, smul_zero, add_zero, add_zero]
  have hproj_l : projPair σ a d (suMat σ m g *ᵥ u) = l • projPair σ a d u := by
    rw [hgu, projPair_smul]
  have hp_eq : projPair σ a d u = l • projPair σ a d u := hproj_g.symm.trans hproj_l
  have h1 : 1 - l = 0 := by
    have h : (1 - l) • projPair σ a d u = 0 := by
      rw [sub_smul, one_smul, ← hp_eq, sub_self]
    rcases smul_eq_zero.1 h with h' | h'
    · exact h'
    · exact absurd h' hp0
  have hl : l = 1 := (sub_eq_zero.mp h1).symm
  rw [hl, map_one]

theorem sigma_eq_of_mem_lineSL [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {g : SU σ m}
    (hg : g ∈ lineSL σ a d) {u : Fin m → F} {l : F} (hgu : suMat σ m g *ᵥ u = l • u)
    (huu : uForm σ u u = 0) (hu : u ∉ perpPair σ a d) : σ l = l := by
  by_cases hp0 : projPair σ a d u = 0
  · exact sigma_eq_of_mem_lineSL_of_projPair_eq_zero hσ haa hdd had hg hgu huu hu hp0
  · exact sigma_eq_of_mem_lineSL_of_projPair_ne_zero hσ haa hdd had hg hgu hp0

theorem pow_mul_eq_one_of_mem_lineSL [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {a d : Fin m → F}
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) {g : SU (unitaryInvolution F 2 f) m}
    (hg : g ∈ lineSL (unitaryInvolution F 2 f) a d) {u : Fin m → F} {l : F}
    (hgu : suMat (unitaryInvolution F 2 f) m g *ᵥ u = l • u)
    (huu : uForm (unitaryInvolution F 2 f) u u = 0)
    (hu : u ∉ perpPair (unitaryInvolution F 2 f) a d) :
    g ^ (2 * (2 ^ f - 1)) = 1 := by
  have hu0 : u ≠ 0 := fun h =>
    hu (by rw [h]; exact (perpPair (unitaryInvolution F 2 f) a d).zero_mem)
  have hl : l ≠ 0 := by
    intro hl0
    have h := hgu
    rw [hl0, zero_smul] at h
    exact suMat_mulVec_ne_zero (unitaryInvolution F 2 f) g hu0 h
  have hσl : unitaryInvolution F 2 f l = l :=
    sigma_eq_of_mem_lineSL (unitaryInvolution_involutive hF) haa hdd had hg hgu huu hu
  have hlpow : l ^ 2 ^ f = l := by
    rw [← unitaryInvolution_apply (K := F) (p := 2) (f := f) l]
    exact hσl
  have hlunit : l ^ (2 ^ f - 1) = 1 := by
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
    have h : l ^ (2 ^ f - 1) * l = l := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hlpow]
    exact mul_right_cancel₀ hl (by simpa using h)
  let s : SU (unitaryInvolution F 2 f) m := g ^ (2 ^ f - 1)
  have hs : s ∈ lineSL (unitaryInvolution F 2 f) a d := by
    dsimp [s]
    exact Subgroup.pow_mem _ hg _
  have hpow : ∀ n : ℕ, suMat (unitaryInvolution F 2 f) m (g ^ n) *ᵥ u = l ^ n • u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, ← mulVec_mulVec, hgu, mulVec_smul, ih, smul_smul, pow_succ']
  have hsu : suMat (unitaryInvolution F 2 f) m s *ᵥ u = u := by
    dsimp [s]
    rw [hpow, hlunit, one_smul]
  have hs2 : s * s = 1 :=
    mul_self_eq_one_of_mem_lineSL (unitaryInvolution_involutive hF) haa hdd had hs hsu hu
  have h : g ^ (2 * (2 ^ f - 1)) = s * s := by
    dsimp [s]
    rw [← pow_add]
    congr 1
    ring
  rw [h, hs2]

private theorem not_dvd_two_mul_sub_one {q : ℕ} (hq : 4 ≤ q) : ¬q + 1 ∣ 2 * (q - 1) := by
  intro h
  have hq' : 4 ≤ q := hq
  have h1 : q + 1 ∣ 2 * (q + 1) := dvd_mul_left _ _
  have h2 : q + 1 ∣ 2 * (q + 1) - 2 * (q - 1) := Nat.dvd_sub h1 h
  have h3 : 2 * (q + 1) - 2 * (q - 1) = 4 := by omega
  rw [h3] at h2
  have h4 : q + 1 ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) h2
  omega

theorem mulVec_ne_smul_of_orderOf [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {K : Type*} [Group K]
    (Φ : SU (unitaryInvolution F 2 f) m →* K) {a d : Fin m → F}
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) {g : SU (unitaryInvolution F 2 f) m}
    (hg : g ∈ lineSL (unitaryInvolution F 2 f) a d) (hord : orderOf (Φ g) = 2 ^ f + 1)
    {u : Fin m → F} (huu : uForm (unitaryInvolution F 2 f) u u = 0)
    (hu : u ∉ perpPair (unitaryInvolution F 2 f) a d) (l : F) :
    suMat (unitaryInvolution F 2 f) m g *ᵥ u ≠ l • u := by
  intro hgu
  have hpow := pow_mul_eq_one_of_mem_lineSL hF haa hdd had hg hgu huu hu
  have hdvd : orderOf (Φ g) ∣ 2 * (2 ^ f - 1) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hpow, map_one]
  rw [hord] at hdvd
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact not_dvd_two_mul_sub_one hq hdvd

theorem mul_self_ne_one_of_orderOf {K : Type*} [Group K] (Φ : SU σ m →* K) {g : SU σ m}
    {f : ℕ} (hf : 1 ≤ f) (hord : orderOf (Φ g) = 2 ^ f + 1) : g * g ≠ 1 := by
  intro h
  have h2 : (Φ g) ^ 2 = 1 := by simpa [pow_two] using congrArg Φ h
  have hdvd : orderOf (Φ g) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at hdvd
  have hle : 2 ^ f + 1 ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have hgt : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

end ModelRank

end CFSG.Timmesfeld.Transvection