module

public import CFSG.RankThree.PartOne.CTP.SpPair
public import CFSG.RankThree.PartOne.CTP.Su4Geom

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

section Plane

theorem exists_aniso_of_nondeg (hσ : IsUnitaryInvolution σ) {W : Submodule K (Fin n → K)}
    (hW : W ≠ ⊥) (hnd : ∀ w ∈ W, (∀ u ∈ W, herm σ u w = 0) → w = 0) :
    ∃ w ∈ W, herm σ w w ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  exact hw0 (hnd w hw fun u hu => herm_eq_zero_of_forall_isotropic hσ (S := W) h hu hw)

theorem exists_hyperbolic_pair_of_nondeg_plane (hσ : IsUnitaryInvolution σ)
    {W : Submodule K (Fin n → K)} (hdim : Module.finrank K W = 2)
    (hnd : ∀ w ∈ W, (∀ u ∈ W, herm σ u w = 0) → w = 0) :
    ∃ x ∈ W, ∃ y ∈ W, herm σ x x = 0 ∧ herm σ y y = 0 ∧ herm σ x y = 1 := by
  classical
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨w₁, hw₁, ha₁⟩ := exists_aniso_of_nondeg hσ hWne hnd
  have hw₁0 : w₁ ≠ 0 := fun h => ha₁ (by rw [h, herm_zero_left])
  obtain ⟨w, hw, hwn⟩ : ∃ w ∈ W, w ∉ Submodule.span K {w₁} := by
    by_contra hcon
    push Not at hcon
    have hle : W ≤ Submodule.span K {w₁} := hcon
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hw₁0] at this
    omega
  obtain ⟨w₂, hw₂def⟩ : ∃ w₂ : Fin n → K, w₂ = w - (herm σ w₁ w / herm σ w₁ w₁) • w₁ := ⟨_, rfl⟩
  have hw₂W : w₂ ∈ W := by
    rw [hw₂def]
    exact W.sub_mem hw (W.smul_mem _ hw₁)
  have hw₁w₂ : herm σ w₁ w₂ = 0 := by
    rw [hw₂def, herm_sub_right, herm_smul_right]
    field_simp
    ring
  have hw₂n : w₂ ∉ Submodule.span K {w₁} := by
    intro h
    apply hwn
    have : w = w₂ + (herm σ w₁ w / herm σ w₁ w₁) • w₁ := by rw [hw₂def]; abel
    rw [this]
    exact Submodule.add_mem _ h (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₁))
  have hw₂0 : w₂ ≠ 0 := fun h => hw₂n (h ▸ Submodule.zero_mem _)
  have hspan : Submodule.span K {w₁, w₂} = W := by
    have hle : Submodule.span K {w₁, w₂} ≤ W := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact hw₁
      · exact hw₂W)
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_pair_of_not_mem hw₁0 hw₂n, hdim])
  have h21 : herm σ w₂ w₁ = 0 := herm_eq_zero_comm σ hσ.invol hw₁w₂
  have ha₂ : herm σ w₂ w₂ ≠ 0 := by
    intro h0
    apply hw₂0
    refine hnd w₂ hw₂W fun u hu => ?_
    rw [← hspan] at hu
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hu
    rw [herm_add_left, herm_smul_left, herm_smul_left, hw₁w₂, h0]
    ring
  have hfix₁ : σ (herm σ w₁ w₁) = herm σ w₁ w₁ := herm_self_fixed σ hσ.invol w₁
  have hfix₂ : σ (herm σ w₂ w₂) = herm σ w₂ w₂ := herm_self_fixed σ hσ.invol w₂
  obtain ⟨c, hc⟩ := hσ.norm_surj (-herm σ w₂ w₂ / herm σ w₁ w₁)
    (by rw [map_div₀, map_neg, hfix₁, hfix₂]) (div_ne_zero (neg_ne_zero.mpr ha₂) ha₁)
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hiso : ∀ d : K, σ d * d = σ c * c →
      herm σ (d • w₁ + w₂) (d • w₁ + w₂) = 0 := by
    intro d hd
    have key : herm σ (d • w₁ + w₂) (d • w₁ + w₂) =
        σ d * d * herm σ w₁ w₁ + herm σ w₂ w₂ := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hw₁w₂, h21]
      ring
    rw [key, hd, hc]
    field_simp
    ring
  have hxx' : herm σ (c • w₁ + w₂) ((ω * c) • w₁ + w₂) = (1 - ω) * herm σ w₂ w₂ := by
    have key : herm σ (c • w₁ + w₂) ((ω * c) • w₁ + w₂) =
        σ c * (ω * c) * herm σ w₁ w₁ + herm σ w₂ w₂ := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hw₁w₂, h21]
      ring
    have h2 : σ c * (ω * c) * herm σ w₁ w₁ = ω * (σ c * c) * herm σ w₁ w₁ := by ring
    rw [key, h2, hc]
    field_simp
    ring
  have hκ : (1 - ω) * herm σ w₂ w₂ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hω1)) ha₂
  have hxW : c • w₁ + w₂ ∈ W := W.add_mem (W.smul_mem _ hw₁) hw₂W
  have hx'W : (ω * c) • w₁ + w₂ ∈ W := W.add_mem (W.smul_mem _ hw₁) hw₂W
  have hx'x' : herm σ ((ω * c) • w₁ + w₂) ((ω * c) • w₁ + w₂) = 0 := by
    refine hiso (ω * c) ?_
    rw [map_mul]
    linear_combination (σ c * c) * hω
  refine ⟨c • w₁ + w₂, hxW, ((1 - ω) * herm σ w₂ w₂)⁻¹ • ((ω * c) • w₁ + w₂),
    W.smul_mem _ hx'W, hiso c rfl, ?_, ?_⟩
  · rw [herm_smul_left, herm_smul_right, hx'x', mul_zero, mul_zero]
  · rw [herm_smul_right, hxx', inv_mul_cancel₀ hκ]

end Plane

section Stable

variable {p : ℕ} [NeZero p] {ζ : K}

theorem le_iSup_inf_eigU (hζ : IsPrimitiveRoot ζ p) {g : SUid σ 4} (hg : g ^ p = 1)
    {S : Submodule K (Fin 4 → K)} (hS : ∀ v ∈ S, g • v ∈ S) : S ≤ ⨆ l, S ⊓ eigU g l := by
  classical
  let f : Module.End K (Fin 4 → K) := Matrix.mulVecLin (matU g)
  have hfS : ∀ x ∈ S, f x ∈ S := hS
  have hfp : f ^ p = 1 := actU_pow_eq_one hg
  have hf'p : f.restrict hfS ^ p = 1 :=
    LinearMap.ext fun x => Subtype.ext (by
      rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, hfp]
      rfl)
  have htop := CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hζ hf'p
  intro x hx
  have hx' : (⟨x, hx⟩ : S) ∈ (⊤ : Submodule K S) := Submodule.mem_top
  rw [← htop] at hx'
  have hmap := Submodule.mem_map_of_mem (f := S.subtype) hx'
  rw [Submodule.map_iSup] at hmap
  have hle : (⨆ l, Submodule.map S.subtype (Module.End.eigenspace (f.restrict hfS) l)) ≤
      ⨆ l, S ⊓ eigU g l := by
    refine iSup_mono fun l => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    show S.subtype y ∈ eigU g l
    rw [mem_eigU, smul_def]
    have := Module.End.mem_eigenspace_iff.mp hy
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  exact hle hmap

theorem exists_mem_inf_add_of_stableU {g : SUid σ 4} {l : K}
    (hzero : ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eigU g μ = ⊥) {S : Submodule K (Fin 4 → K)}
    (hS : S ≤ ⨆ μ, S ⊓ eigU g μ) {v : Fin 4 → K} (hv : v ∈ S) :
    ∃ a ∈ S ⊓ eigU g l, ∃ b ∈ S ⊓ eigU g l⁻¹, a + b = v := by
  have hle : (⨆ μ, S ⊓ eigU g μ) ≤ (S ⊓ eigU g l) ⊔ (S ⊓ eigU g l⁻¹) := by
    refine iSup_le fun μ => ?_
    by_cases h1 : μ = l
    · rw [h1]
      exact le_sup_left
    by_cases h2 : μ = l⁻¹
    · rw [h2]
      exact le_sup_right
    · rw [hzero μ h1 h2, inf_bot_eq]
      exact bot_le
  exact Submodule.mem_sup.mp (hle (hS hv))

end Stable

section Pairing

theorem exists_herm_ne_zero_of_isCompl {L L' : Submodule K (Fin n → K)} (hc : IsCompl L L')
    (hL : ∀ x ∈ L, ∀ y ∈ L, herm σ x y = 0) {x : Fin n → K} (hx : x ∈ L) (hx0 : x ≠ 0) :
    ∃ y ∈ L', herm σ x y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hx0
  refine eq_zero_of_herm σ fun y => ?_
  have hy : y ∈ L ⊔ L' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨l, hl, l', hl', rfl⟩ := Submodule.mem_sup.mp hy
  rw [herm_add_right, hL x hx l hl, hcon l' hl', add_zero]

end Pairing

end CFSG.RankThree.PartOne.CTP
