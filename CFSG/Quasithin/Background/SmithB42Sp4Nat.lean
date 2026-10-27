module

public import CFSG.Quasithin.Background.SmithB51Sp4Bound
public import CFSG.Quasithin.Background.HSp4Alpha

public section

namespace CFSG.Quasithin.B42Sp4

open CFSG.Quasithin.H CFSG.Quasithin.H.Sp4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (radical tau coe_tau tau_sq tau_comm
  card_radical)
open scoped Matrix

variable {K : Type} [Field K]

abbrev spM (γ : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

@[expose] def fixK (Γ₀ : Subgroup (StatedSp 2 K)) : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {v | ∀ γ ∈ Γ₀, spM γ *ᵥ v = v}
  add_mem' := fun {v w} hv hw γ hγ => by rw [Matrix.mulVec_add, hv γ hγ, hw γ hγ]
  zero_mem' := fun γ _ => Matrix.mulVec_zero _
  smul_mem' := fun c v hv γ hγ => by rw [Matrix.mulVec_smul, hv γ hγ]

theorem mem_fixK {Γ₀ : Subgroup (StatedSp 2 K)} {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ fixK Γ₀ ↔ ∀ γ ∈ Γ₀, spM γ *ᵥ v = v := Iff.rfl

theorem card_fixV_map_natAut (Γ₀ : Subgroup (StatedSp 2 K)) :
    Nat.card ↥(fixV (Γ₀.map (natAut (StatedSp 2 K)))) = Nat.card ↥(fixK Γ₀) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, fun γ hγ => ?_⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  · have h := x.2 _ ⟨γ, hγ, rfl⟩
    exact congrArg Multiplicative.toAdd h
  · rintro _ ⟨γ, hγ, rfl⟩
    exact congrArg Multiplicative.ofAdd (v.2 γ hγ)

theorem map_comap_natAut {B : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))}
    (hB : B ≤ natImage (StatedSp 2 K)) :
    (B.comap (natAut (StatedSp 2 K))).map (natAut (StatedSp 2 K)) = B :=
  Subgroup.map_comap_eq_self hB

theorem natAut_injective : Function.Injective (natAut (StatedSp 2 K)) :=
  matHom_injective.comp Subtype.val_injective

section Card

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem card_fixK (Γ₀ : Subgroup (StatedSp 2 K)) :
    Nat.card ↥(fixK Γ₀) = Nat.card K ^ Module.finrank K (fixK Γ₀) :=
  Module.natCard_eq_pow_finrank

omit [Finite K] [CharP K 2] in
theorem fixK_le_fixLin {Γ₀ : Subgroup (StatedSp 2 K)} {γ : StatedSp 2 K} (hγ : γ ∈ Γ₀) :
    fixK Γ₀ ≤ fixLin (spM γ) := fun _ hv => hv γ hγ

omit [Finite K] [CharP K 2] in
theorem eq_bot_of_finrank_fixK {Γ₀ : Subgroup (StatedSp 2 K)}
    (h : 4 ≤ Module.finrank K (fixK Γ₀)) : Γ₀ = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  by_contra hγ1
  have h1 := finrank_fixLin_le_three hγ1
  have h2 : Module.finrank K ↥(fixK Γ₀) ≤ Module.finrank K ↥(fixLin
      (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) :=
    Submodule.finrank_mono (fixK_le_fixLin hγ)
  omega

omit [CharP K 2] in
theorem card_le_of_finrank_fixK_three {Γ₀ : Subgroup (StatedSp 2 K)}
    (h : Module.finrank K (fixK Γ₀) = 3) : Nat.card Γ₀ ≤ Nat.card K := by
  have hne : Γ₀ ≠ ⊥ := by
    intro hb
    have : fixK Γ₀ = ⊤ := by
      rw [eq_top_iff]
      intro v _ γ hγ
      rw [hb, Subgroup.mem_bot] at hγ
      rw [hγ, spM, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
    rw [this, finrank_top, Module.finrank_fintype_fun_eq_card] at h
    simp at h
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ht1' : (t : StatedSp 2 K) ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have hle := fixK_le_fixLin (Γ₀ := Γ₀) (t.2)
  have h3 : 3 ≤ Module.finrank K (fixLin (spM (t : StatedSp 2 K))) := by
    rw [← h]
    exact Submodule.finrank_mono hle
  have heq : fixK Γ₀ = fixLin (spM (t : StatedSp 2 K)) :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      have : Module.finrank K ↥(fixLin (spM (t : StatedSp 2 K))) ≤ 3 :=
        finrank_fixLin_le_three ht1'
      omega)
  refine card_le_of_three ht1' h3 fun g hg v hv => ?_
  have hv' : v ∈ fixK Γ₀ := by rw [heq]; exact hv
  exact hv' g hg

theorem card_sq_mul_card_fixK_cube_le (Γ₀ : Subgroup (StatedSp 2 K))
    (hΓ : ∀ x ∈ Γ₀, x * x = 1) :
    Nat.card Γ₀ ^ 2 * Nat.card ↥(fixK Γ₀) ^ 3 ≤ (Nat.card K ^ 4) ^ 3 := by
  set q := Nat.card K with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  set c := Module.finrank K (fixK Γ₀) with hc
  have hc4 : c ≤ 4 := by
    have := Submodule.finrank_le (fixK Γ₀)
    rw [Module.finrank_fintype_fun_eq_card] at this
    simpa using this
  rw [card_fixK]
  have hcube := card_le_cube Γ₀ hΓ
  rcases (by omega : c = 4 ∨ c = 3 ∨ c ≤ 2) with h4 | h3 | h2
  · have hb := eq_bot_of_finrank_fixK (Γ₀ := Γ₀) (by omega)
    have h1 : Nat.card Γ₀ = 1 := by rw [hb, Subgroup.card_bot]
    rw [h1, ← hc, h4, one_pow, one_mul, ← hq]
  · have h1 := card_le_of_finrank_fixK_three (Γ₀ := Γ₀) (by omega)
    rw [← hc, h3]
    calc Nat.card Γ₀ ^ 2 * (q ^ 3) ^ 3 ≤ q ^ 2 * (q ^ 3) ^ 3 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 2)
      _ ≤ q ^ 3 * (q ^ 3) ^ 3 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq1 (by norm_num))
      _ = (q ^ 4) ^ 3 := by ring
  · rw [← hc]
    calc Nat.card Γ₀ ^ 2 * (q ^ c) ^ 3 ≤ (q ^ 3) ^ 2 * (q ^ 2) ^ 3 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hcube 2)
            (Nat.pow_le_pow_left (Nat.pow_le_pow_right hq1 h2) 3)
      _ = (q ^ 4) ^ 3 := by ring

omit [Finite K] [CharP K 2] in
theorem tau_mulVec_inl {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (v : Fin 2 ⊕ Fin 2 → K)
    (i : Fin 2) : (spM (tau hC) *ᵥ v) (Sum.inl i) = v (Sum.inl i) + ∑ j, C i j * v (Sum.inr j) := by
  rw [spM, coe_tau]
  simp [Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]

omit [Finite K] [CharP K 2] in
theorem tau_mulVec_inr {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (v : Fin 2 ⊕ Fin 2 → K)
    (i : Fin 2) : (spM (tau hC) *ᵥ v) (Sum.inr i) = v (Sum.inr i) := by
  rw [spM, coe_tau]
  simp [Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]

omit [Finite K] [CharP K 2] in
theorem mem_fixK_of_le_radical {Γ₁ : Subgroup (StatedSp 2 K)} (hΓ : Γ₁ ≤ radical K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : ∀ j, v (Sum.inr j) = 0) : v ∈ fixK Γ₁ := by
  intro γ hγ
  obtain ⟨C, hC, rfl⟩ := hΓ hγ
  ext i
  rcases i with i | i
  · rw [tau_mulVec_inl]
    simp [hv]
  · rw [tau_mulVec_inr]

@[expose] def planeK (K : Type) [Field K] : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {v | ∀ j, v (Sum.inr j) = 0}
  add_mem' := fun {v w} hv hw j => by simp [hv j, hw j]
  zero_mem' := fun j => rfl
  smul_mem' := fun c v hv j => by simp [hv j]

omit [Finite K] [CharP K 2] in
theorem card_planeK [Finite K] : Nat.card ↥(planeK K) = Nat.card K ^ 2 := by
  have e : ↥(planeK K) ≃ (Fin 2 → K) :=
    { toFun := fun v i => v.1 (Sum.inl i)
      invFun := fun x => ⟨Sum.elim x 0, fun j => rfl⟩
      left_inv := fun v => by
        apply Subtype.ext
        ext i
        rcases i with i | i
        · rfl
        · exact (v.2 i).symm
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_fun]
  simp

omit [Finite K] [CharP K 2] in
theorem fixK_radical : fixK (radical K) = planeK K := by
  ext v
  constructor
  · intro hv j
    have h1 := hv (tau (C := 1) Matrix.transpose_one) ⟨1, Matrix.transpose_one, rfl⟩
    have h2 := congrFun h1 (Sum.inl j)
    rw [tau_mulVec_inl] at h2
    simpa [Matrix.one_apply] using h2
  · intro hv
    exact mem_fixK_of_le_radical le_rfl hv

theorem card_mul_card_fixK_le_of_le_radical {Γ₁ : Subgroup (StatedSp 2 K)}
    (hΓ : Γ₁ ≤ radical K) : Nat.card Γ₁ * Nat.card ↥(fixK Γ₁) ≤ Nat.card K ^ 5 := by
  set q := Nat.card K with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have hsq : ∀ x ∈ Γ₁, x * x = 1 := fun x hx => by
    obtain ⟨C, hC, rfl⟩ := hΓ hx
    rw [← sq]
    exact tau_sq hC
  set c := Module.finrank K (fixK Γ₁) with hc
  have hc4 : c ≤ 4 := by
    have := Submodule.finrank_le (fixK Γ₁)
    rw [Module.finrank_fintype_fun_eq_card] at this
    simpa using this
  have hc2 : 2 ≤ c := by
    have hle : planeK K ≤ fixK Γ₁ := fun v hv => mem_fixK_of_le_radical hΓ hv
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank K ↥(planeK K) = 2 := by
      have h3 := card_planeK (K := K)
      rw [Module.natCard_eq_pow_finrank (K := K)] at h3
      have hq2 : 2 ≤ q := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      exact Nat.pow_right_injective hq2 h3
    omega
  rw [card_fixK]
  rcases (by omega : c = 4 ∨ c = 3 ∨ c = 2) with h4 | h3 | h2
  · have hb := eq_bot_of_finrank_fixK (Γ₀ := Γ₁) (by omega)
    have h1 : Nat.card Γ₁ = 1 := by rw [hb, Subgroup.card_bot]
    rw [h1, ← hc, h4, one_mul]
    exact Nat.pow_le_pow_right hq1 (by norm_num)
  · have h1 := card_le_of_finrank_fixK_three (Γ₀ := Γ₁) (by omega)
    rw [← hc, h3]
    calc Nat.card Γ₁ * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ h1
      _ ≤ q ^ 5 := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right hq1 (by norm_num)
  · rw [← hc, h2]
    calc Nat.card Γ₁ * q ^ 2 ≤ q ^ 3 * q ^ 2 :=
          Nat.mul_le_mul_right _ (card_le_cube Γ₁ hsq)
      _ = q ^ 5 := by ring

theorem natImage_card_sq_mul_card_fixV_cube_le {B : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))}
    (hB : B ≤ natImage (StatedSp 2 K)) (hBe : IsElemAbelian2 B) :
    Nat.card B ^ 2 * Nat.card ↥(fixV B) ^ 3 ≤ Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) ^ 3 := by
  set Γ₀ := B.comap (natAut (StatedSp 2 K)) with hΓ₀
  have hmap := map_comap_natAut hB
  have hcard : Nat.card Γ₀ = Nat.card B := by
    rw [← hmap, Subgroup.card_map_of_injective natAut_injective]
  have hsq : ∀ x ∈ Γ₀, x * x = 1 := fun x hx => by
    apply natAut_injective
    rw [map_mul, map_one, ← sq]
    exact hBe.2 _ hx
  have h := card_sq_mul_card_fixK_cube_le Γ₀ hsq
  rw [← card_fixV_map_natAut, hmap, hcard] at h
  rw [card_stdMod]
  simpa using h

noncomputable abbrev radImage (K : Type) [Field K] : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) :=
  (radical K).map (natAut (StatedSp 2 K))

omit [Finite K] [CharP K 2] in
theorem radImage_le : radImage K ≤ natImage (StatedSp 2 K) := Subgroup.map_le_range _ _

omit [Finite K] [CharP K 2] in
theorem card_radImage : Nat.card (radImage K) = Nat.card K ^ 3 := by
  rw [Subgroup.card_map_of_injective natAut_injective, card_radical]

omit [CharP K 2] in
theorem card_fixV_radImage : Nat.card ↥(fixV (radImage K)) = Nat.card K ^ 2 := by
  rw [card_fixV_map_natAut, fixK_radical, card_planeK]

omit [Finite K] in
theorem isElemAbelian2_radImage : IsElemAbelian2 (radImage K) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, ⟨C, hC, rfl⟩, rfl⟩ _ ⟨y, ⟨D, hD, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, tau_comm]
  · rintro _ ⟨x, ⟨C, hC, rfl⟩, rfl⟩
    rw [← map_pow, tau_sq, map_one]

omit [CharP K 2] in
theorem radImage_ne_bot : radImage K ≠ ⊥ := by
  intro h
  have h1 := card_radImage (K := K)
  rw [h, Subgroup.card_bot] at h1
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have : 2 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq2 3
  omega

theorem card_mul_card_fixV_le_of_le_radImage
    {B : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))} (hB : B ≤ radImage K) :
    Nat.card B * Nat.card ↥(fixV B) ≤
      Nat.card (radImage K) * Nat.card ↥(fixV (radImage K)) := by
  set Γ₁ := B.comap (natAut (StatedSp 2 K)) with hΓ₁
  have hmap := map_comap_natAut (hB.trans radImage_le)
  have hcard : Nat.card Γ₁ = Nat.card B := by
    rw [← hmap, Subgroup.card_map_of_injective natAut_injective]
  have hΓR : Γ₁ ≤ radical K := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hB hx
    rwa [natAut_injective hxy] at hy
  have h := card_mul_card_fixK_le_of_le_radical hΓR
  rw [← card_fixV_map_natAut, hmap, hcard] at h
  rw [card_radImage, card_fixV_radImage]
  calc Nat.card B * Nat.card ↥(fixV B) ≤ Nat.card K ^ 5 := h
    _ = Nat.card K ^ 3 * Nat.card K ^ 2 := by ring

end Card

end CFSG.Quasithin.B42Sp4
