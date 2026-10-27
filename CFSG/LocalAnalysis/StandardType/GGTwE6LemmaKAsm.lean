module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKCop
public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKSpecial

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open scoped Matrix

section Asm


private theorem e6WeylMat_mulVec (w w' : WeylGroup Tag.E6) (y : Fin 6 → ZMod 3) :
    e6WeylMat (w * w') *ᵥ y = e6WeylMat w *ᵥ (e6WeylMat w' *ᵥ y) := by
  rw [map_mul]
  exact (Matrix.mulVec_mulVec y (e6WeylMat w) (e6WeylMat w')).symm

private theorem e6WeylMat_mul_inv_mulVec (g : WeylGroup Tag.E6) (y : Fin 6 → ZMod 3) :
    e6WeylMat g *ᵥ (e6WeylMat g⁻¹ *ᵥ y) = y := by
  have h : e6WeylMat g * e6WeylMat g⁻¹ = 1 := by
    have hm := map_mul e6WeylMat g g⁻¹
    rw [mul_inv_cancel, map_one] at hm
    exact hm.symm
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

private theorem e6WeylMat_inv_mulVec_injective (g : WeylGroup Tag.E6) :
    Function.Injective fun y : Fin 6 → ZMod 3 => e6WeylMat g⁻¹ *ᵥ y := by
  intro y₁ y₂ h
  have h' := congrArg (fun y => e6WeylMat g *ᵥ y) h
  rw [e6WeylMat_mul_inv_mulVec, e6WeylMat_mul_inv_mulVec] at h'
  exact h'

private def fixSub (Y : Set (Fin 6 → ZMod 3)) : Subgroup (WeylGroup Tag.E6) where
  carrier := {w | ∀ y ∈ Y, e6WeylMat w *ᵥ y = y}
  one_mem' := by intro y _; rw [map_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y hy
    rw [e6WeylMat_mulVec, hb y hy, ha y hy]
  inv_mem' := by
    intro w hw y hy
    have h2 : e6WeylMat w⁻¹ * e6WeylMat w = 1 := by
      have hm := map_mul e6WeylMat w⁻¹ w
      rw [inv_mul_cancel, map_one] at hm
      exact hm.symm
    calc e6WeylMat w⁻¹ *ᵥ y
        = e6WeylMat w⁻¹ *ᵥ (e6WeylMat w *ᵥ y) := by rw [hw y hy]
      _ = (e6WeylMat w⁻¹ * e6WeylMat w) *ᵥ y :=
            Matrix.mulVec_mulVec y (e6WeylMat w⁻¹) (e6WeylMat w)
      _ = 1 *ᵥ y := by rw [h2]
      _ = y := Matrix.one_mulVec y

private theorem e6WeylMat_conj_mulVec (g a : WeylGroup Tag.E6) (y : Fin 6 → ZMod 3)
    (ha : e6WeylMat a *ᵥ y = y) :
    e6WeylMat (g⁻¹ * a * g) *ᵥ (e6WeylMat g⁻¹ *ᵥ y) = e6WeylMat g⁻¹ *ᵥ y := by
  have hmul : e6WeylMat (g⁻¹ * a * g) = e6WeylMat g⁻¹ * e6WeylMat a * e6WeylMat g := by
    rw [map_mul, map_mul]
  rw [hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    e6WeylMat_mul_inv_mulVec, ha]

private theorem e6WeylMat_inv_apply_smul (g : WeylGroup Tag.E6) (k : Fin Tag.E6.rank) (j : Fin 6) :
    e6WeylMat g⁻¹ (e6Idx.symm k) j =
      (((g • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) (e6Idx j) : ℤ) : ZMod 3) := by
  simp only [e6WeylMat_apply, e6WeylEntry, inv_inv, Equiv.apply_symm_apply]

private theorem pairing_smul (α : Fin Tag.E6.rank → ℤ) (g : WeylGroup Tag.E6)
    (y : Fin 6 → ZMod 3) :
    ∑ i : Fin 6, (((g • α) (e6Idx i) : ℤ) : ZMod 3) * y i =
      ∑ i : Fin 6, ((α (e6Idx i) : ℤ) : ZMod 3) * (e6WeylMat g⁻¹ *ᵥ y) i := by
  have hpt : ∀ i : Fin 6,
      (((g • α) (e6Idx i) : ℤ) : ZMod 3) =
        ∑ k : Fin Tag.E6.rank, ((α k : ℤ) : ZMod 3) * e6WeylMat g⁻¹ (e6Idx.symm k) i := by
    intro i
    rw [smul_eq_sum_single g α]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [e6WeylMat_inv_apply_smul]
  have hreindex :
      (∑ k : Fin Tag.E6.rank,
          ∑ i : Fin 6, ((α k : ℤ) : ZMod 3) * e6WeylMat g⁻¹ (e6Idx.symm k) i * y i) =
        ∑ k' : Fin 6,
          ∑ i : Fin 6, ((α (e6Idx k') : ℤ) : ZMod 3) * e6WeylMat g⁻¹ k' i * y i := by
    refine (Fintype.sum_equiv e6Idx
      (fun k' : Fin 6 =>
        ∑ i : Fin 6, ((α (e6Idx k') : ℤ) : ZMod 3) * e6WeylMat g⁻¹ k' i * y i)
      (fun k : Fin Tag.E6.rank =>
        ∑ i : Fin 6, ((α k : ℤ) : ZMod 3) * e6WeylMat g⁻¹ (e6Idx.symm k) i * y i)
      (fun k' => by simp only [Equiv.symm_apply_apply])).symm
  calc ∑ i : Fin 6, (((g • α) (e6Idx i) : ℤ) : ZMod 3) * y i
      = ∑ i : Fin 6,
          (∑ k : Fin Tag.E6.rank,
            ((α k : ℤ) : ZMod 3) * e6WeylMat g⁻¹ (e6Idx.symm k) i) * y i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hpt i]
    _ = ∑ i : Fin 6, ∑ k : Fin Tag.E6.rank,
          ((α k : ℤ) : ZMod 3) * e6WeylMat g⁻¹ (e6Idx.symm k) i * y i := by
          simp only [Finset.sum_mul]
    _ = ∑ k : Fin Tag.E6.rank, ∑ i : Fin 6,
          ((α k : ℤ) : ZMod 3) * e6WeylMat g⁻¹ (e6Idx.symm k) i * y i := by
          rw [Finset.sum_comm]
    _ = ∑ k' : Fin 6, ∑ i : Fin 6,
          ((α (e6Idx k') : ℤ) : ZMod 3) * e6WeylMat g⁻¹ k' i * y i := hreindex
    _ = ∑ i : Fin 6, ((α (e6Idx i) : ℤ) : ZMod 3) * (e6WeylMat g⁻¹ *ᵥ y) i := by
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

private theorem exists_primary_decomp (u : WeylGroup Tag.E6) :
    ∃ a b : WeylGroup Tag.E6,
      a ∈ Subgroup.zpowers u ∧ b ∈ Subgroup.zpowers u ∧
        u = b * a ∧ IsPGroup 3 (Subgroup.zpowers a) ∧ Nat.Coprime (orderOf b) 3 := by
  obtain ⟨e, m, hm, hem⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u).ne' 3 (by norm_num)
  have hcop3m : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm
  have hcop : Nat.Coprime (3 ^ e) m := hcop3m.pow_left e
  have hbez_nat := Nat.gcd_eq_gcd_ab (3 ^ e) m
  rw [hcop.gcd_eq_one] at hbez_nat
  simp only [Nat.cast_one] at hbez_nat
  have hbez : (3 : ℤ) ^ e * ((3 ^ e).gcdA m) + (m : ℤ) * ((3 ^ e).gcdB m) = 1 := by
    push_cast at hbez_nat
    linarith
  let a : WeylGroup Tag.E6 := u ^ ((m : ℤ) * ((3 ^ e).gcdB m))
  let b : WeylGroup Tag.E6 := u ^ ((3 : ℤ) ^ e * ((3 ^ e).gcdA m))
  have ha3 : a ^ (3 ^ e) = 1 := by
    show (u ^ ((m : ℤ) * ((3 ^ e).gcdB m))) ^ (3 ^ e : ℕ) = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hexp : ((m : ℤ) * ((3 ^ e).gcdB m)) * ((3 ^ e : ℕ) : ℤ) = (orderOf u : ℤ) * ((3 ^ e).gcdB m) := by
      rw [hem]
      push_cast
      ring
    rw [hexp, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hbm : b ^ m = 1 := by
    show (u ^ ((3 : ℤ) ^ e * ((3 ^ e).gcdA m))) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hexp : ((3 : ℤ) ^ e * ((3 ^ e).gcdA m)) * (m : ℤ) = (orderOf u : ℤ) * ((3 ^ e).gcdA m) := by
      rw [hem]
      push_cast
      ring
    rw [hexp, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hu : u = b * a := by
    show u = u ^ ((3 : ℤ) ^ e * ((3 ^ e).gcdA m)) * u ^ ((m : ℤ) * ((3 ^ e).gcdB m))
    conv_lhs => rw [← zpow_one u]
    rw [← hbez, zpow_add]
  have hAord : orderOf a ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one ha3
  have hAp : IsPGroup 3 (Subgroup.zpowers a) := by
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hAord
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  have hbord : orderOf b ∣ m := orderOf_dvd_of_pow_eq_one hbm
  have hbCop : Nat.Coprime (orderOf b) 3 := by
    have h3 : ¬ 3 ∣ orderOf b := fun h => hm (h.trans hbord)
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  exact ⟨a, b, Subgroup.zpow_mem_zpowers u _, Subgroup.zpow_mem_zpowers u _,
    hu, hAp, hbCop⟩

theorem lemmaKCheck : LemmaKCheck := by
  intro Y hY u hu
  let Yset : Set (Fin 6 → ZMod 3) := (Y : Set (Fin 6 → ZMod 3))
  have hY81 : 81 ≤ Nat.card Yset := by
    have hcard : Nat.card Yset = Nat.card Y := rfl
    rw [hcard]
    have h34 : (3 : ℕ) ^ 4 = 81 := by norm_num
    rw [← h34]
    exact hY
  have huStab : u ∈ fixSub Yset := hu
  have hzpow_le : Subgroup.zpowers u ≤ fixSub Yset := Subgroup.zpowers_le.2 huStab
  obtain ⟨a, b, ha_mem, hb_mem, hu_ba, hAp, hbCop⟩ := exists_primary_decomp u
  have haStab : a ∈ fixSub Yset := hzpow_le ha_mem
  have hbStab : b ∈ fixSub Yset := hzpow_le hb_mem
  have hbR : b ∈ Subgroup.closure {s | ∃ α ∈ sigmaZ3 Yset, s = rootReflection α} :=
    mem_closure_sigmaZ3_of_coprime Yset hbStab hbCop
  have haR : a ∈ Subgroup.closure {s | ∃ α ∈ sigmaZ3 Yset, s = rootReflection α} := by
    obtain ⟨g, hg⟩ := exists_conj_le_lemKP hAp
    let p : WeylGroup Tag.E6 := g⁻¹ * a * g
    have hp : p ∈ lemKP := hg a (Subgroup.mem_zpowers a)
    let Y' : Set (Fin 6 → ZMod 3) := (fun y => e6WeylMat g⁻¹ *ᵥ y) '' Yset
    have hY'card : Nat.card Y' = Nat.card Yset :=
      Nat.card_image_of_injective (e6WeylMat_inv_mulVec_injective g) Yset
    have hY'81 : 81 ≤ Nat.card Y' := by rw [hY'card]; exact hY81
    have hfix' : ∀ y' ∈ Y', e6WeylMat p *ᵥ y' = y' := by
      rintro y' ⟨y, hy, rfl⟩
      exact e6WeylMat_conj_mulVec g a y (haStab y hy)
    rcases lemKP_special hp Y' hY'81 hfix' with hp1 | ⟨α, β, hα, hβ, hpαβ, hpairα, hpairβ⟩
    · have ha1 : a = 1 := by
        have hpg : g⁻¹ * a * g = 1 := hp1
        calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
          _ = g * 1 * g⁻¹ := by rw [hpg]
          _ = 1 := by group
      rw [ha1]
      exact Subgroup.one_mem _
    · have hpairα' : ∀ y ∈ Yset,
          ∑ i : Fin 6, (((g • α) (e6Idx i) : ℤ) : ZMod 3) * y i = 0 := by
        intro y hy
        rw [pairing_smul α g y]
        exact hpairα _ ⟨y, hy, rfl⟩
      have hpairβ' : ∀ y ∈ Yset,
          ∑ i : Fin 6, (((g • β) (e6Idx i) : ℤ) : ZMod 3) * y i = 0 := by
        intro y hy
        rw [pairing_smul β g y]
        exact hpairβ _ ⟨y, hy, rfl⟩
      have hαR : rootReflection (g • α) ∈
          Subgroup.closure {s | ∃ α ∈ sigmaZ3 Yset, s = rootReflection α} :=
        Subgroup.subset_closure ⟨g • α, ⟨IsRoot.smul hα g, hpairα'⟩, rfl⟩
      have hβR : rootReflection (g • β) ∈
          Subgroup.closure {s | ∃ α ∈ sigmaZ3 Yset, s = rootReflection α} :=
        Subgroup.subset_closure ⟨g • β, ⟨IsRoot.smul hβ g, hpairβ'⟩, rfl⟩
      have ha_eq : a = rootReflection (g • α) * rootReflection (g • β) := by
        rw [rootReflection_smul_root g hα, rootReflection_smul_root g hβ]
        have hpdef : p = g⁻¹ * a * g := rfl
        rw [hpαβ] at hpdef
        calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
          _ = g * (rootReflection α * rootReflection β) * g⁻¹ := by rw [← hpdef]
          _ = (g * rootReflection α * g⁻¹) * (g * rootReflection β * g⁻¹) := by group
      rw [ha_eq]
      exact Subgroup.mul_mem _ hαR hβR
  rw [hu_ba]
  exact Subgroup.mul_mem _ hbR haR

end Asm

end CFSG.StandardType.TwE6LemmaK
