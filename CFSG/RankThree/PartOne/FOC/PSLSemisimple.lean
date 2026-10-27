module

public import CFSG.RankThree.PartOne.FOC.PSLDecomp

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Matrix Subgroup CFSG
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCLinPlane
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Numeric

theorem dvd_of_not_pow {F : Type} [Field F] [Finite F] {p m : ℕ} (hp : p.Prime) {δ : Fˣ}
    (hδp : δ ^ p = 1) (hδ : ∀ μ : Fˣ, μ ^ m ≠ δ) : p ∣ m ∧ p ∣ Nat.card Fˣ := by
  constructor
  · by_contra hpm
    have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
    obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    apply hδ (δ ^ r)
    have h1 : m * r = p * (m * r / p) + 1 := by
      have := Nat.div_add_mod (m * r) p
      rw [hr] at this
      omega
    rw [← pow_mul, mul_comm r m, h1, pow_add, pow_mul, hδp, one_pow, one_mul, pow_one]
  · by_contra hpc
    have h1 : orderOf δ ∣ p := orderOf_dvd_of_pow_eq_one hδp
    have h2 : orderOf δ ∣ Nat.card Fˣ := orderOf_dvd_natCard δ
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · have hδ1 : δ = 1 := orderOf_eq_one_iff.mp h
      exact hδ 1 (by rw [one_pow, hδ1])
    · exact hpc (h ▸ h2)

end Numeric

section Block

open scoped _root_.Classical

variable {n : ℕ} {K : Type} [Field K] [Finite K] {A : Matrix.SpecialLinearGroup (Fin n) K}

omit [Finite K] in
theorem mem_sup_of_det_eq_pow {hsq : Squarefree (minpoly K (slEnd A))}
    {b : primaryFactors (slEnd A)} (hb : GoodBlock b)
    {w : PiGL (Efac (slEnd A)) (mult (slEnd A))}
    {B : Matrix.SpecialLinearGroup (Fin n) K}
    (hwB : blockTheta hsq w = Matrix.SpecialLinearGroup.toGL B)
    {μ : (Efac (slEnd A) b)ˣ}
    (hμ : GeneralLinearGroup.det (w b) = μ ^ mult (slEnd A) b) :
    proj n K B ∈ Qb hsq b ⊔ Subgroup.centralizer (Qb hsq b : Set (projectiveSL n K)) := by
  set m := mult (slEnd A) b with hm
  set sμ : GL (Fin m) (Efac (slEnd A) b) := GeneralLinearGroup.scalar (Fin m) μ with hsμ
  have hs₀det : GeneralLinearGroup.det (w b * sμ⁻¹) = 1 := by
    rw [map_mul, map_inv, hsμ, hμ]
    have : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin m) μ) = μ ^ m := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar]
      simp [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Units.val_pow_eq_pow_val]
    rw [this, mul_inv_cancel]
  obtain ⟨s, hs⟩ : w b * sμ⁻¹ ∈
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin m) (Efac (slEnd A) b) →* _).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hs₀det
  set w' : PiGL (Efac (slEnd A)) (mult (slEnd A)) := Function.update w b sμ with hw'
  have hw : w = blockEmbed (Efac (slEnd A)) (mult (slEnd A)) b s * w' := by
    funext c
    by_cases hc : c = b
    · subst hc
      simp only [Pi.mul_apply, blockEmbed_apply_self, hw', Function.update_self, hs]
      group
    · simp only [Pi.mul_apply, blockEmbed_apply_of_ne hc, hw', Function.update_of_ne hc, one_mul]
  have hmemf : blockTheta hsq (blockEmbed (Efac (slEnd A)) (mult (slEnd A)) b s) ∈
      blockImage hsq b := mem_blockImage.mpr ⟨s, rfl⟩
  obtain ⟨f, hf⟩ := blockImage_le_range_toGL_of_good hsq b hb hmemf
  have hfB : f ∈ blkSL hsq b := by
    rw [mem_blkSL, hf]
    exact hmemf
  obtain ⟨C', hC'⟩ : ∃ C' : Matrix.SpecialLinearGroup (Fin n) K, C' = f⁻¹ * B := ⟨_, rfl⟩
  have hBfC : B = f * C' := by rw [hC']; group
  have hC'w : Matrix.SpecialLinearGroup.toGL C' = blockTheta hsq w' := by
    rw [hC', map_mul, map_inv, hf, ← hwB, hw, map_mul]
    group
  have hC'comm : ∀ q ∈ blkSL hsq b, C' * q = q * C' := by
    intro q hq
    obtain ⟨t, ht⟩ : ∃ t : Matrix.SpecialLinearGroup (Fin m) (Efac (slEnd A) b),
        blockTheta hsq (blockEmbed (Efac (slEnd A)) (mult (slEnd A)) b t) =
          Matrix.SpecialLinearGroup.toGL q := by
      have := (mem_blkSL.mp hq)
      obtain ⟨t, ht⟩ := mem_blockImage.mp this
      exact ⟨t, ht⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, hC'w, ← ht, ← map_mul, ← map_mul]
    congr 1
    funext c
    by_cases hc : c = b
    · subst hc
      simp only [Pi.mul_apply, blockEmbed_apply_self, hw', Function.update_self]
      exact GeneralLinearGroup.scalar_commute μ _
    · simp only [Pi.mul_apply, blockEmbed_apply_of_ne hc, hw', Function.update_of_ne hc, mul_one,
        one_mul]
  have hfm : proj n K f ∈ Qb hsq b := ⟨f, hfB, rfl⟩
  have hcm : proj n K C' ∈ Subgroup.centralizer (Qb hsq b : Set (projectiveSL n K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul, hC'comm q hq]
  rw [hBfC, map_mul]
  exact Subgroup.mul_mem_sup hfm hcm

end Block

section Final

open scoped _root_.Classical

variable {n : ℕ} {K : Type} [Field K] [Finite K] {A : Matrix.SpecialLinearGroup (Fin n) K}

@[expose] noncomputable def blockToGL (hsq : Squarefree (minpoly K (slEnd A)))
    (b : primaryFactors (slEnd A)) :
    Matrix.SpecialLinearGroup (Fin (mult (slEnd A) b)) (Efac (slEnd A) b) →* GL (Fin n) K :=
  (blockTheta hsq).comp (blockEmbed (Efac (slEnd A)) (mult (slEnd A)) b)

omit [Finite K] in
theorem blockToGL_injective (hsq : Squarefree (minpoly K (slEnd A)))
    (b : primaryFactors (slEnd A)) : Function.Injective (blockToGL hsq b) :=
  (blockTheta_injective hsq).comp (blockEmbed_injective b)

@[expose] noncomputable def blockToSL (hsq : Squarefree (minpoly K (slEnd A)))
    {b : primaryFactors (slEnd A)} (hb : GoodBlock b) :
    Matrix.SpecialLinearGroup (Fin (mult (slEnd A) b)) (Efac (slEnd A) b) →*
      Matrix.SpecialLinearGroup (Fin n) K :=
  (MonoidHom.ofInjective (Matrix.SpecialLinearGroup.toGL_injective (n := Fin n) (R := K))).symm.toMonoidHom.comp
    ((blockToGL hsq b).codRestrict
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range
      (fun s => blockImage_le_range_toGL_of_good hsq b hb (mem_blockImage.mpr ⟨s, rfl⟩)))

omit [Finite K] in
theorem toGL_blockToSL (hsq : Squarefree (minpoly K (slEnd A))) {b : primaryFactors (slEnd A)}
    (hb : GoodBlock b)
    (s : Matrix.SpecialLinearGroup (Fin (mult (slEnd A) b)) (Efac (slEnd A) b)) :
    Matrix.SpecialLinearGroup.toGL (blockToSL hsq hb s) = blockToGL hsq b s := by
  have h := (MonoidHom.ofInjective (Matrix.SpecialLinearGroup.toGL_injective (n := Fin n) (R := K))).apply_symm_apply
    ⟨blockToGL hsq b s, blockImage_le_range_toGL_of_good hsq b hb (mem_blockImage.mpr ⟨s, rfl⟩)⟩
  exact congrArg Subtype.val h

omit [Finite K] in
theorem blockToSL_injective (hsq : Squarefree (minpoly K (slEnd A))) {b : primaryFactors (slEnd A)}
    (hb : GoodBlock b) : Function.Injective (blockToSL hsq hb) := by
  intro s t h
  apply blockToGL_injective hsq b
  rw [← toGL_blockToSL hsq hb, ← toGL_blockToSL hsq hb, h]

theorem not_localRankLeTwo_of_good_block {p : ℕ} (hp : p.Prime)
    (hsq : Squarefree (minpoly K (slEnd A))) {b : primaryFactors (slEnd A)} (hb : GoodBlock b)
    (hm5 : 5 ≤ mult (slEnd A) b) (hpF : p ∣ Nat.card (Efac (slEnd A) b)ˣ) :
    ¬ LocalRankLeTwo p (projectiveSL n K) := by
  refine not_localRankLeTwo_of_SL_hom hp hm5 hpF ((proj n K).comp (blockToSL hsq hb)) ?_
  intro s hs
  have hc : blockToSL hsq hb s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hs
  rw [Subgroup.mem_center_iff]
  intro t
  apply blockToSL_injective hsq hb
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hc (blockToSL hsq hb t)

theorem mem_sup_centralizer_of_component_psl {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : (p : K) ≠ 0) (hn : 1 ≤ n) (hrank : LocalRankLeTwo p (projectiveSL n K))
    {b x : projectiveSL n K} (hbp : b ^ p = 1) (hxp : x ^ p = 1) (hbx : b * x = x * b)
    {E : Subgroup (projectiveSL n K)}
    (hE : IsComponentOf (Subgroup.centralizer ({b} : Set (projectiveSL n K))) E) :
    x ∈ E ⊔ Subgroup.centralizer (E : Set (projectiveSL n K)) := by
  have hZ := not_dvd_card_scalars_of_localRankLeTwo hp hp5 hn hrank
  obtain ⟨A, rfl, hAp⟩ := exists_lift_pow_eq_one hp hZ hbp
  obtain ⟨B, rfl, hBp⟩ := exists_lift_pow_eq_one hp hZ hxp
  have hAB : A * B = B * A := commute_of_proj_commute hp hZ hAp hbx
  have hsq := squarefree_slEnd hpK hAp
  obtain ⟨b₁, hgood, rfl⟩ := exists_good_block_of_component hp hZ hAp hsq hE
  have hBmem : Matrix.SpecialLinearGroup.toGL B ∈ (blockTheta hsq).range := by
    rw [range_blockTheta, range_commutantUnitsToGL_eq_centralizer (x := slEnd A)
      (Matrix.SpecialLinearGroup.toGL A) rfl]
    exact toGL_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.mpr hAB.symm)
  obtain ⟨w, hw⟩ := hBmem
  have hwp : w ^ p = 1 := by
    apply blockTheta_injective hsq
    rw [map_pow, hw, ← map_pow, hBp, map_one, map_one]
  by_contra hnot
  have hδp : GeneralLinearGroup.det (w b₁) ^ p = 1 := by
    rw [← map_pow]
    have := congrFun hwp b₁
    simpa using congrArg GeneralLinearGroup.det this
  have hδ : ∀ μ : (Efac (slEnd A) b₁)ˣ, μ ^ mult (slEnd A) b₁ ≠ GeneralLinearGroup.det (w b₁) :=
    fun μ hμ => hnot (mem_sup_of_det_eq_pow hgood hw hμ.symm)
  obtain ⟨hpm, hpF⟩ := dvd_of_not_pow hp hδp hδ
  have hm2 : 2 ≤ mult (slEnd A) b₁ := by
    unfold GoodBlock at hgood
    omega
  have hm5 : 5 ≤ mult (slEnd A) b₁ := hp5.trans (Nat.le_of_dvd (by omega) hpm)
  exact not_localRankLeTwo_of_good_block hp hsq hgood hm5 hpF hrank

end Final

end CFSG.RankThree.PartOne.FOC
