module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.ClassicalGroups.Unitary.Generation
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSUTv
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsJ
import CFSG.Open.StatedAPI
import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockUnitary
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfPSU
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Timmesfeld.Bridge.Asc72Triangle
import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped Matrix MatrixGroups

section CharTwo

variable {F : Type} [Field F] [CharP F 2]

private theorem one_add_map_one (σ : F ≃+* F) : (1 : F) + σ 1 = 0 := by
  rw [map_one]
  exact CharTwo.add_self_eq_zero 1

end CharTwo

section Geometry

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem exists_smul_eq_of_hyperbolic_pair (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 3 ≤ n)
    {a b a' b' : Fin n → F} (ha : herm σ a a = 0) (hb : herm σ b b = 0)
    (hab : herm σ a b = 1) (ha' : herm σ a' a' = 0) (hb' : herm σ b' b' = 0)
    (hab' : herm σ a' b' = 1) : ∃ g : SUid σ n, g • a = a' ∧ g • b = b' := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hab
    exact zero_ne_one hab
  have ha0' : a' ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hab'
    exact zero_ne_one hab'
  obtain ⟨t, -, hta⟩ := exists_mem_T_smul_eq_of_iso hσ hn ha0 ha ha0' ha'
  obtain ⟨b₁, hb₁def⟩ : ∃ b₁, b₁ = t • b := ⟨_, rfl⟩
  have hb₁ : herm σ b₁ b₁ = 0 := by rw [hb₁def, herm_smul_smul, hb]
  have hab₁ : herm σ a' b₁ = 1 := by rw [← hta, hb₁def, herm_smul_smul, hab]
  obtain ⟨d, hd⟩ : ∃ d, d = b' - b₁ := ⟨_, rfl⟩
  have hdp : herm σ a' d = 0 := by rw [hd, herm_sub_right, hab', hab₁, sub_self]
  have hb'eq : b' = b₁ + d := by rw [hd]; abel
  have hc : herm σ d b₁ + σ (herm σ d b₁) = -herm σ d d := by
    have h1 : herm σ (b₁ + d) (b₁ + d) = 0 := by rw [← hb'eq]; exact hb'
    simp only [herm_add_left, herm_add_right, hb₁] at h1
    rw [herm_conj σ hσ.invol d b₁] at h1
    linear_combination h1
  refine ⟨eichler hσ.invol ha' hdp hc * t, ?_, ?_⟩
  · rw [mul_smul, hta, eichler_smul_self]
  · rw [mul_smul, ← hb₁def, eichler_smul, hab₁, one_smul, hb'eq]
    module

end Geometry

section Torus

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

theorem exists_mem_T_smul_eq_smul_of_fixed (hσ : IsUnitaryInvolution σ) {n : ℕ} {a : Fin n → F}
    (ha0 : a ≠ 0) (ha : herm σ a a = 0) {l : F} (hl0 : l ≠ 0) (hl : σ l = l) :
    ∃ t ∈ T σ n, t • a = l • a := by
  obtain ⟨b, hb, hab⟩ := exists_partner hσ ha0 ha
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ.invol, hab, map_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hx₁ : (l - 1) + σ (l - 1) = 0 := by
    rw [map_sub, map_one, hl]
    linear_combination (l - 1) * h2
  have hx₂ : (l⁻¹ - 1) + σ (l⁻¹ - 1) = 0 := by
    rw [map_sub, map_one, map_inv₀, hl]
    linear_combination (l⁻¹ - 1) * h2
  have hy₁ : (1 : F) + σ 1 = 0 := one_add_map_one σ
  have hy₂ : l + σ l = 0 := by
    rw [hl]
    linear_combination l * h2
  refine ⟨tv hσ.invol ha hx₁ * tv hσ.invol hb hy₁ * tv hσ.invol ha hx₂ * tv hσ.invol hb hy₂,
    (T σ n).mul_mem ((T σ n).mul_mem ((T σ n).mul_mem (tv_mem_T _ _ _) (tv_mem_T _ _ _))
      (tv_mem_T _ _ _)) (tv_mem_T _ _ _), ?_⟩
  rw [mul_smul, mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, tv_smul]
  simp only [herm_add_right, herm_smul_right, ha, hb, hab, hba, mul_zero, add_zero, mul_one]
  have hll : (l⁻¹ - 1) * l = 1 - l := by rw [sub_mul, inv_mul_cancel₀ hl0, one_mul]
  simp only [zero_add, hll]
  match_scalars
  · ring
  · linear_combination h2

end Torus

section Conj

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

private theorem exists_fixed_mul_self_eq {d : F} (hd : σ d = d) (hd0 : d ≠ 0) :
    ∃ l : F, l ≠ 0 ∧ σ l = l ∧ l * l = d := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) d
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hd0 (by rw [hr, mul_zero])
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hσr : σ r = r := by
    have h1 : σ r * σ r = r * r := by rw [← map_mul, ← hr, hd, hr]
    have h3 : (σ r + r) * (σ r + r) = 0 := by linear_combination h1 + (σ r * r + r * r) * h2
    have h4 : σ r + r = 0 := mul_self_eq_zero.mp h3
    linear_combination h4 + (-r) * h2
  exact ⟨r, hr0, hσr, hr.symm⟩

theorem exists_suTv_smul_eq (hσ : IsUnitaryInvolution σ) {n : ℕ} {a a' : Fin n → F}
    (ha0 : a ≠ 0) (ha : herm σ a a = 0) (ha0' : a' ≠ 0) (ha' : herm σ a' a' = 0) :
    ∃ t : SUid σ n, suTv hσ (t • a) 1 = suTv hσ a' 1 := by
  obtain ⟨d, hd, had, ha'd⟩ := exists_cno hσ ha0 ha ha0'
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have step : ∀ x : Fin n → F, herm σ x x = 0 → herm σ x d ≠ 0 →
      ∃ t ∈ T σ n, ∃ c : F, c ≠ 0 ∧ t • x = c • d := by
    intro x hx hxd
    have hs0 : τ / herm σ x d ≠ 0 := div_ne_zero hτ0 hxd
    have hb : herm σ ((τ / herm σ x d) • d) ((τ / herm σ x d) • d) = 0 := by
      rw [herm_smul_left, herm_smul_right, hd]
      ring
    have hxb : herm σ x ((τ / herm σ x d) • d) = τ := by
      rw [herm_smul_right]
      field_simp
    obtain ⟨t, ht, htx⟩ := exists_mem_T_smul_of_traceZero hσ.invol hx hb
      (by rw [hxb]; exact hτ0) (by rw [hxb]; exact hτ)
    exact ⟨t, ht, τ / herm σ x d, hs0, htx⟩
  obtain ⟨t₁, -, c₁, hc₁, ht₁⟩ := step a ha had
  obtain ⟨t₂, -, c₂, hc₂, ht₂⟩ := step a' ha' ha'd
  have ht₃ : (t₂⁻¹ * t₁) • a = (c₁ * c₂⁻¹) • a' := by
    have hd' : t₂⁻¹ • d = c₂⁻¹ • a' := by
      rw [inv_smul_eq_iff, smul_comm, ht₂, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
    rw [mul_smul, ht₁, smul_comm, hd', smul_smul]
  have hc : c₁ * c₂⁻¹ ≠ 0 := mul_ne_zero hc₁ (inv_ne_zero hc₂)
  set c := c₁ * c₂⁻¹ with hcdef
  have hN0 : σ c * c ≠ 0 := mul_ne_zero ((map_ne_zero σ).mpr hc) hc
  obtain ⟨l, hl0, hσl, hll⟩ := exists_fixed_mul_self_eq
    (d := (σ c * c)⁻¹) (by rw [map_inv₀, hσ.norm_fixed]) (inv_ne_zero hN0)
  obtain ⟨t₄, -, ht₄⟩ := exists_mem_T_smul_eq_smul_of_fixed hσ ha0' ha' hl0 hσl
  refine ⟨t₄ * (t₂⁻¹ * t₁), ?_⟩
  have h1 : (1 : F) + σ 1 = 0 := one_add_map_one σ
  rw [mul_smul, ht₃, smul_comm, ht₄, smul_smul, suTv_smul_vec hσ ha' h1, map_mul, hσl]
  congr 1
  rw [mul_one]
  calc σ c * l * (c * l) = (σ c * c) * (l * l) := by ring
    _ = 1 := by rw [hll, mul_inv_cancel₀ hN0]

end Conj

section Block

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem map_blockSel (m k i : ℕ) :
    (blockSel F m k i).map σ = blockSel F m k i := by
  ext a j
  simp only [Matrix.map_apply, blockSel_apply]
  split_ifs <;> simp

private theorem herm_blockSel_mulVec {m k i : ℕ} (x : Fin k → F) (y : Fin m → F) :
    herm σ (blockSel F m k i *ᵥ x) y = herm σ x ((blockSel F m k i)ᵀ *ᵥ y) := by
  have hL := map_blockSel (F := F) (σ := σ) m k i
  have h1 : (fun a => σ ((blockSel F m k i *ᵥ x) a)) =
      blockSel F m k i *ᵥ fun j => σ (x j) := by
    funext a
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (congrFun hL a) j
    simp only [Matrix.map_apply] at this
    rw [this]
  have e1 : herm σ (blockSel F m k i *ᵥ x) y =
      (fun a => σ ((blockSel F m k i *ᵥ x) a)) ⬝ᵥ y := rfl
  have e2 : herm σ x ((blockSel F m k i)ᵀ *ᵥ y) =
      (fun j => σ (x j)) ⬝ᵥ ((blockSel F m k i)ᵀ *ᵥ y) := rfl
  rw [e1, e2, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

private theorem herm_blockSel_blockSel {m k i : ℕ} (h : i + k ≤ m) (x y : Fin k → F) :
    herm σ (blockSel F m k i *ᵥ x) (blockSel F m k i *ᵥ y) = herm σ x y := by
  rw [herm_blockSel_mulVec, Matrix.mulVec_mulVec, blockSel_transpose_mul_self h,
    Matrix.one_mulVec]

private theorem blockSel_mulVec_transpose {k : ℕ} (y : Fin (k + 2) → F) (h0 : y 0 = 0)
    (h1 : y 1 = 0) :
    blockSel F (k + 2) k 2 *ᵥ ((blockSel F (k + 2) k 2)ᵀ *ᵥ y) = y := by
  have hk : 2 + k ≤ k + 2 := by omega
  funext a
  rw [blockSel_mulVec]
  by_cases ha : 2 ≤ a.val ∧ a.val < 2 + k
  · rw [dif_pos ha, blockSel_transpose_mulVec hk]
    congr 1
    ext
    simp only [blockIdx_val]
    omega
  · rw [dif_neg ha]
    have : a.val < 2 := by
      have := a.isLt
      omega
    interval_cases hv : a.val
    · have : a = 0 := Fin.ext hv
      rw [this, h0]
    · have : a = 1 := Fin.ext hv
      rw [this, h1]

private theorem blockSel_mulVec_zero_one {k : ℕ} (v : Fin k → F) :
    (blockSel F (k + 2) k 2 *ᵥ v) 0 = 0 ∧ (blockSel F (k + 2) k 2 *ᵥ v) 1 = 0 := by
  rw [blockSel_mulVec, blockSel_mulVec]
  refine ⟨dif_neg ?_, dif_neg ?_⟩ <;> simp

private theorem blockSel_mulVec_injective {k : ℕ} :
    Function.Injective (fun v : Fin k → F => blockSel F (k + 2) k 2 *ᵥ v) := by
  intro v w hvw
  have hk : 2 + k ≤ k + 2 := by omega
  have h1 := congrArg (fun y => (blockSel F (k + 2) k 2)ᵀ *ᵥ y) hvw
  simpa only [Matrix.mulVec_mulVec, blockSel_transpose_mul_self hk, Matrix.one_mulVec] using h1

end Block

section Embed

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem blockEmb_smul {m k i : ℕ} (h : i + k ≤ m) (A : Su F 2 n k) (v : Fin m → F) :
    blockEmb F 2 n m k i h A • v = v + blockSel F m k i *ᵥ
      ((((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) - 1) *ᵥ ((blockSel F m k i)ᵀ *ᵥ v)) := by
  rw [smul_def]
  change blockMat m i ((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) *ᵥ v = _
  unfold blockMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private theorem blockEmb_suTv (hσ : IsUnitaryInvolution (unitaryInvolution F 2 n)) {m k : ℕ}
    (h : 2 + k ≤ m) {e : Fin k → F} (he : herm (unitaryInvolution F 2 n) e e = 0) {s : F}
    (hs : s + unitaryInvolution F 2 n s = 0) :
    blockEmb F 2 n m k 2 h (suTv hσ e s) = suTv hσ (blockSel F m k 2 *ᵥ e) s := by
  apply ext_smul
  intro v
  have hLe : herm (unitaryInvolution F 2 n) (blockSel F m k 2 *ᵥ e) (blockSel F m k 2 *ᵥ e) =
      0 := by
    rw [herm_blockSel_blockSel h, he]
  have hA : ∀ y : Fin k → F, ((((suTv hσ e s : SUid (unitaryInvolution F 2 n) k) : GL (Fin k) F) :
      Matrix (Fin k) (Fin k) F) - 1) *ᵥ y = (s * herm (unitaryInvolution F 2 n) e y) • e := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← smul_def, suTv_smul hσ he hs, add_sub_cancel_left]
  rw [blockEmb_smul, suTv_smul hσ hLe hs, herm_blockSel_mulVec, hA, Matrix.mulVec_smul]

private theorem blockEmb_smul_single {k : ℕ} (h : 2 + k ≤ k + 2) (A : Su F 2 n k) :
    blockEmb F 2 n (k + 2) k 2 h A • (Pi.single 0 1 : Fin (k + 2) → F) = Pi.single 0 1 := by
  have hT : (blockSel F (k + 2) k 2)ᵀ *ᵥ (Pi.single 0 1 : Fin (k + 2) → F) = 0 := by
    funext y
    rw [blockSel_transpose_mulVec h]
    simp [blockIdx, Fin.ext_iff]
  rw [blockEmb_smul, hT, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

end Embed

section Hom

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

local notation "σ₂" => unitaryInvolution F 2 n

private theorem exists_hom_perp (hF : Nat.card F = (2 ^ n) ^ 2) {k : ℕ} (hk : 1 ≤ k)
    {p q : Fin (k + 2) → F} (hp : herm σ₂ p p = 0) (hq : herm σ₂ q q = 0)
    (hpq : herm σ₂ p q = 1) :
    ∃ Θ : SUid σ₂ k →* StatedProj (StatedSU (k + 2) (2 ^ n) F), Function.Injective Θ ∧
      (∀ v : Fin k → F, herm σ₂ v v = 0 → ∀ s : F, s + σ₂ s = 0 →
        ∃ e : Fin (k + 2) → F, herm σ₂ e e = 0 ∧ herm σ₂ e p = 0 ∧ herm σ₂ e q = 0 ∧
          (v ≠ 0 → e ≠ 0) ∧ Θ (suTv (isUnitaryInvolution_unitaryInvolution hF) v s) =
            kFactsSuProjTv hF (k + 2) e s) ∧
      (∀ e : Fin (k + 2) → F, e ≠ 0 → herm σ₂ e e = 0 → herm σ₂ e p = 0 → herm σ₂ e q = 0 →
        ∃ v : Fin k → F, v ≠ 0 ∧ herm σ₂ v v = 0 ∧
          Θ (suTv (isUnitaryInvolution_unitaryInvolution hF) v 1) =
            kFactsSuProjTv hF (k + 2) e 1) := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hinv := hσ.invol
  have hkk : 2 + k ≤ k + 2 := by omega
  obtain ⟨W⟩ := hσ.nonempty_wittData
  obtain ⟨g, hg1, hg2⟩ := exists_smul_eq_of_hyperbolic_pair hσ (by omega : 3 ≤ k + 2)
    (W.herm_hypA_hypA (m := k)) (W.herm_hypB_hypB (m := k)) (W.herm_hypA_hypB (m := k)) hp hq hpq
  let Θ₀ : SUid σ₂ k →* SUid σ₂ (k + 2) :=
    (MulAut.conj g).toMonoidHom.comp (blockEmb F 2 n (k + 2) k 2 hkk)
  have hΘ₀ : ∀ (v : Fin k → F) (s : F), herm σ₂ v v = 0 → s + σ₂ s = 0 →
      Θ₀ (suTv hσ v s) = suTv hσ (g • (blockSel F (k + 2) k 2 *ᵥ v)) s := by
    intro v s hv hs
    change g * blockEmb F 2 n (k + 2) k 2 hkk (suTv hσ v s) * g⁻¹ = _
    rw [blockEmb_suTv hσ hkk hv hs, suTv_conj hσ g (by rw [herm_blockSel_blockSel hkk, hv]) hs]
  have hΘ : ∀ (v : Fin k → F) (s : F), herm σ₂ v v = 0 → s + σ₂ s = 0 →
      (kFactsSuProj hF (k + 2)).comp Θ₀ (suTv hσ v s) =
        kFactsSuProjTv hF (k + 2) (g • (blockSel F (k + 2) k 2 *ᵥ v)) s := by
    intro v s hv hs
    change kFactsSuProj hF (k + 2) (Θ₀ (suTv hσ v s)) = _
    rw [hΘ₀ v s hv hs]
    rfl
  have h1 : (1 : F) + σ₂ 1 = 0 := one_add_map_one σ₂
  have hLperp : ∀ v : Fin k → F, herm σ₂ (blockSel F (k + 2) k 2 *ᵥ v) (W.hypA k) = 0 ∧
      herm σ₂ (blockSel F (k + 2) k 2 *ᵥ v) (W.hypB k) = 0 := by
    intro v
    obtain ⟨h0, h1⟩ := blockSel_mulVec_zero_one (F := F) v
    refine ⟨herm_eq_zero_comm σ₂ hinv ?_, herm_eq_zero_comm σ₂ hinv ?_⟩
    · rw [W.herm_hypA_left, h0, h1]
      simp
    · rw [W.herm_hypB_left, h0, h1]
      simp
  have hperp : ∀ v : Fin k → F, herm σ₂ (g • (blockSel F (k + 2) k 2 *ᵥ v)) p = 0 ∧
      herm σ₂ (g • (blockSel F (k + 2) k 2 *ᵥ v)) q = 0 := by
    intro v
    obtain ⟨h1, h2⟩ := hLperp v
    exact ⟨by rw [← hg1, herm_smul_smul]; exact h1, by rw [← hg2, herm_smul_smul]; exact h2⟩
  refine ⟨(kFactsSuProj hF (k + 2)).comp Θ₀, ?_, ?_, ?_⟩
  ·
    rw [injective_iff_map_eq_one]
    intro A hA
    have hA' : kFactsSuProj hF (k + 2) (Θ₀ A) = kFactsSuProj hF (k + 2) 1 := by
      rw [map_one]
      exact hA
    obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF _ _).mp hA'
    have hΘv : ∀ v : Fin (k + 2) → F, (u : F) • (Θ₀ A • v) = v := by
      intro v
      have h3 : Θ₀ A • ((u : F) • v) = v := by
        calc Θ₀ A • ((u : F) • v)
            = ((((Θ₀ A : SUid σ₂ (k + 2)) : GL (Fin (k + 2)) F) :
                Matrix (Fin (k + 2)) (Fin (k + 2)) F) * ((u : F) • 1)) *ᵥ v := by
              rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
              rfl
          _ = ((((1 : SUid σ₂ (k + 2)) : GL (Fin (k + 2)) F) :
                Matrix (Fin (k + 2)) (Fin (k + 2)) F)) *ᵥ v := by rw [hu]
          _ = v := by
              change (1 : SUid σ₂ (k + 2)) • v = v
              exact one_smul _ _
      rw [smul_comm, h3]
    have hB : ∀ v : Fin (k + 2) → F,
        (u : F) • (blockEmb F 2 n (k + 2) k 2 hkk A • v) = v := by
      intro v
      have hconj : blockEmb F 2 n (k + 2) k 2 hkk A = g⁻¹ * Θ₀ A * g := by
        change _ = g⁻¹ * (g * blockEmb F 2 n (k + 2) k 2 hkk A * g⁻¹) * g
        group
      rw [hconj, mul_smul, mul_smul, smul_comm (u : F) g⁻¹, hΘv, inv_smul_smul]
    have hu1 : (u : F) = 1 := by
      have h4 := hB (Pi.single 0 1)
      rw [blockEmb_smul_single hkk A] at h4
      have h5 := congrFun h4 0
      simpa using h5
    have hBone : blockEmb F 2 n (k + 2) k 2 hkk A = 1 := by
      apply ext_smul
      intro v
      have h6 := hB v
      rw [hu1, one_smul] at h6
      exact h6.trans (one_smul _ v).symm
    exact blockEmb_injective (K := F) (p := 2) (f := n) hkk (hBone.trans (map_one _).symm)
  · intro v hv s hs
    refine ⟨g • (blockSel F (k + 2) k 2 *ᵥ v), ?_, (hperp v).1, (hperp v).2, ?_, hΘ v s hv hs⟩
    · rw [herm_smul_smul, herm_blockSel_blockSel hkk, hv]
    · intro hv0 h0
      apply hv0
      refine blockSel_mulVec_injective (a₁ := v) (a₂ := 0) ?_
      show blockSel F (k + 2) k 2 *ᵥ v = blockSel F (k + 2) k 2 *ᵥ 0
      rw [Matrix.mulVec_zero]
      exact (smul_eq_zero_iff_eq g).mp h0
  · intro e he0 he hep heq
    have hgp : g⁻¹ • p = W.hypA k := by rw [← hg1, inv_smul_smul]
    have hgq : g⁻¹ • q = W.hypB k := by rw [← hg2, inv_smul_smul]
    have hya : herm σ₂ (W.hypA k) (g⁻¹ • e) = 0 := by
      refine herm_eq_zero_comm σ₂ hinv ?_
      rw [← hgp, herm_smul_smul]
      exact hep
    have hyb : herm σ₂ (W.hypB k) (g⁻¹ • e) = 0 := by
      refine herm_eq_zero_comm σ₂ hinv ?_
      rw [← hgq, herm_smul_smul]
      exact heq
    obtain ⟨hy0, hy1⟩ := W.coord_eq_zero_of_perp hya hyb
    have hL := blockSel_mulVec_transpose (g⁻¹ • e) hy0 hy1
    have hv : herm σ₂ ((blockSel F (k + 2) k 2)ᵀ *ᵥ (g⁻¹ • e))
        ((blockSel F (k + 2) k 2)ᵀ *ᵥ (g⁻¹ • e)) = 0 := by
      rw [← herm_blockSel_blockSel hkk, hL, herm_smul_smul, he]
    have hge : g • (blockSel F (k + 2) k 2 *ᵥ ((blockSel F (k + 2) k 2)ᵀ *ᵥ (g⁻¹ • e))) = e := by
      rw [hL, smul_inv_smul]
    refine ⟨(blockSel F (k + 2) k 2)ᵀ *ᵥ (g⁻¹ • e), ?_, hv, ?_⟩
    · intro h0
      apply he0
      rw [← hge, h0]
      simp
    · rw [hΘ _ 1 hv h1, hge]

end Hom

section Classes

open CFSG.LieType.BorelTits CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

local notation "σ₂" => unitaryInvolution F 2 n

private theorem isConj_kFactsSuProjTv_iff (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {a : Fin m → F} (ha0 : a ≠ 0) (ha : herm σ₂ a a = 0)
    (x : StatedProj (StatedSU m (2 ^ n) F)) :
    IsConj (kFactsSuProjTv hF m a 1) x ↔
      ∃ e : Fin m → F, e ≠ 0 ∧ herm σ₂ e e = 0 ∧ x = kFactsSuProjTv hF m e 1 := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + σ₂ 1 = 0 := one_add_map_one σ₂
  constructor
  · intro h
    obtain ⟨c, rfl⟩ := isConj_iff.mp h
    obtain ⟨g, rfl⟩ := kFacts_suProj_surjective hF m c
    refine ⟨g • a, ?_, ?_, kFacts_suProj_conj_suProjTv hF g ha h1⟩
    · intro h0
      exact ha0 ((smul_eq_zero_iff_eq g).mp h0)
    · rw [herm_smul_smul, ha]
  · rintro ⟨e, he0, he, rfl⟩
    obtain ⟨t, ht⟩ := exists_suTv_smul_eq hσ ha0 ha he0 he
    refine isConj_iff.mpr ⟨kFactsSuProj hF m t, ?_⟩
    rw [kFacts_suProj_conj_suProjTv hF t ha h1]
    unfold kFactsSuProjTv
    rw [ht]

private theorem mem_commonCommute_iff (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 3 ≤ m)
    {a p q : Fin m → F} (ha0 : a ≠ 0) (ha : herm σ₂ a a = 0) (hp : herm σ₂ p p = 0)
    (hq : herm σ₂ q q = 0) (x : StatedProj (StatedSU m (2 ^ n) F)) :
    (IsConj (kFactsSuProjTv hF m a 1) x ∧ Commute x (kFactsSuProjTv hF m p 1) ∧
        Commute x (kFactsSuProjTv hF m q 1)) ↔
      ∃ e : Fin m → F, e ≠ 0 ∧ herm σ₂ e e = 0 ∧ herm σ₂ e p = 0 ∧ herm σ₂ e q = 0 ∧
        x = kFactsSuProjTv hF m e 1 := by
  have h1 : (1 : F) + σ₂ 1 = 0 := one_add_map_one σ₂
  constructor
  · rintro ⟨hx, hxp, hxq⟩
    obtain ⟨e, he0, he, rfl⟩ := (isConj_kFactsSuProjTv_iff hF ha0 ha x).mp hx
    exact ⟨e, he0, he, herm_eq_zero_of_commute_kFactsSuProjTv hF hm he0 he hp hxp,
      herm_eq_zero_of_commute_kFactsSuProjTv hF hm he0 he hq hxq, rfl⟩
  · rintro ⟨e, he0, he, hep, heq, rfl⟩
    exact ⟨(isConj_kFactsSuProjTv_iff hF ha0 ha _).mpr ⟨e, he0, he, rfl⟩,
      kFacts_suProjTv_comm_of_herm_eq_zero hF he hp hep h1 h1,
      kFacts_suProjTv_comm_of_herm_eq_zero hF he hq heq h1 h1⟩

end Classes

section Core

open CFSG.LieType.BorelTits CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

local notation "σ₂" => unitaryInvolution F 2 n

omit [Finite F] [CharP F 2] in
private theorem rank_vecMulVec_eq_one {m : ℕ} {u w : Fin m → F} (hu : u ≠ 0) (hw : w ≠ 0) :
    (Matrix.vecMulVec u w).rank = 1 := by
  apply le_antisymm (Matrix.rank_vecMulVec_le u w)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h0
  have hcol : (Matrix.vecMulVec u w).col j ∈
      Submodule.span F (Set.range (Matrix.vecMulVec u w).col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [h0, Submodule.mem_bot] at hcol
  apply hu
  have h1 : w j • u = 0 := by
    rw [← hcol]
    ext i
    simp [Matrix.vecMulVec_apply, mul_comm]
  exact (smul_eq_zero.1 h1).resolve_left hj

private theorem isUnitaryTransvectionIn_kFactsSuProjTv (hF : Nat.card F = (2 ^ n) ^ 2) {k : ℕ}
    {e : Fin k → F} (he0 : e ≠ 0) (he : herm σ₂ e e = 0) :
    IsUnitaryTransvectionIn k n (kFactsSuProjTv hF k e 1) := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + σ₂ 1 = 0 := one_add_map_one σ₂
  refine ⟨MulEquiv.subgroupCongr (SUid_eq_statedSU hF k) (suTv hσ e 1), rfl, ?_⟩
  have hM : ((((suTv hσ e 1 : SUid σ₂ k) : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)) =
      tvMat σ₂ e 1 := by
    rw [suTv, dif_pos ⟨he, h1⟩]
    rfl
  change Matrix.rank ((((suTv hσ e 1 : SUid σ₂ k) : GL (Fin k) F) :
    Matrix (Fin k) (Fin k) F) - 1) = 1
  rw [hM, tvMat, add_sub_cancel_left, one_smul]
  refine rank_vecMulVec_eq_one he0 ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.1 he0
  intro h0
  exact (map_ne_zero σ₂).mpr hi (congrFun h0 i)

theorem exists_hom_closure_commonCommute_unitary (hF : Nat.card F = (2 ^ n) ^ 2) {k : ℕ}
    (hk : 2 ≤ k) {s u w : StatedProj (StatedSU (k + 2) (2 ^ n) F)}
    (hs : IsUnitaryTransvectionIn (k + 2) n s) (hu : IsConj s u) (hw : IsConj s w)
    (huw : ¬ Commute u w) :
    ∃ (Θ : SUid σ₂ k →* StatedProj (StatedSU (k + 2) (2 ^ n) F)) (t₀ : SUid σ₂ k),
      Function.Injective Θ ∧ IsUnitaryTransvectionIn k n (kFactsSuProj hF k t₀) ∧
        Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w} = (T σ₂ k).map Θ ∧
        ∀ x, (IsConj s x ∧ Commute x u ∧ Commute x w) ↔
          ∃ h : SUid σ₂ k, Θ (h * t₀ * h⁻¹) = x := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hinv := hσ.invol
  have h1 : (1 : F) + σ₂ 1 = 0 := one_add_map_one σ₂
  obtain ⟨a, ha0, ha, rfl⟩ := kFacts_su_exists_centre hF hs
  obtain ⟨p, hp0, hp, rfl⟩ := (isConj_kFactsSuProjTv_iff hF ha0 ha u).mp hu
  obtain ⟨q, hq0, hq, rfl⟩ := (isConj_kFactsSuProjTv_iff hF ha0 ha w).mp hw
  have hpq : herm σ₂ p q ≠ 0 := fun h0 =>
    huw (kFacts_suProjTv_comm_of_herm_eq_zero hF hp hq h0 h1 h1)
  obtain ⟨q', hq'def⟩ : ∃ q', q' = (herm σ₂ p q)⁻¹ • q := ⟨_, rfl⟩
  have hq' : herm σ₂ q' q' = 0 := by
    rw [hq'def, herm_smul_left, herm_smul_right, hq]
    ring
  have hpq' : herm σ₂ p q' = 1 := by
    rw [hq'def, herm_smul_right, inv_mul_cancel₀ hpq]
  have hperp : ∀ e : Fin (j + 2 + 2) → F, herm σ₂ e q = 0 ↔ herm σ₂ e q' = 0 := by
    intro e
    rw [hq'def, herm_smul_right]
    exact ⟨fun h => by rw [h, mul_zero],
      fun h => (mul_eq_zero.mp h).resolve_left (inv_ne_zero hpq)⟩
  obtain ⟨Θ, hΘinj, hΘ1, hΘ2⟩ := exists_hom_perp hF (by omega) hp hq' hpq'
  have hSx : ∀ x, (IsConj (kFactsSuProjTv hF (j + 2 + 2) a 1) x ∧
      Commute x (kFactsSuProjTv hF (j + 2 + 2) p 1) ∧
      Commute x (kFactsSuProjTv hF (j + 2 + 2) q 1)) ↔
      ∃ e : Fin (j + 2 + 2) → F, e ≠ 0 ∧ herm σ₂ e e = 0 ∧ herm σ₂ e p = 0 ∧
        herm σ₂ e q' = 0 ∧ x = kFactsSuProjTv hF (j + 2 + 2) e 1 := by
    intro x
    rw [mem_commonCommute_iff hF (by omega) ha0 ha hp hq x]
    simp only [hperp]
  obtain ⟨W⟩ := hσ.nonempty_wittData
  have he₀ : herm σ₂ (W.hypA j) (W.hypA j) = 0 := W.herm_hypA_hypA
  have he₀0 : W.hypA j ≠ 0 := W.hypA_ne_zero
  refine ⟨Θ, suTv hσ (W.hypA j) 1, hΘinj,
    isUnitaryTransvectionIn_kFactsSuProjTv hF he₀0 he₀, ?_, ?_⟩
  · rw [Set.ext hSx]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨e, he0, he, hep, heq, rfl⟩
      obtain ⟨v, hv0, hv, hΘv⟩ := hΘ2 e he0 he hep heq
      exact ⟨suTv hσ v 1, mem_T_of_smul hv h1 (suTv_smul hσ hv h1), hΘv⟩
    · rintro _ ⟨g', hg', rfl⟩
      refine (Subgroup.closure_le (K := (Subgroup.closure {x | ∃ e : Fin (j + 2 + 2) → F,
        e ≠ 0 ∧ herm σ₂ e e = 0 ∧ herm σ₂ e p = 0 ∧ herm σ₂ e q' = 0 ∧
          x = kFactsSuProjTv hF (j + 2 + 2) e 1}).comap Θ)).mpr ?_ hg'
      rintro g'' ⟨a', c, ha', hc, hact⟩
      have hg'' : g'' = suTv hσ a' c := ext_smul σ₂ fun v => by rw [hact, suTv_smul hσ ha' hc]
      rw [SetLike.mem_coe, Subgroup.mem_comap, hg'']
      obtain ⟨e, he, hep, heq, hne, hΘe⟩ := hΘ1 a' ha' c hc
      rw [hΘe]
      by_cases hz : a' = 0 ∨ c = 0
      · have : suTv hσ a' c = 1 := by
          apply ext_smul
          intro v
          rw [suTv_smul hσ ha' hc, one_smul]
          rcases hz with hz | hz
          · rw [hz, smul_zero, add_zero]
          · rw [hz, zero_mul, zero_smul, add_zero]
        rw [← hΘe, this, map_one]
        exact Subgroup.one_mem _
      · push Not at hz
        have he0 := hne hz.1
        have hσc : σ₂ c = c := (CharTwo.add_eq_zero.mp hc).symm
        obtain ⟨μ, hμ⟩ := hσ.norm_surj c hσc hz.2
        have hμ0 : μ ≠ 0 := by
          rintro rfl
          rw [map_zero, zero_mul] at hμ
          exact hz.2 hμ.symm
        have hTc : kFactsSuProjTv hF (j + 2 + 2) e c =
            kFactsSuProjTv hF (j + 2 + 2) (μ • e) 1 := by
          rw [kFacts_suProjTv_smul_vec hF he h1, mul_one, hμ]
        rw [hTc]
        refine Subgroup.subset_closure ⟨μ • e, smul_ne_zero hμ0 he0, ?_, ?_, ?_, rfl⟩
        · rw [herm_smul_left, herm_smul_right, he, mul_zero, mul_zero]
        · rw [herm_smul_left, hep, mul_zero]
        · rw [herm_smul_left, heq, mul_zero]
  · intro x
    rw [hSx x]
    constructor
    · rintro ⟨e, he0, he, hep, heq, rfl⟩
      obtain ⟨v, hv0, hv, hΘv⟩ := hΘ2 e he0 he hep heq
      obtain ⟨t, ht⟩ := exists_suTv_smul_eq hσ he₀0 he₀ hv0 hv
      refine ⟨t, ?_⟩
      rw [suTv_conj hσ t he₀ h1, ht, hΘv]
    · rintro ⟨t, rfl⟩
      rw [suTv_conj hσ t he₀ h1]
      have ht₀ : herm σ₂ (t • W.hypA j) (t • W.hypA j) = 0 := by rw [herm_smul_smul, he₀]
      obtain ⟨e, he, hep, heq, hne, hΘe⟩ := hΘ1 (t • W.hypA j) ht₀ 1 h1
      exact ⟨e, hne fun h0 => he₀0 ((smul_eq_zero_iff_eq t).mp h0), he, hep, heq, hΘe⟩

end Core

section Center

open CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

local notation "σ₂" => unitaryInvolution F 2 n

omit [Finite F] in
private theorem scalar_two_eq_one {c : F} (hc : (Matrix.scalar (Fin 2) c).det = 1) : c = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : c ^ 2 = 1 := by simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hc
  have h4 : (c + 1) ^ 2 = 0 := by linear_combination h3 + (c + 1) * h2
  have h5 : c + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h4
  linear_combination h5 - h2

private theorem center_statedSU_two (hF : Nat.card F = (2 ^ n) ^ 2) :
    Subgroup.center (StatedSU 2 (2 ^ n) F) =
      (StatedScalars (Fin 2) F).subgroupOf (StatedSU 2 (2 ^ n) F) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  let e : SL(2, fixedSubfield F 2 n) ≃* StatedSU 2 (2 ^ n) F :=
    ((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hF 2))
  have hc : Subgroup.center SL(2, fixedSubfield F 2 n) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have h2 : (2 : fixedSubfield F 2 n) = 0 := CharTwo.two_eq_zero
    have h3 : r ^ 2 = 1 := by simpa using hr
    have h4 : (r + 1) ^ 2 = 0 := by linear_combination h3 + (r + 1) * h2
    have h5 : r = 1 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h4
      linear_combination this - h2
    apply Subtype.ext
    rw [← hrA, h5, map_one]
    rfl
  have hZ : Subgroup.center (StatedSU 2 (2 ^ n) F) = ⊥ := by
    rw [← map_center_mulEquiv e, hc, Subgroup.map_bot]
  rw [hZ]
  symm
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  obtain ⟨c, hcg⟩ := (Subgroup.mem_subgroupOf.mp hg : (g : GL (Fin 2) F) ∈ StatedScalars (Fin 2) F)
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU g.2
  have hgm : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (c : F) := by
    rw [← hcg, Matrix.GeneralLinearGroup.coe_scalar]
  rw [hgm] at hdet
  have hc1 : c = 1 := Units.ext (by rw [scalar_two_eq_one hdet, Units.val_one])
  have h1 : (Matrix.GeneralLinearGroup.scalar (Fin 2)) c = 1 := by rw [hc1, map_one]
  exact Subtype.ext (hcg.symm.trans h1)

private theorem center_statedSU (hF : Nat.card F = (2 ^ n) ^ 2) {k : ℕ} (hk : 2 ≤ k)
    (hk3 : k = 3 → 2 ^ n ≠ 2) :
    Subgroup.center (StatedSU k (2 ^ n) F) =
      (StatedScalars (Fin k) F).subgroupOf (StatedSU k (2 ^ n) F) := by
  by_cases hk2 : k = 2
  · subst hk2
    exact center_statedSU_two hF
  · exact (isQuasisimple_statedSU_of_card (p := 2) (f := n) hF (by omega)
      (fun h => hk3 (Prod.mk.inj h).1 (Prod.mk.inj h).2)).2

private theorem ker_kFactsSuProj_eq_center (hF : Nat.card F = (2 ^ n) ^ 2) {k : ℕ}
    (hk : 2 ≤ k) (hk3 : k = 3 → 2 ^ n ≠ 2) :
    (kFactsSuProj hF k).ker = Subgroup.center (SUid σ₂ k) := by
  have hN := center_statedSU hF hk hk3
  let eSU : SUid σ₂ k ≃* StatedSU k (2 ^ n) F := MulEquiv.subgroupCongr (SUid_eq_statedSU hF k)
  have hmap := map_center_mulEquiv eSU
  ext g
  rw [MonoidHom.mem_ker]
  have h1 : kFactsSuProj hF k g = 1 ↔
      eSU g ∈ (StatedScalars (Fin k) F).subgroupOf (StatedSU k (2 ^ n) F) :=
    QuotientGroup.eq_one_iff _
  rw [h1, ← hN, ← hmap]
  constructor
  · intro hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
    have : y = g := eSU.injective hyg
    rwa [← this]
  · intro hg
    exact Subgroup.mem_map_of_mem _ hg

end Center

section Main

open CFSG.Open CFSG.LieType.BorelTits

theorem isUnitaryTransvection_closure_commonCommute {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 4 ≤ m) (hmf : (m, f) ≠ (5, 1))
    (h : IsUnitaryTransvection X m f s) {u w : X} (hu : IsConj s u) (hw : IsConj s w)
    (huw : ¬ Commute u w) :
    ∃ t : X, ∃ ht : t ∈ Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w},
      IsConj s t ∧ Commute t u ∧ Commute t w ∧
      IsUnitaryTransvection
        (Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w}) (m - 2) f ⟨t, ht⟩ ∧
      ∀ x, (IsConj s x ∧ Commute x u ∧ Commute x w) ↔
        ∃ g ∈ Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w},
          g * t * g⁻¹ = x := by
  classical
  obtain ⟨F, hFfield, hFfin, hF, e, hrank⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 2 ≤ k := by omega
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_sq (p := 2) (f := f) hF
  have hk3 : k = 3 → 2 ^ f ≠ 2 := by
    intro h3 h2
    apply hmf
    have : f = 1 := Nat.pow_right_injective (le_refl 2) (h2.trans (pow_one 2).symm)
    rw [h3, this]
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  let ψ₀ : X →* StatedProj (StatedSU (k + 2) (2 ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψinj : Function.Injective ψ₀ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ψ : X ≃* StatedProj (StatedSU (k + 2) (2 ^ f) F) := MulEquiv.ofBijective ψ₀ ⟨hψinj, hψsurj⟩
  have hψ : ∀ x, ψ x = e (QuotientGroup.mk x) := fun x => rfl
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => ψ.injective (by rw [map_mul, map_mul]; exact h.eq)⟩
  have hconj : ∀ x y : X, IsConj x y ↔ IsConj (ψ x) (ψ y) := fun x y =>
    ⟨fun h => MonoidHom.map_isConj ψ.toMonoidHom h, fun h => by
      simpa using MonoidHom.map_isConj ψ.symm.toMonoidHom h⟩
  obtain ⟨Θ, t₀, hΘinj, ht₀, hclos, hchar⟩ := exists_hom_closure_commonCommute_unitary hF hk
    (s := ψ s) (u := ψ u) (w := ψ w) (by rw [hψ]; exact hrank) ((hconj _ _).mp hu)
    ((hconj _ _).mp hw) (fun h => huw ((hcomm _ _).mpr h))
  have hT : T (unitaryInvolution F 2 f) k = ⊤ :=
    T_eq_top hσ hk fun h3 => exists_norm_ne_one hF (hk3 h3)
  have hrange : Θ.range = Subgroup.closure
      {y | IsConj (ψ s) y ∧ Commute y (ψ u) ∧ Commute y (ψ w)} := by
    rw [hclos, hT, MonoidHom.range_eq_map]
  set S : Set X := {x | IsConj s x ∧ Commute x u ∧ Commute x w} with hSdef
  have hSψ : ∀ x : X, x ∈ S ↔
      ψ x ∈ {y | IsConj (ψ s) y ∧ Commute y (ψ u) ∧ Commute y (ψ w)} := fun x =>
    ⟨fun ⟨a, b, c⟩ => ⟨(hconj _ _).mp a, (hcomm _ _).mp b, (hcomm _ _).mp c⟩,
      fun ⟨a, b, c⟩ => ⟨(hconj _ _).mpr a, (hcomm _ _).mpr b, (hcomm _ _).mpr c⟩⟩
  let Θ' : SUid (unitaryInvolution F 2 f) k →* X := ψ.symm.toMonoidHom.comp Θ
  have hΘ' : ∀ y, ψ (Θ' y) = Θ y := fun y => ψ.apply_symm_apply (Θ y)
  have hΘ'inj : Function.Injective Θ' := ψ.symm.injective.comp hΘinj
  have hL : Θ'.range = Subgroup.closure S := by
    rw [MonoidHom.range_comp, hrange, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hSψ]
      simpa using hy
    · intro hx
      exact ⟨ψ x, (hSψ x).mp hx, by simp⟩
  have ht_mem : Θ' t₀ ∈ Subgroup.closure S := hL ▸ ⟨t₀, rfl⟩
  have htS : Θ' t₀ ∈ S := by
    rw [hSψ, hΘ']
    exact (hchar (Θ t₀)).mpr ⟨1, by simp⟩
  refine ⟨Θ' t₀, ht_mem, htS.1, htS.2.1, htS.2.2, ?_, ?_⟩
  · rw [Nat.add_sub_cancel]
    let Φ : SUid (unitaryInvolution F 2 f) k ≃* ↥(Subgroup.closure S) :=
      (MonoidHom.ofInjective hΘ'inj).trans (MulEquiv.subgroupCongr hL)
    have hΦc : (Subgroup.center (SUid (unitaryInvolution F 2 f) k)).map Φ.toMonoidHom =
        Subgroup.center ↥(Subgroup.closure S) := map_center_mulEquiv Φ
    let e₁ : SUid (unitaryInvolution F 2 f) k ⧸
        Subgroup.center (SUid (unitaryInvolution F 2 f) k) ≃*
        ↥(Subgroup.closure S) ⧸ Subgroup.center ↥(Subgroup.closure S) :=
      QuotientGroup.congr _ _ Φ hΦc
    let e₂ : SUid (unitaryInvolution F 2 f) k ⧸
        Subgroup.center (SUid (unitaryInvolution F 2 f) k) ≃*
        StatedProj (StatedSU k (2 ^ f) F) :=
      (QuotientGroup.quotientMulEquivOfEq (ker_kFactsSuProj_eq_center hF hk hk3).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective (kFactsSuProj hF k)
          (kFacts_suProj_surjective hF k))
    unfold IsUnitaryTransvection
    refine ⟨F, hFfield, hFfin, hF, e₁.symm.trans e₂, ?_⟩
    have hΦt : Φ t₀ = ⟨Θ' t₀, ht_mem⟩ := Subtype.ext rfl
    have he't : (e₁.symm.trans e₂) (QuotientGroup.mk ⟨Θ' t₀, ht_mem⟩) =
        kFactsSuProj hF k t₀ := by
      rw [← hΦt]
      change e₂ (e₁.symm (QuotientGroup.mk (Φ t₀))) = _
      rw [show (QuotientGroup.mk (Φ t₀) : ↥(Subgroup.closure S) ⧸ _) = e₁ (QuotientGroup.mk t₀)
        from (QuotientGroup.congr_mk _ _ Φ hΦc t₀).symm, MulEquiv.symm_apply_apply]
      rfl
    rw [he't]
    exact ht₀
  · intro x
    constructor
    · intro hx
      obtain ⟨h, hh⟩ := (hchar (ψ x)).mp ((hSψ x).mp hx)
      refine ⟨Θ' h, hL ▸ ⟨h, rfl⟩, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      apply ψ.injective
      rw [hΘ', hh]
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨h, rfl⟩ : g ∈ Θ'.range := hL ▸ hg
      rw [← map_inv, ← map_mul, ← map_mul]
      refine (hSψ _).mpr ?_
      rw [hΘ']
      exact (hchar _).mpr ⟨h, rfl⟩

end Main

end CFSG.OddTranspositions.PartFour
