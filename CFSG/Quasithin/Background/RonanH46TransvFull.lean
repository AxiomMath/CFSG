module

public import CFSG.Quasithin.Background.RonanH46ZQ

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem tdPowFour (hK : Nat.card K = (2 ^ 1) ^ 2) (x : K) : x ^ 4 = x := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  have h := FiniteField.pow_card x
  rwa [hc] at h

private theorem tdOmega (hK : Nat.card K = (2 ^ 1) ^ 2) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, hc]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hω0 : ω ≠ 0 := fun h => hω (by simp [h])
  have hω1 : ω ≠ 1 := fun h => hω (by simp [h])
  have h4 := tdPowFour hK ω
  have h3 : ω ^ 3 = 1 := by
    apply mul_left_cancel₀ hω0
    linear_combination h4
  have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact ⟨ω, h⟩

private theorem tdMem4 (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (x : K) : x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 := tdPowFour hK x
  have hprod : x * (x + 1) * (x ^ 2 + x + 1) = 0 := by
    linear_combination h4 + (x + x ^ 3 + x ^ 2) * h2
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (by linear_combination h' - h2))
  · have hfac : (x - ω) * (x - (ω + 1)) = 0 := by
      linear_combination h - (ω * x + x + 1) * h2 + hω
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h')))
    · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h')))

theorem trace_dual (hK : Nat.card K = (2 ^ 1) ^ 2) (e : K → K)
    (hadd : ∀ a b, e (a + b) = e a + e b) (hF2 : ∀ a, e a = 0 ∨ e a = 1) :
    ∃ s : K, ∀ c : K, e c = s * bar 1 c + bar 1 s * c := by
  obtain ⟨ω, hω⟩ := tdOmega hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbar : ∀ x : K, bar 1 x = x ^ 2 := fun x => by
    rw [CFSG.Quasithin.H.SU3.bar_apply, pow_one]
  have e0 : e 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    grind
  refine ⟨e ω + e 1 * ω, fun c => ?_⟩
  have hadd' : e (ω + 1) = e ω + e 1 := hadd ω 1
  simp only [hbar]
  rcases hF2 ω with ha | ha <;> rcases hF2 1 with hb | hb <;>
    rcases tdMem4 hK hω c with rfl | rfl | rfl | rfl <;>
    simp only [e0, hadd', ha, hb] <;>
    grind

private noncomputable def rowMat (r : Fin 2 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, r 0, r 1; bar 1 (r 0), 0, 0; bar 1 (r 1), 0, 0]

private theorem rowMat_herm (hK : Nat.card K = (2 ^ 1) ^ 2) (r : Fin 2 → K) :
    (conjM 1 (rowMat r))ᵀ = rowMat r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowMat, conjM, bar_bar hK]

private noncomputable def rowEl (hK : Nat.card K = (2 ^ 1) ^ 2) (r : Fin 2 → K) : ↥(V2z 1 K) :=
  ⟨mkH (rowMat r) (rowMat_herm hK r), mem_V2z.2 ⟨by simp [mat_mkH, rowMat],
    by simp [mat_mkH, rowMat], by simp [mat_mkH, rowMat]⟩⟩

private theorem mat_rowEl (hK : Nat.card K = (2 ^ 1) ^ 2) (r : Fin 2 → K) :
    mat ((rowEl hK r : ↥(V2z 1 K)) : HMod 1 K) = rowMat r := rfl

private theorem rowEl_add (hK : Nat.card K = (2 ^ 1) ^ 2) (r r' : Fin 2 → K) :
    rowEl hK (r + r') = rowEl hK r * rowEl hK r' := by
  apply Subtype.ext
  apply mat_injective
  rw [Subgroup.coe_mul, mat_mul, mat_rowEl, mat_rowEl, mat_rowEl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowMat, map_add]

private theorem rowV2_rowEl (hK : Nat.card K = (2 ^ 1) ^ 2) (r : Fin 2 → K) :
    rowV2 1 K (rowEl hK r) = Multiplicative.ofAdd r := by
  rw [rowV2_apply]
  congr 1
  funext i
  fin_cases i <;> simp [mat_rowEl, rowMat]


theorem QZ_transvections (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∀ τ : MulAut ↥(V2z 1 K),
      (∀ x : ↥(V2z 1 K), ((τ x : ↥(V2z 1 K)) : HMod 1 K) * ((x : ↥(V2z 1 K)) : HMod 1 K)⁻¹ ∈
        V1z 1 K) →
      ∃ q ∈ (QZs K).map (rho hK), ∀ x : ↥(V2z 1 K),
        q (x : HMod 1 K) = ((τ x : ↥(V2z 1 K)) : HMod 1 K) := by
  intro τ hτ
  have hbar : ∀ x : K, bar 1 x = x ^ 2 := fun x => by
    rw [CFSG.Quasithin.H.SU3.bar_apply, pow_one]
  have hsq : ∀ x : K, x ^ 2 = x → x = 0 ∨ x = 1 := fun x h => by
    have hx : x * (x - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr (sub_eq_zero.mp h')
  set δ : ↥(V2z 1 K) → HMod 1 K := fun x => (τ x : HMod 1 K) * (x : HMod 1 K)⁻¹ with hδdef
  have hδ : ∀ x y : ↥(V2z 1 K), mat (δ (x * y)) = mat (δ x) + mat (δ y) := by
    intro x y
    simp only [hδdef, map_mul, Subgroup.coe_mul, mat_mul, mat_inv]
    abel
  have hδ1 : ∀ x, δ x ∈ V1z 1 K := hτ
  set d : ↥(V2z 1 K) → K := fun x => mat (δ x) 0 0 with hd
  have hdadd : ∀ x y, d (x * y) = d x + d y := fun x y => by
    simp only [hd]
    rw [hδ]
    rfl
  have hd01 : ∀ x, d x = 0 ∨ d x = 1 := fun x => by
    have h := herm_apply (δ x) 0 0
    rw [hbar] at h
    exact hsq _ h
  have hδone : δ 1 = 1 := by simp [hδdef]
  have hV1ext : ∀ X Y : HMod 1 K, X ∈ V1z 1 K → Y ∈ V1z 1 K → mat X 0 0 = mat Y 0 0 → X = Y := by
    intro X Y hX hY h
    apply mat_injective
    ext i j
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      exact h
    · rw [hX i j hij, hY i j hij]
  have hdV1 : ∀ x : ↥(V2z 1 K), (x : HMod 1 K) ∈ V1z 1 K → d x = 0 := by
    intro x hx
    by_contra hne
    have hd1 : d x = 1 := (hd01 x).resolve_left hne
    have hx1 : (x : HMod 1 K) ≠ 1 := by
      intro h
      have h' : x = 1 := Subtype.ext h
      rw [h'] at hd1
      simp [hd, hδone, mat_one] at hd1
    have hx00 : mat (x : HMod 1 K) 0 0 = 1 := by
      have h := herm_apply (x : HMod 1 K) 0 0
      rw [hbar] at h
      rcases hsq _ h with h0 | h1
      · exact absurd (hV1ext _ _ hx (V1z 1 K).one_mem (by rw [h0, mat_one]; rfl)) hx1
      · exact h1
    have hτx : (τ x : HMod 1 K) = δ x * (x : HMod 1 K) := by simp [hδdef]
    have hτV1 : (τ x : HMod 1 K) ∈ V1z 1 K := by
      rw [hτx]
      exact (V1z 1 K).mul_mem (hδ1 x) hx
    have hτ1 : (τ x : HMod 1 K) = 1 := by
      apply hV1ext _ _ hτV1 (V1z 1 K).one_mem
      rw [hτx, mat_mul, Matrix.add_apply, hx00, mat_one]
      have : mat (δ x) 0 0 = 1 := hd1
      rw [this]
      simp [CharTwo.add_self_eq_zero]
    have hτ1' : τ x = τ 1 := by
      rw [map_one]
      exact Subtype.ext hτ1
    exact hx1 (congrArg Subtype.val (τ.injective hτ1'))
  have hrow : ∀ x : ↥(V2z 1 K),
      d x = d (rowEl hK ![mat (x : HMod 1 K) 0 1, mat (x : HMod 1 K) 0 2]) := by
    intro x
    set r : Fin 2 → K := ![mat (x : HMod 1 K) 0 1, mat (x : HMod 1 K) 0 2] with hr
    have h1 : rowV2 1 K (x * (rowEl hK r)⁻¹) = 1 := by
      rw [map_mul, map_inv, rowV2_rowEl, rowV2_apply, mul_inv_cancel]
    have h2 := hdV1 _ (rowV2_eq_one_iff.1 h1)
    have h3 := hdadd (x * (rowEl hK r)⁻¹) (rowEl hK r)
    rw [inv_mul_cancel_right, h2, zero_add] at h3
    exact h3
  set ε : (Fin 2 → K) → K := fun r => d (rowEl hK r) with hε
  have hεadd : ∀ r r', ε (r + r') = ε r + ε r' := fun r r' => by
    simp only [hε]
    rw [rowEl_add, hdadd]
  have hε01 : ∀ r, ε r = 0 ∨ ε r = 1 := fun r => hd01 _
  have hdε : ∀ x : ↥(V2z 1 K), d x = ε (Pi.single 0 (mat (x : HMod 1 K) 0 1)) +
      ε (Pi.single 1 (mat (x : HMod 1 K) 0 2)) := by
    intro x
    have hvec : (![mat (x : HMod 1 K) 0 1, mat (x : HMod 1 K) 0 2] : Fin 2 → K) =
        Pi.single 0 (mat (x : HMod 1 K) 0 1) + Pi.single 1 (mat (x : HMod 1 K) 0 2) := by
      ext i
      fin_cases i <;> simp
    rw [hrow x, ← hεadd, ← hvec]
  obtain ⟨s₀, hs₀⟩ := trace_dual hK (fun c => ε (Pi.single 0 c))
    (fun a b => by rw [Pi.single_add, hεadd]) (fun a => hε01 _)
  obtain ⟨s₁, hs₁⟩ := trace_dual hK (fun c => ε (Pi.single 1 c))
    (fun a b => by rw [Pi.single_add, hεadd]) (fun a => hε01 _)
  obtain ⟨g, hg, g01, g02⟩ := exists_QZs s₀ s₁
  refine ⟨rho hK g, Subgroup.mem_map.2 ⟨g, hg, rfl⟩, fun x => ?_⟩
  set X : HMod 1 K := (x : HMod 1 K) with hX
  have hb : hermBlkZ X = 0 := mem_V2z_iff_hermBlkZ.1 x.2
  have hτe : (τ x : HMod 1 K) = δ x * X := by simp [hδdef, hX]
  have hblk := QZ_act_block hK hg X
  have r0 := QZ_act_row hK hg X 0
  have r1 := QZ_act_row hK hg X 1
  simp only [Fin.succ_zero_eq_one] at r0
  simp only [Fin.succ_one_eq_two] at r1
  have b11 : mat X 1 1 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 0) 0
  have b12 : mat X 1 2 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 0) 1
  have b21 : mat X 2 1 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 1) 0
  have b22 : mat X 2 2 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 1) 1
  have c00 := QZ_act_corner hK hg x.2
  rw [g01, g02] at r0 r1 c00
  have hoff : ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → mat (rho hK g X) i j = mat X i j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd ⟨rfl, rfl⟩ hij
    · change mat (rho hK g X) 0 1 = mat X 0 1
      rw [r0, b11, b21]
      ring
    · change mat (rho hK g X) 0 2 = mat X 0 2
      rw [r1, b12, b22]
      ring
    · change mat (rho hK g X) 1 0 = mat X 1 0
      rw [← herm_apply (rho hK g X) 1 0, ← herm_apply X 1 0, r0, b11, b21]
      ring_nf
    · change mat (rho hK g X) 1 1 = mat X 1 1
      simpa [hermBlkZ] using congrFun (congrFun hblk 0) 0
    · change mat (rho hK g X) 1 2 = mat X 1 2
      simpa [hermBlkZ] using congrFun (congrFun hblk 0) 1
    · change mat (rho hK g X) 2 0 = mat X 2 0
      rw [← herm_apply (rho hK g X) 2 0, ← herm_apply X 2 0, r1, b12, b22]
      ring_nf
    · change mat (rho hK g X) 2 1 = mat X 2 1
      simpa [hermBlkZ] using congrFun (congrFun hblk 1) 0
    · change mat (rho hK g X) 2 2 = mat X 2 2
      simpa [hermBlkZ] using congrFun (congrFun hblk 1) 1
  apply mat_injective
  ext i j
  rw [hτe, mat_mul, Matrix.add_apply]
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij
    have hdx : mat (δ x) 0 0 = d x := rfl
    rw [c00, hdx, hdε x, hs₀ (mat X 0 1), hs₁ (mat X 0 2)]
    ring
  · rw [hδ1 x i j hij, zero_add]
    exact hoff i j hij

end CFSG.Quasithin.RonanH46
