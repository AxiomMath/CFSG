module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iInvol
public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16Groups
public import CFSG.RankThree.PartTwo.Sec21.Hering233iF8
public import CFSG.RankThree.PartTwo.Sec21.HeringRootsU58
import CFSG.RankThree.PartTwo.Sec6.Item63
public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)

namespace Hering233i

open Matrix
open scoped Matrix
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.RankThree.PartTwo.Sec21.TablesU58 CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.RankThree.PartTwo.Sec21.RootsU58
open CFSG.Assembly.LowTwoRank

@[expose] noncomputable def uvec (i j : Fin 5) : Fin 5 → K := Pi.single i 1 + Pi.single j 1

@[expose] noncomputable def nU (i j : Fin 5) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.vecMulVec (uvec i j) (uvec i j)

theorem uvec_mem_F8 (i j x : Fin 5) : uvec i j x ∈ F8 := by
  have h1 : (1 : K) ∈ F8 := by rw [mem_F8]; exact one_pow 8
  have h0 : ∀ a : Fin 5, ((Pi.single a (1 : K) : Fin 5 → K) x) ∈ F8 := by
    intro a
    by_cases h : x = a
    · subst h
      rw [Pi.single_eq_same]
      exact h1
    · rw [Pi.single_eq_of_ne h]
      exact F8.zero_mem
  exact F8.add_mem (h0 i) (h0 j)

theorem frob_of_mem_F8 {c : K} (hc : c ∈ F8) : iterateFrobenius K 2 3 c = c := by
  rw [iterateFrobenius_def]
  exact mem_F8.mp hc

theorem nU_symm (i j : Fin 5) : (nU i j)ᵀ = nU i j := Matrix.transpose_vecMulVec _ _

theorem nU_frob (i j : Fin 5) : (nU i j).map (iterateFrobenius K 2 3) = nU i j := by
  ext x y
  simp only [Matrix.map_apply, nU, Matrix.vecMulVec_apply, map_mul,
    frob_of_mem_F8 (uvec_mem_F8 i j x), frob_of_mem_F8 (uvec_mem_F8 i j y)]

theorem nU_mul {i j k l : Fin 5} (h : uvec i j ⬝ᵥ uvec k l = 0) : nU i j * nU k l = 0 := by
  rw [nU, nU, Matrix.vecMulVec_mul_vecMulVec, h, zero_smul]
  ext x y
  simp [Matrix.vecMulVec_apply]

theorem uvec_eq_zero {i j x : Fin 5} (hxi : x ≠ i) (hxj : x ≠ j) : uvec i j x = 0 := by
  simp [uvec, Pi.single_apply, hxi, hxj]

theorem nU_block {v : Fin 4 → ZMod 3} {i j : Fin 5} (hij : ext3 v i = ext3 v j) {x y : Fin 5}
    (hxy : ext3 v x ≠ ext3 v y) : nU i j x y = 0 := by
  rw [nU, Matrix.vecMulVec_apply]
  by_cases hx : x = i ∨ x = j
  · by_cases hy : y = i ∨ y = j
    · exfalso
      apply hxy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hij
      · exact hij.symm
      · rfl
    · push Not at hy
      rw [uvec_eq_zero hy.1 hy.2, mul_zero]
  · push Not at hx
    rw [uvec_eq_zero hx.1 hx.2, zero_mul]

theorem dot_01_01 : uvec 0 1 ⬝ᵥ uvec 0 1 = 0 := by
  simp [uvec, dotProduct, Fin.sum_univ_five, Pi.single_apply, ← two_mul, two_eq_zero]

theorem dot_23_23 : uvec 2 3 ⬝ᵥ uvec 2 3 = 0 := by
  simp [uvec, dotProduct, Fin.sum_univ_five, Pi.single_apply, ← two_mul, two_eq_zero]

theorem dot_34_34 : uvec 3 4 ⬝ᵥ uvec 3 4 = 0 := by
  simp [uvec, dotProduct, Fin.sum_univ_five, Pi.single_apply, ← two_mul, two_eq_zero]

theorem dot_01_23 : uvec 0 1 ⬝ᵥ uvec 2 3 = 0 := by
  simp [uvec, dotProduct, Fin.sum_univ_five, Pi.single_apply]

theorem dot_23_01 : uvec 2 3 ⬝ᵥ uvec 0 1 = 0 := by
  simp [uvec, dotProduct, Fin.sum_univ_five, Pi.single_apply]

theorem dot_01_34 : uvec 0 1 ⬝ᵥ uvec 3 4 = 0 := by
  simp [uvec, dotProduct, Fin.sum_univ_five, Pi.single_apply]

theorem dot_34_01 : uvec 3 4 ⬝ᵥ uvec 0 1 = 0 := by
  simp [uvec, dotProduct, Fin.sum_univ_five, Pi.single_apply]

theorem nilPairU0 : NilPair (nU 2 3) (nU 0 1) :=
  ⟨nU_mul dot_23_23, nU_mul dot_23_01, nU_mul dot_01_23, nU_mul dot_01_01⟩

theorem nilPairU1 : NilPair (nU 0 1) (nU 3 4) :=
  ⟨nU_mul dot_01_01, nU_mul dot_01_34, nU_mul dot_34_01, nU_mul dot_34_34⟩

theorem nilPairU2 : NilPair (nU 0 1) (nU 2 3) :=
  ⟨nU_mul dot_01_01, nU_mul dot_01_23, nU_mul dot_23_01, nU_mul dot_23_23⟩

theorem hindU0 : ∀ s t : K, s • nU 2 3 + t • nU 0 1 = 0 → s = 0 ∧ t = 0 := by
  intro s t h
  have h1 := congrFun₂ h 2 3
  have h2 := congrFun₂ h 0 1
  simp [nU, uvec, Matrix.vecMulVec_apply, Pi.single_apply] at h1 h2
  exact ⟨h1, h2⟩

theorem hindU1 : ∀ s t : K, s • nU 0 1 + t • nU 3 4 = 0 → s = 0 ∧ t = 0 := by
  intro s t h
  have h1 := congrFun₂ h 0 1
  have h2 := congrFun₂ h 3 4
  simp [nU, uvec, Matrix.vecMulVec_apply, Pi.single_apply] at h1 h2
  exact ⟨h1, h2⟩

theorem hindU2 : ∀ s t : K, s • nU 0 1 + t • nU 2 3 = 0 → s = 0 ∧ t = 0 := by
  intro s t h
  have h1 := congrFun₂ h 0 1
  have h2 := congrFun₂ h 2 3
  simp [nU, uvec, Matrix.vecMulVec_apply, Pi.single_apply] at h1 h2
  exact ⟨h1, h2⟩

theorem gUnit_mem_SU {N₁ N₂ : Matrix (Fin 5) (Fin 5) K} (h : NilPair N₁ N₂) (hs₁ : N₁ᵀ = N₁)
    (hs₂ : N₂ᵀ = N₂) (hf₁ : N₁.map (iterateFrobenius K 2 3) = N₁)
    (hf₂ : N₂.map (iterateFrobenius K 2 3) = N₂) {s t : K} (hs : s ∈ F8) (ht : t ∈ F8) :
    gUnit h two_eq_zero s t ∈ StatedSU 5 (2 ^ 3) K := by
  rw [mem_SUI_iff]
  exact ⟨det_eq_one_of_mul_self (gMat_sq h two_eq_zero s t) two_eq_zero,
    gMat_unitary (iterateFrobenius K 2 3) h two_eq_zero hs₁ hs₂ hf₁ hf₂
      (frob_of_mem_F8 hs) (frob_of_mem_F8 ht)⟩

theorem su_E16_of_pair {N₁ N₂ : Matrix (Fin 5) (Fin 5) K} (P₁ P₂ : AddSubgroup K)
    (hP₁ : P₁ ≤ F8) (hP₂ : P₂ ≤ F8) (hP : 16 ≤ Nat.card P₁ * Nat.card P₂)
    (h : NilPair N₁ N₂) (hs₁ : N₁ᵀ = N₁) (hs₂ : N₂ᵀ = N₂)
    (hf₁ : N₁.map (iterateFrobenius K 2 3) = N₁) (hf₂ : N₂.map (iterateFrobenius K 2 3) = N₂)
    (hind : ∀ s t : K, s • N₁ + t • N₂ = 0 → s = 0 ∧ t = 0) :
    ∃ E : Subgroup SUI, IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
      ∀ g ∈ E, ∃ s ∈ P₁, ∃ t ∈ P₂, mU g = gMat N₁ N₂ s t := by
  obtain ⟨E, hEab, hEcard, hEel⟩ := exists_E16_gfam P₁ P₂ hP h two_eq_zero hind
  have hle : E ≤ StatedSU 5 (2 ^ 3) K := fun g hg => by
    obtain ⟨s, hs, t, ht, hgst⟩ := hEel g hg
    rw [mem_SUI_iff, hgst]
    exact ⟨det_eq_one_of_mul_self (gMat_sq h two_eq_zero s t) two_eq_zero,
      gMat_unitary (iterateFrobenius K 2 3) h two_eq_zero hs₁ hs₂ hf₁ hf₂
        (frob_of_mem_F8 (hP₁ hs)) (frob_of_mem_F8 (hP₂ ht))⟩
  refine ⟨E.subgroupOf (StatedSU 5 (2 ^ 3) K), isElemAbelian_subgroupOf hEab _, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hEcard
  · intro g hg
    exact hEel (g : GL (Fin 5) K) (Subgroup.mem_subgroupOf.mp hg)

theorem su_cent_E16 {v : Fin 4 → ZMod 3} {a b c d : Fin 5} (hab : ext3 v a = ext3 v b)
    (hcd : ext3 v c = ext3 v d) (h : NilPair (nU a b) (nU c d))
    (hind : ∀ s t : K, s • nU a b + t • nU c d = 0 → s = 0 ∧ t = 0) :
    ∃ E₀ : Subgroup SUI, IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 2 ^ 4 ∧
      E₀ ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI) := by
  obtain ⟨E, hEab, hcard, hel⟩ := su_E16_of_pair F8 F8 le_rfl le_rfl
    (by have := eight_le_card_F8; nlinarith) h (nU_symm a b) (nU_symm c d) (nU_frob a b)
    (nU_frob c d) hind
  refine ⟨E, hEab, hcard, fun g hg => ?_⟩
  obtain ⟨s, -, t, -, hgst⟩ := hel g hg
  apply mem_centralizer_of_isBlockDiag_δ
  rw [hgst]
  intro x y hxy
  have hne : x ≠ y := fun e => hxy (by rw [e])
  simp only [gMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nU_block hab hxy,
    nU_block hcd hxy, mul_zero, add_zero, Matrix.one_apply_ne hne]

theorem isComponent_normal_U (v : Fin 4 → ZMod 3)
    {Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI))}
    (hY : CFSG.IsComponent Y) : Y.Normal := by
  have hmem : Y ∈ {Z : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} :
      Set SUI)) | CFSG.IsComponent Z} := hY
  rw [RootsU58.components_big v] at hmem
  obtain ⟨κ, rfl⟩ := hmem
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (idOutsideSU_le_cv v κ.1)).mpr
    (cv_le_normalizer v κ.1)

@[expose] def F2 : AddSubgroup K where
  carrier := {c | c = 0 ∨ c = 1}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (add_zero 0)
    · exact Or.inr (zero_add 1)
    · exact Or.inr (add_zero 1)
    · exact Or.inl (by rw [one_add_one_eq_two]; exact two_eq_zero)
  neg_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl neg_zero
    · exact Or.inr (CharTwo.neg_eq 1)

theorem mem_F2 {c : K} : c ∈ F2 ↔ c = 0 ∨ c = 1 := Iff.rfl

theorem F2_le_F8 : F2 ≤ F8 := by
  intro c hc
  rcases mem_F2.mp hc with rfl | rfl
  · exact F8.zero_mem
  · rw [mem_F8]
    exact one_pow 8

theorem two_le_card_F2 : 2 ≤ Nat.card F2 := by
  have : Nontrivial F2 :=
    ⟨⟨⟨0, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  exact Finite.one_lt_card

theorem mem_normalizer_of_involution {H : Type*} [Group H] {S : Subgroup H} {g : H}
    (hg : g * g = 1) (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set H) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h2 := h _ hx
  have e : g * (g * x * g⁻¹) * g⁻¹ = x := by
    rw [hinv]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by simp only [mul_assoc]
      _ = x := by rw [hg, one_mul, mul_one]
  rwa [e] at h2

theorem nU_idOutside {S : Set (Fin 5)} {i j : Fin 5} (hi : i ∈ S) (hj : j ∈ S) {x y : Fin 5}
    (hxy : x ∉ S ∨ y ∉ S) : nU i j x y = 0 := by
  rw [nU, Matrix.vecMulVec_apply]
  rcases hxy with hx | hy
  · rw [uvec_eq_zero (x := x) (fun e => hx (by rw [e]; exact hi))
      (fun e => hx (by rw [e]; exact hj)), zero_mul]
  · rw [uvec_eq_zero (x := y) (fun e => hy (by rw [e]; exact hi))
      (fun e => hy (by rw [e]; exact hj)), mul_zero]

theorem permMatU_swap01 : permMatU (Equiv.swap 0 1) = 1 + nU 0 1 := by
  ext x y
  rw [permMatU_apply, Matrix.add_apply, nU, Matrix.vecMulVec_apply]
  fin_cases x <;> fin_cases y <;>
    simp [uvec, Pi.single_apply, Equiv.swap_apply_def, Matrix.one_apply, one_add_one_eq_two,
      two_eq_zero]

@[expose] noncomputable def Wsw : SUI := permSU (Equiv.swap 0 1)

theorem mU_Wsw : mU Wsw = 1 + nU 0 1 := permMatU_swap01

@[expose] noncomputable def Aelt (s : K) (hs : s ∈ F8) : SUI :=
  ⟨gUnit nilPairU0 two_eq_zero s 0, gUnit_mem_SU nilPairU0 (nU_symm 2 3) (nU_symm 0 1)
    (nU_frob 2 3) (nU_frob 0 1) hs F8.zero_mem⟩

theorem mU_Aelt (s : K) (hs : s ∈ F8) : mU (Aelt s hs) = gMat (nU 2 3) (nU 0 1) s 0 := rfl

theorem Aelt_mem_cent (s : K) (hs : s ∈ F8) :
    Aelt s hs ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set SUI) := by
  apply mem_centralizer_of_isBlockDiag_δ
  rw [mU_Aelt]
  intro x y hxy
  have hne : x ≠ y := fun e => hxy (by rw [e])
  simp only [gMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    nU_block (v := std 0) (i := 2) (j := 3) (by decide) hxy, mul_zero, zero_mul, add_zero,
    Matrix.one_apply_ne hne]

theorem Aelt_mem_Z (s : K) (hs : s ∈ F8) :
    Aelt s hs ∈ idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0} := by
  rw [mem_idOutsideSU, mU_Aelt]
  intro x y hxy
  have h1 := nU_idOutside (S := {i : Fin 5 | ext3 (std 0) i = 0}) (i := 2) (j := 3)
    (by decide) (by decide) hxy
  simp only [gMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1, mul_zero, zero_mul,
    add_zero]

theorem Wsw_comm (z : SUI) (hz : z ∈ idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0}) :
    Wsw * z = z * Wsw := by
  apply mU_injective
  rw [mU_mul, mU_mul, mU_Wsw]
  rw [mem_idOutsideSU] at hz
  have hz1 : ∀ x y, (x = 0 ∨ x = 1) → mU z x y = (1 : Matrix (Fin 5) (Fin 5) K) x y :=
    fun x y hx => hz x y (Or.inl (by rcases hx with rfl | rfl <;> decide))
  have hz2 : ∀ x y, (y = 0 ∨ y = 1) → mU z x y = (1 : Matrix (Fin 5) (Fin 5) K) x y :=
    fun x y hy => hz x y (Or.inr (by rcases hy with rfl | rfl <;> decide))
  have e1 : uvec 0 1 ᵥ* mU z = uvec 0 1 := by
    have : uvec 0 1 ᵥ* mU z = uvec 0 1 ᵥ* (1 : Matrix (Fin 5) (Fin 5) K) := by
      funext y
      simp only [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x = 0 ∨ x = 1
      · rw [hz1 x y hx]
      · push Not at hx
        rw [uvec_eq_zero hx.1 hx.2, zero_mul, zero_mul]
    rw [this, Matrix.vecMul_one]
  have e2 : mU z *ᵥ uvec 0 1 = uvec 0 1 := by
    have : mU z *ᵥ uvec 0 1 = (1 : Matrix (Fin 5) (Fin 5) K) *ᵥ uvec 0 1 := by
      funext x
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y = 0 ∨ y = 1
      · rw [hz2 x y hy]
      · push Not at hy
        rw [uvec_eq_zero hy.1 hy.2, mul_zero, mul_zero]
    rw [this, Matrix.one_mulVec]
  have e3 : nU 0 1 * mU z = nU 0 1 := by
    rw [nU, Matrix.vecMulVec_mul, e1]
  have e4 : mU z * nU 0 1 = nU 0 1 := by
    rw [nU, Matrix.mul_vecMulVec, e2]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e3, e4]

theorem Wsw_conj_c : Wsw * δ (Multiplicative.ofAdd (std 0)) * Wsw⁻¹ =
    δ (Multiplicative.ofAdd (std 0)) ^ 2 := by
  rw [Wsw, permSU_conj, reindexSU_δ]
  have h : res3 (ext3 (std 0) ∘ ⇑(Equiv.swap (0 : Fin 5) 1)) = 2 • std 0 := by decide
  rw [h, δ_two_smul]

theorem su_zero_model :
    ∃ E₀ : Subgroup SUI, IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 2 ^ 4 ∧
      E₀ ≤ Subgroup.normalizer
        ((Subgroup.zpowers (δ (Multiplicative.ofAdd (std 0))) : Subgroup SUI) : Set SUI) ∧
      E₀ ≤ Subgroup.normalizer
        ((idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0} : Subgroup SUI) : Set SUI) := by
  obtain ⟨E, hEab, hcard, hel⟩ := su_E16_of_pair F8 F2 le_rfl F2_le_F8
    (by have h1 := eight_le_card_F8; have h2 := two_le_card_F2; nlinarith)
    nilPairU0 (nU_symm 2 3) (nU_symm 0 1) (nU_frob 2 3) (nU_frob 0 1) hindU0
  have key : ∀ g ∈ E, g * g = 1 ∧
      g * δ (Multiplicative.ofAdd (std 0)) * g⁻¹ ∈
        Subgroup.zpowers (δ (Multiplicative.ofAdd (std 0))) ∧
      ∀ z ∈ idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0},
        g * z * g⁻¹ ∈ idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0} := by
    intro g hg
    obtain ⟨s, hs, t, ht, hgst⟩ := hel g hg
    have hgg : g * g = 1 :=
      mU_injective (by rw [mU_mul, hgst, gMat_sq nilPairU0 two_eq_zero s t, mU_one])
    refine ⟨hgg, ?_⟩
    rcases mem_F2.mp ht with rfl | rfl
    · have hgA : g = Aelt s hs := mU_injective (by rw [hgst, mU_Aelt])
      subst hgA
      refine ⟨?_, fun z hz => ?_⟩
      · have hAc : Aelt s hs * δ (Multiplicative.ofAdd (std 0)) =
            δ (Multiplicative.ofAdd (std 0)) * Aelt s hs :=
          Subgroup.mem_centralizer_singleton_iff.mp (Aelt_mem_cent s hs)
        rw [mul_inv_eq_iff_eq_mul.mpr hAc]
        exact Subgroup.mem_zpowers _
      · have hA := Aelt_mem_Z s hs
        exact (idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0}).mul_mem
          ((idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0}).mul_mem hA hz)
          ((idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0}).inv_mem hA)
    · have hgAW : g = Aelt s hs * Wsw := by
        apply mU_injective
        rw [hgst, mU_mul, mU_Aelt, mU_Wsw]
        simp only [gMat, one_smul, zero_smul, add_zero, add_mul, mul_add, one_mul, mul_one,
          Matrix.smul_mul, nilPairU0.h12, smul_zero]
      subst hgAW
      refine ⟨?_, fun z hz => ?_⟩
      · have hAc : Aelt s hs * δ (Multiplicative.ofAdd (std 0)) =
            δ (Multiplicative.ofAdd (std 0)) * Aelt s hs :=
          Subgroup.mem_centralizer_singleton_iff.mp (Aelt_mem_cent s hs)
        have hAc2 : Aelt s hs * δ (Multiplicative.ofAdd (std 0)) ^ 2 =
            δ (Multiplicative.ofAdd (std 0)) ^ 2 * Aelt s hs :=
          (Commute.pow_right (show Commute (Aelt s hs) (δ (Multiplicative.ofAdd (std 0)))
            from hAc) 2).eq
        have : Aelt s hs * Wsw * δ (Multiplicative.ofAdd (std 0)) *
            (Aelt s hs * Wsw)⁻¹ = δ (Multiplicative.ofAdd (std 0)) ^ 2 := by
          rw [_root_.mul_inv_rev]
          calc Aelt s hs * Wsw * δ (Multiplicative.ofAdd (std 0)) * (Wsw⁻¹ * (Aelt s hs)⁻¹)
              = Aelt s hs * (Wsw * δ (Multiplicative.ofAdd (std 0)) * Wsw⁻¹) * (Aelt s hs)⁻¹ := by
                group
            _ = Aelt s hs * δ (Multiplicative.ofAdd (std 0)) ^ 2 * (Aelt s hs)⁻¹ := by
                rw [Wsw_conj_c]
            _ = δ (Multiplicative.ofAdd (std 0)) ^ 2 := mul_inv_eq_iff_eq_mul.mpr hAc2
        rw [this]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      · have hA := Aelt_mem_Z s hs
        have hW : Wsw * z * Wsw⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr (Wsw_comm z hz)
        have : Aelt s hs * Wsw * z * (Aelt s hs * Wsw)⁻¹ = Aelt s hs * z * (Aelt s hs)⁻¹ := by
          rw [_root_.mul_inv_rev]
          calc Aelt s hs * Wsw * z * (Wsw⁻¹ * (Aelt s hs)⁻¹)
              = Aelt s hs * (Wsw * z * Wsw⁻¹) * (Aelt s hs)⁻¹ := by group
            _ = Aelt s hs * z * (Aelt s hs)⁻¹ := by rw [hW]
        rw [this]
        exact (idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0}).mul_mem
          ((idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0}).mul_mem hA hz)
          ((idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0}).inv_mem hA)
  refine ⟨E, hEab, hcard, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨hgg, hc, -⟩ := key g hg
    refine mem_normalizer_of_involution hgg fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hc k
  · obtain ⟨hgg, -, hz⟩ := key g hg
    exact mem_normalizer_of_involution hgg hz

theorem fin4_cases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide

theorem su_model (i : Fin 4) {c : SUI} (hc : c = δ (Multiplicative.ofAdd (std i))) :
    ∃ E₀ : Subgroup SUI, IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 2 ^ 4 ∧
      E₀ ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup SUI) : Set SUI) ∧
      ∀ Y : Subgroup (Subgroup.centralizer ({c} : Set SUI)), CFSG.IsComponent Y →
        E₀ ≤ Subgroup.normalizer
          ((Y.map (Subgroup.centralizer ({c} : Set SUI)).subtype : Subgroup SUI) : Set SUI) := by
  subst hc
  have hcent : ∀ {E₀ : Subgroup SUI},
      E₀ ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd (std i))} : Set SUI) →
      E₀ ≤ Subgroup.normalizer
        ((Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))) : Subgroup SUI) : Set SUI) ∧
      ∀ Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std i))} : Set SUI)),
        CFSG.IsComponent Y → E₀ ≤ Subgroup.normalizer ((Y.map (Subgroup.centralizer
          ({δ (Multiplicative.ofAdd (std i))} : Set SUI)).subtype : Subgroup SUI) : Set SUI) := by
    intro E₀ hE₀
    refine ⟨?_, fun Y hY => ?_⟩
    · have h1 : Subgroup.centralizer ((Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))) :
          Subgroup SUI) : Set SUI) =
          Subgroup.centralizer ({δ (Multiplicative.ofAdd (std i))} : Set SUI) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      intro g hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [h1]
      exact hE₀ hg
    · haveI := isComponent_normal_U (std i) hY
      exact hE₀.trans (Sec6.le_normalizer_map_subtype Y)
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · obtain ⟨E₀, h1, h2, h3, h4⟩ := su_zero_model
    refine ⟨E₀, h1, h2, h3, fun Y hY => ?_⟩
    have hmem : Y ∈ {Z : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} :
        Set SUI)) | CFSG.IsComponent Z} := hY
    rw [RootsU58.components_big (std 0)] at hmem
    obtain ⟨κ, rfl⟩ := hmem
    have hκ : κ.1 = 0 := by
      have key : ∀ κ : ZMod 3, (∃ i j : Fin 5, i ≠ j ∧ ext3 (std 0) i = κ ∧ ext3 (std 0) j = κ) →
          κ = 0 := by decide
      exact key κ.1 κ.2
    have : ((idOutsideSU {i : Fin 5 | ext3 (std 0) i = κ.1}).subgroupOf
        (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set SUI))).map
          (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set SUI)).subtype =
        idOutsideSU {i : Fin 5 | ext3 (std 0) i = 0} := by
      rw [hκ]
      exact Subgroup.map_subgroupOf_eq_of_le (idOutsideSU_le_cv _ _)
    rw [this]
    exact h4
  · obtain ⟨E₀, h1, h2, h3⟩ := su_cent_E16 (v := std 1) (a := 0) (b := 1) (c := 3) (d := 4)
      (by decide) (by decide) nilPairU1 hindU1
    exact ⟨E₀, h1, h2, hcent h3⟩
  · obtain ⟨E₀, h1, h2, h3⟩ := su_cent_E16 (v := std 2) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) nilPairU2 hindU2
    exact ⟨E₀, h1, h2, hcent h3⟩
  · obtain ⟨E₀, h1, h2, h3⟩ := su_cent_E16 (v := std 3) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) nilPairU2 hindU2
    exact ⟨E₀, h1, h2, hcent h3⟩

theorem exists_std_pos_U {G : Type} [Group G] {I A : Subgroup G} (hAI : A ≤ I)
    (Φ₁ : I ≃* SUI) (hΦ₁A : (A.subgroupOf I).map Φ₁.toMonoidHom = A0)
    (hAe : IsElemAbelian 3 A) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) :
    ∃ (Φ : I ≃* SUI) (i : Fin 4) (b₀ : G) (hb₀I : b₀ ∈ I),
      Subgroup.zpowers b₀ = Subgroup.zpowers b ∧
        Φ ⟨b₀, hb₀I⟩ = δ (Multiplicative.ofAdd (std i)) := by
  have hbI : b ∈ I := hAI hbA
  have hmem : Φ₁ ⟨b, hbI⟩ ∈ A0 := by
    rw [← hΦ₁A]
    exact Subgroup.mem_map.mpr ⟨⟨b, hbI⟩, Subgroup.mem_subgroupOf.mpr hbA, rfl⟩
  obtain ⟨y, hy⟩ : Φ₁ ⟨b, hbI⟩ ∈ δ.range := hmem
  have hv : Multiplicative.toAdd y ≠ 0 := by
    intro h0
    apply hb1
    have hy1 : y = 1 := Multiplicative.toAdd.injective h0
    rw [hy1, map_one] at hy
    have h1 : Φ₁ ⟨b, hbI⟩ = Φ₁ 1 := by rw [map_one]; exact hy.symm
    have := congrArg Subtype.val (Φ₁.injective h1)
    simpa using this
  obtain ⟨σ, -, i, hσ⟩ := exists_perm_std _ hv
  have hΦσ : (Φ₁.trans (reindexSU σ)) ⟨b, hbI⟩ =
      δ (Multiplicative.ofAdd (res3 (ext3 (Multiplicative.toAdd y) ∘ σ))) := by
    rw [MulEquiv.trans_apply, ← hy]
    change reindexSU σ (δ (Multiplicative.ofAdd (Multiplicative.toAdd y))) = _
    rw [reindexSU_δ]
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  rcases hσ with h | h
  · refine ⟨Φ₁.trans (reindexSU σ), i, b, hbI, rfl, ?_⟩
    rw [hΦσ, h, res3_ext3]
  · refine ⟨Φ₁.trans (reindexSU σ), i, b ^ 2, Subgroup.pow_mem I hbI 2,
      CFSG.RankThree.PartTwo.Sec21.TablesL44.zpowers_sq hb3, ?_⟩
    have hsq : (⟨b ^ 2, Subgroup.pow_mem I hbI 2⟩ : I) = ⟨b, hbI⟩ ^ 2 := rfl
    rw [hsq, map_pow, hΦσ, h, res3_ext3, δ_two_smul, ← pow_mul]
    calc δ (Multiplicative.ofAdd (std i)) ^ (2 * 2)
        = δ (Multiplicative.ofAdd (std i)) ^ 3 * δ (Multiplicative.ofAdd (std i)) := by
          rw [← pow_succ]
      _ = δ (Multiplicative.ofAdd (std i)) := by rw [δ_pow_three, one_mul]

end Hering233i

open Hering233i CFSG.RankThree.PartTwo.KFacts.KS21.U58 CFSG.RankThree.PartTwo.Sec21.TablesU58 in
theorem terminalE16U58 : TerminalE16U58 := by
  intro G _ _ I A hAI hAe hT B hBA hB3 X hX
  obtain ⟨⟨e⟩, hA⟩ := hT
  obtain ⟨Φ₁, hΦ₁A⟩ := RootsU58.exists_Phi hAI hAe e hA
  obtain ⟨b, hbB, hb1, hBb⟩ := exists_gen_of_card_three hB3
  have hbA : b ∈ A := hBA hbB
  obtain ⟨Φ, i, b₀, hb₀I, hzp, hΦb₀⟩ := exists_std_pos_U hAI Φ₁ hΦ₁A hAe hbA hb1
  have hBb₀ : B = Subgroup.zpowers b₀ := hBb.trans hzp.symm
  subst hBb₀
  have hΦH := map_inf_centralizer_zpowers Φ hb₀I
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b₀ : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hY := CFSG.LocalCores.isComponent_map_mulEquiv (thetaK hHI Φ hΦH) hX
  obtain ⟨E₀, hab, hcard, hB, hYn⟩ := su_model i hΦb₀
  exact transport_E16 Φ hb₀I X hab hcard hB (hYn _ hY)

end CFSG.RankThree.PartTwo.Sec21
