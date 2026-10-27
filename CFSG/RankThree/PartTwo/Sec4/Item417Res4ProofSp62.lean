module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL52
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofA9
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Item434Kit
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open Matrix
open scoped Matrix

local instance decEqH6 : DecidableEq H6 := inferInstance

@[expose] def sm6 (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  M.submatrix finSumFinEquiv finSumFinEquiv

@[expose] def mk6 (M Mi : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (h : sm6 M * sm6 Mi = 1 ∧ sm6 Mi * sm6 M = 1 ∧
      (sm6 M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 M = Matrix.fromBlocks 0 1 (-1) 0) : H6 :=
  ⟨⟨sm6 M, sm6 Mi, h.1, h.2.1⟩, Subgroup.subset_closure h.2.2⟩

@[expose] def z0M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def z0Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def z1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def z1Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def z2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1]

@[expose] def z2Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0]

@[expose] def tM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0]

@[expose] def tMi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0]

@[expose] def mM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0]

@[expose] def hamM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def hbmM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0]

@[expose] def hbmMi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0]

@[expose] def y0M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 1, 1; 0, 1, 1, 1, 0, 1; 1, 1, 1, 0, 0, 0; 0, 1, 1, 1, 1, 0; 1, 0, 1, 1, 1, 0;
    0, 0, 0, 1, 1, 1]

@[expose] def y0Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 0, 1, 0; 1, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0; 0, 1, 0, 1, 0, 1; 1, 0, 0, 0, 1, 1;
    1, 1, 0, 1, 1, 1]

@[expose] def y1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 1, 1; 1, 1, 0, 1, 0, 1; 1, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 1; 1, 0, 1, 0, 1, 1;
    0, 0, 0, 1, 1, 1]

@[expose] def y1Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0; 1, 1, 1, 1, 1, 0; 0, 1, 0, 1, 1, 1; 1, 0, 0, 1, 1, 1;
    1, 1, 0, 0, 0, 1]

@[expose] def y2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 1, 0, 0; 1, 1, 1, 0, 1, 0; 1, 1, 1, 0, 0, 1; 1, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1;
    0, 0, 1, 1, 1, 0]

@[expose] def y2Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 1, 0, 0; 1, 0, 1, 0, 1, 0; 1, 1, 0, 0, 0, 1; 1, 0, 0, 1, 1, 1; 0, 1, 0, 1, 1, 1;
    0, 0, 1, 1, 1, 1]

theorem z06_check : sm6 z0M * sm6 z0Mi = 1 ∧ sm6 z0Mi * sm6 z0M = 1 ∧
    (sm6 z0M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 z0M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem z16_check : sm6 z1M * sm6 z1Mi = 1 ∧ sm6 z1Mi * sm6 z1M = 1 ∧
    (sm6 z1M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 z1M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem z26_check : sm6 z2M * sm6 z2Mi = 1 ∧ sm6 z2Mi * sm6 z2M = 1 ∧
    (sm6 z2M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 z2M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem t6_check : sm6 tM * sm6 tMi = 1 ∧ sm6 tMi * sm6 tM = 1 ∧
    (sm6 tM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 tM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem m6_check : sm6 mM * sm6 mM = 1 ∧ sm6 mM * sm6 mM = 1 ∧
    (sm6 mM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 mM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem ham6_check : sm6 hamM * sm6 hamM = 1 ∧ sm6 hamM * sm6 hamM = 1 ∧
    (sm6 hamM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 hamM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem hbm6_check : sm6 hbmM * sm6 hbmMi = 1 ∧ sm6 hbmMi * sm6 hbmM = 1 ∧
    (sm6 hbmM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 hbmM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem y06_check : sm6 y0M * sm6 y0Mi = 1 ∧ sm6 y0Mi * sm6 y0M = 1 ∧
    (sm6 y0M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 y0M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem y16_check : sm6 y1M * sm6 y1Mi = 1 ∧ sm6 y1Mi * sm6 y1M = 1 ∧
    (sm6 y1M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 y1M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem y26_check : sm6 y2M * sm6 y2Mi = 1 ∧ sm6 y2Mi * sm6 y2M = 1 ∧
    (sm6 y2M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 y2M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def z6 : Fin 3 → H6 :=
  ![mk6 z0M z0Mi z06_check, mk6 z1M z1Mi z16_check, mk6 z2M z2Mi z26_check]

@[expose] def t6' : H6 := mk6 tM tMi t6_check

@[expose] def m6 : H6 := mk6 mM mM m6_check

@[expose] def ham6 : H6 := mk6 hamM hamM ham6_check

@[expose] def hbm6 : H6 := mk6 hbmM hbmMi hbm6_check

@[expose] def y6 : Fin 3 → H6 :=
  ![mk6 y0M y0Mi y06_check, mk6 y1M y1Mi y16_check,
    mk6 y2M y2Mi y26_check]

theorem wreathFacts_sp6 : WreathFacts z6 t6' where
  pow_z := by decide +kernel
  comm_z := by decide +kernel
  inj := by decide +kernel
  pow_t := by decide +kernel
  conj0 := by decide +kernel
  conj1 := by decide +kernel
  conj2 := by decide +kernel
  t_ne := by decide +kernel

@[expose] def zz6 : H6 := vecElt z6 ![1, 1, 1]

@[expose] def fixCard (A : H6) : ℕ :=
  (Finset.univ.filter fun v : Fin 3 ⊕ Fin 3 → ZMod 2 =>
    ((A : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ v =
      v).card

theorem fixCard_conj (g A : H6) : fixCard (g * A * g⁻¹) = fixCard A := by
  set G : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
    ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    with hG
  set Gi : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
    (((g⁻¹ : H6) : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) with hGi
  set M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
    ((A : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    with hM
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have hGiG : Gi * G = 1 := by
    rw [hG, hGi, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hconj : ((g * A * g⁻¹ : H6) : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) = G * M * Gi := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  unfold fixCard
  rw [hconj]
  refine Finset.card_bij (fun v _ => Gi *ᵥ v) ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := congrArg (fun w => Gi *ᵥ w) hv.2
    simp only [Matrix.mulVec_mulVec] at h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul] at h
    rw [Matrix.mulVec_mulVec]
    exact h
  · intro v _ w _ hvw
    have h := congrArg (fun u => G *ᵥ u) hvw
    simp only [Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec] at h
    exact h
  · intro w hw
    rw [Finset.mem_filter] at hw
    refine ⟨G *ᵥ w, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hw2 : M *ᵥ w = w := hw.2
      have h1 : G * M * Gi * G = G * M := by rw [Matrix.mul_assoc (G * M), hGiG, Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hw2]
    · rw [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]

@[expose] def sixVec : Fin 6 → (Fin 3 → ZMod 3) :=
  ![![1, 0, 0], ![2, 0, 0], ![0, 1, 0], ![0, 2, 0], ![0, 0, 1], ![0, 0, 2]]

@[expose] def six6 (i : Fin 6) : H6 := vecElt z6 (sixVec i)

@[expose] def sixIdx (x : H6) : Fin 6 :=
  if x = six6 1 then 1 else if x = six6 2 then 2 else if x = six6 3 then 3 else
  if x = six6 4 then 4 else if x = six6 5 then 5 else 0

@[expose] def lineIdx6 (x : H6) : Fin 4 :=
  if x = vecElt z6 (lv 1) ∨ x = vecElt z6 (lv 1) ^ 2 then 1 else
  if x = vecElt z6 (lv 2) ∨ x = vecElt z6 (lv 2) ^ 2 then 2 else
  if x = vecElt z6 (lv 3) ∨ x = vecElt z6 (lv 3) ^ 2 then 3 else 0

theorem fix_cases6 : (∀ v : Fin 3 → ZMod 3, fixCard (vecElt z6 v) = 16 →
      ∃ i : Fin 6, vecElt z6 v = six6 i) ∧
    (∀ v : Fin 3 → ZMod 3, fixCard (vecElt z6 v) = 1 →
      ∃ k : Fin 4, vecElt z6 v = vecElt z6 (lv k) ∨ vecElt z6 v = vecElt z6 (lv k) ^ 2) := by
  decide +kernel

theorem six_spec : (∀ i : Fin 6, sixIdx (six6 i) = i ∧ fixCard (six6 i) = 16) ∧
    (∀ k : Fin 4, lineIdx6 (vecElt z6 (lv k)) = k ∧ lineIdx6 (vecElt z6 (lv k) ^ 2) = k ∧
      (vecElt z6 (lv k) ^ 2) ^ 2 = vecElt z6 (lv k) ∧ fixCard (vecElt z6 (lv k)) = 1 ∧
      vecElt z6 (lv k) = z6 0 * z6 1 ^ (lv k 1).val * z6 2 ^ (lv k 2).val) := by
  decide +kernel

theorem fixing_cases6 : ∀ i j k : Fin 6,
    (∀ l : Fin 4, lineIdx6 (six6 i * six6 j ^ (lv l 1).val * six6 k ^ (lv l 2).val) = l) →
    (six6 i = z6 0 ∧ six6 j = z6 1 ∧ six6 k = z6 2) ∨
      (six6 i = (z6 0)⁻¹ ∧ six6 j = (z6 1)⁻¹ ∧ six6 k = (z6 2)⁻¹) := by
  decide +kernel

@[expose] def xw (v : Fin 3 → ZMod 3) (j : Fin 3) : H6 := vecElt z6 v * t6' ^ (j : ℕ)

theorem witness_dist : ∀ (v : Fin 3 → ZMod 3) (j : Fin 3), j ≠ 0 → xw v j ^ 3 = 1 →
    ∀ a b c d : Fin 3, zz6 ^ (a : ℕ) * xw v j ^ (b : ℕ) = zz6 ^ (c : ℕ) * xw v j ^ (d : ℕ) →
      a = c ∧ b = d := by
  decide +kernel

theorem witness_spec : ∀ (v : Fin 3 → ZMod 3) (j : Fin 3), j ≠ 0 → xw v j ^ 3 = 1 →
    ∃ k : Fin 3, y6 k ^ 3 = 1 ∧ y6 k * zz6 = zz6 * y6 k ∧ y6 k * xw v j = xw v j * y6 k ∧
      ∀ a b : Fin 3, y6 k ≠ zz6 ^ (a : ℕ) * xw v j ^ (b : ℕ) := by
  decide +kernel

theorem t6_z0_ne : t6' * z6 0 ≠ z6 0 * t6' := by
  decide +kernel

theorem factorization_card_H6' : (Nat.card H6).factorization 3 = 4 := by
  rw [CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.card_H6,
    show (1451520 : ℕ) = 3 ^ 4 * 17920 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_W6 : Nat.card (wreathW z6 t6') = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := le_card_wreathW wreathFacts_sp6
  have h2 := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts_sp6)
  rw [factorization_card_H6'] at h2
  have : Nat.card (wreathW z6 t6') ≤ 81 := by simpa using h2
  omega

theorem mem_of_card_nine {D : Subgroup H6} (hD9 : Nat.card D = 9) {x : H6} (hz : zz6 ∈ D)
    (hx : x ∈ D) (hinj : ∀ a b c d : Fin 3, zz6 ^ (a : ℕ) * x ^ (b : ℕ) =
      zz6 ^ (c : ℕ) * x ^ (d : ℕ) → a = c ∧ b = d) {y : H6} (hy : y ∈ D) :
    ∃ a b : Fin 3, y = zz6 ^ (a : ℕ) * x ^ (b : ℕ) := by
  classical
  set f : Fin 3 × Fin 3 → H6 := fun p => zz6 ^ (p.1 : ℕ) * x ^ (p.2 : ℕ) with hf
  have hfi : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain ⟨h1, h2⟩ := hinj a b c d h
    rw [h1, h2]
  set S : Finset H6 := Finset.univ.image f with hS
  have hScard : S.card = 9 := by
    rw [hS, Finset.card_image_of_injective _ hfi]
    rfl
  have hSD : (S : Set H6) ⊆ D := by
    intro w hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
    exact D.mul_mem (D.pow_mem hz _) (D.pow_mem hx _)
  have hDfin : (D : Set H6).Finite := Set.toFinite _
  have hDS : (D : Set H6) ⊆ S := by
    by_contra hns
    obtain ⟨w, hwD, hwS⟩ := Set.not_subset.mp hns
    have hss : insert w S ⊆ hDfin.toFinset := by
      intro u hu
      rw [Set.Finite.mem_toFinset]
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hwD
      · exact hSD hu
    have hcard := Finset.card_le_card hss
    rw [Finset.card_insert_of_notMem hwS, hScard] at hcard
    have hD : hDfin.toFinset.card = 9 := by
      rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
      exact hD9
    omega
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (hDS hy)
  exact ⟨p.1, p.2, hp.symm⟩

theorem false_of_card_nine {D : Subgroup H6} (hDe : CFSG.Assembly.IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9)
    (hmax : ∀ x : H6, x ^ 3 = 1 → (∀ d ∈ D, x * d = d * x) → x ∈ D) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wreathFacts_sp6
  have hDp : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hDe.2 x x.2)⟩
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW z6 t6')
    (by rw [card_W6, factorization_card_H6']; norm_num) hDp
  set D₁ := D.map (MulAut.conj g⁻¹).toMonoidHom with hD₁
  have hD₁W : D₁ ≤ wreathW z6 t6' := Item434AltPerm.map_conj_inv_le hg
  have hD₁e : CFSG.Assembly.IsElemAbelian 3 D₁ := Res423Two.isElemAbelian_map' _ hDe
  have hD₁9 : Nat.card D₁ = 9 := by
    rw [hD₁, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD9]
  have hmax₁ : ∀ x : H6, x ^ 3 = 1 → (∀ d ∈ D₁, x * d = d * x) → x ∈ D₁ := by
    intro x hx3 hxD
    have hx' : g * x * g⁻¹ ∈ D := by
      refine hmax _ (by rw [conj_pow, hx3]; group) fun d hd => ?_
      have hd' : g⁻¹ * d * g ∈ D₁ := ⟨d, hd, by simp⟩
      have h1 := hxD _ hd'
      calc g * x * g⁻¹ * d = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by rw [h1]
        _ = d * (g * x * g⁻¹) := by group
    refine ⟨_, hx', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcomm : ∀ a ∈ D₁, ∀ b ∈ D₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD₁e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hle : D₁ ≤ baseA z6
  ·
    obtain ⟨x, hxA, hxD⟩ : ∃ x ∈ baseA z6, x ∉ D₁ := by
      by_contra hc
      push Not at hc
      have := Subgroup.card_le_of_le (fun x hx => hc x hx : baseA z6 ≤ D₁)
      rw [card_baseA hf, hD₁9] at this
      omega
    apply hxD
    refine hmax₁ x ((isElemAbelian_baseA hf).2 x hxA) fun d hd => ?_
    exact congrArg Subtype.val ((isElemAbelian_baseA hf).1.is_comm.comm ⟨x, hxA⟩ ⟨d, hle hd⟩)
  · obtain ⟨x, hxD, hxA⟩ : ∃ x ∈ D₁, x ∉ baseA z6 := by
      by_contra hc
      push Not at hc
      exact hle hc
    obtain ⟨v, j, rfl⟩ := mem_wreathW hf (hD₁W hxD)
    have hj : j ≠ 0 := by
      rintro rfl
      apply hxA
      rw [Fin.val_zero, pow_zero, mul_one]
      exact vecElt_mem_baseA hf v
    set x := vecElt z6 v * t6' ^ (j : ℕ) with hx
    have hx3 : x ^ 3 = 1 := hD₁e.2 x hxD
    have hint : baseA z6 ⊓ D₁ ≤ Subgroup.zpowers zz6 := by
      rintro b ⟨hbA, hbD⟩
      obtain ⟨u, rfl⟩ := (mem_baseA_iff hf).mp hbA
      have hc := hcomm _ hbD _ hxD
      have huv : vecElt z6 u * vecElt z6 v = vecElt z6 v * vecElt z6 u := by
        rw [← vecElt_add hf, ← vecElt_add hf, add_comm]
      have h2 : vecElt z6 u * t6' ^ (j : ℕ) = t6' ^ (j : ℕ) * vecElt z6 u := by
        have h3 : vecElt z6 v * (vecElt z6 u * t6' ^ (j : ℕ)) =
            vecElt z6 v * (t6' ^ (j : ℕ) * vecElt z6 u) := by
          rw [← mul_assoc, ← huv, mul_assoc, hc, hx, mul_assoc]
        exact mul_left_cancel h3
      obtain ⟨h01, h12⟩ := eq_of_commute hf hj h2
      exact vecElt_mem_zpowers_of_const hf h01 h12
    have hrW : (baseA z6).relIndex (wreathW z6 t6') = 3 := by
      have hle' : baseA z6 ≤ wreathW z6 t6' := le_sup_left
      have h := Subgroup.relIndex_mul_card (H := baseA z6) (K := wreathW z6 t6')
      rw [inf_of_le_left hle', card_baseA hf, card_W6] at h
      omega
    have hrD : (baseA z6).relIndex D₁ ≤ 3 := by
      have h1 := Subgroup.relIndex_le_of_le_right (H := baseA z6) hD₁W (by rw [hrW]; norm_num)
      omega
    have hcardint : 3 ≤ Nat.card (baseA z6 ⊓ D₁ : Subgroup H6) := by
      have h := Subgroup.relIndex_mul_card (H := baseA z6) (K := D₁)
      rw [hD₁9] at h
      by_contra hlt
      have : (baseA z6).relIndex D₁ * Nat.card (baseA z6 ⊓ D₁ : Subgroup H6) ≤ 3 * 2 :=
        Nat.mul_le_mul hrD (by omega)
      omega
    have hzD : zz6 ∈ D₁ := by
      have hz3 : Nat.card (Subgroup.zpowers zz6) ≤ 3 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one ((isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)))
      have heq : baseA z6 ⊓ D₁ = Subgroup.zpowers zz6 :=
        Subgroup.eq_of_le_of_card_ge hint (by omega)
      have : zz6 ∈ baseA z6 ⊓ D₁ := heq ▸ Subgroup.mem_zpowers zz6
      exact this.2
    have hdist := witness_dist v j hj hx3
    obtain ⟨k, hy3, hyz, hyx, hyne⟩ := witness_spec v j hj hx3
    have hyD : y6 k ∈ D₁ := by
      refine hmax₁ _ hy3 fun d hd => ?_
      obtain ⟨a, b, rfl⟩ := mem_of_card_nine hD₁9 hzD hxD hdist hd
      exact ((Commute.pow_right hyz a).mul_right (Commute.pow_right hyx b)).eq
    obtain ⟨a, b, hab⟩ := mem_of_card_nine hD₁9 hzD hxD hdist hyD
    exact hyne a b hab

theorem nmh6_apply (h : Subgroup.normalizer (baseA z6 : Set H6)) (x : baseA z6) :
    (((baseA z6).normalizerMonoidHom h x : baseA z6) : H6) = (h : H6) * (x : H6) * (h : H6)⁻¹ :=
  rfl

@[expose] def vecA6 (v : Fin 3 → ZMod 3) : baseA z6 :=
  ⟨vecElt z6 v, vecElt_mem_baseA wreathFacts_sp6 v⟩

theorem coe_vecA6 (v : Fin 3 → ZMod 3) : ((vecA6 v : baseA z6) : H6) = vecElt z6 v :=
  rfl

theorem conj_vecElt_fix {g : H6} (hN : g ∈ Subgroup.normalizer (baseA z6 : Set H6))
    (u : Fin 3 → ZMod 3) : ∃ w : Fin 3 → ZMod 3, g * vecElt z6 u * g⁻¹ = vecElt z6 w ∧
      fixCard (vecElt z6 w) = fixCard (vecElt z6 u) := by
  have hmem : g * vecElt z6 u * g⁻¹ ∈ baseA z6 :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (vecElt_mem_baseA wreathFacts_sp6 u)
  obtain ⟨w, hw⟩ := (mem_baseA_iff wreathFacts_sp6).mp hmem
  exact ⟨w, hw.symm, by rw [hw, fixCard_conj]⟩

theorem conj_six {g : H6} (hN : g ∈ Subgroup.normalizer (baseA z6 : Set H6)) (i : Fin 6) :
    ∃ i' : Fin 6, g * six6 i * g⁻¹ = six6 i' := by
  obtain ⟨w, hw, hfix⟩ := conj_vecElt_fix hN (sixVec i)
  rw [show vecElt z6 (sixVec i) = six6 i from rfl, (six_spec.1 i).2] at hfix
  obtain ⟨i', hi'⟩ := fix_cases6.1 w hfix
  exact ⟨i', by rw [show six6 i = vecElt z6 (sixVec i) from rfl, hw, hi']⟩

theorem conj_line {g : H6} (hN : g ∈ Subgroup.normalizer (baseA z6 : Set H6)) (k : Fin 4) :
    ∃ j : Fin 4, g * vecElt z6 (lv k) * g⁻¹ = vecElt z6 (lv j) ∨
      g * vecElt z6 (lv k) * g⁻¹ = vecElt z6 (lv j) ^ 2 := by
  obtain ⟨w, hw, hfix⟩ := conj_vecElt_fix hN (lv k)
  rw [(six_spec.2 k).2.2.2.1] at hfix
  obtain ⟨j, hj⟩ := fix_cases6.2 w hfix
  exact ⟨j, by rw [hw]; exact hj⟩

theorem autIn_line6 (φ : autIn ⊤ (baseA z6)) (k : Fin 4) :
    (φ : MulAut (baseA z6)) (vecA6 (lv k)) =
      vecA6 (lv (lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv k)) : baseA z6) : H6))) ∨
    (φ : MulAut (baseA z6)) (vecA6 (lv k)) =
      vecA6 (lv (lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv k)) : baseA z6) : H6)))
        ^ 2 := by
  obtain ⟨g, hN, -, hg⟩ := mem_autIn_iff.mp φ.2
  have h1 : (((φ : MulAut (baseA z6)) (vecA6 (lv k)) : baseA z6) : H6) =
      g * vecElt z6 (lv k) * g⁻¹ := by
    rw [← hg]
    rfl
  obtain ⟨j, hj | hj⟩ := conj_line hN k
  · left
    apply Subtype.ext
    rw [h1, hj, (six_spec.2 j).1]
    rfl
  · right
    apply Subtype.ext
    rw [h1, hj, (six_spec.2 j).2.1]
    rfl

theorem autIn_six6 (φ : autIn ⊤ (baseA z6)) (i : Fin 6) :
    (φ : MulAut (baseA z6)) (vecA6 (sixVec i)) =
      vecA6 (sixVec (sixIdx (((φ : MulAut (baseA z6)) (vecA6 (sixVec i)) : baseA z6) : H6))) := by
  obtain ⟨g, hN, -, hg⟩ := mem_autIn_iff.mp φ.2
  obtain ⟨i', hi'⟩ := conj_six hN i
  have h1 : (((φ : MulAut (baseA z6)) (vecA6 (sixVec i)) : baseA z6) : H6) = g * six6 i * g⁻¹ := by
    rw [← hg]
    rfl
  apply Subtype.ext
  rw [h1, hi', (six_spec.1 i').1]
  rfl

theorem lineIdx6_sq (φ : autIn ⊤ (baseA z6)) (k : Fin 4) :
    lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv k) ^ 2) : baseA z6) : H6) =
      lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv k)) : baseA z6) : H6) := by
  rw [map_pow]
  rcases autIn_line6 φ k with h | h
  · rw [h]
    change lineIdx6 (vecElt z6 (lv _) ^ 2) = lineIdx6 (vecElt z6 (lv _))
    rw [(six_spec.2 _).1, (six_spec.2 _).2.1]
  · rw [h]
    change lineIdx6 ((vecElt z6 (lv _) ^ 2) ^ 2) = lineIdx6 (vecElt z6 (lv _) ^ 2)
    rw [(six_spec.2 _).2.2.1, (six_spec.2 _).1, (six_spec.2 _).2.1]

@[expose] noncomputable def lineAct6 : autIn ⊤ (baseA z6) →* Function.End (Fin 4) where
  toFun φ := fun k => lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv k)) : baseA z6) : H6)
  map_one' := by
    funext k
    exact (six_spec.2 k).1
  map_mul' φ ψ := by
    funext k
    change lineIdx6 (((φ : MulAut (baseA z6)) ((ψ : MulAut (baseA z6)) (vecA6 (lv k))) :
      baseA z6) : H6) = lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv (lineIdx6
        (((ψ : MulAut (baseA z6)) (vecA6 (lv k)) : baseA z6) : H6)))) : baseA z6) : H6)
    rcases autIn_line6 ψ k with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      exact lineIdx6_sq φ _

@[expose] noncomputable def sixAct6 : autIn ⊤ (baseA z6) →* Function.End (Fin 6) where
  toFun φ := fun i => sixIdx (((φ : MulAut (baseA z6)) (vecA6 (sixVec i)) : baseA z6) : H6)
  map_one' := by
    funext i
    exact (six_spec.1 i).1
  map_mul' φ ψ := by
    funext i
    change sixIdx (((φ : MulAut (baseA z6)) ((ψ : MulAut (baseA z6)) (vecA6 (sixVec i))) :
      baseA z6) : H6) = sixIdx (((φ : MulAut (baseA z6)) (vecA6 (sixVec (sixIdx
        (((ψ : MulAut (baseA z6)) (vecA6 (sixVec i)) : baseA z6) : H6)))) : baseA z6) : H6)
    rw [← autIn_six6 ψ i]

@[expose] noncomputable def linePerm6 : autIn ⊤ (baseA z6) →* Equiv.Perm (Fin 4) :=
  Equiv.Perm.equivUnitsEnd.symm.toMonoidHom.comp lineAct6.toHomUnits

@[expose] noncomputable def sixPerm6 : autIn ⊤ (baseA z6) →* Equiv.Perm (Fin 6) :=
  Equiv.Perm.equivUnitsEnd.symm.toMonoidHom.comp sixAct6.toHomUnits

@[expose] def unitsToZ2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      decide

@[expose] noncomputable def phi6 :
    autIn ⊤ (baseA z6) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) :=
  (unitsToZ2.comp (Equiv.Perm.sign.comp sixPerm6)).prod linePerm6

theorem linePerm6_apply (φ : autIn ⊤ (baseA z6)) (k : Fin 4) :
    linePerm6 φ k = lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv k)) : baseA z6) : H6) :=
  rfl

theorem sixPerm6_apply (φ : autIn ⊤ (baseA z6)) (i : Fin 6) :
    sixPerm6 φ i = sixIdx (((φ : MulAut (baseA z6)) (vecA6 (sixVec i)) : baseA z6) : H6) :=
  rfl

@[expose] def invPerm6 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

theorem inv_six_spec : (∀ i : Fin 6, sixIdx (six6 i)⁻¹ = invPerm6 i) ∧
    Equiv.Perm.sign invPerm6 = -1 := by
  decide +kernel

theorem conj_vecElt_inv {g : H6} (h0 : g * z6 0 * g⁻¹ = (z6 0)⁻¹)
    (h1 : g * z6 1 * g⁻¹ = (z6 1)⁻¹) (h2 : g * z6 2 * g⁻¹ = (z6 2)⁻¹) (v : Fin 3 → ZMod 3) :
    g * vecElt z6 v * g⁻¹ = (vecElt z6 v)⁻¹ := by
  have hf := wreathFacts_sp6
  have hconj : ∀ x : H6, g * x * g⁻¹ = MulAut.conj g x := fun x => rfl
  rw [vecElt, hconj, map_mul, map_mul, map_pow, map_pow, map_pow, ← hconj, ← hconj, ← hconj,
    h0, h1, h2, inv_pow, inv_pow, inv_pow]
  set X := z6 0 ^ (v 0).val with hX
  set Y := z6 1 ^ (v 1).val with hY
  set Z := z6 2 ^ (v 2).val with hZ
  have c01 : X⁻¹ * Y⁻¹ = Y⁻¹ * X⁻¹ :=
    ((Commute.pow_pow (hf.comm_z 0 1) (v 0).val (v 1).val).inv_left.inv_right).eq
  have c02 : X⁻¹ * Z⁻¹ = Z⁻¹ * X⁻¹ :=
    ((Commute.pow_pow (hf.comm_z 0 2) (v 0).val (v 2).val).inv_left.inv_right).eq
  have c12 : Y⁻¹ * Z⁻¹ = Z⁻¹ * Y⁻¹ :=
    ((Commute.pow_pow (hf.comm_z 1 2) (v 1).val (v 2).val).inv_left.inv_right).eq
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  calc X⁻¹ * Y⁻¹ * Z⁻¹ = Y⁻¹ * (X⁻¹ * Z⁻¹) := by rw [c01, mul_assoc]
    _ = Y⁻¹ * (Z⁻¹ * X⁻¹) := by rw [c02]
    _ = Y⁻¹ * Z⁻¹ * X⁻¹ := by rw [mul_assoc]
    _ = Z⁻¹ * Y⁻¹ * X⁻¹ := by rw [c12]
    _ = Z⁻¹ * (Y⁻¹ * X⁻¹) := by rw [mul_assoc]

theorem nmh6_eq_one (h : Subgroup.normalizer (baseA z6 : Set H6))
    (hc0 : (h : H6) * z6 0 = z6 0 * (h : H6)) (hc1 : (h : H6) * z6 1 = z6 1 * (h : H6))
    (hc2 : (h : H6) * z6 2 = z6 2 * (h : H6)) :
    (baseA z6).normalizerMonoidHom h = 1 := by
  have hle : baseA z6 ≤ Subgroup.centralizer ({(h : H6)} : Set H6) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;>
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact hc0.symm
    · exact hc1.symm
    · exact hc2.symm
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [nmh6_apply]
  have hx := Subgroup.mem_centralizer_singleton_iff.mp (hle x.2)
  rw [← hx, mul_inv_cancel_right]
  rfl

theorem mul_comm_of_conj_eq6 {y c : H6} (h : y * c * y⁻¹ = c) : y * c = c * y := by
  calc y * c = y * c * y⁻¹ * y := by group
    _ = c * y := by rw [h]

theorem phi6_injective : Function.Injective phi6 := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have hφ1 : linePerm6 φ = 1 := congrArg Prod.snd hφ
  have hφ2 : unitsToZ2 (Equiv.Perm.sign (sixPerm6 φ)) = 1 := congrArg Prod.fst hφ
  have hfix : ∀ l : Fin 4, lineIdx6 (((φ : MulAut (baseA z6)) (vecA6 (lv l)) : baseA z6) : H6) =
      l := fun l => by
    rw [← linePerm6_apply, hφ1]
    rfl
  obtain ⟨g, hN, -, hg⟩ := mem_autIn_iff.mp φ.2
  obtain ⟨i, hi⟩ := conj_six hN 0
  obtain ⟨j, hj⟩ := conj_six hN 2
  obtain ⟨k, hk⟩ := conj_six hN 4
  have hz0 : six6 0 = z6 0 := by decide +kernel
  have hz1 : six6 2 = z6 1 := by decide +kernel
  have hz2 : six6 4 = z6 2 := by decide +kernel
  rw [hz0] at hi
  rw [hz1] at hj
  rw [hz2] at hk
  have hline : ∀ l : Fin 4,
      lineIdx6 (six6 i * six6 j ^ (lv l 1).val * six6 k ^ (lv l 2).val) = l := by
    intro l
    have h1 : (((φ : MulAut (baseA z6)) (vecA6 (lv l)) : baseA z6) : H6) =
        g * vecElt z6 (lv l) * g⁻¹ := by
      rw [← hg]
      rfl
    have h2 := hfix l
    rw [h1] at h2
    have h3 : six6 i * six6 j ^ (lv l 1).val * six6 k ^ (lv l 2).val =
        g * vecElt z6 (lv l) * g⁻¹ := by
      rw [(six_spec.2 l).2.2.2.2, ← hi, ← hj, ← hk, conj_pow, conj_pow]
      group
    rw [h3]
    exact h2
  rcases fixing_cases6 i j k hline with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · apply Subtype.ext
    rw [← hg]
    exact nmh6_eq_one _ (mul_comm_of_conj_eq6 (by rw [hi, h1]))
      (mul_comm_of_conj_eq6 (by rw [hj, h2])) (mul_comm_of_conj_eq6 (by rw [hk, h3]))
  · exfalso
    have hinv := conj_vecElt_inv (g := g) (by rw [hi, h1]) (by rw [hj, h2]) (by rw [hk, h3])
    have hP : sixPerm6 φ = invPerm6 := by
      ext i'
      rw [sixPerm6_apply]
      have h4 : (((φ : MulAut (baseA z6)) (vecA6 (sixVec i')) : baseA z6) : H6) =
          (six6 i')⁻¹ := by
        rw [← hg]
        exact hinv (sixVec i')
      rw [h4, inv_six_spec.1 i']
    rw [hP, inv_six_spec.2] at hφ2
    exact absurd hφ2 (by decide)

theorem mem_normalizer_A06 {g : H6} (h0 : g * z6 0 * g⁻¹ ∈ baseA z6)
    (h1 : g * z6 1 * g⁻¹ ∈ baseA z6) (h2 : g * z6 2 * g⁻¹ ∈ baseA z6) :
    g ∈ Subgroup.normalizer (baseA z6 : Set H6) := by
  have hle : baseA z6 ≤ (baseA z6).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    · exact h0
    · exact h1
    · exact h2
  exact Subgroup.mem_normalizer_fintype fun x hx => hle hx

theorem gens6_conj : (∀ i : Fin 3, m6 * z6 i * m6⁻¹ = (z6 i)⁻¹) ∧
    ham6 * z6 0 * ham6⁻¹ = vecElt z6 ![0, 2, 0] ∧ ham6 * z6 1 * ham6⁻¹ = vecElt z6 ![2, 0, 0] ∧
    ham6 * z6 2 * ham6⁻¹ = vecElt z6 ![0, 0, 1] ∧
    hbm6 * z6 0 * hbm6⁻¹ = vecElt z6 ![2, 0, 0] ∧ hbm6 * z6 1 * hbm6⁻¹ = vecElt z6 ![0, 0, 1] ∧
    hbm6 * z6 2 * hbm6⁻¹ = vecElt z6 ![0, 2, 0] := by
  decide +kernel

theorem m6_mem : m6 ∈ Subgroup.normalizer (baseA z6 : Set H6) :=
  mem_normalizer_A06 (by rw [gens6_conj.1 0]; exact inv_mem (z_mem_baseA 0))
    (by rw [gens6_conj.1 1]; exact inv_mem (z_mem_baseA 1))
    (by rw [gens6_conj.1 2]; exact inv_mem (z_mem_baseA 2))

theorem ham6_mem : ham6 ∈ Subgroup.normalizer (baseA z6 : Set H6) := by
  obtain ⟨-, h0, h1, h2, -⟩ := gens6_conj
  exact mem_normalizer_A06 (h0 ▸ vecElt_mem_baseA wreathFacts_sp6 _)
    (h1 ▸ vecElt_mem_baseA wreathFacts_sp6 _) (h2 ▸ vecElt_mem_baseA wreathFacts_sp6 _)

theorem hbm6_mem : hbm6 ∈ Subgroup.normalizer (baseA z6 : Set H6) := by
  obtain ⟨-, -, -, -, h0, h1, h2⟩ := gens6_conj
  exact mem_normalizer_A06 (h0 ▸ vecElt_mem_baseA wreathFacts_sp6 _)
    (h1 ▸ vecElt_mem_baseA wreathFacts_sp6 _) (h2 ▸ vecElt_mem_baseA wreathFacts_sp6 _)

@[expose] noncomputable def autA6 (g : H6) (hg : g ∈ Subgroup.normalizer (baseA z6 : Set H6)) :
    autIn ⊤ (baseA z6) :=
  ⟨(baseA z6).normalizerMonoidHom ⟨g, hg⟩, mem_autIn_iff.mpr ⟨g, hg, Subgroup.mem_top _, rfl⟩⟩

theorem autA6_apply (g : H6) (hg : g ∈ Subgroup.normalizer (baseA z6 : Set H6))
    (x : baseA z6) : (((autA6 g hg : MulAut (baseA z6)) x : baseA z6) : H6) = g * x * g⁻¹ :=
  rfl

@[expose] def hamPerm6 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 2

@[expose] def hbmPerm6 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * (Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 3 5)

theorem gens6_act :
    (∀ k : Fin 4, lineIdx6 (m6 * vecElt z6 (lv k) * m6⁻¹) = k) ∧
    (∀ i : Fin 6, sixIdx (m6 * six6 i * m6⁻¹) = invPerm6 i) ∧
    (∀ k : Fin 4, lineIdx6 (ham6 * vecElt z6 (lv k) * ham6⁻¹) = Equiv.swap (0 : Fin 4) 1 k) ∧
    (∀ i : Fin 6, sixIdx (ham6 * six6 i * ham6⁻¹) = hamPerm6 i) ∧
    (∀ k : Fin 4, lineIdx6 (hbm6 * vecElt z6 (lv k) * hbm6⁻¹) = finRotate 4 k) ∧
    (∀ i : Fin 6, sixIdx (hbm6 * six6 i * hbm6⁻¹) = hbmPerm6 i) ∧
    Equiv.Perm.sign hamPerm6 = 1 ∧ Equiv.Perm.sign hbmPerm6 = 1 := by
  decide +kernel

theorem phi6_autA6 {g : H6} (hg : g ∈ Subgroup.normalizer (baseA z6 : Set H6))
    {σ : Equiv.Perm (Fin 6)} {τ : Equiv.Perm (Fin 4)}
    (hσ : ∀ i : Fin 6, sixIdx (g * six6 i * g⁻¹) = σ i)
    (hτ : ∀ k : Fin 4, lineIdx6 (g * vecElt z6 (lv k) * g⁻¹) = τ k) :
    phi6 (autA6 g hg) = (unitsToZ2 (Equiv.Perm.sign σ), τ) := by
  have h6 : sixPerm6 (autA6 g hg) = σ := Equiv.ext fun i => by
    rw [sixPerm6_apply, autA6_apply, coe_vecA6]
    exact hσ i
  have h4 : linePerm6 (autA6 g hg) = τ := Equiv.ext fun k => by
    rw [linePerm6_apply, autA6_apply, coe_vecA6]
    exact hτ k
  rw [phi6, MonoidHom.prod_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h6, h4]

theorem phi6_surjective : Function.Surjective phi6 := by
  obtain ⟨hm1, hm2, ha1, ha2, hb1, hb2, hsa, hsb⟩ := gens6_act
  have hM := phi6_autA6 m6_mem hm2 (τ := 1) hm1
  have hA := phi6_autA6 ham6_mem ha2 ha1
  have hB := phi6_autA6 hbm6_mem hb2 hb1
  rw [inv_six_spec.2] at hM
  rw [hsa] at hA
  rw [hsb] at hB
  have hu1 : unitsToZ2 1 = 1 := map_one _
  rw [hu1] at hA hB
  have htop := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 2))
    support_finRotate (0 : Fin 4)
  have h01 : finRotate 4 (0 : Fin 4) = 1 := by decide
  rw [h01] at htop
  have hle : Subgroup.closure ({finRotate 4, Equiv.swap (0 : Fin 4) 1} :
      Set (Equiv.Perm (Fin 4))) ≤ phi6.range.comap (MonoidHom.inr _ _) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hB⟩
    · exact ⟨_, hA⟩
  rintro ⟨s, σ⟩
  have hσ : ((1 : Multiplicative (ZMod 2)), σ) ∈ phi6.range :=
    hle (htop ▸ Subgroup.mem_top σ)
  have hs : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hs (Multiplicative.toAdd s) with h | h
  · have : s = 1 := Multiplicative.toAdd.injective (by rw [h]; rfl)
    rw [this]
    exact hσ
  · have : s = unitsToZ2 (-1) := Multiplicative.toAdd.injective (by rw [h]; decide)
    rw [this]
    obtain ⟨φ, hφ⟩ := hσ
    refine ⟨autA6 m6 m6_mem * φ, ?_⟩
    rw [map_mul, hM, hφ]
    rfl

@[expose] noncomputable def autIn_A06_equiv :
    autIn ⊤ (baseA z6) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective phi6 ⟨phi6_injective, phi6_surjective⟩

theorem k417DatumSp62_holds : K417DatumSp62 := by
  intro D hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wreathFacts_sp6
  set ψ := Item434SmallTwoIII.sp62Equiv with hψ
  set D' := D.map ψ.toMonoidHom with hD'
  have hD'dat : Res417Three.IsDatum417 H6 D' := Res417Three.IsDatum417.map ψ hD
  obtain ⟨hDe, hmax, F, hFD, hF9, -⟩ := hD'dat
  have hcard : Nat.card D' = Nat.card D := Subgroup.card_map_of_injective ψ.injective
  have hDp : IsPGroup 3 D' := fun x => ⟨1, Subtype.ext (by simpa using hDe.2 x x.2)⟩
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW z6 t6')
    (by rw [card_W6, factorization_card_H6']; norm_num) hDp
  set D₁ := D'.map (MulAut.conj g⁻¹).toMonoidHom with hD₁
  have hD₁W : D₁ ≤ wreathW z6 t6' := Item434AltPerm.map_conj_inv_le hg
  have hD₁e : CFSG.Assembly.IsElemAbelian 3 D₁ := Res423Two.isElemAbelian_map' _ hDe
  have hD₁c : Nat.card D₁ = Nat.card D' :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
  have hge : 9 ≤ Nat.card D' := hF9.trans (Subgroup.card_le_of_le hFD)
  have hle81 : Nat.card D' ≤ 81 := by
    rw [← hD₁c, ← card_W6]
    exact Subgroup.card_le_of_le hD₁W
  have hne81 : Nat.card D' ≠ 81 := by
    intro h81
    have hD₁eq : D₁ = wreathW z6 t6' :=
      Subgroup.eq_of_le_of_card_ge hD₁W (by rw [hD₁c, h81, card_W6])
    apply t6_z0_ne
    have ht : t6' ∈ D₁ := hD₁eq ▸ t_mem_wreathW
    have hz : z6 0 ∈ D₁ := hD₁eq ▸ (le_sup_left : baseA z6 ≤ wreathW z6 t6') (z_mem_baseA 0)
    exact congrArg Subtype.val (hD₁e.1.is_comm.comm ⟨_, ht⟩ ⟨_, hz⟩)
  rw [hk] at hge hle81 hne81
  have hk3 : k = 2 ∨ k = 3 := by
    have h1 : 2 ≤ k := by
      by_contra h
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : k ≤ 4 := by
      by_contra h
      have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases (show k = 2 ∨ k = 3 ∨ k = 4 by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (by rw [h]; norm_num) hne81
  rcases hk3 with rfl | rfl
  · exact (false_of_card_nine hDe (by rw [hk]; norm_num) hmax).elim
  · have h27 : Nat.card D' = 27 := by rw [hk]; norm_num
    refine ⟨hcard ▸ h27, ?_⟩
    have hD₁eq : D₁ = baseA z6 :=
      eq_baseA_of_le_wreathW hf card_W6 hD₁W hD₁e (by rw [hD₁c, h27])
    have f1 := Sporadic.autInTopCongr ψ D
    have f2 := Sporadic.autInTopCongr (MulAut.conj g⁻¹) D'
    rw [show D'.map (MulAut.conj g⁻¹ : H6 ≃* H6).toMonoidHom = baseA z6 from hD₁eq] at f2
    exact ⟨f1.trans (f2.trans autIn_A06_equiv)⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Four
