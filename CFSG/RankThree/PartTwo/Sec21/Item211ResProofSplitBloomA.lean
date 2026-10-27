module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitNine
public import CFSG.RankThree.PartTwo.Toolkit.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def stabV {k : ℕ} (v : Fin k → ZMod 3) : Subgroup (GL (Fin k) (ZMod 3)) where
  carrier := {y | ((y : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc ((a⁻¹ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v
        = ((a⁻¹ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
            (((a : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v) := by rw [ha]
      _ = v := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]

theorem zpow_mulVec_eq {k : ℕ} {x : GL (Fin k) (ZMod 3)} {v : Fin k → ZMod 3}
    (hx : ((x : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v = v) (j : ℤ) :
    ((x ^ j : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v = v :=
  (stabV v).zpow_mem (show x ∈ stabV v from hx) j

theorem zpowers_eq_of_card_thirteen {H : Type*} [Group H] {F : Subgroup H}
    (hF : Nat.card F = 13) {x : H} (hx : x ∈ F) (hx1 : x ≠ 1) : Subgroup.zpowers x = F := by
  have hle : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hx
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have hdvd : Nat.card (Subgroup.zpowers x) ∣ 13 := hF ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hdvd with h1 | h1
  · exfalso
    rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
    exact hx1 h1
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hF, h1])

theorem zpow_conj_eq {G : Type} [Group G] {w c : G} (hwc : w * c * w⁻¹ = c) (j : ℤ) :
    w ^ j * c * (w ^ j)⁻¹ = c := by
  have hcomm : Commute w c := by
    change w * c = c * w
    calc w * c = w * c * w⁻¹ * w := by group
      _ = c * w := by rw [hwc]
  rw [(hcomm.zpow_left j).eq, mul_inv_cancel_right]

variable {G : Type} [Group G] {A B N : Subgroup G}

theorem SplitHyp.concl_of_bloomCaseA [Finite G] (h : SplitHyp A B N)
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* B)
    (hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a)
    (hA : Toolkit.BloomCaseA (M1 N f)) : SplitConcl A B N := by
  obtain ⟨F, hFM, -, hF13, hMF, -⟩ := hA
  obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := eq_bot_iff.mpr fun y hy => hcon y hy
    rw [hbot, Subgroup.card_bot] at hF13
    norm_num at hF13
  have hFx : Subgroup.zpowers x = F := zpowers_eq_of_card_thirteen hF13 hxF hx1
  have hX1 : ((x : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) ≠ 1 := fun e =>
    hx1 (Units.ext (by rw [e, Units.val_one]))
  have hinv : ∀ g ∈ M1 N f, ∀ v ∈ fixSub ((x : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3)
      (ZMod 3)), ((g : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈
        fixSub ((x : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    intro g hg v hv
    have hgx : g⁻¹ * x * g⁻¹⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hMF ((M1 N f).inv_mem hg)) x).mp hxF
    rw [← hFx] at hgx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgx
    have hxj := zpow_mulVec_eq (mem_fixSub.mp hv) j
    rw [hj, inv_inv] at hxj
    rw [mem_fixSub, Matrix.mulVec_mulVec, ← Units.val_mul,
      show x * g = g * (g⁻¹ * x * g) by group, Units.val_mul, ← Matrix.mulVec_mulVec, hxj]
  have hfix0 : ∀ v : Fin 3 → ZMod 3,
      ((x : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v → v = 0 := by
    intro v hv
    rcases h.isIrreducibleOn_M1 f _ hinv with h0 | ht
    · have := mem_fixSub.mpr hv
      rw [h0] at this
      exact (Submodule.mem_bot _).mp this
    · exact absurd ht (fixSub_ne_top hX1)
  obtain ⟨n, hn, hnx⟩ := h.exists_of_mem_M1 f (hFM hxF)
  have hx13 : x ^ (2 * 6 + 1) = 1 := by
    have : (⟨x, hxF⟩ : F) ^ Nat.card F = 1 := pow_card_eq_one'
    rw [hF13] at this
    exact congrArg Subtype.val this
  have hq : TrivQ A B n := h.trivQ_of_matB_pow f hfB hn (j := 6) (by rw [hnx]; exact hx13)
  have hfixB : ∀ b ∈ B, n * b * n⁻¹ = b → b = 1 := by
    intro b hb hnb
    obtain ⟨v, rfl⟩ := exists_eltB f hb
    rw [h.conj_eltB_eq_iff f hn, hnx] at hnb
    rw [hfix0 v hnb, eltB_zero]
  obtain ⟨c, hcA, hcB, hnc⟩ := h.exists_fixed_of_fpf hn hq hfixB
  refine h.concl_of_matSet f F ?_ ?_ hcA hcB ?_
  · intro m hm y hy
    exact (Subgroup.mem_normalizer_iff.mp (hMF (h.matB_mem_M1 f hm)) y).mp hy
  · intro v hv
    exact hfix0 v (by rw [← hnx]; exact hv n hn (by rw [hnx]; exact hxF))
  · intro r hr hrF
    rw [← hFx] at hrF
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hrF
    have hnj : n ^ j ∈ N := N.zpow_mem hn j
    have he : matB f (h.nb hr) = matB f (h.nb hnj) := by
      rw [← hj, ← hnx, ← map_zpow]
      rfl
    rw [h.conj_eq_of_matB_eq f hfB hr hnj he c hcA, zpow_conj_eq hnc j]

end CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof
