module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13cBaseA

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private lemma plh_sgS_le_Vtail {Y : Submodule K (Fin 4 → K)} (hY : Y ≤ Vtail) :
    sgS K f 4 Y ≤ Vtail := by
  intro v hv
  show v 0 = 0
  have hv' : sgv K f 4 v ∈ Y := hv
  have h0 : (sgv K f 4 v) 0 = 0 := hY hv'
  have h1 : sg K f (v 0) = 0 := h0
  exact (sg K f).map_eq_zero_iff.mp h1

private lemma plh_inf_eq_bot_iff {A B : Submodule K (Fin 4 → K)} (hA : finrank K A = 1) :
    A ⊓ B = ⊥ ↔ ¬ A ≤ B := by
  constructor
  · intro h hle
    have hAle : A ≤ ⊥ := by
      rw [← h]
      exact le_inf le_rfl hle
    have hbot : A = ⊥ := le_bot_iff.mp hAle
    have hfin : finrank K A = 0 := by rw [hbot, finrank_bot]
    omega
  · intro h
    by_contra hne
    have hle1 : finrank K ↥(A ⊓ B) ≤ 1 := by
      rw [← hA]
      exact Submodule.finrank_mono inf_le_left
    have hne1 : finrank K ↥(A ⊓ B) ≠ 1 := by
      intro heq
      have hAB : A ≤ B := by
        have he : A ⊓ B = A :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [heq, hA])
        rw [← he]
        exact inf_le_right
      exact h hAB
    have h0 : finrank K ↥(A ⊓ B) = 0 := by omega
    exact hne (Submodule.finrank_eq_zero.mp h0)

private lemma plh_line_of_pts {u v : Submodule K (Fin 4 → K)} (hu : BPt u) (hv : BPt v)
    (huv : u ≠ v) : u ⊔ v ≤ Vtail ∧ finrank K ↥(u ⊔ v) = 2 :=
  ⟨sup_le hu.1 hv.1, finrank_sup_of_ne_pts hu.2 hv.2 huv⟩

private lemma plh_line_sgS (hK : Nat.card K = (2 ^ f) ^ 2) {u : Submodule K (Fin 4 → K)}
    (hu : BPt u) (hnu : sgS K f 4 u ≠ u) :
    u ⊔ sgS K f 4 u ≤ Vtail ∧ finrank K ↥(u ⊔ sgS K f 4 u) = 2 := by
  refine ⟨sup_le hu.1 (plh_sgS_le_Vtail f hu.1), ?_⟩
  exact finrank_sup_of_ne_pts hu.2
    (by rw [finrank_sgS (K := K) (f := f) (n := 4) hK u, hu.2]) (Ne.symm hnu)

private lemma plh_finrank_three {a b t : Submodule K (Fin 4 → K)} (ha : BPt a) (hb : BPt b)
    (ht : BPt t) (hab : a ≠ b) (htab : ¬ t ≤ a ⊔ b) :
    finrank K ↥(a ⊔ b ⊔ t) = 3 := by
  have hab2 : finrank K ↥(a ⊔ b) = 2 := finrank_sup_of_ne_pts ha.2 hb.2 hab
  have hdisj : Disjoint (a ⊔ b) t := by
    rw [disjoint_iff, inf_comm]
    exact (plh_inf_eq_bot_iff ht.2).mpr htab
  rw [finrank_sup_of_disjoint hdisj, hab2, ht.2]

theorem a13c_cone (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ x y z : Submodule K (Fin 4 → K), BPt x → BPt y → BPt z →
      BAdj (D13c (K := K) f) x y → BAdj (D13c (K := K) f) y z → BAdj (D13c (K := K) f) z x →
      ∃ t, BPt t ∧ BAdj (D13c (K := K) f) x t ∧ BAdj (D13c (K := K) f) y t ∧
        BAdj (D13c (K := K) f) z t ∧ finrank K ↥(x ⊔ y ⊔ t) = 3 ∧
        finrank K ↥(y ⊔ z ⊔ t) = 3 ∧ finrank K ↥(z ⊔ x ⊔ t) = 3 := by
  classical
  intro x y z hx hy hz hxy hyz hzx
  have hnx : sgS K f 4 x ≠ x := nonrat_of_okL f hK le_sup_left hx.2 hxy.2.1
  have hny : sgS K f 4 y ≠ y := nonrat_of_okL f hK le_sup_right hy.2 hxy.2.2
  have hnz : sgS K f 4 z ≠ z := nonrat_of_okL f hK le_sup_right hz.2 hyz.2.2
  let S : Finset (Submodule K (Fin 4 → K)) :=
    {x ⊔ sgS K f 4 x, y ⊔ sgS K f 4 y, z ⊔ sgS K f 4 z, x ⊔ y, y ⊔ z, z ⊔ x}
  have hS : ∀ T ∈ S, T ≤ Vtail ∧ finrank K T = 2 := by
    intro T hT
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl
    · exact plh_line_sgS f hK hx hnx
    · exact plh_line_sgS f hK hy hny
    · exact plh_line_sgS f hK hz hnz
    · exact plh_line_of_pts hx hy hxy.1
    · exact plh_line_of_pts hy hz hyz.1
    · exact plh_line_of_pts hz hx hzx.1
  have hcard : S.card ≤ 6 :=
    Finset.card_le_six (a := x ⊔ sgS K f 4 x) (b := y ⊔ sgS K f 4 y)
      (c := z ⊔ sgS K f 4 z) (d := x ⊔ y) (e := y ⊔ z) (f := z ⊔ x)
  obtain ⟨t, htV, ht1, htnt, hT⟩ := exists_nonrat_point_avoid f hK hq S hS hcard
  have ht : BPt t := ⟨htV, ht1⟩
  have hxt : BAdj (D13c (K := K) f) x t :=
    badj_a3_13c f hK hx ht hnx htnt (hT (x ⊔ sgS K f 4 x) (by simp [S]))
  have hyt : BAdj (D13c (K := K) f) y t :=
    badj_a3_13c f hK hy ht hny htnt (hT (y ⊔ sgS K f 4 y) (by simp [S]))
  have hzt : BAdj (D13c (K := K) f) z t :=
    badj_a3_13c f hK hz ht hnz htnt (hT (z ⊔ sgS K f 4 z) (by simp [S]))
  exact ⟨t, ht, hxt, hyt, hzt,
    plh_finrank_three hx hy ht hxy.1 (hT (x ⊔ y) (by simp [S])),
    plh_finrank_three hy hz ht hyz.1 (hT (y ⊔ z) (by simp [S])),
    plh_finrank_three hz hx ht hzx.1 (hT (z ⊔ x) (by simp [S]))⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
