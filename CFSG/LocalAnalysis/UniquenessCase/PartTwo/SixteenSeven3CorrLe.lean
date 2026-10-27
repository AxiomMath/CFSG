module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FifteenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenCorr
import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c167_le_conj_of_rk_le_gen (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) {b : ℕ} (hlt : ((D.k + b : ℕ) : ℕ∞) < rMV D.M V)
    {A : Subgroup G} (hAM : A ≤ D.M) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hmQ : E3.mQuot (conjSubgroup V g) A = D.k) (hrk : rk ↥(barSub ⊥ V hV A) ≤ b) :
    E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer (V : Set G)) ≤ D.k + b ∧
      V ≤ conjSubgroup D.M g := by
  have hh : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hP := hh.pairFacts
  have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hCA : A ⊓ centralizer (V : Set G) ≤ A := inf_le_left
  have hCV : A ⊓ centralizer (V : Set G) ≤ conjSubgroup V g ⊓ centralizer (V : Set G) :=
    inf_le_inf_right _ hAg
  have hm : E3.mQuot (conjSubgroup V g) (A ⊓ centralizer (V : Set G)) ≤ D.k + b := by
    rw [E3.mQuot_add hCA hAg, hmQ, ← s16c167_rk_barSub_eq_mQuot hV hAst]
    omega
  refine ⟨(E3.mQuot_mono hCV).trans hm, ?_⟩
  have hnorm : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hh.inCalV
  have hlt' : (E3.mQuot (conjSubgroup V g) (A ⊓ centralizer (V : Set G)) : ℕ∞) <
      rMV (conjSubgroup D.M g) (conjSubgroup V g) := by
    rw [rMV_conj hnorm g]
    exact lt_of_le_of_lt (by exact_mod_cast hm) hlt
  have hcent := centralizer_le_of_mQuot_lt_rMV (inf_le_left.trans hAg) hlt'
  intro v hv
  apply hcent
  rw [Subgroup.mem_centralizer_iff]
  intro c hc'
  exact (Subgroup.mem_centralizer_iff.1 hc'.2 v hv).symm

theorem s16c167_relIndex_dvd_two_of_sq_mem {H : Subgroup G} {t : G}
    (hn : t ∈ normalizer (H : Set G)) (hsq : t ^ 2 ∈ H) :
    H.relIndex (H ⊔ zpowers t) ∣ 2 := by
  rw [Subgroup.relIndex_dvd_two_iff]
  refine ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), ?_⟩
  intro b hb
  have hle : zpowers t ≤ normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hn
  obtain ⟨x, hx, s, hs, rfl⟩ := (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hle).1 hb
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  have h2 : t ^ (2 : ℤ) ∈ H := by simpa using hsq
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · right
    refine H.mul_mem hx ?_
    rw [zpow_mul]
    exact H.zpow_mem h2 m
  · left
    have h3 : t ^ (2 * m + 1) * t = (t ^ (2 : ℤ)) ^ (m + 1) := by
      rw [← zpow_add_one, ← zpow_mul]
      congr 1
      ring
    rw [mul_assoc, h3]
    exact H.mul_mem hx (H.zpow_mem h2 (m + 1))

theorem Desc1614Three.relIndex_le_two (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) {U : Subgroup G} (h : Desc1614Three D V L hV U) :
    (D.M ⊓ centralizer (V : Set G)).relIndex (D.M ⊓ centralizer (U : Set G)) ≤ 2 := by
  obtain ⟨t, htM, ht2, -, -, hCU, -⟩ := h
  have hMV : D.M ≤ normalizer (V : Set G) := hc.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hconj : ∀ s ∈ D.M, ∀ y ∈ D.M ⊓ centralizer (V : Set G),
      s * y * s⁻¹ ∈ D.M ⊓ centralizer (V : Set G) := by
    intro s hs y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨D.M.mul_mem (D.M.mul_mem hs hy.1) (D.M.inv_mem hs), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : s⁻¹ * v * s ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (hMV (D.M.inv_mem hs)) v).1 hv
      simpa using this
    have h1 : (s⁻¹ * v * s) * y = y * (s⁻¹ * v * s) := Subgroup.mem_centralizer_iff.1 hy.2 _ hv'
    calc v * (s * y * s⁻¹) = s * ((s⁻¹ * v * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * v * s)) * s⁻¹ := by rw [h1]
      _ = s * y * s⁻¹ * v := by group
  have hn : t ∈ normalizer ((D.M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj t htM y hy, fun hy => ?_⟩
    have h := hconj t⁻¹ (D.M.inv_mem htM) _ hy
    have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rwa [e] at h
  rw [hCU]
  exact Nat.le_of_dvd (by norm_num) (s16c167_relIndex_dvd_two_of_sq_mem hn
    (Subgroup.mem_inf.2 ⟨D.M.pow_mem htM 2, ht2⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
