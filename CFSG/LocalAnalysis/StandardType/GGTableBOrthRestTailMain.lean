module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.SeitzReduction.OmegaPilot

namespace OrthRestTail

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def TorusConcl (Q : (ι → K) → K) (p r : ℕ) : Prop :=
  ∃ U E : Subgroup (GL ι K), U ≤ LargeEvenOmega Q ∧ E ≤ LargeEvenOmega Q ∧ U ≠ ⊥ ∧
    (∀ g ∈ U, g ^ 2 = 1) ∧ E ≤ Subgroup.normalizer (U : Set (GL ι K)) ∧ IsElemAbelian p E ∧
    Nat.card E = p ^ r

variable [CharP K 2] {Q : QuadraticForm K (ι → K)} {m : ℕ} (F : HypFrame Q m)

theorem torusConcl_even {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M σ : Matrix.SpecialLinearGroup (Fin 2) K} (hM : orderOf M = p) (hσ : σ * M * σ⁻¹ = M⁻¹)
    (hm : 3 ≤ m) (hme : Even m) {P : Subgroup (GL ι K)} {SP : Set ι} (hPS : P ≤ suppSub K SP)
    (hSP : Disjoint SP (F.pairSet 0 m)) (hPab : IsElemAbelian p P)
    (hPΩ : P ≤ LargeEvenOmega ⇑Q) {e : ℕ} (hPc : Nat.card P = p ^ e) :
    TorusConcl ⇑Q p (m - 1 + e) := by
  have hMp : M ^ p = 1 := hM ▸ pow_orderOf_eq_one M
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hme
  have hk2 : 2 + 2 * (k - 1) ≤ m := by omega
  set B := F.block01 (by omega)
  set T0 := blkTorus B ⊥ (Subgroup.zpowers M) with hT0
  set T1 := fullTorus F M 2 (k - 1) hk2 with hT1
  have hS0 : T0 ≤ suppSub K (F.pairSet 0 2) :=
    (blkTorus_le_suppSub _ _ _).trans (suppSub_mono (F.range_block01_subset _))
  have hS1 : T1 ≤ suppSub K (F.pairSet 2 m) :=
    (fullTorus_le_suppSub F M 2 (k - 1) hk2).trans
      (suppSub_mono (F.pairSet_mono le_rfl (by omega)))
  have hd01 : Disjoint (F.pairSet 0 2) (F.pairSet 2 m) := F.pairSet_disjoint le_rfl
  have hS01 : T0 ⊔ T1 ≤ suppSub K (F.pairSet 0 m) :=
    sup_le (hS0.trans (suppSub_mono (F.pairSet_mono le_rfl (by omega))))
      (hS1.trans (suppSub_mono (F.pairSet_mono (by omega) le_rfl)))
  have hdP : Disjoint (F.pairSet 0 m) SP := hSP.symm
  set g₀ := B.blkGL (unipSL, 1) with hg₀
  have hg₀S : g₀ ∈ suppSub K (F.pairSet 0 2) :=
    suppSub_mono (F.range_block01_subset _) (B.blkGL_mem_suppSub _)
  have hcent : T0 ⊔ T1 ⊔ P ≤ Subgroup.centralizer {g₀} := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
      have ha : a = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hab).1
      rw [Subgroup.mem_centralizer_singleton_iff, hg₀, ← map_mul, ← map_mul, ha]
      congr 1
      exact Prod.ext (by simp) (by simp)
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_suppSub hd01 hg₀S (hS1 hy)).symm
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_suppSub hdP
        (suppSub_mono (F.pairSet_mono le_rfl (by omega)) hg₀S) (hPS hy)).symm
  refine ⟨Subgroup.zpowers g₀, T0 ⊔ T1 ⊔ P, Subgroup.zpowers_le.mpr (F.siegel_mem_omega hm),
    sup_le (sup_le (blkTorus_le_omega hpo hMp hσ _ bot_le le_rfl)
      (fullTorus_le_omega F hpo hMp hσ 2 _ _)) hPΩ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    have := B.blkGL_injective (h.trans (map_one B.blkGL).symm)
    exact unipSL_ne_one (congrArg Prod.fst this)
  · intro g hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h2 : g₀ ^ 2 = 1 := by
      rw [hg₀, ← map_pow, show ((unipSL, 1) : Matrix.SpecialLinearGroup (Fin 2) K ×
        Matrix.SpecialLinearGroup (Fin 2) K) ^ 2 = 1 from Prod.ext unipSL_sq (one_pow 2), map_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h2,
      _root_.one_zpow]
  · refine le_normalizer_of_commute fun x hx y hy => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp (hcent hy)
    exact (Commute.zpow_left (show Commute g₀ y from hy'.symm) j).eq
  · exact TableB.isElemAbelian_sup (TableB.isElemAbelian_sup
      (isElemAbelian_blkTorus B isElemAbelian_bot' (isElemAbelian_zpowers' hMp))
      (isElemAbelian_fullTorus F hMp 2 _ _)
      fun a ha c hc => commute_of_mem_suppSub hd01 (hS0 ha) (hS1 hc)) hPab
      fun a ha c hc => commute_of_mem_suppSub hdP (hS01 ha) (hPS hc)
  · rw [card_sup_of_suppSub hdP hS01 hPS, card_sup_of_suppSub hd01 hS0 hS1, card_blkTorus,
      Subgroup.card_bot, Nat.card_zpowers, hM, card_fullTorus F hM, hPc,
      show m - 1 + e = 1 + 2 * (k - 1) + e by omega, pow_add, pow_add, pow_one]
    ring

theorem torusConcl_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M σ : Matrix.SpecialLinearGroup (Fin 2) K} (hM : orderOf M = p) (hσ : σ * M * σ⁻¹ = M⁻¹)
    (hm : 3 ≤ m) (hmo : Odd m) {P : Subgroup (GL ι K)} {SP : Set ι} (hPS : P ≤ suppSub K SP)
    (hSP : Disjoint SP (F.pairSet 0 m)) (hPab : IsElemAbelian p P)
    (hPΩ : P ≤ LargeEvenOmega ⇑Q) {e : ℕ} (hPc : Nat.card P = p ^ e) :
    TorusConcl ⇑Q p (m - 1 + e) := by
  have hMp : M ^ p = 1 := hM ▸ pow_orderOf_eq_one M
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hmo
  have hk2 : 0 + 2 * k ≤ m := by omega
  set T1 := fullTorus F M 0 k hk2 with hT1
  have hS1 : T1 ≤ suppSub K (F.pairSet 0 (m - 1)) :=
    (fullTorus_le_suppSub F M 0 k hk2).trans (suppSub_mono (F.pairSet_mono le_rfl (by omega)))
  have hS1' : T1 ≤ suppSub K (F.pairSet 0 m) :=
    hS1.trans (suppSub_mono (F.pairSet_mono le_rfl (by omega)))
  have hdP : Disjoint (F.pairSet 0 m) SP := hSP.symm
  have hst := F.hyp ⟨m - 1, by omega⟩
  have hs1 : F.X ⟨m - 1, by omega⟩ ∉ F.pairSet 0 (m - 1) :=
    F.X_not_mem_pairSet (Or.inr (by dsimp only; omega))
  have ht1 : F.Y ⟨m - 1, by omega⟩ ∉ F.pairSet 0 (m - 1) :=
    F.Y_not_mem_pairSet (Or.inr (by dsimp only; omega))
  have hsP : F.X ⟨m - 1, by omega⟩ ∉ SP := fun h =>
    Set.disjoint_left.mp hSP h ⟨⟨m - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega,
      Or.inl rfl⟩
  have htP : F.Y ⟨m - 1, by omega⟩ ∉ SP := fun h =>
    Set.disjoint_left.mp hSP h ⟨⟨m - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega,
      Or.inr rfl⟩
  obtain ⟨g, hg, hg1⟩ := F.exists_eich_ne_one hm
  have hEΩ : T1 ⊔ P ≤ LargeEvenOmega ⇑Q := sup_le (fullTorus_le_omega F hpo hMp hσ 0 _ _) hPΩ
  refine ⟨eichSub hst (F.pairSet 0 (m - 1)) ⊓ LargeEvenOmega ⇑Q, T1 ⊔ P, inf_le_right, hEΩ, ?_,
    fun g hg => eichSub_sq hst hg.1, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hg
    exact hg1 (Subgroup.mem_bot.mp hg)
  · refine le_normalizer_inf (sup_le ?_ ?_) (hEΩ.trans (le_normalizer_self _))
    · exact le_normalizer_eichSub hst hs1 ht1 hS1
        ((fullTorus_le_omega F hpo hMp hσ 0 _ _).trans (TableBOrth.omega_le_orth _))
        fun h hh w hw k hk => (hS1 hh).mulVec_eq_zero hw k hk
    · refine le_normalizer_eichSub hst hsP htP hPS (hPΩ.trans (TableBOrth.omega_le_orth _))
        fun h hh w hw k hk => ?_
      have hfix := IsSuppMat.mulVec_eq_self (hPS hh) (v := w) fun j hj =>
        hw j fun hj' => Set.disjoint_left.mp hSP hj (F.pairSet_mono le_rfl (by omega) hj')
      rw [hfix]
      exact hw k hk
  · exact TableB.isElemAbelian_sup (isElemAbelian_fullTorus F hMp 0 _ _) hPab
      fun a ha c hc => commute_of_mem_suppSub hdP (hS1' ha) (hPS hc)
  · rw [card_sup_of_suppSub hdP hS1' hPS, card_fullTorus F hM, hPc, ← pow_add]
    congr 1
    omega

theorem torusConcl_of_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M σ : Matrix.SpecialLinearGroup (Fin 2) K} (hM : orderOf M = p) (hσ : σ * M * σ⁻¹ = M⁻¹)
    (hm : 3 ≤ m) {P : Subgroup (GL ι K)} {SP : Set ι} (hPS : P ≤ suppSub K SP)
    (hSP : Disjoint SP (F.pairSet 0 m)) (hPab : IsElemAbelian p P)
    (hPΩ : P ≤ LargeEvenOmega ⇑Q) {e : ℕ} (hPc : Nat.card P = p ^ e) :
    TorusConcl ⇑Q p (m - 1 + e) := by
  rcases Nat.even_or_odd m with h | h
  · exact torusConcl_even F hp hp2 hM hσ hm h hPS hSP hPab hPΩ hPc
  · exact torusConcl_odd F hp hp2 hM hσ hm h hPS hSP hPab hPΩ hPc

end OrthRestTail

end CFSG.StandardType
