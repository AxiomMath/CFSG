module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.Quasithin.Background.Asc81cPfTrans2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614_rkIdx_le (D : Data G) {V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : Min1614 D V U) : rkIdx (imgTil ⊥ V hV U) ≤ D.k + 2 := by
  have h1 := s16n9b_rkIdx_imgTil_le ⊥ V hV U
  have h2 : (E3.mQuot V U : ℕ∞) ≤ ((D.k + 2 : ℕ) : ℕ∞) := hU.2.2.1.trans_le hU.2.2.2
  exact h1.trans (by exact_mod_cast h2)

theorem s1614_exists_involution (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : D.M ≤ normalizer (V : Set G)) {U : Subgroup G} (hUV : U ≤ V) (hU0 : U ≠ ⊥)
    (hUC : ¬ centralizer (U : Set G) ≤ D.M) (hUΓ : U ∉ gammaEleven D.M V) :
    ∃ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 ∧
      imgTil ⊥ V hV U ≤ fixV (Subgroup.zpowers t) := by
  classical
  have hMst : D.M ≤ stabTil ⊥ V :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hcont : ∃ x : G, x ∈ D.M ⊓ centralizer (U : Set G) ∧ (∃ k : ℕ, orderOf x = 2 ^ k) ∧
      x ∉ centralizer (V : Set G) := by
    by_contra hcon
    apply hUΓ
    refine ⟨hUV, hU0, hUC, ?_⟩
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hx, hk⟩
    by_contra hxV
    exact hcon ⟨x, hx, hk, hxV⟩
  obtain ⟨x, hxMC, ⟨k, hxk⟩, hxV⟩ := hcont
  have hxM : x ∈ D.M := hxMC.1
  have hxC : x ∈ centralizer (U : Set G) := hxMC.2
  let g : ↥(stabTil ⊥ V) := ⟨x, hMst hxM⟩
  let φ : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV g
  have hφM : φ ∈ Mbar D.M ⊥ V hV := actTil_mem_barSub ⊥ V hV hxM (hMst hxM)
  have hφ1 : φ ≠ 1 := by
    intro h
    have h1 := (actTil_eq_one_iff ⊥ V hV g).1 h
    apply hxV
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h2 := Subgroup.mem_bot.1 (h1 v hv)
    have h3 : x * v * x⁻¹ = v := by
      have := mul_inv_eq_one.1 h2
      simpa using this
    calc v * x = (x * v * x⁻¹) * x := by rw [h3]
      _ = x * v := by group
  have hord : orderOf φ ∣ 2 ^ k := by
    have h1 : orderOf φ ∣ orderOf g := orderOf_map_dvd (actTil ⊥ V hV) g
    have h2 : orderOf g = 2 ^ k := (Subgroup.orderOf_coe g).symm.trans hxk
    exact h2 ▸ h1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hφ1 (orderOf_eq_one_iff.1 (by simpa using hb))
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
  refine ⟨φ ^ (2 ^ c), Subgroup.pow_mem _ hφM _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hb]; exact pow_dvd_pow 2 (by omega)),
      hb, pow_succ]
    exact Nat.mul_div_cancel_left 2 (by positivity)
  · intro q hq
    obtain ⟨y, hyU, rfl⟩ := (mem_imgTil ⊥ V hV U q).1 hq
    have hφq : φ (mkTil ⊥ V hV y) = mkTil ⊥ V hV y := by
      show actTil ⊥ V hV g (mkTil ⊥ V hV y) = _
      rw [actTil_mk]
      congr 1
      refine IntMod.val_injective ?_
      rw [actStab_apply_val]
      have h1 := Subgroup.mem_centralizer_iff.1 hxC y.val hyU
      show x * y.val * x⁻¹ = y.val
      rw [← h1]
      group
    have hqφ : mkTil ⊥ V hV y ∈ fixV (Subgroup.zpowers φ) :=
      mem_fixV_zpowers_iff_apply.2 hφq
    exact mem_fixV_zpowers_iff_apply.2
      (hqφ _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers φ) _))

theorem s1614_nu_prime (D : Data G) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hP : PairFacts D.M ⊥ V) {U : Subgroup G}
    (hUC : ¬ centralizer (U : Set G) ≤ D.M) {p : ℕ} (hp : p ∈ D.sig)
    {B : Subgroup (MulAut (Vtil ⊥ V hV))} (hB : B ≤ Mbar D.M ⊥ V hV) (hBp : IsPGroup p ↥B)
    (hBc : ¬ IsCyclic ↥B) {z : Vtil ⊥ V hV} (hz : z ∈ imgTil ⊥ V hV U) (hz1 : z ≠ 1)
    (hzB : z ∈ fixV B) : False := by
  obtain ⟨x, hxU, hxz⟩ := (mem_imgTil ⊥ V hV U z).1 hz
  have hx0 : x.val ∉ (⊥ : Subgroup G) := by
    intro h
    apply hz1
    rw [← hxz]
    have : x = 1 := IntMod.val_injective (by rw [IntMod.val_one]; exact Subgroup.mem_bot.1 h)
    rw [this, map_one]
  have hE : B ≤ ptCent (Mbar D.M ⊥ V hV) (mkTil ⊥ V hV x) := by
    intro b hb
    refine Subgroup.mem_inf.2 ⟨hB hb, ?_⟩
    rw [MulAction.mem_stabilizer_iff, hxz]
    exact mem_fixV.1 hzB b hb
  have hc := centralizer_le_of_noncyclic_bar D h61 (D.sig_prime p hp).1 (D.sig_prime p hp).2 hp hV
    hP (Or.inl rfl) (by simp) x hx0 hE hBp hBc
  exact hUC (le_trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)) hc)

theorem s1614_false_of_row (D : Data G) (h61 : UC6.R6_1 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) {U : Subgroup G}
    (hU : Min1614 D V U) (hUΓ : U ∉ gammaEleven D.M V)
    (hk : D.k < mBar D.M ⊥ V hV) (hrk : D.k + 2 < rk (Vtil ⊥ V hV))
    (hrow : ∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 → D.k < rkIdx (fixV (Subgroup.zpowers t)) →
      ∀ W : Subgroup (Vtil ⊥ V hV), W ≤ fixV (Subgroup.zpowers t) → rkIdx W ≤ D.k + 2 →
        ∃ z ∈ W, z ≠ 1 ∧ ∃ p ∈ D.sig, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)),
          B ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ z ∈ fixV B) :
    False := by
  have hP : PairFacts D.M ⊥ V := hc.setting.hyp16.hyp125.pairFacts
  by_cases hU0 : U = ⊥
  · subst hU0
    have h1 := s1614_rkIdx_le D hV hU
    have h2 : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
      unfold imgTil intSub
      rw [Subgroup.bot_subgroupOf]
      exact Subgroup.map_bot _
    rw [h2] at h1
    have h3 := rk_add_rkIdx (⊥ : Subgroup (Vtil ⊥ V hV))
    rw [rk_bot] at h3
    omega
  · obtain ⟨t, htM, ht2, htU⟩ :=
      s1614_exists_involution D hV hP.le_normalizer hU.1 hU0 hU.2.1 hUΓ
    have hmt : D.k < rkIdx (fixV (Subgroup.zpowers t)) :=
      lt_of_lt_of_le hk (CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two htM ht2)
    obtain ⟨z, hzW, hz1, p, hp, B, hB, hBp, hBc, hzB⟩ :=
      hrow t htM ht2 hmt (imgTil ⊥ V hV U) htU (s1614_rkIdx_le D hV hU)
    exact s1614_nu_prime D h61 hV hP hU.2.1 hp hB hBp hBc hzW hz1 hzB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
