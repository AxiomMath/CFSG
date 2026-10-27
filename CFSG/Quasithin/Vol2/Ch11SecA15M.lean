module

public import CFSG.Quasithin.Vol2.Ch11SecA15Kind
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch11SecA15Block

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem card_quot_ne_SL2 (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {m : ℕ} (hm : 1 ≤ m) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 2 ^ m * oSL2 m := by
  have hn : 2 ≤ n := h.one_lt
  intro hc
  rcases card_quot_cases hG2 h1102 h with ⟨-, hc'⟩ | ⟨-, hc'⟩ | ⟨-, hc'⟩ <;> rw [hc] at hc'
  · have h1 := eq_of_two_pow_mul_odd (odd_oSL2 hm) (odd_oSL3 (by omega)) hc'
    subst h1
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    exact not_dvd_oSL2_oSL3 (n := n) (by omega) (h2 ▸ dvd_rfl)
  · have h1 := eq_of_two_pow_mul_odd (odd_oSL2 hm) (odd_oSp4 (by omega)) hc'
    subst h1
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    exact not_dvd_oSL2_oSp4 (n := n) (by omega) (h2 ▸ dvd_rfl)
  · have h1 := eq_of_two_pow_mul_odd (odd_oSL2 hm) (odd_oG2 (by omega)) hc'
    subst h1
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    exact not_dvd_oSL2_oG2 (n := n) (by omega) (h2 ▸ dvd_rfl)

theorem card_quot_ne_SL42 (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 2 ^ 6 * 315 := by
  have hn : 2 ≤ n := h.one_lt
  intro hc
  rcases card_quot_cases hG2 h1102 h with ⟨-, hc'⟩ | ⟨-, hc'⟩ | ⟨-, hc'⟩ <;> rw [hc] at hc'
  · have h1 := eq_of_two_pow_mul_odd (by decide) (odd_oSL3 (by omega)) hc'
    obtain rfl : n = 2 := by omega
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    revert h2
    decide
  · have h1 := eq_of_two_pow_mul_odd (by decide) (odd_oSp4 (by omega)) hc'
    omega
  · have h1 := eq_of_two_pow_mul_odd (by decide) (odd_oG2 (by omega)) hc'
    omega

theorem not_concl443TwoI (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (M VB : Subgroup G) : ¬ Concl443TwoI G T M L VB := by
  rintro ⟨-, ⟨k, hk, hX⟩ | hX | hX | ⟨e⟩ | ⟨e⟩ | ⟨-, hZ, ⟨e⟩⟩ | hX, -⟩
  ·
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hX
    have ψ := φ.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    refine card_quot_ne_SL2 hG2 h1102 h (m := k) (by omega) ?_
    rw [Nat.card_congr ψ.toEquiv, card_PSL_two hK, card_SL_two hK]
  ·
    refine card_quot_ne hG2 h1102 h (N := 168) (by norm_num) ?_
    rw [card_of_isPSL (k := 3) (p := 2) (e := 1) (by norm_num)
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hX)]
    decide
  ·
    refine card_quot_ne_SL42 hG2 h1102 h ?_
    rw [card_of_isPSL (k := 4) (p := 2) (e := 1) (by norm_num)
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hX)]
    decide
  ·
    refine card_quot_ne hG2 h1102 h (N := 360) (by norm_num) ?_
    rw [Nat.card_congr e.some.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  ·
    refine card_quot_ne hG2 h1102 h (N := 2520) (by norm_num) ?_
    rw [Nat.card_congr e.some.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  ·
    refine card_quot_ne hG2 h1102 h (N := 1080) (by norm_num) ?_
    rw [(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr e.toEquiv, hZ, nat_card_alternatingGroup, Nat.card_fin]
    decide
  ·
    exact card_quot_ne hG2 h1102 h (N := 6048) (by norm_num) (card_of_isPSU_three
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hX))

omit [Finite G] in
theorem conjSubgroupsBy_eq_singleton {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    conjSubgroupsBy X L = {L} := by
  ext K
  simp only [conjSubgroupsBy, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hX hx) z).mp hz
    · intro hy
      refine ⟨x⁻¹ * y * x, ?_, by simp [mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hX hx)) y).mp hy
      simpa [mul_assoc] using this
  · rintro rfl
    refine ⟨1, X.one_mem, ?_⟩
    ext y
    simp

theorem not_orth4213 (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (M V : Subgroup G) : ¬ Orth4213 G M L V := by
  rintro ⟨-, hX, -⟩
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hX
  have ψ := φ.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  refine card_quot_ne_SL2 hG2 h1102 h (m := 2) (by omega) ?_
  rw [Nat.card_congr ψ.toEquiv, card_PSL_two hK, card_SL_two hK]

theorem isUniqueM_L' (h4213 : TmpL6_4_2_13) (hG2 : FactG2DerivedOrder) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    IsUniqueM L (Subgroup.normalizer (L : Set G)) := by
  have hH421 : Ch10.TmpL6_Hyp4_2_1 G T (Subgroup.normalizer (L : Set G)) L :=
    ⟨h.fsu.simple, h.fsu.nonabelian, h.fsu.qtke, h.fsu.sylow, isMaxTwoLocal_M h331 h,
      h.normal, h.fsu.maximal, h.fsu.faithful, Subgroup.le_normalizer, h.fsu.quasisimple⟩
  have hO : pCoreOf 2 L ≠ ⊥ := fun h0 =>
    fsuV_ne_bot h (le_bot_iff.mp (h0 ▸ fsuV_le_pCoreOf_L h1102 h))
  have hNot : IsNotation4211 T (Subgroup.normalizer (L : Set G)) L L := by
    refine ⟨Subgroup.le_normalizer, fun x hx => Set.mem_mul.mpr ⟨x, hx, 1,
      (pCoreOf 2 (L ⊔ T)).one_mem, mul_one x⟩, ?_, hO⟩
    rw [conjSubgroupsBy_eq_singleton h.normal, conjSubgroupsBy_eq_singleton Subgroup.le_normalizer]
  rcases h4213 G T _ L L hH421 hNot with h' | ⟨hC, -⟩ | hO
  · exact h'
  · exact (not_concl443TwoI hG2 h1102 h _ _ hC).elim
  · exact (not_orth4213 hG2 h1102 h _ _ hO).elim

end CFSG.Quasithin.Vol2.Ch11.SecA
