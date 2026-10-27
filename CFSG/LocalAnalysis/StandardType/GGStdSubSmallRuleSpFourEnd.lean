module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourTwo
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall

public section

namespace CFSG.StandardType.SpFour

open Module Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

theorem exists_noncomm_of_quasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem layer_eq_of_commute {G : Type*} [Group G] [Finite G] {C D : Subgroup G}
    (hD : IsComponentOf D C)
    (hcomm : ∀ g ∈ C, g ∈ Subgroup.centralizer (D : Set G) → ∀ g' ∈ C, g * g' = g' * g) :
    LargeEvenLayer C = D := by
  refine le_antisymm (sSup_le fun K hK => ?_) (le_sSup hD)
  by_cases hKD : K = D
  · exact hKD.le
  exfalso
  obtain ⟨hKC, hKs, hKqA⟩ := hK
  obtain ⟨hDC, hDs, hDqA⟩ := hD
  have hKq : CFSG.IsQuasisimple K := (TableBSymp.isQuasisimple_iff _).mp hKqA
  have hDq : CFSG.IsQuasisimple D := (TableBSymp.isQuasisimple_iff _).mp hDqA
  have hK'c : CFSG.IsComponent (K.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hKq,
      hKs.subgroupOf⟩
  have hD'c : CFSG.IsComponent (D.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDC).symm hDq,
      hDs.subgroupOf⟩
  rcases CFSG.LocalCores.distinct_components_commute hK'c hD'c with h | h
  · have h1 := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hKC, inf_eq_left.mpr hDC] at h1
    exact hKD h1
  · have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hKcentr : ∀ k ∈ K, k ∈ Subgroup.centralizer (D : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h2 : (⟨k, hKC hk⟩ : ↥C) ∈ K.subgroupOf C := hk
      have h3 := Subgroup.mem_centralizer_iff.mp (h1 h2) ⟨d, hDC hd⟩
        (show (⟨d, hDC hd⟩ : ↥C) ∈ D.subgroupOf C from hd)
      exact congrArg Subtype.val h3
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_quasisimple hKq
    exact hab (Subtype.ext (hcomm a (hKC a.2) (hKcentr a a.2) b (hKC b.2)))

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem isCyclicOn_of_finrank_two (hK : Nat.card K = 2) {y : StatedSp m K} (hy3 : y ^ 3 = 1)
    (hrk : finrank K (LinearMap.range (spEnd y - 1)) = 2) :
    OddIso.IsCyclicOn (spEnd y) (LinearMap.range (spEnd y - 1)) := by
  set W := LinearMap.range (spEnd y - 1) with hW
  have hW0 : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrk
    omega
  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hw₁W : spEnd y w₀ ∈ W := OddIso.range_invariant (spEnd y) hw₀W
  have hw₁ : spEnd y w₀ ≠ 0 := fun h => hw₀ (spEnd_injective' y (h.trans (map_zero _).symm))
  have hw₁₀ : spEnd y w₀ ≠ w₀ := fun h =>
    hw₀ (OddIso.eq_zero_of_fixed_range (p := 3) ⟨1, by norm_num⟩ (spEnd_pow hy3) hw₀W h)
  have hindep : LinearIndependent K ![w₀, spEnd y w₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases eq_zero_or_eq_one_of_card hK s with rfl | rfl <;>
      rcases eq_zero_or_eq_one_of_card hK t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at hst
      exact absurd hst hw₁
    · rw [zero_smul, one_smul, add_zero] at hst
      exact absurd hst hw₀
    · rw [one_smul, one_smul] at hst
      have h1 : spEnd y w₀ = -w₀ := eq_neg_of_add_eq_zero_right hst
      refine absurd ?_ hw₁₀
      rw [h1]
      exact neg_eq_of_add_eq_zero_right (SpFin.add_self_eq_zero_mod K w₀)
  have hspan : finrank K (Submodule.span K (Set.range ![w₀, spEnd y w₀])) = 2 := by
    rw [finrank_span_eq_card hindep]
    simp
  have hSW : Submodule.span K (Set.range ![w₀, spEnd y w₀]) ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hw₀W
    · exact hw₁W
  have hSeq : Submodule.span K (Set.range ![w₀, spEnd y w₀]) = W :=
    Submodule.eq_of_le_of_finrank_eq hSW (by rw [hspan, hrk])
  refine ⟨w₀, hw₀W, ?_⟩
  rw [← hSeq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact OddIso.pow_mem_cyc (spEnd y) w₀ 0
  · exact OddIso.pow_mem_cyc (spEnd y) w₀ 1

theorem eq_zpowers_of_fix (hK : Nat.card K = 2) {Ã : Subgroup (StatedSp m K)}
    (hÃ : IsElemAbelian 3 Ã) {y : StatedSp m K} (hy : y ∈ Ã) (hy1 : y ≠ 1)
    (hrk : finrank K (LinearMap.range (spEnd y - 1)) = 2) {s : StatedSp m K} (hs : s ∈ Ã)
    (hfix : ∀ u ∈ LinearMap.ker (spEnd y - 1), spEnd s u = u) : s ∈ Subgroup.zpowers y := by
  classical
  haveI := SpFin.finite_statedSp_group (K := K) (m := m)
  haveI := finite_units_end (K := K) (V := Fin m ⊕ Fin m → K)
  have hy3 : y ^ 3 = 1 := hÃ.2 y hy
  set Z : Subgroup (StatedSp m K) := Ã ⊓ fixSub (LinearMap.ker (spEnd y - 1)) with hZ
  have hyZ : y ∈ Z := ⟨hy, fun u hu => mem_ker_sub_one_iff.mp hu⟩
  have hsZ : s ∈ Z := ⟨hs, hfix⟩
  set X : Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ := Z.map (spLin m K) with hX
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hÃ ha.1 hb.1]
  have hexp : ∀ a ∈ X, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hÃ.2 a ha.1, map_one]
  have hWX : ∀ a ∈ X, ∀ w ∈ LinearMap.range (spEnd y - 1),
      (a : Module.End K (Fin m ⊕ Fin m → K)) w ∈ LinearMap.range (spEnd y - 1) := by
    rintro _ ⟨a, ha, rfl⟩ w hw
    exact SpFin.rng_invariant' (x₀ := spLin m K y) (g := spLin m K a)
      (by rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hÃ hy ha.1]) hw
  have h1 := card_sq_le hK 2 (LinearMap.range (spEnd y - 1)) hrk X hcomm hexp hWX
  have hbot : (X ⊓ fixG (LinearMap.range (spEnd y - 1)) :
      Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, haf⟩
    rw [Subgroup.mem_bot]
    have h2 : a = 1 := by
      apply spEnd_injective
      refine LinearMap.ext fun v => ?_
      obtain ⟨v₁, hv₁, w, hw, rfl⟩ := OddIso.exists_fix_add_range (p := 3) ⟨1, by norm_num⟩
        (spEnd_pow hy3) v
      rw [map_add, ha.2 v₁ hv₁, haf w hw, spEnd_one, Module.End.one_apply]
    rw [h2, map_one]
  rw [hbot, Subgroup.card_bot, one_pow, mul_one] at h1
  have hcardX : Nat.card X = Nat.card Z :=
    (Nat.card_congr (Z.equivMapOfInjective (spLin m K) spLin_injective).toEquiv).symm
  rw [hcardX] at h1
  have hZ3 : Nat.card Z ≤ 3 := by nlinarith [h1]
  have hle : Subgroup.zpowers y ≤ Z := Subgroup.zpowers_le.mpr hyZ
  have heq : Subgroup.zpowers y = Z := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
    exact hZ3)
  rw [heq]
  exact hsZ

theorem endNodeAt_of_six (hK : Nat.card K = 2) {Ã : Subgroup (StatedSp 4 K)}
    (hÃ : IsElemAbelian 3 Ã) {y : StatedSp 4 K} (hy : y ∈ Ã) (hy1 : y ≠ 1)
    (blocks : SpPrimaryBlocks 2 1 3 y (proj 4 K y)) (hd : spFixedDim y = 6) :
    EndNodeAt Ã y ∧ ¬ LargeEvenSmall (layerC y) := by
  classical
  haveI := SpFin.finite_statedSp_group (K := K) (m := 4)
  have hy3 : y ^ 3 = 1 := hÃ.2 y hy
  have hy3' : spLin 4 K y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hsum : finrank K (LinearMap.ker (spEnd y - 1)) +
      finrank K (LinearMap.range (spEnd y - 1)) = 2 * 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl (SpFin.isCompl_fix_rng hy3')
    rw [SpFin.finrank_spSpace 4] at h
    exact h
  have hfix : finrank K (LinearMap.ker (spEnd y - 1)) = spFixedDim y := by
    rw [← blocks.fixed_eq]
    rfl
  have hrk : finrank K (LinearMap.range (spEnd y - 1)) = 2 := by omega
  have hDq : CFSG.IsQuasisimple (spFixedFactor y) :=
    SpFin.isQuasisimple_fixedFactor_of_six_le hK blocks (by omega)
  have hDcomp : CFSG.Assembly.IsComponentOf (spFixedFactor y)
      (Subgroup.centralizer ({y} : Set _)) :=
    SpFin.isComponentOf_of_normalized (spFixedFactor_le_centralizer y)
      (fun c hc q hq => spFixedFactor_conj hc hq) hDq
  have hcyc := isCyclicOn_of_finrank_two hK hy3 hrk
  have hlay : layerC y = spFixedFactor y :=
    layer_eq_of_commute hDcomp fun g hg hgD g' hg' =>
      sp_commute_of_centralizes ⟨1, by norm_num⟩ hy3 hcyc hg hg' hgD
  refine ⟨⟨by rw [hlay]; exact hDcomp, fun s hs => ?_⟩, ?_⟩
  · rw [hlay]
    constructor
    · intro hcent
      have hsD : s ∈ Subgroup.centralizer (spFixedFactor y : Set (StatedSp 4 K)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro d hd'
        exact (hcent d hd').symm
      obtain ⟨l, hl⟩ := scalar_on_fix_of_centralizes hsD
      have hker0 : LinearMap.ker (spEnd y - 1) ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hfix
        omega
      obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker0
      have hl1 : l = 1 := by
        rcases eq_zero_or_eq_one_of_card hK l with hl0 | hl1
        · exfalso
          have h1 := hl u₀ hu₀
          rw [hl0, zero_smul] at h1
          exact hu₀0 (spEnd_injective' s (h1.trans (map_zero _).symm))
        · exact hl1
      refine eq_zpowers_of_fix hK hÃ hy hy1 hrk hs fun u hu => ?_
      rw [hl u hu, hl1, one_smul]
    · intro hmem j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hj' : Commute j y :=
        Subgroup.mem_centralizer_singleton_iff.mp (spFixedFactor_le_centralizer y hj)
      exact (hj'.symm.zpow_left k).eq
  · rw [hlay]
    have hB : ((spForm 4 K).restrict (primaryComponent (spEnd y) (X - 1))).IsAlt :=
      fun v => spForm_isAlt (v : Fin 4 ⊕ Fin 4 → K)
    obtain ⟨φ, -⟩ := blocks.fixedFactor (X_sub_one_mem_primaryFactors y (by omega))
    obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB blocks.fixed_nondegenerate
    have hs3 : s = 3 := by
      have h1 : spFixedDim y = finrank K (primaryComponent (spEnd y) (X - 1)) := rfl
      omega
    subst hs3
    have hc : Nat.card (spFixedFactor y) = Nat.card (StatedSp 3 K) :=
      Nat.card_congr (φ.trans e).toEquiv
    rw [SymplecticFlag.card_statedSp, hK] at hc
    have h7 : 7 ∣ Nat.card (spFixedFactor y) := by
      rw [hc]
      decide +kernel
    exact IOneOrthEnd.not_largeEvenSmall_of_seven_dvd h7

end CFSG.StandardType.SpFour
