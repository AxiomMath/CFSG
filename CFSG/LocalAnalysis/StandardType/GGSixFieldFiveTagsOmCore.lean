module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmSpin

public section

namespace CFSG.StandardType

namespace FieldFiveOm

open CFSG.Assembly QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCOrthogonal LayerCores LayerCores.OrthSplit LayerCores.OrthRegular
  LayerFacts OmNonsplit

theorem center_commutator_orth_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {R : QuadraticForm K W}
    (hR : (polarBilin R).Nondegenerate) (h4 : 4 ≤ Module.finrank K W) (hns : ¬ SplitFour R) :
    Subgroup.center ↥⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆ = ⊥ := by
  classical
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  by_cases hT : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0
  · exact CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT
  obtain ⟨m, hm⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hR
  have hd : Module.finrank K W = 4 ∨ Module.finrank K W = 6 := by
    by_contra hd
    push Not at hd
    exact hT (CFSG.RankThree.PartOne.exists_threeSingular_of_dim R hR (m := m) (by omega)
      (by omega))
  have hts : ∀ U : Submodule K W, Module.finrank K U = Module.finrank K W / 2 →
      ∃ u ∈ U, R u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    rcases hd with hd | hd
    · exact hns ⟨hd, U, by omega, hcon⟩
    · exact hT ⟨U, by omega, hcon⟩
  obtain ⟨hs, -, hna, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR hd hts
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    apply hna
    intro u v
    have hu : u ∈ Subgroup.center _ := h ▸ Subgroup.mem_top u
    exact (Subgroup.mem_center_iff.mp hu v).symm

section Fix

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem fix_freeSp_of_fix {T : V ≃ₗ[K] V} [Fintype (Subgroup.zpowers T)]
    (hB : (Fintype.card (Subgroup.zpowers T) : K) ≠ 0) {M : V ≃ₗ[K] V}
    (hM : ∀ v, M (T v - v) = T v - v) :
    ∀ y ∈ freeSp (Subgroup.zpowers T), M y = y := by
  intro y hy
  let H : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {b | ∀ v, M (b v - v) = b v - v}
      one_mem' := fun v => by simp
      mul_mem' := fun {b c} hb hc v => by
        have e : (b * c) v - v = (b (c v) - c v) + (c v - v) := by
          rw [LinearEquiv.mul_apply]
          abel
        rw [e, map_add, hb, hc]
      inv_mem' := fun {b} hb v => by
        have h1 : b (b⁻¹ v) = v := by
          rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id_eq]
        have e : b⁻¹ v - v = -(b (b⁻¹ v) - b⁻¹ v) := by rw [h1, neg_sub]
        show M (b⁻¹ v - v) = b⁻¹ v - v
        rw [e, map_neg, hb] }
  have hBH : Subgroup.zpowers T ≤ H := Subgroup.zpowers_le.mpr hM
  have e : y = (Fintype.card (Subgroup.zpowers T) : K)⁻¹ •
      ∑ b : Subgroup.zpowers T, (y - (b : V ≃ₗ[K] V) y) := by
    have h0 : avg (Subgroup.zpowers T) y = 0 := hy
    rw [avg_apply] at h0
    rw [Finset.sum_sub_distrib, smul_sub, h0, sub_zero, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hB, one_smul]
  rw [e, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : M ((b : V ≃ₗ[K] V) y - y) = (b : V ≃ₗ[K] V) y - y := hBH b.2 y
  rw [← neg_sub, map_neg, h1]

end Fix

section SpinCent

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem comap_spinAction_centralizer (hinj : Function.Injective (spinAction Q))
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) (H : Subgroup (spinGroup Q)) :
    ((Subgroup.centralizer (H.map (spinAction Q) : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) ⊓ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆).comap (spinAction Q) =
      Subgroup.centralizer (H : Set (spinGroup Q)) := by
  ext g
  simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨hg, -⟩, -⟩ w hw
    exact hinj (by rw [map_mul, map_mul]; exact hg _ ⟨w, hw, rfl⟩)
  · intro hg
    refine ⟨⟨?_, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v =>
      map_spinAction Q g v⟩, by rw [← hrange]; exact ⟨g, rfl⟩⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hg w hw]

end SpinCent

section Orth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_fixedCore_orth (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 2)
    {T : V ≃ₗ[K] V} (hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hT5 : T ^ 5 = 1)
    {S : Subgroup (V ≃ₗ[K] V)} (hSq : CFSG.IsQuasisimple S)
    (hSO : S ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hSfix : ∀ M ∈ S, ∀ v, M (T v - v) = T v - v) :
    ∃ L : Subgroup (V ≃ₗ[K] V), S ≤ L ∧ CFSG.IsQuasisimple L ∧
      L ≤ Subgroup.centralizer (Subgroup.zpowers T : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q ∧
      IsSubnormal L (Subgroup.centralizer (Subgroup.zpowers T : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) ∧ OmModel K L ∧
      ∀ b ∈ TauCeti.QuadraticMap.orthogonalGroup Q, b * T = T * b → b ^ 5 = 1 →
        ∃ k ∈ L, (∀ l ∈ L, b⁻¹ * l * b = k⁻¹ * l * k) ∧ k ^ 5 = 1 ∧
          (k = 1 → ∀ M ∈ S, M * b = b * M ∧ ∀ v, M (b v - v) = b v - v) ∧
          ((∀ l ∈ L, l * k = k * l) → k = 1) := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype (Subgroup.zpowers T) := Fintype.ofFinite _
  have hodd5 : ∀ {G : Type} [Group G] {g : G}, g ^ 5 = 1 → Odd (orderOf g) := fun hg =>
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hg)
  have hA : (Fintype.card (Subgroup.zpowers T) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_card_ne_zero_of_odd (hodd5 hT5)
  have hAO : Subgroup.zpowers T ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr hTO
  set O₀ := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp (Subgroup.zpowers T)))
    with hO₀
  have hR₀ := nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO)
  have hSN : S ≤ fixPart hA Q := fun M hM =>
    mem_fixPart_of_fixes hA hQ hAO (hSO hM) (fix_freeSp_of_fix hA (hSfix M hM))
  have hSr : S ≤ (extFix hA).range := hSN.trans (Subgroup.map_le_range _ _)
  have hS'q : CFSG.IsQuasisimple (S.comap (extFix hA)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((S.comap (extFix hA)).equivMapOfInjective _ (extFix_injective hA)).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hSr))).symm hSq
  have hS'O₀ : S.comap (extFix hA) ≤ O₀ := fun g hg => by
    obtain ⟨g', hg', hgg'⟩ := hSN hg
    rwa [extFix_injective hA hgg'] at hg'
  have h3 : 3 ≤ Module.finrank K (fixSp (Subgroup.zpowers T)) := by
    by_contra h
    exact not_le_of_isSolvable hS'q (isSolvable_orthogonalGroup_of_finrank_le_two hR₀ (by omega))
      hS'O₀
  have hnsp : ¬ SplitFour (Q.restrict (fixSp (Subgroup.zpowers T))) := by
    intro hsp
    obtain ⟨hexc, -⟩ := orthogonal_regular_space_coverage _ hR₀ h3
    exact not_le_of_isSolvable hS'q
      (isSolvable_of_no_prime_gt_three' (hexc (Or.inr ⟨hsp, Or.inl hK⟩))) hS'O₀
  have h4 : 4 ≤ Module.finrank K (fixSp (Subgroup.zpowers T)) := by
    obtain ⟨k, hk⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo _ hR₀
    omega
  obtain ⟨hq₀, hodd₀⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hR₀ h3 hnsp
  have hZ₀ := center_commutator_orth_eq_bot hR₀ h4 hnsp
  have hLN : (⁅O₀, O₀⁆).map (extFix hA) ≤ fixPart hA Q :=
    Subgroup.map_mono (ggCommutator_self_le O₀)
  refine ⟨(⁅O₀, O₀⁆).map (extFix hA), ?_, ?_, hLN.trans (fixPart_le hA hAO), ?_, ?_, ?_⟩
  · calc S = ⁅S, S⁆ := (ggCommutator_eq_of_isQuasisimple hSq).symm
      _ ≤ ⁅fixPart hA Q, fixPart hA Q⁆ := Subgroup.commutator_mono hSN hSN
      _ = (⁅O₀, O₀⁆).map (extFix hA) := by rw [Subgroup.map_commutator]; rfl
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((⁅O₀, O₀⁆).equivMapOfInjective _ (extFix_injective hA)) hq₀
  · exact ggSubnormal_of_normal (hLN.trans (fixPart_le hA hAO)) fun u hu s hs =>
      conj_mem_map_extFix hA hAO
        (fun u hu s hs => LayerPDiv.conj_mem_commutator_self O₀ hu hs) hu hs
  · exact Or.inl ⟨fixSp (Subgroup.zpowers T), inferInstance, inferInstance, inferInstance,
      Q.restrict (fixSp (Subgroup.zpowers T)), hR₀, h4, hnsp,
      ⟨((⁅O₀, O₀⁆).equivMapOfInjective _ (extFix_injective hA)).symm⟩⟩
  intro b hbO hbT hb5
  have hbC : b ∈ Subgroup.centralizer (Subgroup.zpowers T : Set (V ≃ₗ[K] V)) ⊓
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, hbO⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute T b from hbT.symm) k).eq
  obtain ⟨⟨b₀, b₁⟩, hb01, hb⟩ :
      b ∈ (O₀.prod (freeCent (Subgroup.zpowers T) Q)).map (split hA) := by
    rw [← centralizer_eq_map_split hA hAO]
    exact hbC
  obtain ⟨hb₀O, -⟩ := Subgroup.mem_prod.mp hb01
  have hb₀5 : b₀ ^ 5 = 1 := by
    have h1 : split hA ((b₀, b₁) ^ 5) = split hA 1 := by rw [map_pow, hb, hb5, map_one]
    simpa using congrArg Prod.fst (split_injective hA h1)
  have hb₀c : b₀ ∈ ⁅O₀, O₀⁆ := hodd₀ b₀ hb₀O (hodd5 hb₀5)
  refine ⟨extFix hA b₀, ⟨b₀, hb₀c, rfl⟩, ?_, by rw [← map_pow, hb₀5, map_one], ?_, ?_⟩
  · rintro _ ⟨l₀, -, rfl⟩
    rw [← hb]
    show (split hA (b₀, b₁))⁻¹ * split hA (l₀, 1) * split hA (b₀, b₁) =
      (split hA (b₀, 1))⁻¹ * split hA (l₀, 1) * split hA (b₀, 1)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext rfl (by simp)
  · intro hk1 M hM
    have hb₀1 : b₀ = 1 := extFix_injective hA (hk1.trans (map_one _).symm)
    subst hb₀1
    obtain ⟨m₀, -, rfl⟩ := hSN hM
    refine ⟨?_, fun v => ?_⟩
    · rw [← hb]
      show split hA (m₀, 1) * split hA (1, b₁) = split hA (1, b₁) * split hA (m₀, 1)
      rw [← map_mul, ← map_mul]
      congr 1
    · have hfree : b v - v ∈ freeSp (Subgroup.zpowers T) := by
        have e : b v - v = ((b₁ ⟨v - avg _ v, sub_avg_mem_freeSp hA v⟩ : freeSp _) : V) -
            (v - avg (Subgroup.zpowers T) v) := by
          rw [← hb, split_apply]
          simp only [LinearEquiv.coe_one, id_eq]
          abel
        rw [e]
        exact Submodule.sub_mem _ (b₁ _).2 (sub_avg_mem_freeSp hA v)
      exact extFix_apply_free hA m₀ ⟨b v - v, hfree⟩
  · intro hc
    have hb₀1 : b₀ = 1 := by
      have hz : (⟨b₀, hb₀c⟩ : ↥⁅O₀, O₀⁆) ∈ Subgroup.center ↥⁅O₀, O₀⁆ := by
        rw [Subgroup.mem_center_iff]
        intro h
        apply Subtype.ext
        show (h : fixSp (Subgroup.zpowers T) ≃ₗ[K] fixSp (Subgroup.zpowers T)) * b₀ = b₀ * h
        exact extFix_injective hA (by rw [map_mul, map_mul]; exact hc _ ⟨h, h.2, rfl⟩)
      rw [hZ₀, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    rw [hb₀1, map_one]

end Orth

end FieldFiveOm

end CFSG.StandardType
