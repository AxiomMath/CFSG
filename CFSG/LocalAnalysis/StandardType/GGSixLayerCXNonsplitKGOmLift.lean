module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmSide

public section

namespace CFSG.StandardType

namespace OmNonsplit

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  LayerCores LayerCores.OrthSplit LayerFacts
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_component_of_fix (hQ : (polarBilin Q).Nondegenerate) {a b : V ≃ₗ[K] V}
    (haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hab : a * b = b * a) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ f) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) (hap : a ^ p = 1) (hbp : b ^ p = 1) [Fintype (Subgroup.zpowers a)]
    (hA : (Fintype.card (Subgroup.zpowers a) : K) ≠ 0)
    {T : Subgroup (fixSp (Subgroup.zpowers a) ≃ₗ[K] fixSp (Subgroup.zpowers a))}
    (hTq : CFSG.IsQuasisimple T) (hTs : CFSG.Assembly.IsSubnormal T
      (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp (Subgroup.zpowers a)))))
    (hpT : ¬ p ∣ Nat.card T) :
    ∃ L : Subgroup (V ≃ₗ[K] V), T.map (extFix hA) ≤ L ∧ CFSG.IsQuasisimple L ∧
      L ≤ Subgroup.centralizer (Subgroup.zpowers b : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q ∧
      CFSG.Assembly.IsSubnormal L (Subgroup.centralizer (Subgroup.zpowers b : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      (∃ k ∈ L, ∀ l ∈ L, a⁻¹ * l * a = k⁻¹ * l * k) ∧ OmModel K L := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype (Subgroup.zpowers b) := Fintype.ofFinite _
  have hB : (Fintype.card (Subgroup.zpowers b) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_card_ne_zero_of_odd
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hbp))
  have hAO : Subgroup.zpowers a ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr haO
  have hBO : Subgroup.zpowers b ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr hbO
  have hbC : b ∈ Subgroup.centralizer (Subgroup.zpowers a : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute a b from hab) k).eq
  have haC : a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute b a from hab.symm) k).eq
  have hBC : Subgroup.zpowers b ≤ Subgroup.centralizer (Subgroup.zpowers a : Set (V ≃ₗ[K] V)) :=
    Subgroup.zpowers_le.mpr hbC
  have hbs : b ∈ stab (Subgroup.zpowers a) := centralizer_le_stab hbC
  have hR₀ := nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO)
  have hb₀ : restrFix (Subgroup.zpowers a) ⟨b, hbs⟩ = 1 := by
    refine eq_one_of_pow_eq_one_orth hR₀ hp hp2 hK hq1 hq2 hTq hTs hpT
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => map_of_mem hbO (x : V)) ?_
    rw [← map_pow]
    have h : (⟨b, hbs⟩ : stab (Subgroup.zpowers a)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hbp)
    rw [h, map_one]
  have hbfix : ∀ v ∈ fixSp (Subgroup.zpowers a), b v = v := fun v hv =>
    congrArg Subtype.val (LinearEquiv.congr_fun hb₀ ⟨v, hv⟩)
  have hfix_le : fixSp (Subgroup.zpowers a) ≤ fixSp (Subgroup.zpowers b) := fun v hv =>
    (mem_fixSp_iff hB).mpr fun g hg => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_apply_eq_self (hbfix v hv) k
  have havg : ∀ v, avg (Subgroup.zpowers a) (avg (Subgroup.zpowers b) v) =
      avg (Subgroup.zpowers a) v := by
    intro v
    have h1 : ∀ g : Subgroup.zpowers b,
        avg (Subgroup.zpowers a) ((g : V ≃ₗ[K] V) v) = avg (Subgroup.zpowers a) v := by
      intro g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      rw [← commute_avg (hBC g.2) v, ← hk]
      exact zpow_apply_eq_self (hbfix _ (avg_mem_fixSp v)) k
    rw [avg_apply (Subgroup.zpowers b) v, map_smul, map_sum, Finset.sum_congr rfl fun g _ => h1 g,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_smul,
      inv_mul_cancel₀ hB, one_smul]
  have hfree_le : freeSp (Subgroup.zpowers b) ≤ freeSp (Subgroup.zpowers a) := fun v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← havg v, hv, map_zero]
  have hTN : T.map (extFix hA) ≤ fixPart hB Q :=
    (Subgroup.map_mono (ggSubnormal_le hTs)).trans
      (fixPart_le_fixPart hA hQ hAO hB hBO hfree_le)
  have hTq' : CFSG.IsQuasisimple (T.map (extFix hA)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (T.equivMapOfInjective _ (extFix_injective hA)) hTq
  by_cases hI : fixSp (Subgroup.zpowers b) ≤ fixSp (Subgroup.zpowers a)
  ·
    have hfree_ge : freeSp (Subgroup.zpowers a) ≤ freeSp (Subgroup.zpowers b) := fun v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      obtain ⟨w, hw⟩ := hI (avg_mem_fixSp (A := Subgroup.zpowers b) v)
      calc avg (Subgroup.zpowers b) v =
            avg (Subgroup.zpowers a) (avg (Subgroup.zpowers b) v) := by rw [← hw, avg_avg hA]
        _ = avg (Subgroup.zpowers a) v := havg v
        _ = 0 := hv
    have hNeq : fixPart hA Q = fixPart hB Q :=
      le_antisymm (fixPart_le_fixPart hA hQ hAO hB hBO hfree_le)
        (fixPart_le_fixPart hB hQ hBO hA hAO hfree_ge)
    refine ⟨T.map (extFix hA), le_rfl, hTq', hTN.trans (fixPart_le hB hBO), ?_,
      ⟨1, one_mem _, fun l hl => ?_⟩, ?_⟩
    · refine ggSubnormal_trans (ggSubnormal_map (extFix hA) hTs) ?_
      show CFSG.Assembly.IsSubnormal (fixPart hA Q) _
      rw [hNeq]
      exact ggSubnormal_of_normal (fixPart_le hB hBO) fun u hu s hs =>
        conj_mem_fixPart hB hBO hu hs
    · have hla : l ∈ Subgroup.centralizer (Subgroup.zpowers a : Set (V ≃ₗ[K] V)) :=
        (fixPart_le hA hAO ((Subgroup.map_mono (ggSubnormal_le hTs)) hl)).1
      have h1 : a * l = l * a := Subgroup.mem_centralizer_iff.mp hla a (Subgroup.mem_zpowers a)
      calc a⁻¹ * l * a = a⁻¹ * (a * l) := by rw [mul_assoc, ← h1]
        _ = 1⁻¹ * l * 1 := by group
    · obtain ⟨h4, ⟨hsp, hT⟩ | ⟨-, hK4, ψ, hψi, hψr⟩⟩ := structure_of_isSubnormal hR₀ hTq hTs
      · exact Or.inl ⟨fixSp (Subgroup.zpowers a), inferInstance, inferInstance, inferInstance,
          Q.restrict (fixSp (Subgroup.zpowers a)), hR₀, h4, hsp,
          ⟨(T.equivMapOfInjective _ (extFix_injective hA)).symm.trans
            (MulEquiv.subgroupCongr hT)⟩⟩
      · exact Or.inr ⟨hK4, ⟨(T.equivMapOfInjective _ (extFix_injective hA)).symm.trans
          ((MulEquiv.subgroupCongr hψr.symm).trans (MonoidHom.ofInjective hψi).symm)⟩⟩
  ·
    have hlt : fixSp (Subgroup.zpowers a) < fixSp (Subgroup.zpowers b) :=
      lt_of_le_not_ge hfix_le hI
    have hR₀b := nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hB hBO)
    have h4a := (structure_of_isSubnormal hR₀ hTq hTs).1
    have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
    have h6 : 6 ≤ finrank K (fixSp (Subgroup.zpowers b)) := by
      obtain ⟨k, hk⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo _ hR₀b
      obtain ⟨k', hk'⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo _ hR₀
      omega
    have hnsp : ¬ SplitFour (Q.restrict (fixSp (Subgroup.zpowers b))) := fun h => by
      have := h.1
      omega
    obtain ⟨hqb, hoddb⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hR₀b (by omega) hnsp
    set O₀ := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp (Subgroup.zpowers b)))
      with hO₀
    have hLN : (⁅O₀, O₀⁆).map (extFix hB) ≤ fixPart hB Q :=
      Subgroup.map_mono (ggCommutator_self_le O₀)
    refine ⟨(⁅O₀, O₀⁆).map (extFix hB), ?_, ?_, hLN.trans (fixPart_le hB hBO), ?_, ?_, ?_⟩
    · calc T.map (extFix hA) = ⁅T.map (extFix hA), T.map (extFix hA)⁆ :=
            (ggCommutator_eq_of_isQuasisimple hTq').symm
        _ ≤ ⁅fixPart hB Q, fixPart hB Q⁆ := Subgroup.commutator_mono hTN hTN
        _ = (⁅O₀, O₀⁆).map (extFix hB) := by rw [Subgroup.map_commutator]; rfl
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((⁅O₀, O₀⁆).equivMapOfInjective _ (extFix_injective hB)) hqb
    · refine ggSubnormal_of_normal (hLN.trans (fixPart_le hB hBO)) fun u hu s hs => ?_
      exact conj_mem_map_extFix hB hBO
        (fun u hu s hs => LayerPDiv.conj_mem_commutator_self O₀ hu hs) hu hs
    · obtain ⟨⟨a₀, a₁⟩, ha01, ha⟩ :
          a ∈ (O₀.prod (freeCent (Subgroup.zpowers b) Q)).map (split hB) := by
        rw [← centralizer_eq_map_split hB hBO]
        exact ⟨haC, haO⟩
      obtain ⟨ha₀O, -⟩ := Subgroup.mem_prod.mp ha01
      have ha₀p : a₀ ^ p = 1 := by
        have h1 : split hB ((a₀, a₁) ^ p) = split hB 1 := by rw [map_pow, ha, hap, map_one]
        simpa using congrArg Prod.fst (split_injective hB h1)
      have ha₀c : a₀ ∈ ⁅O₀, O₀⁆ :=
        hoddb a₀ ha₀O (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one ha₀p))
      refine ⟨extFix hB a₀, ⟨a₀, ha₀c, rfl⟩, ?_⟩
      rintro _ ⟨l₀, -, rfl⟩
      rw [← ha]
      show (split hB (a₀, a₁))⁻¹ * split hB (l₀, 1) * split hB (a₀, a₁) =
        (split hB (a₀, 1))⁻¹ * split hB (l₀, 1) * split hB (a₀, 1)
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext rfl (by simp)
    · exact Or.inl ⟨fixSp (Subgroup.zpowers b), inferInstance, inferInstance, inferInstance,
        Q.restrict (fixSp (Subgroup.zpowers b)), hR₀b, by omega, hnsp,
        ⟨((⁅O₀, O₀⁆).equivMapOfInjective _ (extFix_injective hB)).symm⟩⟩

end OmNonsplit

end CFSG.StandardType
