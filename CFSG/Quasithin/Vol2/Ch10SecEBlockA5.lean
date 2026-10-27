module

public import CFSG.Quasithin.Vol2.Ch10SecEBlock
public import CFSG.Quasithin.Vol2.Ch10SecECase2Elt
public import CFSG.Quasithin.Vol2.Ch10SecB6C23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuUL_le_pCoreOf_L (hyp : Hyp10 G T L I) : fsuUL T L I ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : fsuVM T L I ≤ fsuL0 T L ⊔ T := (SecA.fsuVM_le_T hyp).trans le_sup_right
  have hVO : fsuVM T L I ≤ pCoreOf 2 (fsuL0 T L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVH (fsuL0_sup_le_normalizer T L I)
      (SecA.isPGroup_fsuVM hyp)
  have hVN : fsuVM T L I ≤ Subgroup.normalizer (L : Set G) :=
    (hVO.trans (SecB.pCoreOf_L0T_le_T1 hyp)).trans inf_le_right
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hVN)
    (SecA.le_normalizer_commutator hLV Subgroup.le_normalizer) ?_
  exact (SecA.isPGroup_fsuVM hyp).to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hLV)

theorem pCoreOf_L_le_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    pCoreOf 2 L ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp (mem_cComp_L0T hyp))
  rw [(h3228 G T L I hyp.fsu).2.2, SecA.fsuV_eq_of_cases12 h37 h38 hyp h12] at h1
  exact h1.trans inf_le_right

theorem false_of_isLin2Type_case2 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) {n : ℕ} (hn : 1 ≤ n) (hL : IsLin2Type L n) : False := by
  obtain ⟨x, hxL, y, hyL, w, -, hxw, hyw, hwc, v, hvU, hxv⟩ := case2_elements h2
  obtain ⟨F, _, _, hF, α, -, hαk, β, -, hβk, hβe⟩ := hL
  have hwB : w ∈ blockU L := Subgroup.commutator_mono (fsuUL_le_pCoreOf_L hyp) le_rfl hwc
  have hβw : Multiplicative.toAdd (β ⟨w, hwB⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨w, hwB⟩ = 1 := Multiplicative.toAdd.injective h0
    have h3 : (⟨w, hwB⟩ : ↥(blockU L)) ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h3
    apply hyw
    have h4 := Subgroup.mem_centralizer_iff.mp h3.2 y hyL
    rw [h4]
    group
  have hfix := hβe ⟨x, hxL⟩ ⟨w, hwB⟩ ⟨w, hwB⟩ hxw.symm
  have h2F : (2 : F) = 0 := two_eq_zero_of_card hn (by rw [Nat.card_eq_fintype_card, hF])
  have hsq := mul_self_eq_one_of_mulVec_eq h2F (α ⟨x, hxL⟩).2 hβw hfix.symm
  have hα : α (⟨x, hxL⟩ * ⟨x, hxL⟩) = 1 := by
    apply Subtype.ext
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hsq]
    rfl
  have hker : (⟨x, hxL⟩ * ⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hαk]
    exact hα
  have hxx : x * x ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype hker
  have hc := pCoreOf_L_le_centralizer h37 h38 h3228 hyp (Or.inr h2) hxx
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hvV : v ∈ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV hvU
  apply hxv
  rw [← Subgroup.mem_centralizer_iff.mp hc v hvV]
  group

theorem isA5Block_case2
    (he234 : E2.E23FourStatement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    (hNS : ¬ Subgroup.normalizer (baum T : Set G) ≤ fsuM T L) : IsShort2 L ∧ IsAltType L 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I := Or.inr h2
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hchar : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ fsuL0 T L ⊔ T ≤ Subgroup.normalizer (C : Set G) := by
    intro C hCS hC hch hLN
    apply hNS
    refine (normalizer_le_normalizer_of_characteristic hCS hch).trans
      (SecB.le_fsuM_of_L0T h331 hyp hLN fun h => hC (le_bot_iff.mp ?_))
    rw [← h]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (hyp.fsu.sylow.1.to_le (hCS.trans inf_le_left))
  obtain ⟨K, hKb, hKT, hKC⟩ := he234 G (fsuL0 T L ⊔ T) T
    ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (Ch10.T0 T L : Set G)) (fsuVM T L I)
    (SecA.minParabolic_L0T h37 h38 hyp (SecA.exists_SL_two_of_cases12 hshape hyp h12))
    (SecA.sqtkGroup_L0T hyp) (SecA.charTwo_L0T hyp)
    (SecA.isTwoReducedIn_L0T h3228 hyp (SecA.fsuV_eq_of_cases12 h37 h38 hyp h12)) hJ hchar
  have hn3 : ¬ IsAltType K 3 := fun h3 =>
    false_of_isSolvable_subnormal hyp hKb.1.2.1 hKb.1.2.2 (isSolvable_of_isAltType_three h3) hKT
  have hL : IsShort2 L ∧ ((∃ n, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3 ∨ IsAltType L 5) := by
    rcases eq_or_eq_of_mem_cComp_L0T h37 h38 hyp ht htn (hKC hn3) with rfl | rfl
    · exact ⟨hKb.1.1, hKb.2⟩
    · obtain ⟨⟨hsh, -, -⟩, hty⟩ := hKb
      rw [SecA.conjugate_eq_map] at hsh hty
      refine ⟨(Lin2.isShort2_map_equiv_iff _ L).mp hsh, ?_⟩
      rcases hty with ⟨n, hn, hlin⟩ | h3 | h5
      · exact Or.inl ⟨n, hn, (Lin2.isLin2Type_map_equiv_iff _ L n).mp hlin⟩
      · have h := L238.IsAltType.map_equiv h3 (MulAut.conj t⁻¹).symm
        rw [map_equiv_symm_map_equiv] at h
        exact Or.inr (Or.inl h)
      · have h := L238.IsAltType.map_equiv h5 (MulAut.conj t⁻¹).symm
        rw [map_equiv_symm_map_equiv] at h
        exact Or.inr (Or.inr h)
  obtain ⟨hsh, hty⟩ := hL
  refine ⟨hsh, ?_⟩
  rcases hty with ⟨n, hn, hlin⟩ | h3 | h5
  · exact (false_of_isLin2Type_case2 h37 h38 h3228 hyp h2 hn.le hlin).elim
  · exact (not_isSolvable_of_mem_cComp (mem_cComp_L0T hyp)
      (isSolvable_of_isAltType_three h3)).elim
  · exact h5

end CFSG.Quasithin.Vol2.Ch10.SecE
