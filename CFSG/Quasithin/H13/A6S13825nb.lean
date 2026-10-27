module

public import CFSG.Quasithin.H13.A6S13825b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.SBd8.Flag

open L13825 Setting4 in
theorem L13825.exists_std_equiv_A6 (h21 : Lem13821)
    (h16 : Lem13816) (h1334 : Stmt13_3_4) {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    {S : Setting4 G T L V} (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKn : IsPSL 4 2 1 ↥(S.KSt H K)) (hhat : ¬ IsHatA6 L)
    (hTK' : ¬ T ≤ K ⊔ pCoreOf 2 H) :
    ∃ e : ↥(S.KSt H K) ≃* SpecialLinearGroup (Fin 4) (ZMod 2),
      ((S.KSt H T ⊓ S.KSt H K).subgroupOf (S.KSt H K)).map e.toMonoidHom =
        unitriangular 4 (ZMod 2) ∧
      toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)) =
        flagStabilizer 4 (ZMod 2) (minPar 4 2) := by
  obtain ⟨hKsHs, hHsN, hTsHs, -, hC, e, he⟩ := star_setup h21 h16 hS hH hK (by norm_num) hKn
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hL1K : S.L1 ≤ K := (h21 G T L V S hS H hH K hK).1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hKleH : S.KSt H T ≤ S.KSt H K ↔ T ≤ K ⊔ pCoreOf 2 H := S.kst_le_iff hF hTH hKH
  have hLK : S.KSt H S.L1 ≤ S.KSt H K := S.kst_mono hF hL1K hKH
  have hBK : S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H K := sup_le hLK inf_le_right
  have hUle : upperTriangular 4 (ZMod 2) ≤ toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)) := by
    rw [upperTriangular_eq_unitriangular (Nat.card_zmod 2), ← he]
    exact toSL_mono e le_sup_right
  obtain ⟨hQ, hCc⟩ := eq_flagStabilizer_borelOvergroupCuts hUle
  have hLT : S.KSt H (S.L1 ⊔ T) = S.KSt H S.L1 ⊔ S.KSt H T := S.kst_sup hF hL1H hTH
  have hBLT : S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K) ≤ S.KSt H (S.L1 ⊔ T) := by
    rw [hLT]
    exact sup_le_sup_left inf_le_left _
  have hLTs : Group.IsSolvable ↥(S.KSt H (S.L1 ⊔ T)) :=
    S.kst_isSolvable hF hH.1.1 (S.isSolvable_L1T h1334 hS)
  have hBs : Group.IsSolvable ↥(S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hBLT)
      (Subgroup.inclusion_injective _)
  have hQs := isSolvable_toSL e hBK hBs
  rw [hQ] at hQs
  have hTN : ∀ t ∈ S.KSt H T, ∀ {X : Subgroup G}, X ≤ H →
      T ≤ Subgroup.normalizer (X : Set G) →
      t ∈ Subgroup.normalizer ((S.KSt H X ⊔ (S.KSt H T ⊓ S.KSt H K) : Subgroup _) : Set _) :=
    fun t ht X hXH hTX => mem_normalizer_sup (S.kst_le_normalizer hF hXH hTH hTX ht)
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hHsN (hTsHs ht)⟩)
  have h9 : ¬ 9 ∣ Nat.card ↥(flagStabilizer 4 (ZMod 2)
      (borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
    rw [← hQ, card_toSL e hBK]
    intro h
    refine not_nine_dvd_sup S.T_le_normalizer_L1 hTsyl.2.1 (not_nine_dvd_of_decomp
      (CFSG.LieType.BorelTits.pCoreOf_le 2 S.L1) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S.L1)
      (S.cL1_mem hhat) fun x hx => S.L1_decomp hhat hx) ?_
    exact h.trans ((Subgroup.card_dvd_of_le hBLT).trans (S.card_kst_dvd hF hH.1.1))
  have h3 : 3 ∣ Nat.card ↥(flagStabilizer 4 (ZMod 2)
      (borelOvergroupCuts (toSL e (S.KSt H S.L1 ⊔ (S.KSt H T ⊓ S.KSt H K))))) := by
    rw [← hQ, card_toSL e hBK]
    exact (three_dvd_card_kst S hF hL1H (S.cL1_mem hhat) (S.cL1_cube hhat)
      (fun h => S.cL1_not_mem hhat (by rw [h]; exact Subgroup.one_mem _))).trans
      (Subgroup.card_dvd_of_le le_sup_left)
  obtain ⟨j, hj, hjn, hCj⟩ := cuts_minPar (by norm_num) (by norm_num) hCc hQs h3 h9
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ S.KSt H T, t ∉ S.KSt H K := by
    by_contra hne
    exact hTK' (hKleH.1 fun t ht => by_contra fun h => hne ⟨t, ht, h⟩)
  have hrev := revCuts_eq_of_conj (by norm_num) e hKsHs hHsN hC hTsHs he htT htK
    (hTN t htT hL1H S.T_le_normalizer_L1) hCc hQ
  rw [hCj, revCuts_minPar hjn] at hrev
  have hjj : 4 - j = j := eq_of_minPar_eq hj hjn hrev
  obtain rfl : j = 2 := by omega
  exact ⟨e, he, by rw [hQ, hCj]⟩

end CFSG.Quasithin.H13.A6
