module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.BenderCore
public import CFSG.Quasithin.Recognition.F112Crit.APrime.BenderModule
public import CFSG.Quasithin.Recognition.F112Crit.APrime.BenderP2
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config
public import CFSG.Quasithin.Recognition.F112Crit.Lemma61

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.CosetGeom (critDist odd_critDist_of_not_isFFModule)

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem sup_conjSub_eq_P₂ (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1) {g : G}
    (hg : g ∈ P₂ L1 L2 S) (hg' : g ∉ P₁ L1 L2 S) : S ⊔ conjSub g S = P₂ L1 L2 S := by
  have hP : P₂ L1 L2 S = L2 ⊔ S := P₂_eq_sup_of_vS3 hR hS3 hS
  obtain ⟨l, hlL2, s, hsS, hgs⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (H := L2) (K := S)
      hR.hyp.h2.normalizes).mp (by rw [← hP]; exact hg)
  have hB2leP1 : borelOf L2 S ≤ P₁ L1 L2 S :=
    le_sup_right.trans (le_sup_left.trans le_sup_right)
  have hSP1 : S ≤ P₁ L1 L2 S := le_sup_right.trans le_sup_right
  have hl_notP1 : l ∉ P₁ L1 L2 S := by
    intro hl
    exact hg' (by rw [hgs]; exact (P₁ L1 L2 S).mul_mem hl (hSP1 hsS))
  have hl_notB2 : l ∉ borelOf L2 S := fun h => hl_notP1 (hB2leP1 h)
  have hconj_g : conjSub g S = conjSub l S := by
    rw [hgs, conjSub_mul, F7.conjSub_eq_of_mem hsS]
  have hconjL2 : conjSub l L2 = L2 :=
    F1.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hlL2)
  have hconjS2_le_L2 : conjSub l (S ⊓ L2) ≤ L2 := by
    have h := conjSub_mono l (inf_le_right : S ⊓ L2 ≤ L2)
    rwa [hconjL2] at h
  have hconjS2p : IsPGroup 2 (conjSub l (S ⊓ L2)) :=
    F7.isPGroup_conjSub (hR.hyp.h2.sylow.isPGroup)
  have hM_eq : ((S ⊓ L2 : Subgroup G) ⊔ conjSub l (S ⊓ L2)) = L2 := by
    by_contra hne
    have hM_le_N : ((S ⊓ L2 : Subgroup G) ⊔ conjSub l (S ⊓ L2)) ≤
        Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
      hR.r2.unique_max _ le_sup_left
        (sup_le (inf_le_right : S ⊓ L2 ≤ L2) hconjS2_le_L2) hne
    have hconjS2_le_N : conjSub l (S ⊓ L2) ≤
        Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
      le_sup_right.trans hM_le_N
    have hM2 : IsPGroup 2 ↥(((S ⊓ L2 : Subgroup G) ⊔ conjSub l (S ⊓ L2))) :=
      IsPGroup.to_sup_of_normal_left' hR.hyp.h2.sylow.isPGroup hconjS2p hconjS2_le_N
    have hMeq : ((S ⊓ L2 : Subgroup G) ⊔ conjSub l (S ⊓ L2)) = S ⊓ L2 :=
      hR.hyp.h2.sylow.eq_of_le le_sup_left
        (sup_le (inf_le_right : S ⊓ L2 ≤ L2) hconjS2_le_L2) hM2
    have hconj_le : conjSub l (S ⊓ L2) ≤ S ⊓ L2 := le_sup_right.trans hMeq.le
    have hcard : Nat.card ↥(conjSub l (S ⊓ L2)) = Nat.card ↥(S ⊓ L2) :=
      Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj l))
    have hconj_eq : conjSub l (S ⊓ L2) = S ⊓ L2 :=
      Subgroup.eq_of_le_of_card_ge hconj_le (by rw [hcard])
    have hconj_inv_eq : conjSub l⁻¹ (S ⊓ L2) = S ⊓ L2 := by
      calc conjSub l⁻¹ (S ⊓ L2) = conjSub l⁻¹ (conjSub l (S ⊓ L2)) := by rw [hconj_eq]
        _ = S ⊓ L2 := conjSub_conjSub_inv l (S ⊓ L2)
    have hlN : l ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
      F7.mem_normalizer_of_conj_le hconj_eq.le hconj_inv_eq.le
    exact hl_notB2 ⟨hlL2, hlN⟩
  have hL2_le : L2 ≤ S ⊔ conjSub l S := by
    have hM_le : ((S ⊓ L2 : Subgroup G) ⊔ conjSub l (S ⊓ L2)) ≤ S ⊔ conjSub l S :=
      sup_le ((inf_le_left : S ⊓ L2 ≤ S).trans le_sup_left)
        ((conjSub_mono l (inf_le_left : S ⊓ L2 ≤ S)).trans le_sup_right)
    rwa [hM_eq] at hM_le
  have hSP2 : S ≤ P₂ L1 L2 S := by
    rw [hP]
    exact le_sup_right
  have hconj_le_P2 : conjSub g S ≤ P₂ L1 L2 S := by
    rw [conjSub_le_iff, F7.conjSub_eq_of_mem ((P₂ L1 L2 S).inv_mem hg)]
    exact hSP2
  refine le_antisymm (sup_le hSP2 hconj_le_P2) ?_
  rw [hP]
  refine sup_le ?_ le_sup_left
  rwa [← hconj_g] at hL2_le

theorem amalgamS3_of_setting (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1) :
    AmalgamS3 (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S) S L1 where
  hyp := F112W.amalgamHyp_alpha hR
  charTwo₂ := F112W.charTwo_beta hR
  le := le_sup_left
  le_normalizer := P₁_le_normalizer hR
  vS3 := hS3
  pCoreOf_eq := (pCoreOf_P₁ hR hS).symm
  inf_eq := by
    have hL1P1 : L1 ≤ P₁ L1 L2 S := le_sup_left
    calc L1 ⊓ P₂ L1 L2 S = L1 ⊓ (P₂ L1 L2 S ⊓ P₁ L1 L2 S) := by
          rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hL1P1)]
      _ = L1 ⊓ bigB L1 L2 S := by rw [F112W.inf_alpha_beta hR]
      _ = borelOf L1 S := F1.inf_bigB_eq_borelOf hR
      _ = S := borelOf_eq_of_vS3 hR hS3 hS
  sup_eq := by
    rw [F112W.inf_alpha_beta hR]

theorem amalgamA_of_setting (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1)
    (hc : centerOf (P₂ L1 L2 S) = ⊥) :
    AmalgamA (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S) S L1 where
  toAmalgamS3 := amalgamS3_of_setting hR hS3 hS
  center := hc
  gen := fun g hg hg' => sup_conjSub_eq_P₂ hR hS3 hS hg hg'

theorem configA_of_le_omegaOneCenterOf
    (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1) (hBig : VBig L2)
    (hnL2 : ¬ ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)) (hc : centerOf (P₂ L1 L2 S) = ⊥)
    {W : Subgroup G} (hW : W ≤ omegaOneCenterOf S) (hW0 : W ≠ ⊥) :
    ConfigA (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S) S L1 (conjClosure W (P₂ L1 L2 S)) := by
  obtain ⟨hleE, hQV, hVE, hred⟩ := conjClosure_P₂ (L1 := L1) (L2 := L2) (S := S) hR hW
  have hHV : P₂ L1 L2 S ≤
      Subgroup.normalizer ((conjClosure W (P₂ L1 L2 S) : Subgroup G) : Set G) :=
    hred.2.1
  have hB : BenderVertex (P₂ L1 L2 S) L2 := benderVertex_P₂ hR hS3 hS hBig hnL2
  have hKV : ¬ L2 ≤
      Subgroup.centralizer ((conjClosure W (P₂ L1 L2 S) : Subgroup G) : Set G) :=
    not_le_centralizer_conjClosure hR hS3 hS hc hW hW0
  have hv : AmalgamHypV (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S) S
      (conjClosure W (P₂ L1 L2 S)) :=
    { toAmalgamHyp := F112W.amalgamHyp_alpha hR
      reduced := hred
      cT := hB.inf_centralizer_eq hHV hQV hKV (F112W.isSylowTwoOf_parabolic' hR) }
  have hV : IsElemAbelian 2 (conjClosure W (P₂ L1 L2 S)) := hv.elemAbelian
  have hcore : ∀ x ∈ P₂ L1 L2 S, (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ y ∈ L2, y * x * y⁻¹ * x⁻¹ ∈
        Subgroup.centralizer ((conjClosure W (P₂ L1 L2 S) : Subgroup G) : Set G)) →
      x ∈ pCoreOf 2 (P₂ L1 L2 S) :=
    fun x hx hx2 hxK => hB.mem_pCoreOf_of_centralizer hHV hQV hKV hx hx2 hxK
  have hstar : StarBound (conjClosure W (P₂ L1 L2 S))
      (pCoreOf 2 (P₂ L1 L2 S)) (P₂ L1 L2 S) :=
    hB.starBound_of_core hV hHV hQV hKV hcore
  have hEne : conjClosure W (P₂ L1 L2 S) ≠ ⊥ := by
    intro hbot
    have hWle : W ≤ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact le_conjClosure _ _
    exact hW0 (le_bot_iff.mp hWle)
  have hodd : Odd (critDist (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S)
      (conjClosure W (P₂ L1 L2 S))) :=
    odd_critDist_of_not_isFFModule hv hEne
      (hB.not_isFFModule_of_core hV hHV hQV hKV hcore)
  exact
    { toAmalgamA := amalgamA_of_setting hR hS3 hS hc
      hypV := hv
      ne_bot := hEne
      star := hstar
      odd := hodd }

end CFSG.Quasithin.F112Crit.APrime

end
