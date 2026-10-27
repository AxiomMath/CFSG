module

public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem one_le_of_card_eq {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := Finite.one_lt_card (α := K)
    rw [hK] at this
    norm_num at this
  · exact hm

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem not_isFFModule_of_sum (h51 : AsB51) (hL34 : FactL34) (h8 : Ch10.TmpL6_3_2_2_eight)
    (h : Hyp11 G T L I n) {f : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autOn L (fsuV T I))}
    (hc : RecogCtx _ _ n f) (hinj : Function.Injective f) [IsMulCommutative ↥(fsuV T I)]
    (hCL : I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {t : G} (ht : t ∈ T)
    (hsum : I ⊔ CFSG.conjugate I t = fsuV T I) (hinf : I ⊓ CFSG.conjugate I t = ⊥)
    (hnoniso : ¬ IsXSectionIso₂ L I ⊥ (CFSG.conjugate I t) ⊥) :
    ¬ IsFFModule (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I)))) := by
  have hLV := L_le_normalizer_fsuV h
  have hO2 := pCoreOf_autOn_eq_bot h8 h
  have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal ht
  have hirrP := h.fsu.irrPlus
  rw [show conjClosure L T = L from fsuL0_eq h] at hirrP
  obtain ⟨-, hI1, hLI, -, -, hirr, -⟩ := hirrP
  have hirrA : ∀ J : Subgroup G, J ≤ I → L ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = I := by
    intro J hJ hLJ
    have := hirr J (by rw [hCL]; exact bot_le) hJ hLJ
    rwa [hCL] at this
  have hntA : ¬ I ≤ Subgroup.centralizer (L : Set G) := by
    intro hle
    apply hI1
    rw [← hCL]
    exact (inf_eq_left.mpr hle).symm
  have hcard : Nat.card ↥(autOn L (fsuV T I)) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hc.surj⟩)).symm
  exact InternalSec.not_isFFModule_normalizer_autOn_of_sum h51 (isElemAbelian_fsuV h).2 hLV
    (InternalSec.isQuasisimple_autOn hLV h.fsu.quasisimple hO2 (not_le_centralizer_fsuV h))
    (InternalSec.sqtkGroup_autOn hLV (sqtkGroup_L h)
      (InternalSec.isPGroup_ker_of_card hLV hO2 hcard))
    (le_sup_left.trans hsum.le) (le_sup_right.trans hsum.le) hsum hinf hLI
    (le_normalizer_conjugate htL hLI) hirrA (irr_conjugate htL hirrA) hntA
    (not_le_centralizer_conjugate htL hntA) hnoniso
    (fun d hd π hπ => hc.false_of_SL_zmod_two hL34 hd π hπ)

theorem fsuV_eq_of_325 (h325 : Stmt3_2_5) (h51 : AsB51) (hL34 : FactL34)
    (hG2 : FactG2AdjointOrder) (h8 : Ch10.TmpL6_3_2_2_eight)
    (hFF : ∃ _ : IsMulCommutative ↥(fsuV T I), IsFFModule (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I)))))
    (h : Hyp11 G T L I n) : fsuV T I = I := by
  obtain ⟨-, -, hcases⟩ := h325 G T L I h.fsu (fsuL0_eq h).symm
  rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hCL, hlist, ⟨t, ht, htN⟩, hall⟩
  · exact h1.symm
  · exact h1.symm
  · exfalso
    obtain ⟨-, hsum, hinf, hnoniso⟩ := hall t ht htN
    obtain ⟨f, hc⟩ := exists_recogCtx hG2 h8 h
    obtain ⟨_, hFF'⟩ := hFF
    rcases hlist with ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · have hY : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ (3 * m) * oSL3 m := by
        rw [Nat.card_congr e.toEquiv, card_SL_three' hK]
      obtain ⟨-, hinj⟩ :=
        recog_SL3 hc.shape hc.two_le hc.surj hc.odd (one_le_of_card_eq hK) hY
      exact not_isFFModule_of_sum h51 hL34 h8 h hc hinj hCL ht hsum.symm hinf hnoniso hFF'
    · have hY : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ (4 * m) * oSp4 m := by
        rw [Nat.card_congr e.toEquiv, card_Sp_four hK]
      obtain ⟨-, hinj⟩ :=
        recog_Sp4 hc.shape hc.two_le hc.surj hc.odd (one_le_of_card_eq hK) hY
      exact not_isFFModule_of_sum h51 hL34 h8 h hc hinj hCL ht hsum.symm hinf hnoniso hFF'
    · exact hc.false_of_alt (by norm_num) e
    · exact recog_SL42 hL34 hc.shape hc.two_le hc.surj hc.odd e
    · exact hc.false_of_ten (o := 9765) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_SL_five_two])
    · exact hc.false_of_alt (by norm_num) e

end CFSG.Quasithin.Vol2.Ch11.SecA
