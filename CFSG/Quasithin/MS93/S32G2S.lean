module

public import CFSG.Quasithin.MS93.S32Main
public import CFSG.Quasithin.MS93.S32Types

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L W : Subgroup G}

theorem g2d_of_b42Pair (h45 : NoSL45) (hT : TypeFacts) (hs : IsSecW M L W) (h : PUHyp M T L)
    (hL : Nat.card (Lstar L) = 6048) {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    (hpair : B42ModulePair (autI (hs.isElemAbelian h) L) U Z) :
    G2NaturalDerived (autI (hs.isElemAbelian h) L) U Z 1 := by
  rcases hpair with ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ |
    ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ | hG2d | ⟨π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨α, π, hπ⟩ | hHat | hSL4 | hSL5 | hE4 | hE5
  · exact (false_of_sl2 hs h hT hF hπ).elim
  · obtain ⟨hn, hc⟩ := card_lstar_of_sl3 hs h hF hπ
    exact (ordA_two_ne_6048 hn (hc.symm.trans hL)).elim
  · obtain ⟨hn, hc⟩ := card_lstar_of_sp4 hs h hF hπ
    exact ((ordBC_two_ne (by omega)).2.2 (hc.symm.trans hL)).elim
  · obtain ⟨hn, hc⟩ := card_lstar_of_g2 hs h hT hF hπ
    exact ((ordG2_ne (by omega)).2.2 (hc.symm.trans hL)).elim
  · exact hG2d
  · exact (hT.alt57 _ (hs.rankTwo h) 5 (Or.inl rfl)
      (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
  · have := card_lstar_of_alt6 hs h hπ
    omega
  · exact (hT.alt57 _ (hs.rankTwo h) 7 (Or.inr rfl)
      (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
  · exact (hT.alt57 _ (hs.rankTwo h) 7 (Or.inr rfl)
      (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ)).elim
  · have := card_lstar_of_hat hs h hHat
    omega
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL4
    exact (h45 _ (hs.rankTwo h) 4 (Or.inl rfl)
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL5
    exact (h45 _ (hs.rankTwo h) 5 (Or.inr rfl)
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
  · obtain ⟨π, hπ⟩ := id hE4
    exact (h45 _ (hs.rankTwo h) 4 (Or.inl rfl)
      (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ)).elim
  · obtain ⟨π, hπ⟩ := id hE5
    exact (h45 _ (hs.rankTwo h) 5 (Or.inr rfl)
      (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ)).elim

theorem s32PartG2Struct_of
    (h51 : AsB51) (hSQ : SQTKQuot) (h45 : NoSL45)
    (hT : TypeFacts) (hI : B5.B51IrrInputs) : S32PartG2Struct := by
  intro G _ _ M T L h hgd hXL
  set hX := h.isElemAbelian_Xq with hXdef
  have hs := isSecW_Xq h
  have hMX : M ≤ Subgroup.normalizer (Xq M : Set G) := le_normalizer_Xq M
  have hL : Nat.card (Lstar L) = 6048 := by
    obtain ⟨F, iF, fF, hF, π, hπ⟩ := hgd
    exact card_lstar_of_g2d (isSecW_Uq h) h hT hF hπ
  have hB := hs.b51Hyp h hSQ (h.isFFModule_of_le_Xq hs)
  obtain ⟨⟨-, hcases⟩, -, -, -, h5, -⟩ := b51_Xq h h51 hSQ
  obtain ⟨hIrr, hpair⟩ : commV (autI hX L) ∈ IrrPlus (autI hX L) ⊤ ∧
      B42ModulePair (autI hX L) (commV (autI hX L)) (fixV (autI hX L) ⊓ commV (autI hX L)) := by
    rcases hcases with hi | ⟨-, n, F, iF, fF, hF, I, π, -, -, hreal, -, -⟩ |
      ⟨n, -, hm, π, U₁, U₂, -, h1, -⟩ | ⟨-, n, hn, k, hk1, hkn, I, π, -, -, -, hreal⟩
    · exact ⟨hi.1, hi.2.1⟩
    · obtain ⟨hn, hc⟩ := card_lstar_of_sl3 hs h hF (hreal 0)
      exact (ordA_two_ne_6048 hn (hc.symm.trans hL)).elim
    · exact (h45 _ (hs.rankTwo h) _ hm (FFC.equivOfRealizes (FFModel.nat_faithful _) h1)).elim
    · exact (h45 _ (hs.rankTwo h) _ hn
        (FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩))).elim
  have hG2X := g2d_of_b42Pair h45 hT hs h hL hpair
  have hJK : ffJ (autI hX M) ≠ autI hX L :=
    SmithC27.ne_of_g2NaturalDerived hI IntMod.sq_eq_one hB hIrr hG2X
  have hKJ : autI hX L ≤ ffJ (autI hX M) := hB.2.2.2.1
  have hJM : ffJ (autI hX M) ≤ autI hX M := B6.ffJ_le _
  obtain ⟨F, iF, fF, hF, π, hπ⟩ := id hG2X
  have hF2 : Nat.card F = 2 := hF.trans (pow_one 2)
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  have hU33 : B42TypeU33 ↥(autI hX L) := hT.u33 _ F hF2
    (FFC.equivOfRealizes (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ).symm
  have hKc : Nat.card ↥(autI hX L) = 6048 := B42U33.card_of_b42TypeU33 hU33
  have hcent : ∀ c ∈ autI hX M, (∀ k ∈ autI hX L, c * k = k * c) → c = 1 := by
    intro c hc hck
    obtain ⟨e, he⟩ := hs.two h c hc
    have hz : (⟨c ^ 2 ^ e, he⟩ : ↥(autI hX L)) ∈ Subgroup.center ↥(autI hX L) := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact ((Commute.pow_left (hck k k.2) (2 ^ e)).eq).symm
    rw [hU33.1, Subgroup.mem_bot] at hz
    exact hs.cent h c hc hck e (congrArg Subtype.val hz)
  have hXc : Nat.card ↥(autI hX M) ≤ 12096 :=
    hT.u33aut _ _ _ (hs.autI_L_le h) (hs.autI_le_normalizer h) hcent hU33
  have hJeq : ffJ (autI hX M) = autI hX M := by
    have hlt : autI hX L < ffJ (autI hX M) := lt_of_le_of_ne hKJ (Ne.symm hJK)
    have h2 : 2 * Nat.card ↥(autI hX L) ≤ Nat.card ↥(ffJ (autI hX M)) := by
      have hdvd := Subgroup.card_dvd_of_le hKJ
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : k ≠ 1 := by
        rintro rfl
        rw [mul_one] at hk
        exact hlt.ne (Subgroup.eq_of_le_of_card_ge hKJ hk.le)
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        exact Nat.card_pos.ne' hk
      rw [hk, mul_comm 2]
      exact Nat.mul_le_mul_left (Nat.card ↥(autI hX L)) (by omega : 2 ≤ k)
    exact Subgroup.eq_of_le_of_card_ge hJM (by omega)
  have hsup : commV (autI hX L) ⊔ fixV (autI hX M) = ⊤ := by
    rcases h5 with h5 | ⟨-, hlist, -⟩
    · rwa [hJeq] at h5
    · exfalso
      rcases hlist with ⟨m, F', iF', fF', hF', π', hπ'⟩ | ⟨π', hπ'⟩ | ⟨π', hπ'⟩ | hsl
      · obtain ⟨hm, hc⟩ := card_lstar_of_sp4 hs h hF' hπ'
        exact (ordBC_two_ne (by omega)).2.2 (hc.symm.trans hL)
      · have := card_lstar_of_alt6 hs h hπ'
        omega
      · exact false_of_alt8 hs h hT hπ'
      · obtain ⟨F', iF', fF', hF', π', hπ'⟩ := hsl
        obtain ⟨hn, hc⟩ := card_lstar_of_sl3 hs h hF' hπ'
        exact ordA_two_ne_6048 hn (hc.symm.trans hL)
  have hsupG := congrArg (C124.toG hX) hsup
  rw [C124.toG, Subgroup.map_sup, ← C124.toG, ← C124.toG, toG_commV_Xq h, toG_fixV hX hMX,
    hXL, toG_top] at hsupG
  have hCT : Xq M ⊓ Subgroup.centralizer (M : Set G) ≤ Z0q M T := by
    refine le_trans ?_ (omegaOneCenterOf_le_Z0q M T h.le)
    rw [h.omegaOneCenterOf_eq]
    exact inf_le_inf_left _ (Subgroup.centralizer_le h.le)
  have hCZ : Xq M ⊓ Subgroup.centralizer (M : Set G) ≤ Zq M L :=
    inf_le_inf_left _ (Subgroup.centralizer_le h.L_le)
  have hXZ0 : Xq M = Z0q M T :=
    le_antisymm (hsupG ▸ sup_le (Uq_le_Z0q h.L_le) hCT) h.Z0q_le_Xq
  refine ⟨hXZ0, le_antisymm ?_ ?_⟩
  · rw [← hXZ0, ← hsupG, sup_comm]
    exact sup_le_sup_right hCZ _
  · rw [← hXZ0]
    exact sup_le inf_le_left h.Uq_le_Xq

end CFSG.Quasithin.MS93.S32
