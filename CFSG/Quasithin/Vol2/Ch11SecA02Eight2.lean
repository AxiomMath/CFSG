module

public import CFSG.Quasithin.Vol2.Ch11SecA02Eight
public import CFSG.Quasithin.Vol2.Ch11SecA02Five

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem natural_of_328 (h328 : Stmt3_2_8) (hF : Facts02) (h8 : Ch10.TmpL6_3_2_2_eight)
    (h : Hyp11 G T L I n) (hVI : fsuV T I = I) [IsMulCommutative ↥(fsuV T I)]
    (hFF : IsFFModule (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))))) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L (fsuV T I))) ∧ NaturalCases T L I n := by
  have hfsu : FSU G T L (fsuV T I) := by rw [hVI]; exact h.fsu
  have hV0 : fsuV T I = conjClosure (fsuV T I) T := by rw [hVI]; exact hVI.symm
  obtain ⟨_, hcases⟩ := h328 G T L (fsuV T I) hfsu (fsuL0_eq h).symm hV0 ⟨inferInstance, hFF⟩
  obtain ⟨f, hc⟩ := exists_recogCtx hF.g2Adjoint h8 h
  have hW2 : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hiso : Function.Injective f →
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L (fsuV T I))) :=
    fun hinj => ⟨MulEquiv.ofBijective f ⟨hinj, hc.surj⟩⟩
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8' | h9 | h10 | h11
  · obtain ⟨m, -, K, _, _, hK, π, hπ⟩ := h1
    exact (hc.false_of_SL2 hK π hπ.1).elim
  · rcases h2 with ⟨m, K, _, _, hK, ⟨e⟩, K', _, _, hK', π, hπ⟩ | ⟨⟨e⟩, -, -⟩
    · have hY : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ (3 * m) * oSL3 m := by
        rw [Nat.card_congr e.toEquiv, card_SL_three' hK]
      obtain ⟨rfl, hinj⟩ :=
        recog_SL3 hc.shape hc.two_le hc.surj hc.odd (one_le_of_card_eq hK) hY
      refine ⟨hiso hinj, Or.inl ⟨K', inferInstance, inferInstance, hK', ?_, π, ?_, ?_⟩⟩
      · have hcard : Nat.card ↥(StatedSL 3 K') = Nat.card ↥(autOn L (fsuV T I)) := by
          rw [hY, ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K').toEquiv,
            card_SL_three' hK']
        have : Finite (FFModel.nat (StatedSL 3 K')).Gam := (inferInstance : Finite ↥(StatedSL 3 K'))
        have hbij := (Nat.bijective_iff_surjective_and_card π).mpr ⟨hπ.1, hcard⟩
        exact ⟨(MulEquiv.ofBijective π hbij).symm.trans
          (specialLinearGroupEquivStatedSL 3 K').symm⟩
      · rw [cV_subgroupOf_eq_bot (by norm_num) hπ]
        exact hπ
      · exact hF.noGraphSL3 K' _ (one_le_of_card_eq hK') hK' ↥(fsuV T I) hW2 _ π hπ _
          (conj_mem_autOn_of_T h)
    · have hY : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ 3 * 21 := by
        rw [Nat.card_congr e.toEquiv,
          card_SL_three' (K := ZMod 2) (n := 1) (by rw [Nat.card_zmod]; norm_num)]
        norm_num [oSL3]
      exact (hc.false_of_dvd (by decide) (by norm_num) (dvd_of_eq hY)).elim
  · obtain ⟨m, K, _, _, hK, ⟨e⟩, K', _, _, hK', π, hπ⟩ := h3
    have hY : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ (4 * m) * oSp4 m := by
      rw [Nat.card_congr e.toEquiv, card_Sp_four hK]
    obtain ⟨rfl, hinj⟩ :=
      recog_Sp4 hc.shape hc.two_le hc.surj hc.odd (one_le_of_card_eq hK) hY
    refine ⟨hiso hinj, Or.inr (Or.inl ⟨K', inferInstance, inferInstance, hK', ?_, π, hπ, ?_⟩)⟩
    · have hcard : Nat.card ↥(StatedSp 2 K') = Nat.card ↥(autOn L (fsuV T I)) := by
        rw [hY, card_Sp_four hK']
      have : Finite (FFModel.nat (StatedSp 2 K')).Gam := (inferInstance : Finite ↥(StatedSp 2 K'))
      have hbij := (Nat.bijective_iff_surjective_and_card π).mpr ⟨hπ.1, hcard⟩
      exact ⟨(MulEquiv.ofBijective π hbij).symm⟩
    · exact hF.noGraphSp4 K' _ hc.two_le hK' ↥(fsuV T I) hW2 _ _ π hπ autOn_fixes_cV _
        (conj_mem_autOn_of_T h) (autOn_T_mem_cV_iff h)
  · obtain ⟨m, K, _, _, hK, ⟨e⟩, hG⟩ := h4
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hm1 : m = 1 := by have := one_le_of_card_eq hK; omega
      subst hm1
      have hY : Nat.card ↥(autOn L (fsuV T I)) = 6048 := by
        rw [Nat.card_congr e.toEquiv, hF.g2DerivedTwo K (by rw [hK]; norm_num)]
      exact (hc.false_of_dvd (E := 5) (O := 189) (by decide) (by norm_num)
        ((dvd_of_eq hY).trans (by norm_num))).elim
    · have hY : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ (6 * m) * oG2 m := by
        rw [Nat.card_congr e.toEquiv, hF.g2Derived K m hm hK, oG2, ← pow_mul, ← pow_mul,
          mul_comm m 6, mul_comm m 2]
      obtain ⟨rfl, hinj⟩ :=
        recog_G2 hc.shape hc.two_le hc.surj hc.ker_le hc.odd (by omega) hY
      exact ⟨hiso hinj, Or.inr (Or.inr ⟨K, inferInstance, inferInstance, hK, ⟨e⟩, hG⟩)⟩
  · rcases h5 with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · exact (hc.false_of_alt (by norm_num) e).elim
    · exact (hc.false_of_alt (by norm_num) e).elim
  · obtain ⟨⟨e⟩, -⟩ := h6
    exact (hc.false_of_alt (by norm_num) e).elim
  · obtain ⟨⟨e⟩, -⟩ := h7
    exact (false_of_autOn_sup_alt hc e).elim
  · obtain ⟨-, hZ, ⟨e⟩, -⟩ := h8'
    exact (false_of_3A6 hc hZ e).elim
  · obtain ⟨d, hd, ⟨e⟩, -⟩ := h9
    exact (false_of_autOn_sup_SL hF.l34 h hc hd e).elim
  · obtain ⟨⟨e⟩, -⟩ := h10
    exact (recog_SL42 hF.l34 hc.shape hc.two_le hc.surj hc.odd e).elim
  · obtain ⟨⟨e⟩, -⟩ := h11
    exact (false_of_autOn_sup_SL hF.l34 h hc (Or.inr rfl) e).elim

end CFSG.Quasithin.Vol2.Ch11.SecA
