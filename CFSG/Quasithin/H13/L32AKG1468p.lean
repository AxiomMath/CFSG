module

public import CFSG.Quasithin.H13.L32AKG1468o
public import CFSG.Quasithin.H13.L32AKG1468b
public import CFSG.Quasithin.H13.L32AKG1468n

public section

namespace CFSG.Quasithin.H13.KGBlk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem kg1468Blocks_of (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) :
    KG1468Blocks := by
  intro G _ _ Y R M I hyp hI hIn hc hq hIM hR hB
  have c : BlkCtx Y R M I := ⟨hyp, hI, hIn, hc, hq, hIM, hR, hB⟩
  obtain ⟨e⟩ := hB
  set V := omegaOneCenterOf (pCoreOf 2 (I ⊔ R)) with hV
  obtain ⟨hIV, hD, hOC⟩ := c27_facts (hC27 G) c
  have h1 := (hC27 G Y R M I V hyp hI hq hc hIM hR hV).1
  have hBI : oTwoUpper (I ⊓ M) ≤ I := oTwoUpper_le_inf.trans inf_le_right
  obtain ⟨θ, hθs, hθk⟩ := exists_theta hIV hD hBI e
  obtain ⟨a, haB, ha5⟩ := exists_five_mem e
  obtain ⟨x, hx5⟩ := exists_orderOf_five card_alt_five θ hθs
  have hx5' : orderOf (x : MulAut ↥V) = 5 := by rw [Subgroup.orderOf_coe, hx5]
  have hXP : autOn (oTwoUpper (I ⊓ M)) V ≤ autOn (M ⊓ I) V := autOn_mono oTwoUpper_le_inf
  rcases SBc17.asc27_cases (hC27 G) hyp hI hq hc hIM hR hV with
    hL2 | hA5 | hA7a | hA7b | hAlt | hHat | hExc | hA6Sp4 | hG2 | hSL3 | hL45
  · exact (false_of_borel hXP θ hθs hL2.2.2.2).elim
  · exact (false_of_borel hXP θ hθs hA5.2.2.2.2).elim
  · obtain ⟨-, -, -, e7, P, hP, hmap⟩ := hA7a
    exact (false_of_partition x.2 hx5' e7 (by simp) (by simp) hP hmap).elim
  · obtain ⟨-, -, -, e7, P, hP, hmap⟩ := hA7b
    exact (false_of_partition x.2 hx5' e7 (by simp) (by simp) hP hmap).elim
  · obtain ⟨⟨n, α, hn5, hn8, hshort, hαd, t, htR, htV, hRt, -, σ, hσ, hrel⟩, hMK⟩ := hAlt
    have hD' : I ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 I :=
      hD.trans (SBc17.oTwoZIn_le_pCoreOf_of_center_bot hαd.1 hαd.2.1
        (SBc17.center_alt_bot (by omega)))
    rcases (by omega : n ≤ 6 ∨ n = 7 ∨ n = 8) with hn | rfl | rfl
    · exact (false_of_alt_small hR hIV hD' hn hαd.2.1 htR htV hσ hrel hMK haB ha5).elim
    · left
      have hle := pCoreOf_le_of_alt_seven hR hIV hD' hαd.2.1 htR htV hσ hrel hMK haB ha5
      calc ⁅pCoreOf 2 (oTwoUpper (I ⊓ M)), oTwoUpper (I ⊓ M)⁆ ≤ ⁅pCoreOf 2 I, I⁆ :=
            Subgroup.commutator_mono hle hBI
        _ ≤ Subgroup.centralizer (pCoreOf 2 I : Set G) := hshort.2.2.1.1.trans inf_le_right
        _ ≤ Subgroup.centralizer (pCoreOf 2 (oTwoUpper (I ⊓ M)) : Set G) :=
            Subgroup.centralizer_le hle
    · exact (false_of_alt_eight hR hIV hD' hOC hαd.1 hαd.2.1 htR htV hRt hσ hrel hMK e).elim
  · obtain ⟨hA, hidx, -⟩ := hHat
    exact (false_of_hatA6 hA hidx (five_dvd_card_inf haB ha5)).elim
  · obtain ⟨hA, hidx⟩ := hExc
    exact (false_of_excA7 hA hidx (five_dvd_card_inf haB ha5)).elim
  · obtain ⟨hb | hb, hmax⟩ := hA6Sp4
    · obtain ⟨-, α, hα⟩ := hb
      have hIY : I ≤ Y := le_of_mem_cComp hI
      exact (false_of_a6Block hIY (A4.subnormal_of_normal hIY hIn) hyp.radical.1 hR h1.1 h1.2.1
        hIV hα hmax θ hθs).elim
    · exact (false_of_sp4Block hIV hD hOC hb hmax θ hθk).elim
  · exact (false_of_g2 x.2 hx5' hG2.2.1).elim
  · obtain ⟨hex, hmax, -⟩ := hSL3
    exact (false_of_sl3 hIV ⟨hex, hmax⟩ θ hθs hθk).elim
  · obtain ⟨he, hpar, -⟩ := hL45
    exact (false_of_l45 hIV he hpar θ hθs hθk).elim

end CFSG.Quasithin.H13.KGBlk
