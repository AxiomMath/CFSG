module

public import CFSG.Quasithin.Vol2.Ch10SecK2Ty
public import CFSG.Quasithin.Vol2.Ch10SecK2Tp
public import CFSG.Quasithin.Vol2.Ch10SecKIK2x

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative


theorem factK2Torus_holds : FactK2Torus := by
  intro h56 h36 Γ _ _ H R J L V₁ V hV hc hV₁L hV₁e hLRN hcomm hO2L hNJ hmod hV₁V n hn
    ⟨F, _, _, hF, ⟨e⟩⟩ hC2 hG hlist
  have : IsMulCommutative ↥V := hV.1
  obtain ⟨-, hJN, hO, -, -⟩ := s5_basic hc
  have hq := isQuasisimple_quot h36 h56 hc
  obtain ⟨-, hZY, hcard⟩ := y_structure h36 hc hq hJN hO
  have hT := (lbar_mem_lFamily hc).1
  have hLne := lbar_ne_top hc hJN hO
  obtain ⟨-, -, P, hP, hLP⟩ := hC2
  have hLJ : L ≤ J := hc.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRL : R ≤ Subgroup.normalizer (L : Set Γ) := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsize := relIndex_centralizer_le hmod hn hF e
  have hC : K2Ctx R J L V₁ V n :=
    { hJV := hJN, hOJ := hO, hLJ := hLJ, hRL := hRL, hq := hq, hZY := hZY,
      hP := ⟨P, hP, hLP⟩, hLne := hLne, hT := hT, hn := hn,
      hlevi := ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩, hV₁V := hV₁V,
      hV₁ := fun W hW => ⟨hW, fun g hg => hLRN (Subgroup.mem_sup_right hg.1),
        fun l hl => hLRN (Subgroup.mem_sup_left hl), hcomm, hO2L, hsize.2⟩,
      hne := hsize.1 }
  have hπs : Function.Surjective
      ((piJ hV hJN hO).comp (Subgroup.topEquiv (G := ↥J ⧸ CFSG.pCore 2 ↥J)).toMonoidHom) :=
    (piJ_surjective hV hJN hO).comp (MulEquiv.surjective _)
  have hcardT : Nat.card ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) = Nat.card ↥(autI hV J) ∨
      Nat.card ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) = 3 * Nat.card ↥(autI hV J) := by
    rw [Subgroup.card_top]
    exact hcard
  have hB : ∃ q : ℕ, 4 ≤ q ∧ (∃ k, q = 2 ^ k) ∧
      q * (q ^ 2 - 1) ∣ Nat.card ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) := by
    refine ⟨2 ^ n, by rw [← hF]; exact four_le_card hn hF, ⟨n, rfl⟩, ?_⟩
    obtain ⟨eL⟩ := lbar_modO2_equiv hLJ
    have h1 : Nat.card (ModO2 (modO2Image J L)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr (eL.trans e).toEquiv, card_sl2, hF]
    rw [Subgroup.card_top, ← h1]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨m, K, _, _, hm, hK, hkind⟩ := type_of_list hG hπs hcardT hB hlist
  have hX : KindJ ↥(autOn J V) m := ⟨hm, K, inferInstance, inferInstance, hK, hkind⟩
  obtain ⟨-, -, -, -, hB51⟩ := b56Case1_ffJ h56 hc
  have hV₁U : V₁ ≤ ⁅V, J⁆ := hcomm ▸ Subgroup.commutator_mono hV₁V hLJ
  obtain ⟨-, h1i | h1ii | ⟨k, h1iii⟩ | h1iv⟩ := hB51.1
  · exact torus_case1i hV hC hV₁U hX h1i
  · exact torus_case1ii hV hC hV₁U hX h1ii
  · exact (not_case1iii hX h1iii).elim
  · exact (not_case1iv hX h1iv).elim

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
