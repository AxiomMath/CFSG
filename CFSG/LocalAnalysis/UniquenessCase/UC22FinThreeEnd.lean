module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeAut
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeB0
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.Adapters.Certificate43Check
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22fin3

theorem false_of_endgame (D : Data G) {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76 D) (h17 : S21_17 D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig)
    (hk1 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (hn : 2 ≤ c.n) {K : Subgroup G}
    (hK : K ∈ calC D.M) {n : ℕ} (hL2 : IsL2 ↥(mbarImage D.M c.V K) n) {t : G} (htM : t ∈ D.M)
    (htN : t ∉ normalizer (K : Set G)) {Y : Subgroup G} (hY : Y ∈ calC D.M)
    (hYV : Y ≤ centralizer (c.V : Set G)) {m : ℕ} (hm : 2 ≤ m)
    (eY : Bar2 Y ≃* CFSG.Open.StatedSL 2 (GaloisField 2 m)) {A : Subgroup G} (hBA : c.B0 ≤ A)
    (hA : IsMulCommutative A) (hAYB : A ⊓ Y ⊓ c.B0 = ⊥) (eA : ↥(A ⊓ Y) ≃* ↥c.B0) : False := by
  have hKM : K ≤ D.M := hK.1.le
  have hc2 : (conjSetOf D.M K).ncard = 2 := by
    rcases h17 h1930 c.toCtx21 K hK with hcl | ⟨hc2, -⟩ | ⟨hc2, -⟩
    · have h := PartTwo.TwelveTwentyThree.le_normalizer_conjClosure D.M K
      rw [← hcl] at h
      exact absurd (h htM) htN
    all_goals exact hc2
  obtain ⟨a₀, ha₀⟩ := exists_isL2_bar2 D h17 h1930 c hK (fun h => htN (h htM)) hL2
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M _
    (Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer htM)) hK
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom :=
    fun h => htN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h.symm)
  have hK1 : mbarImage D.M c.V K ≠ ⊥ := fun h => by
    have h3 := three_dvd_card_of_isL2 hL2
    rw [h, Subgroup.card_bot] at h3
    norm_num at h3
  have hYne : ∀ {L : Subgroup G}, L ≤ D.M → mbarImage D.M c.V L ≠ ⊥ → Y ≠ L := fun hLM hL h =>
    hL ((uc22br4_mbarImage_eq_bot_iff D.M c.V _ c.hVM hLM).2 (h ▸ hYV))
  have hYK : Y ≠ K := hYne hKM hK1
  have hYKt : Y ≠ K.map (MulAut.conj t).toMonoidHom := hYne hKt.1.le (by
    rw [P22fin.mbarImage_conj htM hKM]
    exact fun h => hK1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).1 h))
  have hB3 : ¬ 3 ∣ Nat.card c.B0 := fun h3 => by
    obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet (B := c.B0) ⟨Nat.prime_three, h3⟩
    exact uc22p2214_false_of_sp D Ch h1930 c Nat.prime_three hk1 hb hbo
  obtain ⟨r, hr, b, hbB, hbr⟩ := exists_orderOf_mem_B0 D c.toCtx21 hn
  haveI : Fact r.Prime := ⟨hr⟩
  have hr7 := seven_le_of_dvd_card_B0 D c.toCtx21 (by omega) hB3 hr
    (hbr ▸ Subgroup.orderOf_dvd_natCard c.B0 hbB)
  have hr2 : r ≠ 2 := by omega
  obtain ⟨a, haAY, har, hab, hna⟩ := exists_commute_orderOf hBA hA hAYB eA hr hbB hbr
  have haM : a ∈ D.M := hY.1.le haAY.2
  have hbM : b ∈ D.M := c.hBM hbB
  rcases dvd_or_commute_orderOf_three_pair hK hc2 ha₀ htM hr hr2 hbM
      (hbr ▸ pow_orderOf_eq_one b) with hrK | ⟨⟨x₁, hx₁, h₁, hb₁⟩, x₂, hx₂, h₂, hb₂⟩
  · classical
    have hYs : IsL2 (Bar2 Y) m :=
      uc22p22d_isL2_of_statedSL hm (GaloisField.card 2 m (by omega)) eY
    have hKts : IsL2 (Bar2 (K.map (MulAut.conj t).toMonoidHom)) a₀ := by
      unfold IsL2 at ha₀ ⊢
      exact CFSG.Blueprint.LieModel.of_mulEquiv (UC6S846.bar2Equiv
        (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)) ha₀
    have hS : ∀ L ∈ ({Y, K, K.map (MulAut.conj t).toMonoidHom} : Finset (Subgroup G)),
        L ∈ calC D.M ∧ (∃ e, IsL2 (Bar2 L) e) ∧ r ∣ Nat.card L := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro L (rfl | rfl | rfl)
      · exact ⟨hY, ⟨m, hYs⟩, har ▸ Subgroup.orderOf_dvd_natCard _ haAY.2⟩
      · exact ⟨hK, ⟨a₀, ha₀⟩, hrK⟩
      · exact ⟨hKt, ⟨a₀, hKts⟩,
          (Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
            (MulAut.conj t).injective).symm ▸ hrK⟩
    have h3 := card_le_pRank_of_finset (X := D.M) hr hr2 (fun L hL => (hS L hL).1)
      (fun L hL => by
        obtain ⟨e, he⟩ := (hS L hL).2.1
        rw [P22y.center_eq_bot_of_isL2Ev (P22fin.isL2Ev_of_isL2 he).1, Subgroup.card_bot]
        exact hr.not_dvd_one)
      (fun L hL => (hS L hL).2.2)
    rw [Finset.card_eq_three.2 ⟨Y, K, _, hYK, hYKt, hne, rfl⟩] at h3
    exact uc22p2214_false_of_sp D Ch h1930 c hr (UC6S846.sp_of_mem_sig hSg
      (UC6S846.not_solvable_of_mem_calC hK) (hσ r hr hr7 h3)) hbB hbr
  · have haY : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ ∈ barImage D.M Y :=
      ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.2 haAY.2, rfl⟩
    have hx : x₂ ∉ zpowers x₁ := fun hx => by
      obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hK
      have hL2K : IsL2 ↥(barImage D.M K) a₀ := by
        unfold IsL2 at ha₀ ⊢
        exact CFSG.Blueprint.LieModel.of_mulEquiv e ha₀
      have hz : (⟨x₂, zpowers_le.2 hx₁ hx⟩ : ↥(barImage D.M K)) ∈ center ↥(barImage D.M K) :=
        Subgroup.mem_center_iff.2 fun y =>
          Subtype.ext (uc22p22l_barImage_commute hK hKt hne y y.2 x₂ hx₂)
      rw [P22y.center_eq_bot_of_isL2Ev (P22fin.isL2Ev_of_isL2 hL2K).1, Subgroup.mem_bot] at hz
      have h1 : x₂ = 1 := congrArg Subtype.val hz
      rw [h1, orderOf_one] at h₂
      norm_num at h₂
    have hb1 : b ≠ 1 := fun h => by
      rw [h, orderOf_one] at hbr
      exact hr.one_lt.ne hbr
    obtain ⟨hE, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hr
      (hbr ▸ pow_orderOf_eq_one b) (har ▸ pow_orderOf_eq_one a) hb1 hna hab.eq.symm
    have hEM : zpowers b ⊔ zpowers a ≤ D.M := sup_le (zpowers_le.2 hbM) (zpowers_le.2 haM)
    exact false_of_two_le_pRank D h76 h1930 c.toCtx21 hk1 hr hEM hE hEc hbB
      (Subgroup.mem_sup_left (mem_zpowers b)) hbr
      (two_le_pRank_centralizer hEM hr hr2 (IsPGroup.of_card hEc) h₁ h₂
        (uc22p22l_barImage_commute hK hKt hne x₁ hx₁ x₂ hx₂) hx
        (mem_centralizer_barImage_sup haM hbM
          (uc22p22l_barImage_commute hY hK hYK _ haY x₁ hx₁) hb₁)
        (mem_centralizer_barImage_sup haM hbM
          (uc22p22l_barImage_commute hY hKt hYKt _ haY x₂ hx₂) hb₂))

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
