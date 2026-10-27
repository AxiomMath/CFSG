module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54ThmA
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Orbit
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Psi
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Unitary
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54BorelRank
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59Case
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2OrbitFrame
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2FamCl
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2FamEx
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2G2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Tits
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMax
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54AS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LieType.Universal

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt OInf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

private theorem exists_umaxBQ_of_hasBQRank {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    {r : ℕ} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (hQR : HasBQRank ↥L r) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K)
      (nn : Fin D.rank → K) (H : Fin D.rank → Subgroup K) (π : K →* ↥L) (e : ℕ),
      D.rank = r ∧ UMaxBQ L T M D nn H π e := by
  obtain ⟨K, hK, hKfin, D, nn, H, π, e, hBQ, hrank⟩ := hQR
  obtain ⟨π', hU⟩ := exists_umaxBQ hLn hLs hnab hT hMt hMax hBQ
  exact ⟨K, hK, hKfin, D, nn, H, π', e, hrank, hU⟩

private theorem false_of_hasBQRank_three_le {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    {r : ℕ} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (hQR : HasBQRank ↥L r) (hr : 3 ≤ r) : False := by
  obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
    exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax hQR
  have := hU.rank_le_two
  omega

private theorem false_of_hasBQUneven {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (hQU : HasBQUneven ↥L) : False := by
  obtain ⟨K, hK, hKfin, D, nn, H, π, e, hBQ, i, j, hne⟩ := hQU
  obtain ⟨π', hU⟩ := exists_umaxBQ hLn hLs hnab hT hMt hMax hBQ
  exact hne (hU.card_rootGroup_eq i j)

theorem asch58UniqueMax_and_isSolvable
    {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    (hLn : L.Normal) (hLs : IsSimpleGroup ↥L) (hC : centralizer (L : Set Q) = ⊥)
    (hP : ∃ t n f, CFSG.Models.LieModel ↥L t n 2 f ∧ Asch58Parabolic t n f)
    (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤) (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) :
    Shape54 ⊤ T L ∧ Group.IsSolvable ↥(M ⊓ L) := by
  obtain ⟨t, n, f, hm, hpar⟩ := hP
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hLle : L ≤ centralizer (L : Set Q) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hC] at hLle
    have hbot : L = ⊥ := le_bot_iff.mp hLle
    exact (Subgroup.nontrivial_iff_ne_bot L).1 IsSimpleGroup.toNontrivial hbot
  have hparc : Asch58Parabolic t n f := hpar
  rcases hpar with hpar1 | hpar2
  · obtain ⟨rfl, htD4⟩ := hpar1
    cases t with
    | PSL =>
        have h2 : 2 ≤ n := hm.1.2.2.1
        have hn2 : n ≠ 2 := by
          intro hn
          exact hm.1.2.2.2.1 (by rw [hn]; norm_num)
        have h3 : 3 ≤ n := by omega
        by_cases hn3 : n = 3
        · subst n
          have hL3 : IsL3 ↥L 1 := CFSG.Models.LieModel.toBlueprint (by decide) hm
          obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
            exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax (hasBQRank_psl hm)
          exact ⟨Or.inr (Or.inl (hasQuotShape_oInf_top hLs hnab hC
            (P := fun X _ => IsAlt X 6 ∨ IsL3 X 1) (Or.inr hL3))), hU.isSolvable_inf⟩
        · exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
            (hasBQRank_psl hm) (by omega)).elim
    | PSU =>
        have h3 : 3 ≤ n := hm.1.2.2.1
        have hn3 : n ≠ 3 := by
          intro hn
          exact hm.1.2.2.2 (by rw [hn]; norm_num)
        by_cases h45 : n = 4 ∨ n = 5
        · exact (false_of_hasBQUneven hLn hLs hnab hT hMt hMax
            (hasBQUneven_psu h45 hm)).elim
        · have hn4 : n ≠ 4 := fun h => h45 (Or.inl h)
          have hn5 : n ≠ 5 := fun h => h45 (Or.inr h)
          exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
            (hasBQRank_psu hm) (by omega)).elim
    | PSp =>
        have h2 : 2 ≤ n := hm.1.2.2.1
        have hn2 : n ≠ 2 := by
          intro hn
          exact hm.1.2.2.2 (by rw [hn]; norm_num)
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_psp hm) (by omega)).elim
    | POmegaOdd => exact absurd rfl hm.1.2.2.2
    | POmegaPlus =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_pomegaPlus hm) (by have := hm.1.2.2; omega)).elim
    | POmegaMinus =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_pomegaMinus hm) (by have := hm.1.2.2; omega)).elim
    | G2 => exact absurd hm.1.2.2.2 (by norm_num)
    | F4 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_f4 hm) (by norm_num)).elim
    | E6 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_e6 hm) (by norm_num)).elim
    | E7 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_e7 hm) (by norm_num)).elim
    | E8 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_e8 hm) (by norm_num)).elim
    | twistedE6 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_twistedE6 hm) (by norm_num)).elim
    | trialityD4 => exact absurd rfl htD4
    | twistedB2 => exact absurd hm.1.2.2.2.2.2 (by norm_num)
    | twistedG2 => exact absurd hm.1.2.2.2.1 (by norm_num)
    | twistedF4 => exact absurd hm.1.2.2.2.2.2 (by norm_num)
    | Tits => exact (false_of_uniqueMax_tits hLn hLs hnab hm hT hMt hMax).elim
  · obtain ⟨rfl, hcase⟩ := hpar2
    cases t with
    | PSL =>
        have h2 : 2 ≤ n := hm.1.2.2.1
        by_cases hn2 : n = 2
        · subst n
          have hL2 : IsL2 ↥L 2 := CFSG.Models.LieModel.toBlueprint (by decide) hm
          obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
            exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax (hasBQRank_psl hm)
          exact ⟨Or.inl (hasQuotShape_oInf_top hLs hnab hC
            (P := fun X _ => IsL2 X 2 ∨ IsU3 X 2) (Or.inl hL2)), hU.isSolvable_inf⟩
        · by_cases hn3 : n = 3
          · subst n
            have hL3 : IsL3 ↥L 2 := CFSG.Models.LieModel.toBlueprint (by decide) hm
            obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
              exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax (hasBQRank_psl hm)
            have hr : D.rank = 2 := by omega
            obtain ⟨t₀, ht₀, P, hPL, hPmax, hPN, hPne⟩ := hU.exists_swap hr
            refine ⟨Or.inr (Or.inr (Or.inl ⟨hasQuotShape_oInf_top hLs hnab hC
              (P := fun X _ => IsL3 X 2 ∨ IsSp4 X 2) (Or.inl hL3), t₀, ht₀, ?_⟩)),
              hU.isSolvable_inf⟩
            rw [oInf_top_eq_bot (solvableRadical_eq_bot_of_simple_normal hLs hnab hC)]
            exact actsOnDynkinMod_bot_of_swap hLn hT ht₀ hPL hPmax hPN hPne
          · exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
              (hasBQRank_psl hm) (by omega)).elim
    | PSU =>
        have hn : n = 3 := by
          have h := hparc
          simp [Asch58Parabolic] at h
          exact h
        subst n
        have hU3 : IsU3 ↥L 2 := CFSG.Models.LieModel.toBlueprint (by decide) hm
        obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
          exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax (hasBQRank_psu hm)
        exact ⟨Or.inl (hasQuotShape_oInf_top hLs hnab hC
          (P := fun X _ => IsL2 X 2 ∨ IsU3 X 2) (Or.inr hU3)), hU.isSolvable_inf⟩
    | PSp =>
        have h2 : 2 ≤ n := hm.1.2.2.1
        by_cases hn2 : n = 2
        · subst n
          have hSp4 : IsSp4 ↥L 2 := CFSG.Models.LieModel.toBlueprint (by decide) hm
          obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
            exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax (hasBQRank_psp hm)
          have hr : D.rank = 2 := by omega
          obtain ⟨t₀, ht₀, P, hPL, hPmax, hPN, hPne⟩ := hU.exists_swap hr
          refine ⟨Or.inr (Or.inr (Or.inl ⟨hasQuotShape_oInf_top hLs hnab hC
            (P := fun X _ => IsL3 X 2 ∨ IsSp4 X 2) (Or.inr hSp4), t₀, ht₀, ?_⟩)),
            hU.isSolvable_inf⟩
          rw [oInf_top_eq_bot (solvableRadical_eq_bot_of_simple_normal hLs hnab hC)]
          exact actsOnDynkinMod_bot_of_swap hLn hT ht₀ hPL hPmax hPN hPne
        · exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
            (hasBQRank_psp hm) (by omega)).elim
    | POmegaOdd => exact absurd rfl hm.1.2.2.2
    | POmegaPlus =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_pomegaPlus hm) (by have := hm.1.2.2; omega)).elim
    | POmegaMinus => exact absurd hparc (by simp [Asch58Parabolic])
    | G2 =>
        have hn0 : n = 0 := hm.1.2.2.1
        subst n
        obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
          exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax (hasBQRank_g2 hm)
        have hr : D.rank = 2 := by omega
        obtain ⟨t₀, ht₀, P, hPL, hPmax, hPN, hPne⟩ := hU.exists_swap hr
        exact (false_of_swap_g2 hLn hm hT ht₀ hPL hPmax hPN hPne).elim
    | F4 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_f4 hm) (by norm_num)).elim
    | E6 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_e6 hm) (by norm_num)).elim
    | E7 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_e7 hm) (by norm_num)).elim
    | E8 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_e8 hm) (by norm_num)).elim
    | twistedE6 =>
        exact (false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax
          (hasBQRank_twistedE6 hm) (by norm_num)).elim
    | trialityD4 => exact absurd hparc (by simp [Asch58Parabolic])
    | twistedB2 => exact absurd hparc (by simp [Asch58Parabolic])
    | twistedG2 => exact absurd hparc (by simp [Asch58Parabolic])
    | twistedF4 => exact absurd hparc (by simp [Asch58Parabolic])
    | Tits => exact absurd hparc (by simp [Asch58Parabolic])

theorem asch80ThmA54Case_chev2
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Asch80ThmA54Case fun X _ => CFSG.Models.EvenLieType X := by
  intro Q _ _ L T M hKQ hLn hLs hLnab hC hP hL0 hT hM hMax
  have hL0facts : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧
        ∃ a b : L, a * b ≠ b * a :=
    fun X _ hX => CFSG.LocalAnalysis.UniquenessCase.UC22.uc22lb_listB_facts
      CFSG.LocalAnalysis.UniquenessCase.UC22.listBExceptionalFacts
      ((isCalL0_iff_asc1930ListB X).1 hX)
  obtain ⟨t, n, f, hm⟩ := hP
  rcases admissible_two_parameter_cases hm.1 with hA | hB | hCar | hU
  · exact absurd (isCalL0_of_lieModel_two hm hA) hL0
  · obtain ⟨hshape, hsolv⟩ :=
      asch58UniqueMax_and_isSolvable hLn hLs hC ⟨t, n, f, hm, hB⟩ hT hM hMax
    have hcat : CFSG.Open.IsCatalogGroup ↥L :=
      (hKQ.of_injective L.subtype L.subtype_injective).isCatalogGroup_of_surjective ⊤ hLnab
        (Subgroup.subtype ⊤) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
    have hq : Group.IsSolvable (Q ⧸ L) :=
      isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
        (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
          (hS _ hLs hLnab hcat))
    have hMsolv : Group.IsSolvable ↥M := by
      refine Group.isSolvable_of_ker_le_range (G' := ↥(M ⊓ L)) (G'' := Q ⧸ L)
        (Subgroup.inclusion (inf_le_left : M ⊓ L ≤ M))
        ((QuotientGroup.mk' L).comp M.subtype) ?_ (hG' := hsolv) (hG'' := hq)
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      rw [Subgroup.inclusion_range, Subgroup.mem_subgroupOf]
      exact ⟨x.2, hx⟩
    exact Or.inr ⟨Asch59.not_hasCompFactor_isCalL0_of_isSolvable hL0facts hMsolv, hshape⟩
  · obtain ⟨rfl, ht⟩ := hCar
    have h :=
      letI : IsSimpleGroup ↥L := hLs
      pRank_three_normalizer_of_cartanRankLarge hLnab hm ht
    exact Or.inl ⟨3, Nat.prime_three, by norm_num,
      pRank_perfectCore_lGen_of_pRank_normalizer hS hL0facts hKQ hLn hLs hLnab hC hT
        Nat.prime_three h.1 fun S => lt_trans (by norm_num) (h.2 S)⟩
  · obtain ⟨rfl, rfl, hn⟩ := hU
    have h := asch58UnitaryFive_holds ↥L n hn hm
    exact Or.inl ⟨5, by norm_num, by norm_num,
      pRank_perfectCore_lGen_of_pRank_normalizer hS hL0facts hKQ hLn hLs hLnab hC hT
        (by norm_num) h.1 h.2⟩

end CFSG.LocalAnalysis.WeakClosure81
