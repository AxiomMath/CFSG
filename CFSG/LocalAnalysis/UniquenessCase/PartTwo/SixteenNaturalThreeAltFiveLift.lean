module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCoverParabolic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveParabolic
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentreTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5RankA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_exists_permuting_nine_of_threeNat_isAlt_five
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5)
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV)
      (lBar V₀ V hV L)) = 168) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      Nat.card ↥Y = 9 ∧ (∀ y ∈ Y, y ^ 3 = 1) ∧
      ¬ IsCyclic ↥Y ∧ Permutes Y D.T := by
  classical
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let K : Subgroup (MulAut (Vtil V₀ V hV)) := s1t3KBar A H
  let Tb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T
  obtain ⟨N, hNA, hHN, -, hNKcomm, hNKbot, hNKsup, hKcases⟩ := hT.structure_of_seven h7
  have hHKbot : H ⊓ K = ⊥ := by
    have hle : H ⊓ K ≤ N ⊓ K := inf_le_inf_right K hHN
    rw [hNKbot] at hle
    exact le_bot_iff.mp hle
  have hHnorm : (H.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT.le).2 hT.normal
  have hKnormAmb : A ≤ Subgroup.normalizer (K : Set (MulAut (Vtil V₀ V hV))) := by
    have hAC : A ≤ Subgroup.normalizer
        (Subgroup.centralizer (H : Set (MulAut (Vtil V₀ V hV))) :
          Set (MulAut (Vtil V₀ V hV))) :=
      hT.normal.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup H)
    have hA : A ≤ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.le_normalizer (H := A)
    have h := (le_inf hA hAC).trans
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := A) (K := Subgroup.centralizer (H : Set (MulAut (Vtil V₀ V hV)))))
    simpa [K, s1t3KBar] using h
  have hKnorm : (K.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : K ≤ A)).2 hKnormAmb
  have hKsimple : IsSimpleGroup ↥K := by
    rcases hKcases with h7K | h21K | ⟨h168K, hKs⟩
    · omega
    · omega
    · exact hKs
  have hKnc : ¬ IsMulCommutative ↥K := by
    intro hcomm
    have hcommK : IsMulCommutative ↥K := hcomm
    have hprime : (Nat.card ↥K).Prime := (Group.is_simple_iff_prime_card).1 hKsimple
    rw [hK] at hprime
    norm_num at hprime
  have hKnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hKnc (isMulCommutative_iff.mpr h)
  have hKsimpleI : IsSimpleGroup ↥K := hKsimple
  have hKq : CFSG.Open.IsQuasisimple ↥K :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hKnab).1
  have hHsimple : IsSimpleGroup ↥H := s16h_e3_isSimpleGroup_of_isAlt hA5
  have hHq : CFSG.Open.IsQuasisimple ↥H := hT.quasi
  have hKcomp : IsComponentOf K A :=
    ⟨inf_le_left, CFSG.Open.IsSubnormal.step (inf_le_left : K ≤ A) hKnorm
      (CFSG.Open.IsSubnormal.refl A), hKq⟩
  have hHcomp : IsComponentOf H A :=
    ⟨hT.le, CFSG.Open.IsSubnormal.step hT.le hHnorm
      (CFSG.Open.IsSubnormal.refl A), hHq⟩
  have hHcard : Nat.card ↥H = 60 := s16h_e3_card_isAlt_five hA5
  have hFact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥H) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ hquot
    obtain ⟨eQ⟩ := hquot
    refine CFSG.AGLEmbeddingD2.McLaughlin.not_dvd_card_center_of_perfect hQ.1 ?_
    rw [Nat.card_congr eQ.toEquiv, hHcard]
    norm_num
  have hKcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥K) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ hquot
    obtain ⟨eQ⟩ := hquot
    refine CFSG.AGLEmbeddingD2.McLaughlin.not_dvd_card_center_of_perfect hQ.1 ?_
    rw [Nat.card_congr eQ.toEquiv, hK]
    norm_num
  obtain ⟨YH, hYHmem, hYHM, hYHnorm, hYHbar, hYH3⟩ :=
    s168e3_exists_normal_cover_prime_free (B := H) (p := 3) c hHcomp hHsimple hT.normal
      Nat.prime_three (by norm_num) hHcover
  obtain ⟨YK, hYKmem, hYKM, hYKnorm, hYKbar, hYK3⟩ :=
    s168e3_exists_normal_cover_prime_free (B := K) (p := 3) c hKcomp hKsimple hKnormAmb
      Nat.prime_three (by norm_num) hKcover
  let C : Subgroup G := YH ⊔ YK
  let P : Subgroup ↥D.M := YH.subgroupOf D.M
  let Q : Subgroup ↥D.M := YK.subgroupOf D.M
  have hCM : C ≤ D.M := sup_le hYHM hYKM
  have hPnorm : P.Normal := hYHnorm
  have hQnorm : Q.Normal := hYKnorm
  have hCnorm : (C.subgroupOf D.M).Normal := by
    rw [show C = YH ⊔ YK from rfl, Subgroup.subgroupOf_sup hYHM hYKM]
    exact Subgroup.sup_normal _ _
  have hMstab : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hMnorm : D.M ≤ normalizer (V : Set G) := c.setting.hyp16.hyp125.pairFacts.le_normalizer
  let E : Subgroup G := F11.CTilde D.M V₀ V
  let f : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMstab
  have hkerf : f.ker = E.subgroupOf D.M := by
    change (barHom V₀ V hV hMstab).ker = (F11.CTilde D.M V₀ V).subgroupOf D.M
    rw [ker_barHom V₀ V hV hMnorm hMstab]
  have hYHincl : (YH.subgroupOf D.M).map (Subgroup.inclusion hMstab) =
      YH.subgroupOf (stabTil V₀ V) := by
    rw [← Subgroup.comap_inclusion_subgroupOf hMstab YH]
    refine Subgroup.map_comap_eq_self ?_
    rw [Subgroup.inclusion_range]
    exact Subgroup.subgroupOf_mono (stabTil V₀ V) hYHM
  have hYKincl : (YK.subgroupOf D.M).map (Subgroup.inclusion hMstab) =
      YK.subgroupOf (stabTil V₀ V) := by
    rw [← Subgroup.comap_inclusion_subgroupOf hMstab YK]
    refine Subgroup.map_comap_eq_self ?_
    rw [Subgroup.inclusion_range]
    exact Subgroup.subgroupOf_mono (stabTil V₀ V) hYKM
  have hYHmap : (YH.subgroupOf D.M).map f = H := by
    change (YH.subgroupOf D.M).map (barHom V₀ V hV hMstab) = H
    rw [barHom, ← Subgroup.map_map, hYHincl]
    exact hYHbar
  have hYKmap : (YK.subgroupOf D.M).map f = K := by
    change (YK.subgroupOf D.M).map (barHom V₀ V hV hMstab) = K
    rw [barHom, ← Subgroup.map_map, hYKincl]
    exact hYKbar
  have himage : P.map f ⊓ Q.map f = ⊥ := by
    change (YH.subgroupOf D.M).map f ⊓ (YK.subgroupOf D.M).map f = ⊥
    rw [hYHmap, hYKmap, hHKbot]
  have hPQ : P ⊔ Q = C.subgroupOf D.M := by
    change (YH.subgroupOf D.M) ⊔ (YK.subgroupOf D.M) = (YH ⊔ YK).subgroupOf D.M
    exact (Subgroup.subgroupOf_sup hYHM hYKM).symm
  have hYHsub : (YH ⊓ E).subgroupOf D.M = P ⊓ f.ker := by
    change (YH ⊓ E).comap D.M.subtype = (YH.subgroupOf D.M) ⊓ f.ker
    rw [Subgroup.comap_inf]
    change YH.comap D.M.subtype ⊓ E.comap D.M.subtype = YH.comap D.M.subtype ⊓ f.ker
    rw [show f.ker = E.comap D.M.subtype from hkerf]
  have hYKsub : (YK ⊓ E).subgroupOf D.M = Q ⊓ f.ker := by
    change (YK ⊓ E).comap D.M.subtype = (YK.subgroupOf D.M) ⊓ f.ker
    rw [Subgroup.comap_inf]
    change YK.comap D.M.subtype ⊓ E.comap D.M.subtype = YK.comap D.M.subtype ⊓ f.ker
    rw [show f.ker = E.comap D.M.subtype from hkerf]
  have hCsub : (C ⊓ E).subgroupOf D.M = (C.subgroupOf D.M) ⊓ f.ker := by
    change (C ⊓ E).comap D.M.subtype = (C.subgroupOf D.M) ⊓ f.ker
    rw [Subgroup.comap_inf]
    change C.comap D.M.subtype ⊓ E.comap D.M.subtype = C.comap D.M.subtype ⊓ f.ker
    rw [show f.ker = E.comap D.M.subtype from hkerf]
  have hYH3' : ¬ 3 ∣ Nat.card ↥(YH ⊓ E) := hYH3
  have hYK3' : ¬ 3 ∣ Nat.card ↥(YK ⊓ E) := hYK3
  have hPZ3 : ¬ 3 ∣ Nat.card ↥(P ⊓ f.ker) := by
    rw [← hYHsub]
    rwa [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYHM)).toEquiv]
  have hQZ3 : ¬ 3 ∣ Nat.card ↥(Q ⊓ f.ker) := by
    rw [← hYKsub]
    rwa [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYKM)).toEquiv]
  have hZnorm : f.ker.Normal := f.normal_ker
  have hPZnorm : (P ⊓ f.ker).Normal := normal_inf_normal P f.ker
  have hBnorm : (Q ⊓ f.ker) ≤
      Subgroup.normalizer ((P ⊓ f.ker : Subgroup ↥D.M) : Set ↥D.M) :=
    Subgroup.le_normalizer_of_normal (H := P ⊓ f.ker) (K := Q ⊓ f.ker)
  have hsup3 : ¬ 3 ∣ Nat.card ↥((P ⊓ f.ker) ⊔ (Q ⊓ f.ker)) :=
    CFSG.LocalAnalysis.GLTheoremA.not_dvd_card_sup_of_le_normalizer Nat.prime_three
      hBnorm hPZ3 hQZ3
  have hjoin : (C.subgroupOf D.M) ⊓ f.ker =
      (P ⊓ f.ker) ⊔ (Q ⊓ f.ker) := by
    rw [← hPQ]
    exact CFSG.GroupTheory.ker_sup_eq_of_normalizer f P Q
      (Subgroup.le_normalizer_of_normal (H := P) (K := Q)) himage
  have hCcard : Nat.card ↥(C ⊓ E) =
      Nat.card ↥((C.subgroupOf D.M) ⊓ f.ker) := by
    rw [← hCsub]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hCM)).toEquiv).symm
  have hC3 : ¬ 3 ∣ Nat.card ↥(C ⊓ E) := by
    rw [hCcard, hjoin]
    exact hsup3
  obtain ⟨J, hTJ, hJL, hJcard, hJexp⟩ := hT.parabolicK_of_isAlt_five hA5 h7 hK
  have hbarSubC : barSub V₀ V hV C = H ⊔ K := by
    change ((C.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)) = H ⊔ K
    rw [show C = YH ⊔ YK from rfl,
      Subgroup.subgroupOf_sup (hYHM.trans hMstab) (hYKM.trans hMstab),
      Subgroup.map_sup]
    change barSub V₀ V hV YH ⊔ barSub V₀ V hV YK = H ⊔ K
    rw [hYHbar, hYKbar]
  have hJrange : J ≤ barSub V₀ V hV C ⊔ Tb := by
    rw [hbarSubC]
    exact hJL
  have hJcard9 : Nat.card ↥J = 3 ^ 2 * Nat.card ↥Tb := by
    simpa using hJcard
  have hY := s168e3_exists_permuting_of_normal_subgroup_three_free (C := C) (a := 2)
    c hCM hCnorm hC3 hTJ hJrange hJcard9 (by norm_num) hJexp
  simpa using hY

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
