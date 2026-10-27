module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL34QuotientModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
public import CFSG.Quasithin.Background.L34HermitianPointStabilizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL34Kernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_l34_s1_false
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hL : IsLn ↥(lBar V₀ V hV L) 3 2)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
      ∈ irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
        ⊓ fixV (lBar V₀ V hV L)) = 9) :
    False := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  haveI : Finite W := inferInstance
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcomm : commSub (⊤ : Subgroup W) H = ⊤ := by
    simpa [wTil, H, W, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hirrH : commSub (⊤ : Subgroup W) H ∈ irrSet H := by
    simpa [H, W] using hirr
  have hdimH : E3.mQuot (⊤ : Subgroup W) (fixV H) = 9 := by
    simpa [hcomm, H, W, top_inf_eq] using hdim
  have hL' : IsLn ↥H 3 2 := by simpa [H] using hL
  have hmodel : BinaryNineTensor H ⊤ (fixV H) 1 :=
    binaryNineTensor_of_l34_quotient_rank_nine hW hL' hcomm hirrH hdimH
  have hcent : Subgroup.centralizer (H : Set (MulAut W)) = ⊥ :=
    centralizer_eq_bot_of_binaryNineTensor_of_commSub_eq_top hmodel hcomm
  have hHA : H ≤ A := by
    simpa [H, A, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs ha)
  have hC : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) = ⊥ := by
    rw [hcent]
    simp
  have hfix : ∀ x : W, x ≠ 1 →
      ∃ b ∈ H, orderOf b = 3 ∧ (b : MulAut W) x = x := by
    intro x hx
    exact exists_order_three_fix_of_binaryNineTensor hW hmodel le_rfl x (Subgroup.mem_top x)
  have hk : S168e3Kernel A 3 :=
    s168e3_kernel_of_l34_point_fixers hHA hAN hC hL' hfix
  have hsig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 ?_
    intro q hq hq2 hq3
    have hbound : CFSG.Open.pRank q A ≤ 1 := by
      have h1 := s16k_pRank_le_of_normalizer (Q := W) (L' := H) (N := A)
        (fun n hn l hl => (Subgroup.mem_normalizer_iff.mp (hAN hn) l).mp hl) hq
      have h2 : CFSG.Open.pRank q
          (A ⊓ Subgroup.centralizer (H : Set (MulAut W))) = 0 := by
        rw [hC]
        apply Nat.eq_zero_of_le_zero
        refine CFSG.SectionRank.pRank_le hq.one_lt ?_
        intro E hE _
        have hE' : E = ⊥ := le_bot_iff.1 hE
        simp [hE']
      have h3 : CFSG.Open.pRank q (⊤ : Subgroup (MulAut ↥H)) ≤
          if q = 3 then 2 else 1 :=
        s16k_pRank_aut_l34 hL' hq hq2
      rw [h2, Nat.zero_add] at h1
      rw [if_neg hq3] at h3
      omega
    have h4 : CFSG.Open.pRank q (Mbar D.M V₀ V hV) = CFSG.Open.pRank q A := rfl
    rw [h4]
    omega
  have h3sig : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  exact s168e3_false_of_kernel c Nat.prime_three h3sig hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
