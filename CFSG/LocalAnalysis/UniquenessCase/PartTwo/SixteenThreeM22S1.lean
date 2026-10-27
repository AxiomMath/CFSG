module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenM22QuotientModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.GroupTheory.PRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22Data

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem s168e3_m22_aut_dvd
    {H A : Subgroup (MulAut W)}
    (hH : IsSpor H .M22)
    (hcent : Subgroup.centralizer (H : Set (MulAut W)) = ⊥)
    (hAnorm : A ≤ Subgroup.normalizer (H : Set (MulAut W))) :
    Nat.card ↥A ∣ 887040 := by
  obtain ⟨eH⟩ := hH
  let f : ↥A →* MulAut ↥H :=
    (Subgroup.normalizerMonoidHom (H := H)).comp (Subgroup.inclusion hAnorm)
  have hker : f.ker = ⊥ := by
    rw [show f = (Subgroup.normalizerMonoidHom (H := H)).comp
        (Subgroup.inclusion hAnorm) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf hAnorm, hcent]
    simp
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hdvd : Nat.card ↥A ∣ Nat.card (MulAut ↥H) :=
    Subgroup.card_dvd_of_injective f hinj
  have hcard : Nat.card (MulAut ↥H) = 887040 := by
    let eH' : ↥H ≃* ↥(CFSG.Blueprint.NativeSporadic.M22) := eH
    have hcongr : Nat.card (MulAut ↥H) =
        Nat.card (MulAut ↥(CFSG.Blueprint.NativeSporadic.M22)) :=
      Nat.card_congr (MulAut.congr eH').toEquiv
    rw [CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.1] at hcongr
    exact hcongr
  rwa [hcard] at hdvd

private theorem s168e3_m22_s1_false_of_data
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hL : IsSpor (lBar V₀ V hV L) .M22)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 10)
    (hcent : Subgroup.centralizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) = ⊥)
    (hfixH : ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ lBar V₀ V hV L, orderOf b = 3 ∧ b x = x) :
    False := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcomm : commSub (⊤ : Subgroup W) H = ⊤ := by
    simpa [wTil, H, W, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hirrPair : commSub (commSub (⊤ : Subgroup W) H) H = commSub (⊤ : Subgroup W) H ∧
      IsIrrOn H (commSub (⊤ : Subgroup W) H)
        (commSub (⊤ : Subgroup W) H ⊓ fixV H) := by
    simpa only [irrSet, Set.mem_setOf_eq, H, W] using hirr
  have hirrOn : IsIrrOn H (⊤ : Subgroup W) (fixV H) := by
    simpa [hcomm, H, W, top_inf_eq] using hirrPair.2
  have hdim' : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10 := by
    simpa [hcomm, H, W, top_inf_eq] using hdim
  have hH : IsSpor H .M22 := by simpa [H] using hL
  have hHA : H ≤ A := by
    simpa [H, A, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAnorm : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs ha)
  have hcent' : Subgroup.centralizer (H : Set (MulAut W)) = ⊥ := by
    simpa [H, W] using hcent
  have hfixH' : ∀ x : W, x ≠ 1 → ∃ b ∈ H, orderOf b = 3 ∧ b x = x := by
    intro x hx
    obtain ⟨b, hb, hord, hbx⟩ := hfixH x hx
    exact ⟨b, by simpa [H] using hb, hord, hbx⟩
  have hAdvd : Nat.card ↥A ∣ 887040 := s168e3_m22_aut_dvd hH hcent' hAnorm
  have hcube : ¬ 3 ^ 3 ∣ Nat.card ↥A := by
    intro h
    exact (by norm_num : ¬ (3 ^ 3 ∣ 887040)) (h.trans hAdvd)
  have hqsq : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ¬ q ^ 2 ∣ Nat.card ↥A := by
    intro q hq hq2 hq3 h
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.not_sq_dvd_mulAut_m22 hq hq2 hq3
      (h.trans hAdvd)
  have hsig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 ?_
    intro q hq hq2 hq3
    have hpbound : CFSG.Open.pRank q (Mbar D.M V₀ V hV) ≤ 1 := by
      have h := CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := A) (k := 1) hq
        (by simpa using hqsq q hq hq2 hq3)
      simpa [A] using h
    omega
  have hfixA : ∀ x : W, x ≠ 1 → ∃ b ∈ A, orderOf b = 3 ∧ b x = x := by
    intro x hx
    obtain ⟨b, hbH, hord, hbx⟩ := hfixH' x hx
    exact ⟨b, hHA hbH, hord, hbx⟩
  have hk : S168e3Kernel A 3 := s168e3_kernel_of_cube Nat.prime_three A hcube hfixA
  have h3sig : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  exact s168e3_false_of_kernel c Nat.prime_three h3sig hk

end Generic

theorem s168e3_m22_s1_false
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hL : IsSpor (lBar V₀ V hV L) .M22)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 10) :
    False := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcomm : commSub (⊤ : Subgroup W) H = ⊤ := by
    simpa [wTil, H, W, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hH : IsSpor H .M22 := by simpa [H] using hL
  have hirrH : commSub (⊤ : Subgroup W) H ∈ irrSet H := by
    simpa [H, W] using hirr
  have hdimH : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10 := by
    have hirrPair : commSub (commSub (⊤ : Subgroup W) H) H = commSub (⊤ : Subgroup W) H ∧
        IsIrrOn H (commSub (⊤ : Subgroup W) H)
          (commSub (⊤ : Subgroup W) H ⊓ fixV H) := by
      simpa only [irrSet, Set.mem_setOf_eq, H, W] using hirr
    have hirrOn : IsIrrOn H (⊤ : Subgroup W) (fixV H) := by
      simpa [hcomm, H, W, top_inf_eq] using hirrPair.2
    simpa [hcomm, H, W, top_inf_eq] using hdim
  exact s168e3_m22_s1_false_of_data c hs hL hirr hdim
    (by
      simpa [H, W] using
        (centralizer_eq_bot_of_m22_quotient_rank_ten (W := W) (H := H)
          hW hH hcomm hirrH hdimH))
    (by
      intro x hx
      simpa [H, W] using
        (exists_order_three_fixing_of_m22_quotient_rank_ten (W := W) (H := H)
          hW hH hcomm hirrH hdimH x))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
