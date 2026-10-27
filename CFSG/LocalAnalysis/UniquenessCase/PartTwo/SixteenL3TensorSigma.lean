module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3TensorPointFixer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenPairComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTensProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open
  Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_sig_eq_singleton_seven_of_l3_tensor
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hK3 : IsL3 ↥K 1)
    (hT : NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 3 1) :
    D.sig = {7} := by
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_two_conj_l3_two c hK hg hne hL hK3
  have hw : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hw' : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
    simpa only [wTil, lBar] using hw
  have hTtop : NatTensor (lBar V₀ V hV L) ⊤ ⊥ 3 1 := by
    simpa only [hw'] using hT
  obtain ⟨Kf, hKfield, hKfinite, hKcard, hrealK⟩ := hTtop
  have hK2 : Nat.card Kf = 2 := by simpa using hKcard
  have hrealZ : (FFModel.tensorNat 3 (ZMod 2)).Realizes (lBar V₀ V hV L) ⊤ ⊥ :=
    @tensorNat_realizes_zmod_two 3 Kf hKfield hKfinite hK2 (Vtil V₀ V hV) inferInstance
      (lBar V₀ V hV L) ⊤ ⊥ hrealK
  have hrealMod : (tensorPairModel SL32 SL32).RealizesMod (lBar V₀ V hV L) := hrealZ
  have hnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    Mbar_le_normalizer_lBar_of_tensor D hV c.setting.hyp151 c.ne hrealZ
  have hcardnorm : Nat.card
      ↥(Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) =
      2 * 168 ^ 2 :=
    s16c7_card_normalizer hrealMod
  have hcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 2 * 168 ^ 2 := by
    rw [← hcardnorm]
    exact Subgroup.card_dvd_of_le hnorm
  have h3not : 3 ∉ D.sig := by
    intro h3
    have hcube : ¬ 3 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      intro hd
      have := hd.trans hcard
      norm_num at this
    have hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 →
        ∃ b ∈ Mbar D.M V₀ V hV, orderOf b = 3 ∧ b x = x := by
      intro x hx
      have hHle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
        simpa only [lBar] using barSub_mono V₀ V hV c.setting.hyp151.le
      obtain ⟨b, hbH, hb3, hbfix⟩ := tensorPair_exists_order_three_fix hrealMod x hx
      exact ⟨b, hHle hbH, hb3, hbfix⟩
    exact s168e3_false_of_kernel c Nat.prime_three h3
      (s168e3_kernel_of_cube Nat.prime_three (Mbar D.M V₀ V hV) hcube hfix)
  have key : ∀ q ∈ D.sig, q = 7 := by
    intro q hq
    obtain ⟨hqp, hq2⟩ := D.sig_prime q hq
    have h2 := c.two_le_pRank_mbar hq
    obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hqp.one_lt (Mbar D.M V₀ V hV)
    have h1 : q ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self q (by omega)
    have h4 : q ∣ 2 * 168 ^ 2 := h1.trans ((Subgroup.card_dvd_of_le hE).trans hcard)
    have hq3 : q ≠ 3 := fun h => h3not (h ▸ hq)
    have hfac : 2 * 168 ^ 2 = 2 ^ 7 * 3 ^ 2 * 7 ^ 2 := by norm_num
    rw [hfac] at h4
    rcases (Nat.Prime.dvd_mul hqp).1 h4 with h5 | h5
    · rcases (Nat.Prime.dvd_mul hqp).1 h5 with h6 | h6
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1
          (hqp.dvd_of_dvd_pow h6)) hq2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1
          (hqp.dvd_of_dvd_pow h6)) hq3
    · exact (Nat.prime_dvd_prime_iff_eq hqp (by norm_num : Nat.Prime 7)).1
        (hqp.dvd_of_dvd_pow h5)
  obtain ⟨p₀, hp₀⟩ := c.std.hx.sig_nonempty
  ext q
  constructor
  · intro hq
    exact key q hq
  · intro hq
    rw [Set.mem_singleton_iff.1 hq, ← key p₀ hp₀]
    exact hp₀

theorem s168e3_case163_8F_of_l3_tensor
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hK3 : IsL3 ↥K 1)
    (hT : NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 3 1) :
    Case163_8F D V₀ V hV L := by
  have hsig : D.sig = {7} :=
    s168e3_sig_eq_singleton_seven_of_l3_tensor c hK hg hne hL hK3 hT
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_two_conj_l3_two c hK hg hne hL hK3
  have hsimple : IsSimpleGroup ↥K := isSimpleGroup_of_isL3 hK3
  obtain ⟨-, -, hprod⟩ := s16k_components_conj hK hg hne hsimple
  obtain ⟨eK⟩ := hprod
  let Kg : Subgroup (MulAut (Vtil V₀ V hV)) := K.map (MulAut.conj g).toMonoidHom
  let e2 : ↥Kg ≃* ↥K :=
    (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  let eprod : ↥(lBar V₀ V hV L) ≃* (↥K × ↥K) :=
    (MulEquiv.subgroupCongr (by simpa only [Kg] using hL)).trans
      (eK.trans (MulEquiv.prodCongr (MulEquiv.refl ↥K) e2))
  have h8 : Case163_8 D V₀ V hV L := by
    refine ⟨⟨↥K, inferInstance, hK3, ⟨eprod⟩⟩, ?_, hs, hsig⟩
    simpa only [wTil, lBar] using hT
  exact case163_8F_of_case163_8 c.setting c.ne c.conc h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
