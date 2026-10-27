module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78At3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Frat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Zc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Norm
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16t_l4_not_solvable (hS : S16tL4Setting D V₀ V L hV) : ¬ Group.IsSolvable ↥D.M := by
  intro hsol
  haveI : Group.IsSolvable ↥D.M := hsol
  obtain ⟨φ, hφsurj, -⟩ :=
    s16t_l4_exists_hom_barSub (hV := hV) (X := D.M) (s16t_l4_le_stabTil hS) le_rfl
  haveI : Group.IsSolvable ↥(Mbar D.M V₀ V hV) := solvable_of_surjective hφsurj
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := s16t_l4_lbar_le_mbar hS
  haveI : Group.IsSolvable ↥(lBar V₀ V hV L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.injective
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := s16t_l4_lbar_simple hS
  exact s16t_l4_lbar_not_commutative hS
    ⟨⟨fun a b =>
      (IsSimpleGroup.comm_iff_isSolvable (G := ↥(lBar V₀ V hV L))).mpr inferInstance a b⟩⟩

theorem s16t_l4_exists_noncyclic_three (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) {A : Subgroup G} (hAY : A ≤ Y) (hA : Nat.card A = 7) :
    ∃ P : Subgroup G, P ≤ normalizer (A : Set G) ⊓ D.M ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P ∧
      ∃ x ∈ P, ∃ a ∈ A, x * a ≠ a * x := by
  have hM : D.M ≤ stabTil V₀ V := s16t_l4_le_stabTil hS
  have hYM : Y ≤ D.M := hY.le
  have hA7 : IsPGroup 7 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hker7 : ¬ 7 ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) :=
    s16t_l4_not_dvd_ker (p := 7) hY (by norm_num) (by norm_num)
  set Abar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV A with hAbar
  have hAbar_card : Nat.card ↥Abar = 7 := by
    rw [hAbar, s16t_l4_card_barSub (p := 7) hM hYM hAY (by norm_num) hA7 hker7, hA]
  have hAbar_le : Abar ≤ lBar V₀ V hV L := by
    rw [hAbar]
    exact (barSub_mono V₀ V hV hAY).trans (le_of_eq hY.bar_eq)
  obtain ⟨y, hyL, hy3, hyN, abar, habar, hyabar⟩ :=
    s16t_l4_exists_three_normalizing hS hAbar_le hAbar_card
  obtain ⟨k, hk3⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card ↥(kBar D.M V₀ V hV L) by
      rw [s16t_l4_card_kbar hS]; norm_num)
  set k' : MulAut (Vtil V₀ V hV) := (k : MulAut (Vtil V₀ V hV)) with hk'def
  have hk'mem : k' ∈ kBar D.M V₀ V hV L := k.2
  have hk'3 : orderOf k' = 3 := (Subgroup.orderOf_coe k).trans hk3
  have hk'M : k' ∈ Mbar D.M V₀ V hV := k.2.1
  have hk'cent : k' ∈ Subgroup.centralizer (lBar V₀ V hV L : Set _) := k.2.2
  have hyM : y ∈ Mbar D.M V₀ V hV := s16t_l4_lbar_le_mbar hS hyL
  have hky : k' * y = y * k' := (Subgroup.mem_centralizer_iff.mp hk'cent y hyL).symm
  have hcomm : ∀ a ∈ Subgroup.zpowers k', ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hm, ← hn]
    exact ((commute_iff_eq k' y).2 hky).zpow_zpow m n |>.eq
  obtain ⟨-, hinfKL, -⟩ := s16t_l4_mbar_direct hS
  have hinf : Subgroup.zpowers k' ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzK : z ∈ kBar D.M V₀ V hV L := Subgroup.zpowers_le.mpr hk'mem hz.1
    have hzL : z ∈ lBar V₀ V hV L := Subgroup.zpowers_le.mpr hyL hz.2
    have hzKL : z ∈ kBar D.M V₀ V hV L ⊓ lBar V₀ V hV L := ⟨hzK, hzL⟩
    rwa [hinfKL, Subgroup.mem_bot] at hzKL
  have hnormal : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers k' : Set _) := by
    intro b hb
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr (fun a ha => hcomm a ha b hb))
  set E : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Subgroup.zpowers k' ⊔ Subgroup.zpowers y with hE
  have hEcard : Nat.card ↥E = 9 := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers k') (Subgroup.zpowers y) hnormal (disjoint_iff.mpr hinf)
    rw [hE, h, Nat.card_zpowers, Nat.card_zpowers, hk'3, hy3]
  have hE3 : IsPGroup 3 ↥E := IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hEM : E ≤ Mbar D.M V₀ V hV := by
    rw [hE]
    exact sup_le (Subgroup.zpowers_le.mpr hk'M) (Subgroup.zpowers_le.mpr hyM)
  have hEnorm : E ≤ Subgroup.normalizer (Abar : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hE]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr hyN)
    have hkcentA : k' ∈ Subgroup.centralizer (Abar : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.centralizer_le (fun x hx => hAbar_le hx) hk'cent
    exact Subgroup.centralizer_le_normalizer _ hkcentA
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    haveI : IsCyclic ↥E := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
    have h9 : 9 ∣ orderOf g := by rw [hg, hEcard]
    have h9' : 9 ∣ orderOf (g : MulAut (Vtil V₀ V hV)) := by rwa [Subgroup.orderOf_coe]
    refine s16t_l4_mbar_not_nine hS ⟨(g : MulAut (Vtil V₀ V hV)), hEM g.2⟩ ?_
    rwa [← Subgroup.orderOf_coe (⟨(g : MulAut (Vtil V₀ V hV)), hEM g.2⟩ :
      ↥(Mbar D.M V₀ V hV))]
  have liftA : ∀ q ∈ E, ∃ n : G, n ∈ normalizer (A : Set G) ∧ n ∈ D.M ∧
      ∃ h : n ∈ stabTil V₀ V, actTil V₀ V hV ⟨n, h⟩ = q :=
    fun q hqE => s16t_l4_barSub_normalizer (p := 7) hM hYM hY.normal hAY (by norm_num) hA
      hker7 (hEM hqE) (hEnorm hqE)
  have hk'bar : k' ∈ barSub V₀ V hV (normalizer (A : Set G) ⊓ D.M) := by
    obtain ⟨n, hnA, hnM, h, hnq⟩ :=
      liftA k' (by rw [hE]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers k'))
    exact (mem_barSub V₀ V hV (normalizer (A : Set G) ⊓ D.M) k').2
      ⟨⟨n, h⟩, ⟨hnA, hnM⟩, hnq⟩
  have hybar : y ∈ barSub V₀ V hV (normalizer (A : Set G) ⊓ D.M) := by
    obtain ⟨n, hnA, hnM, h, hnq⟩ :=
      liftA y (by rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    exact (mem_barSub V₀ V hV (normalizer (A : Set G) ⊓ D.M) y).2
      ⟨⟨n, h⟩, ⟨hnA, hnM⟩, hnq⟩
  have hEle : E ≤ barSub V₀ V hV (normalizer (A : Set G) ⊓ D.M) := by
    rw [hE]
    exact sup_le (Subgroup.zpowers_le.mpr hk'bar) (Subgroup.zpowers_le.mpr hybar)
  obtain ⟨P, hPJ, hP3, hPE⟩ := s16t_l4_exists_lift_barSub (p := 3) hM
    (J := normalizer (A : Set G) ⊓ D.M) inf_le_right hEle (by norm_num) hE3
  have hPnc : ¬ IsCyclic ↥P :=
    s16t_l4_not_isCyclic_of_barSub hM (hPJ.trans inf_le_right) (by rw [hPE]; exact hEnc)
  obtain ⟨b, hbA, hb_abar⟩ := (mem_barSub V₀ V hV A abar).1 habar
  have hyE : y ∈ E := by rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  obtain ⟨g, hgP, hgy⟩ := (mem_barSub V₀ V hV P y).1 (by rw [hPE]; exact hyE)
  refine ⟨P, hPJ, hP3, hPnc, (g : G), hgP, (b : G), hbA, ?_⟩
  intro hgb
  refine hyabar ?_
  have hcommgy : y * abar = abar * y := by
    rw [← hgy, ← hb_abar]
    simp only [← map_mul]
    congr 1
    exact Subtype.ext hgb
  rw [hcommgy, mul_assoc, mul_inv_cancel, mul_one]

theorem s16t_l4_sec7hyp (hS : S16tL4Setting D V₀ V L hV)
    (hSP : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {Y : Subgroup G} (hY : S16tL4Pack D V₀ V L hV Y) {A : Subgroup G} (hAY : A ≤ Y)
    (hA : Nat.card A = 7) (hAM : ¬ normalizer (A : Set G) ≤ D.M) :
    F07.Sec7Hyp D 3 (normalizer (A : Set G)) := by
  refine ⟨by norm_num, by norm_num, hSP, close16_normalizer_ne_top D hA, hAM, ?_⟩
  obtain ⟨P, hPJ, hP3, hPnc, -⟩ := s16t_l4_exists_noncyclic_three hS hY hAY hA
  obtain ⟨E, hEP, hEel, hEcard⟩ :=
    CFSG.Goldschmidt.G63.exists_isElemAbelian_card_sq (G := G) (p := 3) (by norm_num) (by norm_num)
      hP3 hPnc
  have h2 : 2 ≤ CFSG.Open.pRank 3 (normalizer (A : Set G) ⊓ D.M) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.le_pRank' (p := 3) (by norm_num)
      (hEP.trans hPJ) hEel hEcard
  omega

theorem s16t_l4_not_isCyclic_sylow_two (hS : S16tL4Setting D V₀ V L hV) (hV₀ : V₀ ≠ ⊥)
    {Y : Subgroup G} (hY : S16tL4Pack D V₀ V L hV Y) {A : Subgroup G} (hAY : A ≤ Y)
    (hA : Nat.card A = 7) {S : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (normalizer (A : Set G) ⊓ D.M)) :
    ¬ IsCyclic ↥S := by
  have hAM : A ≤ D.M := hAY.trans hY.le
  intro hcyc
  haveI : IsCyclic ↥S := hcyc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := normalizer (A : Set G) ⊓ D.M
  let E : Subgroup G := V ⊓ centralizer (A : Set G)
  have hVT : V ≤ D.T := s15_13A_le_T hS.counterex.setting.hyp16.hyp125
  have hEcard : 4 ≤ Nat.card ↥E :=
    s16t_l4_four_le_card_centralizer hS hV₀ hAM hA (hAY.trans (s16t_l4_le_centralizer_v0 hS hY))
  have hE2 : IsPGroup 2 ↥E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hV.2 (g : G) g.2.1
  have hEK : E ≤ K := by
    refine le_inf ?_ ?_
    · exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
    · exact inf_le_left.trans (hVT.trans D.sylowM.le)
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hSsub : IsCyclic ↥(S.subgroupOf K) :=
    isCyclic_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSyl.le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSyl.le).injective
  haveI : IsCyclic ↥(S.subgroupOf K) := hSsub
  haveI : IsCyclic ↥Q :=
    isCyclic_of_injective (f := (MulEquiv.subgroupCongr hQ).toMonoidHom)
      (MulEquiv.subgroupCongr hQ).injective
  have hE'2 : IsPGroup 2 (E.subgroupOf K) := hE2.comap_subtype
  obtain ⟨Q', hQ'⟩ := hE'2.exists_le_sylow
  haveI : IsCyclic ↥Q' :=
    isCyclic_of_surjective (f := (Sylow.equiv Q Q').toMonoidHom) (Sylow.equiv Q Q').surjective
  haveI : IsCyclic ↥(E.subgroupOf K) :=
    isCyclic_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hQ').toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ').surjective
  haveI : IsCyclic ↥E :=
    isCyclic_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hEK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hEK).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
  have hg4 : 4 ≤ orderOf g := by rw [hg]; exact hEcard
  have hg2 : orderOf g ∣ 2 := by
    rw [← Subgroup.orderOf_coe g, orderOf_dvd_iff_pow_eq_one]
    exact hV.2 (g : G) g.2.1
  have := Nat.le_of_dvd (by norm_num : 0 < 2) hg2
  omega

theorem s16t_l4_normalizer_seven_le (h78 : R7_8At3 D)
    (hSP : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (hS : S16tL4Setting D V₀ V L hV)
    (hV₀ : V₀ ≠ ⊥) {Y : Subgroup G} (hY : S16tL4Pack D V₀ V L hV Y) {A : Subgroup G}
    (hAY : A ≤ Y) (hA : Nat.card A = 7) : normalizer (A : Set G) ≤ D.M := by
  by_contra hAM
  let H : Subgroup G := normalizer (A : Set G)
  have hsec : F07.Sec7Hyp D 3 H := s16t_l4_sec7hyp hS hSP hY hAY hA hAM
  have hAD : A ≤ D.M := hAY.trans hY.le
  have hAK : A ≤ H ⊓ D.M := le_inf Subgroup.le_normalizer hAD
  have hKA : H ⊓ D.M ≤ normalizer (A : Set G) := inf_le_left
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (H ⊓ D.M)
  let D₀ : Subgroup G := CFSG.RankThree.PartOne.omegaOne 3 P
  obtain ⟨-, hcases⟩ := h78 H P D₀ hsec hP rfl
  rcases hcases with h1 | h2
  · obtain ⟨hKeq, -, -⟩ := h1
    have hPn : H ⊓ D.M ≤ normalizer (P : Set G) := by
      rw [hKeq]
      exact inf_le_right
    obtain ⟨P₀, hP₀J, hP₀3, -, x, hx, a, ha, hxa⟩ :=
      s16t_l4_exists_noncyclic_three hS hY hAY hA
    exact hxa (close16_three_centralizes hAK hKA hA hP hPn hP₀J hP₀3 x hx a ha)
  · obtain ⟨-, S, hSylS, -, hScyc, -⟩ := h2
    exact s16t_l4_not_isCyclic_sylow_two hS hV₀ hY hAY hA hSylS hScyc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
