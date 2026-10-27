module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Family
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Assembly
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltContext
public import CFSG.Quasithin.Background.F918Z8Ex2a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Config

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise


private theorem natSpn_map_conj {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {m a : ℕ} (h : NatSpn L I ⊥ m a) {g : MulAut W}
    (ht : ∀ l ∈ L, g * l * g⁻¹ ∈ L) (ht' : ∀ l ∈ L, g⁻¹ * l * g ∈ L) :
    NatSpn L (I.map g.toMonoidHom) ⊥ m a := by
  obtain ⟨hm, K, hKf, hKfin, hcard, hreal⟩ := h
  letI := hKf
  letI := hKfin
  obtain ⟨π, hreal'⟩ := hreal
  refine ⟨hm, K, hKf, hKfin, hcard, ?_⟩
  exact ⟨_, by
    have h := CFSG.Quasithin.RonanF918.realizesVia_map_conj hreal' g ht ht'
    simpa using h⟩

private theorem natSpn_of_secIsoOn {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I J : Subgroup W} {m a : ℕ} (h : NatSpn L I ⊥ m a) (hiso : SecIsoOn L I ⊥ J ⊥)
    (hIinv : XMod.IsInv ↥L I) (hJinv : XMod.IsInv ↥L J) : NatSpn L J ⊥ m a := by
  obtain ⟨hm, K, hKf, hKfin, hcard, hreal⟩ := h
  letI := hKf
  letI := hKfin
  obtain ⟨π, hreal'⟩ := hreal
  have hisoIJ : XMod.Iso ↥L I J := iso_of_secIsoOn_bot hiso
  have hisoJI : XMod.Iso ↥L J I := XMod.Iso.symm hIinv hisoIJ
  have hSecL : SecIsoL L J ⊥ I ⊥ := B5.secIsoL_of_iso hJinv hIinv hisoJI
  exact ⟨hm, K, hKf, hKfin, hcard, ⟨π,
    CFSG.Quasithin.d321i_realizesVia_of_secIsoL hreal' hSecL⟩⟩

private theorem faithful_of_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet L)
    (hfix : fixV L = ⊥) (hsimple : IsSimpleGroup ↥L) :
    ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1 := by
  have hLI : L ≤ stabSub I := Thm14_5.le_stabSub_of_mem_irrSet hI
  have hne : ¬ L ≤ centSub I := by
    apply Thm14_5.not_le_centSub_of_mem_irrSet hI
    rw [hfix, inf_bot_eq]
  intro l hl hfixl
  have hmem : (⟨l, hl⟩ : ↥L) ∈ (Thm14_5.resTo hLI).ker := by
    rw [MonoidHom.mem_ker, Thm14_5.resTo_eq_one_iff]
    exact hfixl
  rcases (MonoidHom.normal_ker (Thm14_5.resTo hLI)).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    apply hne
    intro x hx
    rw [mem_centSub]
    intro u hu
    have h1 : Thm14_5.resTo hLI ⟨x, hx⟩ = 1 := by
      rw [← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top _
    exact (Thm14_5.resTo_eq_one_iff hLI ⟨x, hx⟩).mp h1 u hu

private theorem bParam_le_two_mul {W : Type} [CommGroup W] [Finite W] {n : ℕ}
    (hb : W4Lem4_17Sp4G2N) (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hL : IsComponentOf L Y) (hLn : (L.subgroupOf Y).Normal)
    (hfix : fixV L = ⊥) (hodd : Odd n) (hn : 1 < n)
    (hSG : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSp4 ↥L n ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsG2 ↥L n) :
    bParam L Y ≤ 2 * n := by
  have hNY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).mp hLn
  obtain ⟨T, hTY⟩ := CFSG.Quasithin.E1.exists_isSylowIn_two Y
  have h1 : bParam L Y ≤ bParam L (L ⊔ T) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.bParam_le_of_normal hL.1 hNY hTY
  have hLnT : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (hTY.le.trans hNY))
  have hcomp : IsComponentOf L (L ⊔ T) :=
    ⟨le_sup_left, CFSG.Open.IsSubnormal.step le_sup_left hLnT (CFSG.Open.IsSubnormal.refl _),
      hL.2.2⟩
  have hsyl : IsSylowIn 2 T (L ⊔ T) :=
    CFSG.Quasithin.E6.isSylowIn_of_le hTY le_sup_right (sup_le hL.1 hTY.le)
  have hOddC : Odd (Nat.card ↥(Subgroup.center ↥L)) :=
    GF2Reps13Alt.odd_card_center_of_o2Trivial hO2 hL.1
      (fun y hy l hl => (Subgroup.mem_normalizer_iff.mp (hNY hy) l).mp hl)
  haveI hWnt : Nontrivial W := by
    haveI hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := inferInstance
    haveI hLnt : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI : Subsingleton W := h
    haveI : Subsingleton (MulAut W) :=
      ⟨fun f g => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    exact not_subsingleton ↥L inferInstance
  have hfixT : fixV T ≠ fixV (L ⊔ T) := by
    have hlt : fixV (L ⊔ T) ≤ fixV L := fixV_anti le_sup_left
    rw [hfix] at hlt
    have hbot : fixV (L ⊔ T) = ⊥ := le_bot_iff.mp hlt
    rw [hbot]
    by_cases hT : T = ⊥
    · rw [hT, B1.fixV_bot]
      exact top_ne_bot
    · exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.fixV_ne_bot_of_isPGroup' hW
        hTY.isPGroup
  exact h1.trans (hb W hW (L ⊔ T) L T n le_sup_left le_sup_right rfl hcomp hsyl hfixT hOddC
    (hTY.le.trans hNY) hn hSG)

private theorem exists_irrSet_decomposition {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hW : ∀ w : W, w ^ 2 = 1) (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : L = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV L = ⊥)
    (hsum0 : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
      (fun X' => commV (autQuot X' (⊥ : Subgroup W))))
    {I : Subgroup W} (hI : I ∈ irrSet L) :
    ∃ s : Set (Subgroup W), I ∈ s ∧ s ⊆ irrSet L ∧ sSupIndep s ∧ sSup s = ⊤ ∧
      rk ↥(commV L) = s.ncard * rk ↥I := by
  have hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥ := by
    rw [CFSG.LocalAnalysis.WeakClosure81.iSup_conjSet_eq_biSup_conj, ← hX]
    exact hfix
  have htop : commV L = ⊤ := commV_eq_top_of_basic hW hO2 hB hL hX
  have hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV :=
    Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
  obtain ⟨s, hIs, hsIrr, hsind, hssup⟩ :=
    exists_sSupIndep_irrSet_of_basic hW hO2 hB hL hfixH hsum hI
  have hrkeq : ∀ J ∈ s, rk ↥J = rk ↥I := fun J hJ =>
    rk_eq_of_mem_irrSet_of_basic (I := I) (J := J) hW hO2 hB hL hfixH hsum hI (hsIrr hJ)
  have hrkS : rk ↥(sSup s) = s.ncard * rk ↥I := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Lin_rk_sSup_eq_finsum hsind]
    rw [finsum_mem_eq_finite_toFinset_sum (fun J : Subgroup W => rk ↥J) (Set.toFinite s)]
    rw [Finset.sum_congr rfl (fun J hJ => hrkeq J (by simpa using hJ))]
    rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card s (Set.toFinite s)]
  refine ⟨s, hIs, hsIrr, hsind, hssup.trans htop, ?_⟩
  rw [← hrkS, hssup]

theorem concl146_of_caseI_Sp4
    (hb : W4Lem4_17Sp4G2N) (hMod : K146ModSp4) (hTwo : K146Sp4TwoNat)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {n : ℕ} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : L = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hSp : IsSp4 ↥L n) (hodd : Odd n)
    (hn : 1 < n) (hfix : fixV L = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ max (bParam L Y) n + 2) : Sec18Concl Y L L n := by
  classical
  have hn3 : 3 ≤ n := by
    rcases hodd with ⟨k, hk⟩
    omega
  have hLn : (L.subgroupOf Y).Normal :=
    (Thm14_5.iSup_map_conj_eq_self_iff hL.1).mp hX.symm
  have hsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
  have hbY : bParam L Y ≤ 2 * n :=
    bParam_le_two_mul hb hW hO2 hL hLn hfix hodd hn (Or.inl hSp)
  have hYle : E3.mParam Y ≤ 2 * n + 2 := by
    have hmax : max (bParam L Y) n ≤ 2 * n := max_le hbY (by omega)
    omega
  have hcommVtop : commV L = ⊤ := commV_eq_top_of_basic hW hO2 hB hL hX
  have hd : E3.mParam Y < dMinDeg ↥L := by
    have h4 := (dMinDeg_lower_bounds (L := ↥L)).2.2.1 hSp hn
    omega
  have hnL2 : ∀ e : ℕ, ¬ CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥L e := by
    intro e he
    exact not_isL2_of_shape (Or.inr (Or.inl hSp)) he
  obtain ⟨hsum0, I, hI, hIm⟩ :=
    case2_of_fix_of_lt_dMinDeg hW hO2 hB hL hX hfix hd hnL2
  obtain ⟨hLN, hnorm, hirr, hrkI, hmul, hmN⟩ :=
    setup_of_case2 hW hL hX hfix hsum0 hI hIm
  obtain ⟨s, hIs, hsIrr, hsind, hssup, hrkW⟩ :=
    exists_irrSet_decomposition hW hO2 hB hL hX hfix hsum0 hI
  have hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥ := by
    rw [CFSG.LocalAnalysis.WeakClosure81.iSup_conjSet_eq_biSup_conj, ← hX]
    exact hfix
  have hIne : I ≠ ⊥ := CFSG.LocalAnalysis.WeakClosure81.ne_bot_of_mem_irrSet hI
  have hrkIpos : 0 < rk ↥I := by
    rcases Nat.eq_zero_or_pos (rk ↥I) with h0 | h0
    · exact absurd ((rk_eq_zero_iff hW).mp h0) hIne
    · exact h0
  have hSpS : IsSp4 ↥(autSub L I) n :=
    lieModel_autSub hL hX hfix hsum0 hsimple hI hSp
  obtain ⟨hNatS, hNm⟩ :=
    hMod ↥I (fun u => Subtype.ext (hW (u : W))) (autSub Y I) (autSub L I) n
      (autSub_mono hL.1 I) hnorm hSpS hodd hn hirr (by omega)
  have hkey : n * rk ↥(commV L) ≤ (2 * n + 2) * rk ↥I := by
    calc n * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
          Nat.mul_le_mul_right _ hNm
      _ ≤ E3.mParam Y * rk ↥I := hmul
      _ ≤ (2 * n + 2) * rk ↥I := Nat.mul_le_mul_right _ hYle
  have hns : n * s.ncard ≤ 2 * n + 2 := by
    have h := hkey
    rw [hrkW] at h
    have h2 : (n * s.ncard) * rk ↥I ≤ (2 * n + 2) * rk ↥I := by
      rw [Nat.mul_assoc]
      exact h
    exact Nat.le_of_mul_le_mul_right h2 hrkIpos
  have hspos : 0 < s.ncard := (Set.ncard_pos (Set.toFinite s)).2 ⟨I, hIs⟩
  rcases Nat.lt_or_ge s.ncard 2 with hlt | hge
  ·
    have hs1 : s.ncard = 1 := by omega
    obtain ⟨J, hsJ⟩ := Set.ncard_eq_one.mp hs1
    have hIJ : I = J := by
      have : I ∈ ({J} : Set (Subgroup W)) := by rwa [← hsJ]
      simpa using this
    have hJtop : J = ⊤ := by
      have h := hssup
      rw [hsJ] at h
      simpa using h
    have hItop : I = ⊤ := by rw [hIJ, hJtop]
    have hirrTop : IsIrrOn L ⊤ ⊥ := by
      have h := hI.2
      rw [hItop] at h
      simpa [hfix] using h
    have hNatL : NatSpn L ⊤ ⊥ 4 n :=
      (hMod W hW Y L n hL.1 hLn hSp hodd hn hirrTop hYle).1
    exact Or.inl ⟨hSp, by simpa [hfix] using hNatL⟩
  ·
    have hs2 : s.ncard = 2 := by
      have h3n : 2 * n + 2 < 3 * n := by omega
      have hlt : n * s.ncard < n * 3 := by
        calc n * s.ncard ≤ 2 * n + 2 := hns
          _ < 3 * n := h3n
          _ = n * 3 := by ring
      have : s.ncard < 3 := Nat.lt_of_mul_lt_mul_left hlt
      omega
    have hdiff : (s \ {I}).ncard = 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem hIs, hs2]
    obtain ⟨J, hJt⟩ := Set.ncard_eq_one.mp hdiff
    have hJmem : J ∈ s \ {I} := by rw [hJt]; exact Set.mem_singleton J
    have hJs : J ∈ s := hJmem.1
    have hJI : J ≠ I := hJmem.2
    have hsIJ : s = {I, J} := by
      have hins : s = insert I (s \ {I}) := by
        rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hIs]
      rw [hins, hJt]
    have hdisj : I ⊓ J = ⊥ := by
      have hpair : sSupIndep ({I, J} : Set (Subgroup W)) := by rwa [← hsIJ]
      exact disjoint_iff.1 ((sSupIndep_pair (Ne.symm hJI)).1 hpair)
    have hsupIJ : I ⊔ J = ⊤ := by
      have h := hssup
      rw [hsIJ, sSup_pair] at h
      exact h
    have hIirr : IsIrrOn L I ⊥ := by simpa [hfix] using hI.2
    have hJirr : IsIrrOn L J ⊥ := by
      have h := hsIrr hJs
      simpa [hfix] using h.2
    have hLI : L ≤ stabSub I := Thm14_5.le_stabSub_of_mem_irrSet hI
    obtain ⟨hm4, K, hKf, hKfin, hcard, hrealS⟩ := hNatS
    letI := hKf
    letI := hKfin
    obtain ⟨π, hrealS'⟩ := hrealS
    have hrealI : (FFModel.nat (StatedSp 2 K)).Realizes L I ⊥ :=
      Thm14_5.realizes_of_autSub hLI (faithful_of_mem_irrSet hI hfix hsimple)
        ⟨π, hrealS'⟩
    obtain ⟨πI, hπI⟩ := hrealI
    have hNatI : NatSpn L I ⊥ 4 n := ⟨hm4, K, hKf, hKfin, hcard, ⟨πI, hπI⟩⟩
    have hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV :=
      Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
    obtain ⟨g, hgY, hisoIg⟩ :=
      exists_secIsoOn_of_mem_irrSet_of_basic hW hO2 hB hL hfixH hsum hI (hsIrr hJs)
    have hNY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).mp hLn
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := hNY hgY
    have ht : ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun l hl =>
      (Subgroup.mem_normalizer_iff.mp hgN l).mp hl
    have ht' : ∀ l ∈ L, g⁻¹ * l * g ∈ L := fun l hl =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) l).mp hl
    have hNatIg : NatSpn L (I.map g.toMonoidHom) ⊥ 4 n := natSpn_map_conj hNatI ht ht'
    have hIginv : XMod.IsInv ↥L (I.map g.toMonoidHom) := by
      intro a x hx
      obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hx
      have hai : g⁻¹ * (a : MulAut W) * g ∈ L := ht' a a.2
      have hmem : (g⁻¹ * (a : MulAut W) * g) i ∈ I := hIirr.2.1 _ hai i hi
      have heq : g.toMonoidHom ((g⁻¹ * (a : MulAut W) * g) i) = a • g.toMonoidHom i := by
        change g ((g⁻¹ * (a : MulAut W) * g) i) = (a : MulAut W) (g.toMonoidHom i)
        simp [MulAut.mul_apply]
      rw [← heq]
      exact Subgroup.mem_map_of_mem g.toMonoidHom hmem
    have hJinv : XMod.IsInv ↥L J := (isIrrOn_bot_iff_isIrr.mp hJirr).1
    have hNatJ : NatSpn L J ⊥ 4 n := natSpn_of_secIsoOn hNatIg hisoIg hIginv hJinv
    by_cases hisoIJ : SecIsoOn L I ⊥ J ⊥
    ·
      let Jfun : Fin 2 → Subgroup W := ![I, J]
      have hisoJ : ∀ i, SecIsoOn L I ⊥ (Jfun i) ⊥ := by
        intro i
        fin_cases i
        · simpa [Jfun] using secIsoOn_refl hIirr.2.1 hIirr.2.2.1 bot_le
        · simpa [Jfun] using hisoIJ
      have hind : iSupIndep Jfun := by
        rw [CFSG.Quasithin.iSupIndep_fin_two_iff]
        simpa [Jfun] using (disjoint_iff.mpr hdisj)
      have htopsup : ⨆ i, Jfun i = ⊤ := by
        rw [CFSG.Quasithin.iSup_fin_two_eq]
        simpa [Jfun] using hsupIJ
      have hsum := sumOfNatVia_of_secIsoOn hπI Jfun hisoJ hind htopsup
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨hSp, ⟨K, hKf, hKfin, πI, hcard, hsum⟩⟩))))))))
    ·
      have h3 := hTwo W hW Y L n I J hL.1 hLn hSp hodd hn hNatI hNatJ hdisj hsupIJ hisoIJ
      omega


theorem concl146_of_caseI_G2
    (hb : W4Lem4_17Sp4G2N) (hMod : K146ModG2)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {n : ℕ} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : L = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    (hG2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsG2 ↥L n) (hodd : Odd n)
    (hn : 1 < n) (hfix : fixV L = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ max (bParam L Y) n + 2) : Sec18Concl Y L L n := by
  classical
  have hn3 : 3 ≤ n := by
    rcases hodd with ⟨k, hk⟩
    omega
  have hLn : (L.subgroupOf Y).Normal :=
    (Thm14_5.iSup_map_conj_eq_self_iff hL.1).mp hX.symm
  have hsimple : IsSimpleGroup ↥L :=
    CFSG.LocalAnalysis.EvenBN.G2.isSimpleGroup_of_lieModel_G2 hG2
  have hbY : bParam L Y ≤ 2 * n :=
    bParam_le_two_mul hb hW hO2 hL hLn hfix hodd hn (Or.inr hG2)
  have hYle : E3.mParam Y ≤ 2 * n + 2 := by
    have hmax : max (bParam L Y) n ≤ 2 * n := max_le hbY (by omega)
    omega
  have hd : E3.mParam Y < dMinDeg ↥L := by
    have h6 := (dMinDeg_lower_bounds (L := ↥L)).2.2.2.1 hG2 hn
    omega
  have hnL2 : ∀ e : ℕ, ¬ CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥L e := by
    intro e he
    exact not_isL2_of_shape (Or.inr (Or.inr (Or.inl hG2))) he
  obtain ⟨hsum0, I, hI, hIm⟩ :=
    case2_of_fix_of_lt_dMinDeg hW hO2 hB hL hX hfix hd hnL2
  obtain ⟨hLN, hnorm, hirr, hrkI, hmul, hmN⟩ :=
    setup_of_case2 hW hL hX hfix hsum0 hI hIm
  obtain ⟨s, hIs, hsIrr, hsind, hssup, hrkW⟩ :=
    exists_irrSet_decomposition hW hO2 hB hL hX hfix hsum0 hI
  have hG2S : CFSG.LocalAnalysis.UniquenessCase.UC22.IsG2 ↥(autSub L I) n :=
    lieModel_autSub hL hX hfix hsum0 hsimple hI hG2
  obtain ⟨-, hNm⟩ := hMod ↥I (fun u => Subtype.ext (hW (u : W))) (autSub Y I) (autSub L I) n
    (autSub_mono hL.1 I) hnorm hG2S hodd hn hirr (by omega)
  have hIne : I ≠ ⊥ := CFSG.LocalAnalysis.WeakClosure81.ne_bot_of_mem_irrSet hI
  have hrkIpos : 0 < rk ↥I := by
    rcases Nat.eq_zero_or_pos (rk ↥I) with h0 | h0
    · exact absurd ((rk_eq_zero_iff hW).mp h0) hIne
    · exact h0
  have hkey : 2 * n * rk ↥(commV L) ≤ (2 * n + 2) * rk ↥I := by
    calc 2 * n * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
          Nat.mul_le_mul_right _ hNm
      _ ≤ E3.mParam Y * rk ↥I := hmul
      _ ≤ (2 * n + 2) * rk ↥I := Nat.mul_le_mul_right _ hYle
  have hns : 2 * n * s.ncard ≤ 2 * n + 2 := by
    have h := hkey
    rw [hrkW] at h
    have h2 : (2 * n * s.ncard) * rk ↥I ≤ (2 * n + 2) * rk ↥I := by
      rw [Nat.mul_assoc]
      exact h
    exact Nat.le_of_mul_le_mul_right h2 hrkIpos
  have hspos : 0 < s.ncard := (Set.ncard_pos (Set.toFinite s)).2 ⟨I, hIs⟩
  have hs1 : s.ncard ≤ 1 := by
    by_contra h
    push Not at h
    have h4 : 2 * n * 2 ≤ 2 * n * s.ncard := Nat.mul_le_mul_left _ h
    omega
  have hs1' : s.ncard = 1 := by omega
  obtain ⟨J, hsJ⟩ := Set.ncard_eq_one.mp hs1'
  have hIJ : I = J := by
    have : I ∈ ({J} : Set (Subgroup W)) := by rwa [← hsJ]
    simpa using this
  have hJtop : J = ⊤ := by
    have h := hssup
    rw [hsJ] at h
    simpa using h
  have hItop : I = ⊤ := by rw [hIJ, hJtop]
  have hirrTop : IsIrrOn L ⊤ ⊥ := by
    have h := hI.2
    rw [hItop] at h
    simpa [hfix] using h
  have hNatL : G2Natural L ⊤ ⊥ n :=
    (hMod W hW Y L n hL.1 hLn hG2 hodd hn hirrTop hYle).1
  exact Or.inr (Or.inl ⟨hG2, by simpa [hfix] using hNatL⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
