module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkF
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5One
public import CFSG.Quasithin.Vol2.Ch10SecB3CBor
public import CFSG.Quasithin.Vol2.Ch10SecQ3CJ
public import CFSG.Quasithin.Vol2.Ch10SecQ3CL
public import CFSG.Quasithin.Vol2.Ch10SecQ3CM
public import CFSG.Quasithin.Vol2.Ch10SecQ3CN
public import CFSG.Quasithin.Vol2.Ch10SecQ4S9

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_natData_K
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (he23 : E2.E23Statement) (h1021 : Ch10.Stmt10_2_1)
    (h331 : Stmt3_3_1) (hyp : Ch10.Hyp10 G T L I) {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (hZH' : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (H : Set G) = ⊥)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    {b : G} (hbK : b ∈ K) (hbS : b ∈ Subgroup.normalizer (baum T : Set G))
    (hbo : orderOf b = 2 ^ n - 1)
    (hbD : ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (Ch10.B0 T L) ∧ b ∈ D) :
    ∃ V : Subgroup G, NatData K V n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := h1.1
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hn3 : ¬ Ch10.Case10_1_1Three T L I := fun h3 =>
    (bender_of_cases (Or.inl ⟨n, h1⟩)).2 h3.1
  obtain ⟨hel, hc⟩ := SecF.C10E4.e23Concl_H he23 h1021 h331 hyp hH hZH hn3
  obtain ⟨-, hWO, hO⟩ := SecF.C10P4F.vz_facts h331 hyp hH
  set W := VZ T H with hWdef
  have hHN : H ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ H
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨h2J', I', hD⟩ := e23Data_of_concl hc
  have h2J : oTwoUpper H ≤ thompsonJ H := SecE.twoResidual_eq_oTwoUpper H ▸ h2J'
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ ∈ I' :=
    Finset.card_pos.mp (by rcases hD.card with h | h <;> omega)
  have hbodd : Odd (orderOf b) := by
    rw [hbo]
    exact Nat.Even.sub_odd (by omega) ((by decide : Even 2).pow_of_ne_zero (by omega)) odd_one
  have hbH : b ∈ H := hKH hbK
  have hbW : b ∈ Subgroup.normalizer (W : Set G) := hHN hbH
  have hbR : b ∈ twoResidual H := by
    rw [SecE.twoResidual_eq_oTwoUpper]
    exact mem_oTwoUpper_of_odd hbH hbodd
  have hbZ : b ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro hbZ
    obtain ⟨D, hD', hbD'⟩ := hbD
    have hb1 : b ∈ D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := ⟨hbD', hbZ⟩
    rw [SecA.inf_centralizer_eq_bot_of_case_one h37 h38 h322 hyp h1 hD', Subgroup.mem_bot] at hb1
    rw [hb1, orderOf_one] at hbo
    omega
  set φb := convI hel ⟨b, hbW⟩ with hφb
  have hφb1 : φb ≠ 1 := by
    intro h
    apply hbZ
    have h1 := (convI_eq_one_iff hel _).mp h
    exact Subgroup.centralizer_le (le_conjClosure _ H) h1
  have hφbo : Odd (orderOf φb) := by
    refine hbodd.of_dvd_nat ((orderOf_map_dvd (convI hel) _).trans ?_)
    rw [Subgroup.orderOf_mk]
  have hKW : ¬ K ≤ Subgroup.centralizer (W : Set G) := fun h =>
    hZH (commutator_eq_bot_of_le_centralizer hHK h)
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hKJ : K ≤ thompsonJ H := by
    have h1 := oTwoUpper_mono hKH
    rw [← eq_oTwoUpper_of_perfect hKperf] at h1
    exact h1.trans h2J
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKperf]
  have hAperf : ⁅autI hel K, autI hel K⁆ = autI hel K := by
    rw [← range_convK hel (hKH.trans hHN), MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      hKtop]
  have hAne : autI hel K ≠ ⊥ := fun h => hKW ((autI_eq_bot_iff hel (hKH.trans hHN)).mp h)
  obtain ⟨j, hj, hj2⟩ : ∃ j : ℕ,
      E2.IsL2Natural K₀ (fixV (autI hel (twoResidual H))) j ∧ 2 ≤ j := by
    rcases hD.types K₀ hK₀ with ⟨j, hj⟩ | h5
    · rcases Nat.lt_or_ge j 2 with hj1 | hj2
      · exfalso
        have hj1' : j = 1 := by have := hj.1; omega
        subst hj1'
        have hsol : ∀ L' ∈ I', Group.IsSolvable ↥L' := by
          intro L' hL'
          obtain ⟨t, -, ht⟩ := hD.trans K₀ hK₀ L' hL'
          rw [← ht]
          exact isSolvable_conjAut (isSolvable_of_isL2Natural_one hj) t
        have hS := isSolvable_iSup hD.card hsol hD.comm
        rw [← hD.jeq] at hS
        exact hAne (eq_bot_of_perfect_of_le hS (autI_mono hel hKJ) hAperf)
      · exact ⟨j, hj, hj2⟩
    · exfalso
      have hall := isA5Module_of_isA5Module hD hK₀ h5
      obtain ⟨h3a, -, h3c⟩ := hD.three hall
      have hJ : φb ∈ ⨆ L ∈ I', L := by
        rw [← hD.jeq]
        exact convI_mem_autI hel (h2J' hbR) hbW
      apply hφb1
      refine eq_one_of_A5_components hD.card hD.comm hD.indep h3c hJ hφbo ?_
      intro x hx
      rw [← h3a] at hx ⊢
      exact conj_mem_autI hel hbS hx
  obtain ⟨hCs, hnc, -⟩ := exists_sl2_of_component (Or.inl ⟨hj, hj2⟩)
  obtain ⟨t, ht, hle⟩ := exists_le_autI_map' hel hHN hyp.fsu.sylow.1 hKc hHK h2J hD.jeq hD.comm
    hK₀ hCs hnc
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H :=
    H13.LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer (hTH ht))
  have hK'H : K' ≤ H := le_of_mem_cComp hK'c
  have hJN : autI hel (thompsonJ H) ≤ Subgroup.normalizer (oTwoUpper K₀ : Set _) := by
    rw [hD.jeq]
    refine iSup₂_le fun L' hL' => ?_
    refine le_trans ?_ (SecF.C10P4F.le_normalizer_oTwoUpper K₀)
    by_cases h : L' = K₀
    · rw [h]; exact Subgroup.le_normalizer
    · exact SecE.le_normalizer_of_commute fun a ha b hb => hD.comm L' hL' K₀ hK₀ h a ha b hb
  have hK'J : K' ≤ thompsonJ H := by
    have h1 := oTwoUpper_mono hK'H
    rw [← eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hK'c)] at h1
    exact h1.trans h2J
  have hAtN := (autI_mono hel hK'J).trans hJN
  obtain ⟨Fn, _, _, hFn, ⟨eK⟩⟩ := hKF
  have eK' : ↥K' ⧸ CFSG.pCore 2 ↥K' ≃* Matrix.SpecialLinearGroup (Fin 2) Fn :=
    (C10P34.conjQuot K K' t rfl).symm.trans eK
  have hK'q : CFSG.Open.IsQuasisimple (↥K' ⧸ CFSG.Open.pCore 2 ↥K') := by
    have hq := Ch11.SecA.isQuasisimple_of_mulEquiv_SL2 hn hFn
      ((QuotientGroup.quotientMulEquivOfEq (Lin2.openPCore_eq_pCore 2 ↥K')).trans eK')
    exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hOK' : pCoreOf 2 K' ≤ Subgroup.centralizer (W : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
      (subnormal_of_mem_cComp hK'c)).trans hO
  have heq : oTwoUpper K₀ = autI hel K' :=
    eq_autI_of_normal hel (hK'H.trans hHN) hK'q hOK' hle hAtN hnc
  have hK₀eq : oTwoUpper K₀ = K₀ := by
    obtain ⟨-, F₀, _, _, hF₀, e₀, -⟩ := hj
    have h4' := Ch11.SecA.exists_finset_card_four (K := F₀) hj2
      (by rw [Nat.card_eq_fintype_card, hF₀])
    have := CFSG.LinearGroups.special_linear_isPerfect (K := F₀) (n := 2) le_rfl (Or.inr h4')
    have hp : Group.IsPerfect ↥K₀ :=
      Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
    exact (eq_oTwoUpper_of_perfect (Subgroup.isPerfect_iff.mp hp)).symm
  have hKR : K ≤ twoResidual H := by
    rw [SecE.twoResidual_eq_oTwoUpper, eq_oTwoUpper_of_perfect hKperf]
    exact oTwoUpper_mono hKH
  have hC : fixV (autI hel (twoResidual H)) = ⊥ := by
    have hRN : twoResidual H ≤ Subgroup.normalizer (W : Set G) := (twoResidual_le H).trans hHN
    set C' := W ⊓ Subgroup.centralizer (twoResidual H : Set G) with hC'
    have hTsyl : IsSylowTwoOf T H :=
      ⟨hTH, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow hTH⟩
    have hWT : W ≤ T := hWO.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
    have hC'T : C' ≤ T := inf_le_left.trans hWT
    have hTC' : T ≤ Subgroup.normalizer (C' : Set G) := by
      intro x hx
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hHN (hTH hx), ?_⟩
      have hxR : x ∈ Subgroup.normalizer (twoResidual H : Set G) := by
        rw [SecE.twoResidual_eq_oTwoUpper]
        exact le_normalizer_oTwoUpper H (hTH hx)
      exact SecA.le_normalizer_centralizer (X := Subgroup.normalizer (twoResidual H : Set G))
        le_rfl hxR
    have hC'1 : C' = ⊥ := by
      by_contra hne
      obtain ⟨v, hv, hv1, hvT⟩ :=
        SecA.exists_ne_one_mem_centralizer hyp.fsu.sylow.1 hC'T hTC' hne
      have hv2 : v ^ 2 = 1 := hel.2 v hv.1
      have hvZ : v ∈ quasithinOmegaOneCenter T :=
        Subgroup.subset_closure ⟨⟨hC'T hv, hvT⟩, hv2⟩
      have hle : H ≤ Subgroup.centralizer ({v} : Set G) := by
        rw [hHK]
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hv.2 x (hKR hx)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hvT x hx
      have hvH : v ∈ Subgroup.centralizer (H : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
      have : v ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (H : Set G) := ⟨hvZ, hvH⟩
      rw [hZH', Subgroup.mem_bot] at this
      exact hv1 this
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    have h2 : c.val ∈ C' := ⟨c.val_mem, (mem_fixV_autI hel hRN c).mp hc⟩
    rw [hC'1, Subgroup.mem_bot] at h2
    exact IntMod.val_injective h2
  have hWs : Group.IsSolvable ↥W := Group.isSolvable_of_comm fun a b => hel.1.is_comm.comm a b
  have hWK' : W ≤ Subgroup.normalizer (K' : Set G) := by
    have h1 := (cComp_commutator_perfectCore hK'c (hWO.trans (C1.blockQ_le H)) hWs
      (hK'H.trans hHN)).1
    rw [Subgroup.commutator_comm] at h1
    exact Subgroup.le_normalizer_iff_commutator_le_right.mpr h1
  have hnd := natData_of_autI hel (hK'H.trans hHN) hWK' hOK' (heq.symm.trans hK₀eq)
    (C := fixV (autI hel (twoResidual H))) (by rw [hC, inf_bot_eq]) hj2 hn hj
    ⟨Fn, inferInstance, inferInstance, hFn, ⟨eK'⟩⟩
  have hKK : K'.map (MulAut.conj t⁻¹).toMonoidHom = K := by
    rw [hK', Subgroup.map_map]
    convert Subgroup.map_id K
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨⁅W, K'⁆.map (MulAut.conj t⁻¹).toMonoidHom, ?_⟩
  have := hnd.map_equiv (MulAut.conj t⁻¹)
  rwa [hKK] at this

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
