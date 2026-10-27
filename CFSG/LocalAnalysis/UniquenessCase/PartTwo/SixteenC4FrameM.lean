module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16NormIdx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

section Frame

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16_C4FrameM_commSp_top {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) (hnorm : ∀ c : K, σ c * c = c ^ 3)
    (hcard : Nat.card K = 4) :
    commSp (⊤ : Subgroup (SUid σ 4)) = ⊤ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = 4 := by rwa [Nat.card_eq_fintype_card] at hcard
  have hc1 : (1 : K) + σ (1 : K) = 0 := by
    rw [map_one, one_add_one_eq_two]
    exact h2
  have hsing : ∀ a : Fin 4 → K, herm σ a a = 0 → a ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
    intro a ha
    by_cases hzero : a = 0
    · subst hzero
      exact Submodule.zero_mem _
    · have hex : ∃ i, a i ≠ 0 := by
        by_contra h
        apply hzero
        ext j
        exact not_not.mp (not_exists.mp h j)
      obtain ⟨i, hi⟩ := hex
      set x : Fin 4 → K := (σ (a i))⁻¹ • Pi.single i (1 : K)
      have hx : herm σ a x = 1 := by
        rw [herm_smul_right, herm_single_right, mul_one,
          inv_mul_cancel₀ ((map_ne_zero σ).mpr hi)]
      have hmem : tv hσ.invol ha hc1 • x - x ∈ commSp (⊤ : Subgroup (SUid σ 4)) :=
        sub_mem_commSp (Subgroup.mem_top _) x
      rw [tv_smul hσ.invol ha hc1 x, hx] at hmem
      simpa using hmem
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1} : Finset K)) (t := Finset.univ)
      (by rw [Finset.card_univ, hcard']; simp)
    exact ⟨ω, by rintro rfl; exact hω (by simp), by rintro rfl; exact hω (by simp)⟩
  have hω3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hcard'] at this
  have hs1 : herm σ (Pi.single (0 : Fin 4) (1 : K) + Pi.single (1 : Fin 4) (1 : K))
      (Pi.single (0 : Fin 4) (1 : K) + Pi.single (1 : Fin 4) (1 : K)) = 0 := by
    rw [herm_single_add_single (by decide : (0 : Fin 4) ≠ 1) (1 : K)]
    simpa using hc1
  have hs2 : herm σ (Pi.single (0 : Fin 4) (1 : K) + Pi.single (1 : Fin 4) ω)
      (Pi.single (0 : Fin 4) (1 : K) + Pi.single (1 : Fin 4) ω) = 0 := by
    rw [herm_single_add_single (by decide : (0 : Fin 4) ≠ 1) ω, hnorm ω, hω3]
    simpa using hc1
  have hs3 : herm σ (Pi.single (2 : Fin 4) (1 : K) + Pi.single (3 : Fin 4) (1 : K))
      (Pi.single (2 : Fin 4) (1 : K) + Pi.single (3 : Fin 4) (1 : K)) = 0 := by
    rw [herm_single_add_single (by decide : (2 : Fin 4) ≠ 3) (1 : K)]
    simpa using hc1
  have hs4 : herm σ (Pi.single (2 : Fin 4) (1 : K) + Pi.single (3 : Fin 4) ω)
      (Pi.single (2 : Fin 4) (1 : K) + Pi.single (3 : Fin 4) ω) = 0 := by
    rw [herm_single_add_single (by decide : (2 : Fin 4) ≠ 3) ω, hnorm ω, hω3]
    simpa using hc1
  have ha1 := hsing _ hs1
  have ha2 := hsing _ hs2
  have ha3 := hsing _ hs3
  have ha4 := hsing _ hs4
  have hb1 : Pi.single (1 : Fin 4) (1 : K) ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
    have hsub : Pi.single (1 : Fin 4) (ω - 1) ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
      have h := Submodule.sub_mem _ ha2 ha1
      simpa [Pi.single_sub] using h
    have hsub' : (ω - 1) • Pi.single (1 : Fin 4) (1 : K) ∈
        commSp (⊤ : Subgroup (SUid σ 4)) := by
      rw [← Pi.single_smul]
      simpa using hsub
    have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
    have h := Submodule.smul_mem _ (ω - 1)⁻¹ hsub'
    simpa [smul_smul, inv_mul_cancel₀ hne] using h
  have hb3 : Pi.single (3 : Fin 4) (1 : K) ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
    have hsub : Pi.single (3 : Fin 4) (ω - 1) ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
      have h := Submodule.sub_mem _ ha4 ha3
      simpa [Pi.single_sub] using h
    have hsub' : (ω - 1) • Pi.single (3 : Fin 4) (1 : K) ∈
        commSp (⊤ : Subgroup (SUid σ 4)) := by
      rw [← Pi.single_smul]
      simpa using hsub
    have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
    have h := Submodule.smul_mem _ (ω - 1)⁻¹ hsub'
    simpa [smul_smul, inv_mul_cancel₀ hne] using h
  have hb0 : Pi.single (0 : Fin 4) (1 : K) ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
    have h := Submodule.sub_mem _ ha1 (Submodule.smul_mem _ (1 : K) hb1)
    simpa using h
  have hb2 : Pi.single (2 : Fin 4) (1 : K) ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
    have h := Submodule.sub_mem _ ha3 (Submodule.smul_mem _ (1 : K) hb3)
    simpa using h
  have hbase : ∀ i : Fin 4, Pi.single i (1 : K) ∈ commSp (⊤ : Subgroup (SUid σ 4)) := by
    intro i
    fin_cases i
    · exact hb0
    · exact hb1
    · exact hb2
    · exact hb3
  rw [Submodule.eq_top_iff']
  intro x
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hx : Pi.single i (x i) = (x i) • Pi.single i (1 : K) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hx]
  exact Submodule.smul_mem _ _ (hbase i)

theorem lBar_le_Mbar (hS : Sect16 D V₀ V L hV) :
    lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
  unfold lBar Mbar
  exact barSub_mono V₀ V hV hS.setting.hyp151.le

theorem UFrame.card_V (F : UFrame V₀ V hV L) (hS : Sect16 D V₀ V L hV) :
    Nat.card V = 2 ^ 8 * Nat.card V₀ := by
  have hle : V₀ ≤ V := hS.setting.hyp16.hyp125.pairFacts.le
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (modNull V₀ V hV)
  have h1 : Nat.card V = Nat.card (Vtil V₀ V hV) * Nat.card (modNull V₀ V hV) := hq
  have h2 : Nat.card (modNull V₀ V hV) = Nat.card V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, F.card_Vtil, h2]

theorem UFrame.mSub_V (F : UFrame V₀ V hV L) (hS : Sect16 D V₀ V L hV) :
    mSub V = 8 + mSub V₀ := by
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hV02 : IsPGroup 2 V₀ := hS.setting.hyp16.hyp125.pairFacts.elemAbelian₀.isPGroup
  have hcardV : Nat.card V = 2 ^ mSub V := card_eq_two_pow_mSub hV2
  have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV02
  have h := F.card_V hS
  rw [hcardV, hcardV0, ← pow_add] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h

theorem UFrame.wTil_eq_top (F : UFrame V₀ V hV L) :
    wTil V₀ V hV L = ⊤ := by
  have hwt : wTil V₀ V hV L = commV (lBar V₀ V hV L) := by
    rw [wTil, lBar, ← commV_eq_commSub]
  rw [hwt]
  refine eq_top_iff.2 fun w _ => ?_
  rw [F.mem_commV_iff_commSp (le_refl _) w]
  have hsu : F.suSub (lBar V₀ V hV L) = ⊤ := by
    simp [UFrame.suSub]
  rw [hsu, s16_C4FrameM_commSp_top F.isUnitary F.two_eq_zero F.norm_eq F.card_K]
  trivial

theorem UFrame.Mbar_le_normalizer (F : UFrame V₀ V hV L) (hS : Sect16 D V₀ V L hV) :
    Mbar D.M V₀ V hV ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  intro φ hφ
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  by_contra hnot
  have hgn : (g : G) ∉ nBar D.M V₀ V hV L := by
    intro h
    apply hnot
    obtain ⟨-, h2, h3⟩ := (mem_preBarSub D.M V₀ V hV _).1 (by rw [← nBar]; exact h)
    rwa [show (⟨(g : G), h2⟩ : ↥(stabTil V₀ V)) = g from Subtype.ext rfl, hgφ] at h3
  have hcomm := (hS.setting.hyp151.commute (g : G) hgM hgn).2
  rw [F.wTil_eq_top] at hcomm
  have hbot : barSub V₀ V hV (conjSubgroup L (g : G)) = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun w => ?_
    exact (commSub_eq_bot_iff.mp hcomm) (Subgroup.mem_top w) x hx
  have hLstab : L ≤ stabTil V₀ V :=
    hS.setting.hyp151.le.trans
      (le_stabTil hS.setting.hyp16.hyp125.pairFacts.le_normalizer
        hS.setting.hyp16.hyp125.pairFacts.le_normalizer₀)
  have hginv : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem g.2
  have hne : barSub V₀ V hV (conjSubgroup L (g : G)) ≠ ⊥ := by
    rw [show conjSubgroup L (g : G) = L.map (MulAut.conj (g : G)⁻¹).toMonoidHom from rfl,
      TwelveTwentyThree.barSub_map_conj (V₀ := V₀) (V := V) hV hLstab hginv]
    intro hz
    exact hS.ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective (barSub V₀ V hV L)
        (MulEquiv.injective (MulAut.conj (actTil V₀ V hV ⟨(g : G)⁻¹, hginv⟩)))).1 hz)
  exact hne hbot

theorem UFrame.rho_semilinear (F : UFrame V₀ V hV L) (hS : Sect16 D V₀ V L hV)
    {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar D.M V₀ V hV) :
    ∃ θ : F.K →+* F.K, ∀ (c : F.K) (x : Fin 4 → F.K), F.rho φ (c • x) = θ c • F.rho φ x := by
  have hK : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  refine exists_semilinear_statedSU hK (F.rho φ) ?_
  intro g hg
  have hgSU : g ∈ SUid F.σ 4 := by rw [F.suid_eq_statedSU]; exact hg
  let γ : ↥(SUid F.σ 4) := ⟨g, hgSU⟩
  have hφN : φ ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    F.Mbar_le_normalizer hS hφ
  have hφinvN : φ⁻¹ ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (normalizer _).inv_mem hφN
  have hmem : φ⁻¹ * (F.π γ) * φ ∈ lBar V₀ V hV L := by
    have h := (Subgroup.mem_set_normalizer_iff.1 hφinvN (F.π γ)).1 (F.π γ).2
    simpa using h
  let γ' : ↥(SUid F.σ 4) := F.π.symm ⟨φ⁻¹ * (F.π γ) * φ, hmem⟩
  have hπγ' : (F.π γ' : MulAut (Vtil V₀ V hV)) =
      φ⁻¹ * (F.π γ : MulAut (Vtil V₀ V hV)) * φ := by
    simp [γ']
  refine ⟨(γ' : GL (Fin 4) F.K), ?_, ?_⟩
  · rw [← F.suid_eq_statedSU]
    exact γ'.2
  · intro x
    have hsymm : ∀ y : Fin 4 → F.K, (F.rho φ).symm y = F.vec (φ⁻¹ (F.ofVec y)) := by
      intro y
      apply (F.rho φ).injective
      rw [AddEquiv.apply_symm_apply, F.rho_vec]
      simp
    rw [hsymm, hsymm]
    have hx1 : F.ofVec (g *ᵥ x) =
        (F.π γ : MulAut (Vtil V₀ V hV)) (F.ofVec x) := by
      apply F.vec_injective
      rw [F.vec_ofVec, F.vec_action, CFSG.ClassicalGroups.Unitary.smul_def]
      simp [γ]
    rw [hx1, ← CFSG.ClassicalGroups.Unitary.smul_def,
      ← F.vec_action γ' (φ⁻¹ (F.ofVec x)), hπγ']
    simp [MulAut.mul_apply]

theorem UFrame.mBarGT_one (F : UFrame V₀ V hV L) (hS : Sect16 D V₀ V L hV) :
    MBarGT D.M V₀ V 1 := by
  have hp := hS.setting.hyp16.hyp125.pairFacts
  have hstab : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hmod : Nat.card (modNull V₀ V hV) = Nat.card V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hp.le).toEquiv
  refine ⟨?_, ?_⟩
  · intro m hmM hnot hsquare
    have hms : m ∈ stabTil V₀ V := hstab hmM
    let φ : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨m, hms⟩
    have hφ : φ ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV hmM hms
    have hφne : φ ≠ 1 := by
      intro h1
      exact hnot ((actTil_eq_one_iff V₀ V hV ⟨m, hms⟩).1 h1)
    have hne : ∃ x, F.rho φ x ≠ x := by
      by_contra h
      apply hφne
      refine MulEquiv.ext fun w => ?_
      have hw : F.rho φ (F.vec w) = F.vec w :=
        not_not.mp ((not_exists.mp h) (F.vec w))
      rw [F.rho_vec] at hw
      exact F.vec_injective hw
    obtain ⟨θ, hθ⟩ := F.rho_semilinear hS hφ
    have hfix := card_fix_mul_le (F := F.K) (θ := θ) (F.rho φ) hθ hne
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, F.card_K] at hfix
    norm_num at hfix
    have hcent : (centMod V₀ V m : Set G) =
        (preTil V₀ V hV (fixV (Subgroup.zpowers φ)) : Set G) := by
      ext v
      constructor
      · rintro ⟨hv, hv0⟩
        change v ∈ preTil V₀ V hV (fixV (Subgroup.zpowers φ))
        rw [mem_preTil_iff_of_mem V₀ V hV _ hv, mem_fixV_zpowers]
        change actTil V₀ V hV ⟨m, hms⟩ (mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩)
        rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
        simpa [IntMod.mk, IntMod.val, mul_assoc] using hv0
      · intro h
        have hv : v ∈ V := preTil_le V₀ V hV _ h
        refine ⟨hv, ?_⟩
        have h' : v ∈ preTil V₀ V hV (fixV (Subgroup.zpowers φ)) := h
        rw [mem_preTil_iff_of_mem V₀ V hV _ hv, mem_fixV_zpowers] at h'
        change actTil V₀ V hV ⟨m, hms⟩ (mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) at h'
        rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h'
        simpa [IntMod.mk, IntMod.val, mul_assoc] using h'
    have hfixcard : Nat.card (fixV (Subgroup.zpowers φ)) =
        Nat.card {x : Fin 4 → F.K // F.rho φ x = x} := by
      let e : Vtil V₀ V hV ≃ (Fin 4 → F.K) :=
        Equiv.ofBijective F.vec ⟨F.vec_injective, fun x => ⟨F.ofVec x, F.vec_ofVec x⟩⟩
      refine Nat.card_congr (Equiv.subtypeEquiv e ?_)
      intro w
      show w ∈ fixV (Subgroup.zpowers φ) ↔ F.rho φ (F.vec w) = F.vec w
      rw [mem_fixV_zpowers, F.rho_vec, F.vec_injective.eq_iff]
    have hcentcard : Nat.card (centMod V₀ V m) =
        Nat.card V₀ * Nat.card (fixV (Subgroup.zpowers φ)) := by
      rw [hcent]
      change Nat.card (preTil V₀ V hV (fixV (Subgroup.zpowers φ))) =
        Nat.card V₀ * Nat.card (fixV (Subgroup.zpowers φ))
      unfold preTil
      rw [Subgroup.card_map_of_injective (IntMod.val_injective (hV := hV))]
      have hpre : Nat.card ((fixV (Subgroup.zpowers φ)).comap (mkTil V₀ V hV)) =
          Nat.card (modNull V₀ V hV) * Nat.card (fixV (Subgroup.zpowers φ)) := by
        have h := Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet
          (modNull V₀ V hV) ((fixV (Subgroup.zpowers φ)) : Set (Vtil V₀ V hV)))
        rw [Nat.card_prod] at h
        exact h
      rw [hpre, hmod]
    calc 2 ^ (1 + 1) * Nat.card (centMod V₀ V m)
        = Nat.card V₀ * (Nat.card (fixV (Subgroup.zpowers φ)) * 4) := by
          rw [hcentcard]; norm_num; ring
      _ ≤ Nat.card V₀ * 256 := by
          rw [hfixcard]
          exact Nat.mul_le_mul_left _ hfix
      _ = Nat.card V := by rw [F.card_V hS]; ring
  · intro _
    calc 2 ^ (1 + 1) * Nat.card V₀ = 4 * Nat.card V₀ := by norm_num
      _ ≤ 2 ^ 8 * Nat.card V₀ := by norm_num
      _ = Nat.card V := (F.card_V hS).symm

end Frame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
