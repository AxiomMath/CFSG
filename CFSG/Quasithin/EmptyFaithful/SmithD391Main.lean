module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Cent
public import CFSG.Quasithin.EmptyFaithful.SmithD391FF
public import CFSG.Quasithin.EmptyFaithful.SmithD391XW

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique
open scoped Pointwise

theorem d391Deep_of_inputs (h35 : D35) (hB51 : AsB51) (hA21 : AsA21SQTKSection) : D391Deep := by
  intro W _ _ M Mp T L V hMp
  subst Mp
  intro hD hqM hdeep A hA hAT hA3 hrA hAf
  by_contra htop
  let _i := qAct hD.hyp.Mp_normal
  have hexp := hD.hyp.exp
  have hq : CFSG.IsQuasisimple ↥L := hD.hyp.quasi
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hTM : T ≤ M := hD.hyp.sylow.1
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  obtain ⟨hLV, hVcomm, hVlt, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hlt : V < orbSup T V := d391_lt hdeep
  have hC := d391_cent hD
  obtain ⟨-, ⟨t, htT, htn⟩, hsplitW, h5⟩ := h35 W M L T L V hD hlt hC
  obtain ⟨hsplit, hsumW⟩ := hsplitW t htT htn
  have hZ := z35_of_d3Std hD hlt hC
  set VT := orbSup T V with hVT
  set C := VT ⊓ fixV L with hCdef
  have hG : L ⊔ T ≤ stabSub VT ⊓ stabSub C := n1_sup_le_stabSub_sec hD.hyp
  have hTG : T ≤ stabSub VT ⊓ stabSub C := le_sup_right.trans hG
  obtain ⟨htsT, hsplitX⟩ := split_autSec hTG htT hsplit
  obtain ⟨-, hsumX, hinfX, hnotX⟩ := z35_split_sum hZ htsT hsplitX
  have hXsq : ∀ x : Sec VT C, x ^ 2 = 1 := Bridge.sec_sq_eq_one hexp VT C
  set tM : ↥M := ⟨t, hTM htT⟩ with htM
  have hΛ := d391_Λ_normal hD
  have hirrQ := isIrr_tildeQ hD
  have hnotQ := not_iso_tildeQ hD hlt hC htT (hTM htT) htn
  have hgenQ := iSup_smul_tildeQ hD
  have hdichQ := iso_or_iso_tildeQ hD hlt hC h5 htT (hTM htT) htn
  have hQsq : ∀ q : W ⧸ modFix L (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
  have hsupQ := sup_isoSum_smul hΛ hgenQ hdichQ
  have hApg : IsPGroup 2 ↥(A.subgroupOf M) :=
    isPGroup_two_of_sq_eq_one fun x => Subtype.ext (Subtype.ext (by
      simpa using hA.2.2.2 _ x.2))
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, rk ↥(isoSum (L.subgroupOf M) (tilde L ⊤ V)) =
      k * rk ↥(tilde L ⊤ V) ∧ k * nB (A.subgroupOf M) (tilde L ⊤ V ⊔ tM • tilde L ⊤ V) ≤
        nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) := by
    by_cases hAV : A ≤ stabSub V
    · have hAV' : ∀ a ∈ A.subgroupOf M, a • tilde L ⊤ V = tilde L ⊤ V := by
        intro a ha
        rw [smul_tildeQ hD.hyp.Mp_normal]
        exact congrArg (tilde L ⊤) (mem_stabSub_iff_map_eq.1 (hAV ha))
      have hAtV : ∀ a ∈ A.subgroupOf M, a • tM • tilde L ⊤ V = tM • tilde L ⊤ V := by
        intro a ha
        rw [smul_tildeQ hD.hyp.Mp_normal tM, smul_tildeQ hD.hyp.Mp_normal]
        exact congrArg (tilde L ⊤) (mem_stabSub_iff_map_eq.1
          (mem_stabSub_map_of_split htT htn hsplit (hAT ha) (hAV ha)))
      exact count_nonswap hQsq hΛ hirrQ hnotQ hgenQ hdichQ hApg hAV' hAtV
    · obtain ⟨a₀, ha₀A, ha₀n⟩ : ∃ a₀ ∈ A, a₀ ∉ stabSub V := by
        by_contra hcon
        push Not at hcon
        exact hAV hcon
      have ht₀ : t⁻¹ * a₀ ∈ stabSub V := (hsplit a₀ (hAT ha₀A)).resolve_left ha₀n
      have hAc : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x :=
        fun x hx y hy => Subtype.ext (hA.2.2.1 _ hx _ hy)
      have ha₀2 : (⟨a₀, hA.1 ha₀A⟩ : ↥M) ^ 2 = 1 :=
        Subtype.ext (by simpa using hA.2.2.2 a₀ ha₀A)
      have hA₀A : (A ⊓ stabSub V).subgroupOf M ≤ A.subgroupOf M := fun x hx => hx.1
      have hsplitA : ∀ x ∈ A.subgroupOf M, x ∈ (A ⊓ stabSub V).subgroupOf M ∨
          (⟨a₀, hA.1 ha₀A⟩ : ↥M)⁻¹ * x ∈ (A ⊓ stabSub V).subgroupOf M := by
        intro x hx
        rcases hsplit _ (hAT hx) with h | h
        · exact Or.inl ⟨hx, h⟩
        · right
          refine ⟨A.mul_mem (A.inv_mem ha₀A) hx, ?_⟩
          have h1 := (stabSub V).mul_mem ((stabSub V).inv_mem ht₀) h
          have h2 : (t⁻¹ * a₀)⁻¹ * (t⁻¹ * M.subtype x) = a₀⁻¹ * M.subtype x := by group
          rw [h2] at h1
          exact h1
      have hA₀V : ∀ a ∈ (A ⊓ stabSub V).subgroupOf M, a • tilde L ⊤ V = tilde L ⊤ V := by
        intro a ha
        rw [smul_tildeQ hD.hyp.Mp_normal]
        exact congrArg (tilde L ⊤) (mem_stabSub_iff_map_eq.1 ha.2)
      have ha₀V : (⟨a₀, hA.1 ha₀A⟩ : ↥M) • tilde L ⊤ V = tM • tilde L ⊤ V := by
        rw [smul_tildeQ hD.hyp.Mp_normal, smul_tildeQ hD.hyp.Mp_normal]
        refine congrArg (tilde L ⊤) ?_
        show V.map a₀.toMonoidHom = V.map t.toMonoidHom
        rw [show a₀ = t * (t⁻¹ * a₀) by group, map_mul_aut', mem_stabSub_iff_map_eq.1 ht₀]
      exact count_swap hQsq hΛ hirrQ hnotQ hgenQ hdichQ hApg hAc ha₀A ha₀2 hA₀A hsplitA hA₀V
        ha₀V
  set π : W →* W ⧸ modFix L (⊤ : Subgroup W) := QuotientGroup.mk' (modFix L (⊤ : Subgroup W))
    with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w) := fun g w => rfl
  have hker : π.ker = fixV L := by
    rw [hπ, QuotientGroup.ker_mk']
    exact modFix_top_eq L
  have hAM : (A.subgroupOf M).map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hN1 : nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≤
      rkIdx (fixV A) := by
    have h1 := Z391.nB_top_le_rkIdx_fixV π hπsurj hπM (A.subgroupOf M)
    rwa [hAM] at h1
  have hrA0 : 0 < rk ↥A := hA.rk_pos
  have hN2 : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h := hrA
    unfold rAV at h
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA0
    rw [div_le_iff₀ hpos] at h
    exact_mod_cast h
  have hVTmap : VT.map π = tilde L ⊤ V ⊔ tM • tilde L ⊤ V := by
    have e1 : VT = V ⊔ V.map t.toMonoidHom ⊔ C := hsumW.1
    have e2 : C.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hker]
      exact inf_le_right
    have e3 : (V.map t.toMonoidHom).map π = tM • tilde L ⊤ V := by
      rw [smul_tildeQ hD.hyp.Mp_normal]
      rfl
    calc VT.map π = (V ⊔ V.map t.toMonoidHom ⊔ C).map π := by rw [← e1]
      _ = V.map π ⊔ (V.map t.toMonoidHom).map π ⊔ C.map π := by
          rw [Subgroup.map_sup, Subgroup.map_sup]
      _ = tilde L ⊤ V ⊔ tM • tilde L ⊤ V := by
          rw [e2, sup_bot_eq, e3]
          rfl
  have hGV : L ⊔ T ≤ stabSub VT := hG.trans inf_le_left
  have hGC : L ⊔ T ≤ stabSub C := hG.trans inf_le_right
  have hN : ∀ g ∈ L ⊔ T, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    hMn g ((sup_le hLM hTM) hg) l hl
  have hntV : ¬ L ≤ centSec VT C := by
    intro hLc
    have h1 : commSub VT L ≤ C := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact (hLc hx).2 w hw
    apply hVlt.ne
    refine le_antisymm inf_le_left fun v hv => ⟨hv, ?_⟩
    have h2 : v ∈ commSub VT L := by
      rw [← hVcomm] at hv
      exact commSub_mono (le_orbSup T V) le_rfl hv
    exact (h1 h2).2
  have hAG : A ≤ L ⊔ T := hAT.trans le_sup_right
  have hAVT : A ≤ stabSub VT := hAG.trans hGV
  have hAC : A ≤ stabSub C := hAG.trans hGC
  have hfA : A ⊓ centSec VT C = ⊥ :=
    Z391.inf_centSec_eq_bot hq le_sup_left hAG hN hGV hGC hntV hAf
  have hAsA2 := Z391.isA2_autSec (⟨hAG, hA.2.1, hA.2.2⟩ : IsA2 (L ⊔ T) A) hAVT hAC hfA
  have hAsT : autSec A VT C ≤ autSec T VT C := autSec_mono hAT VT C
  have hrkAs : rk ↥(autSec A VT C) = rk ↥A := B5.rk_autSec_eq hAVT hAC hfA
  have hNX : rkIdx (fixV (autSec A VT C)) ≤
      nB (A.subgroupOf M) (tilde L ⊤ V ⊔ tM • tilde L ⊤ V) := by
    have h2 := Z391.rkIdx_fixV_autSec_le_nB π hπM (A.subgroupOf M) VT
    rw [hAM, hker, hVTmap] at h2
    exact h2
  have hrkV : 0 < rk ↥(tilde L ⊤ V) := by
    by_contra h0
    exact hirrQ.2.1.ne' ((rk_eq_zero_iff hQsq).1 (by omega))
  have hcommV : commV L = ⊤ := Z391.commV_eq_top hMn hVcomm hD.hyp.gen
  have hk2le : 2 ≤ k := by
    by_contra hk
    have hQ₁ : isoSum (L.subgroupOf M) (tilde L ⊤ V) = tilde L ⊤ V := by
      symm
      refine Subgroup.eq_of_le_of_card_ge self_le_isoSum ?_
      rw [card_eq_two_pow hQsq, card_eq_two_pow hQsq, hk1]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have htopQ : VT.map π = ⊤ := by
      rw [hVTmap, ← hsupQ, hQ₁]
    have h1 : VT ⊔ fixV L = ⊤ := by
      have h2 := congrArg (Subgroup.comap π) htopQ
      rwa [Subgroup.comap_map_eq, Subgroup.comap_top, hker] at h2
    apply htop
    rw [eq_top_iff, ← hcommV, commV_eq_commSub, ← h1, commSub_sup_fixV le_rfl]
    exact commSub_le_of_invariant fun x hx w hw =>
      (hGV ((le_sup_left : L ≤ L ⊔ T) hx) w).2 hw
  have hFF : IsFFModule (autSec L VT C ⊔ autSec T VT C) := by
    refine isFFModule_of_rkIdx_le hXsq ⟨hAsT.trans le_sup_right, hAsA2.2.1, hAsA2.2.2⟩ ?_
    have h1 := Nat.mul_le_mul_right (nB (A.subgroupOf M) (tilde L ⊤ V ⊔ tM • tilde L ⊤ V)) hk2le
    omega
  obtain ⟨n, hSND⟩ := sumNatDual_of_isFFModule hB51 hA21 hZ rfl htsT hsumX hnotX hFF
  have hTn : ∀ s ∈ autSec T VT C, ∀ l ∈ autSec L VT C, s * l * s⁻¹ ∈ autSec L VT C :=
    fun s hs l hl => n6_conj_mem hZ hs hl
  have hlt3 := two_mul_rk_lt hXsq hTn hZ.irr htsT hsumX hinfX hnotX hsplitX hSND hAsT
    hAsA2.2.2 hAsA2.2.1
  have hk3 : k ≤ 2 := by
    by_contra hk
    have h1 := Nat.mul_le_mul_right (rkIdx (fixV (autSec A VT C))) (show 3 ≤ k by omega)
    have h2 := Nat.mul_le_mul_left k hNX
    omega
  have hk : rk ↥(isoSum (L.subgroupOf M) (tilde L ⊤ V)) = 2 * rk ↥(tilde L ⊤ V) := by
    rw [hk1, show k = 2 by omega]
  have hAutX := forall_aut_of_sumNatDual hSND hZ.irr (z35_conj_irr hZ htsT) hinfX hnotX
  have hAutQ := d391_aut hD hAutX
  have hinjQ := d391_inj hD h5
  obtain ⟨eL⟩ := d391_mulEquiv hD h5 hSND
  have hn45 : n = 4 ∨ n = 5 := hSND.1
  have hn0 : 0 < n := by rcases hn45 with h | h <;> omega
  have hZQ := d391_center hD hn0 eL
  have hcent : ∀ x ∈ M, (∀ l ∈ L, x * l = l * x) → x = 1 := by
    refine d391_cent_eq_one hD fun x hxM hxL p hp hp2 hxp => ?_
    by_cases hp3 : p = 3
    · subst hp3
      exact d391_eq_one_of_pow_three hD hn45 eL hxM hxL hxp
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · exact absurd (h ▸ hp) (by norm_num)
        · exact h
      have hxΛ : ∀ l ∈ L.subgroupOf M, (⟨x, hxM⟩ : ↥M) * l = l * ⟨x, hxM⟩ :=
        fun l hl => Subtype.ext (hxL _ hl)
      have hxp' : (⟨x, hxM⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hxp)
      exact d391_eq_one_of_fix hD hxM hxL
        (fix_top_of_prime_ge_five hQsq hΛ hirrQ hAutQ hinjQ hZQ hk hsupQ hxΛ hp hp5 hxp')
  have hCΛ : ∀ c : ↥M, (∀ l ∈ L.subgroupOf M, c * l = l * c) → c = 1 := by
    intro c hc
    exact Subtype.ext (hcent c c.2 fun l hl => congrArg Subtype.val (hc ⟨l, hLM hl⟩ hl))
  have hmemL : ∀ m ∈ M, m ∈ L ∨ t⁻¹ * m ∈ L := by
    intro m hm
    rcases hdichQ ⟨m, hm⟩ with h | h
    · exact Or.inl (mem_of_iso_smul hirrQ hAutQ hinjQ hΛ hCΛ h)
    · right
      have h1 : XMod.Iso ↥(L.subgroupOf M) ((tM⁻¹ * ⟨m, hm⟩) • tilde L ⊤ V) (tilde L ⊤ V) := by
        have h2 := XMod.iso_smul (normalizes_whole (L.subgroupOf M) hΛ) tM⁻¹ h
        rwa [smul_smul, inv_smul_smul] at h2
      exact mem_of_iso_smul hirrQ hAutQ hinjQ hΛ hCΛ h1
  apply htop
  rw [eq_top_iff, ← hD.hyp.gen]
  refine iSup₂_le fun m hm => ?_
  rcases hmemL m hm with h | h
  · have hmV : V.map m.toMonoidHom ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact hLV m h v hv
    exact hmV.trans (le_orbSup T V)
  · have hmV : V.map (t⁻¹ * m).toMonoidHom ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact hLV _ h v hv
    rw [show m = t * (t⁻¹ * m) by group, map_mul_aut']
    exact (Subgroup.map_mono hmV).trans (map_le_orbSup htT)

end CFSG.Quasithin
