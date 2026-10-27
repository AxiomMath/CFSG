module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24R
public import CFSG.Goldschmidt.Steps.Sec87d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Fb45b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem conjSubgroup_inv_le_iff (B M : Subgroup G) (g : G) :
    conjSubgroup B g⁻¹ ≤ M ↔ B ≤ conjSubgroup M g :=
  (E3.le_conjSubgroup_iff_inv_le g).symm

private theorem conjSub_eq_conjSubgroup_inv' (h : G) (A : Subgroup G) :
    CFSG.Quasithin.A1b.conjSub h A = conjSubgroup A h⁻¹ := by
  rw [CFSG.Quasithin.A1b.conjSub, conjSubgroup, inv_inv]

theorem mul_inv_mem_of_mQuot_le_one {V U : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V)
    (hm : E3.mQuot V U ≤ 1) {v v' : G} (hv : v ∈ V) (hv' : v' ∈ V) (hvU : v ∉ U)
    (hv'U : v' ∉ U) : v * v'⁻¹ ∈ U := by
  have hr := E3.relIndex_eq_two_pow hV U
  interval_cases h : E3.mQuot V U
  · exact absurd (Subgroup.relIndex_eq_one.1 (by rw [hr, pow_zero]) hv) hvU
  · have h2 : (U.subgroupOf V).index = 2 := by rw [← Subgroup.relIndex, hr, pow_one]
    have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨v, hv⟩) (b := (⟨v', hv'⟩ : V)⁻¹)).2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this ⟨fun h => absurd h hvU, fun h => absurd (by simpa using U.inv_mem h) hv'U⟩

theorem quad_ne_zero_of_transvection {W : Type*} [CommGroup W] {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) (σ : MulAut W) (hσQ : ∀ x, Q (σ x) = Q x)
    (hidx : ∀ x y, σ x ≠ x → σ y ≠ y → σ (x * y⁻¹) = x * y⁻¹) {v₀ : W} (hv₀ : σ v₀ ≠ v₀) :
    Q (σ v₀ * v₀⁻¹) ≠ 0 := by
  set c := σ v₀ * v₀⁻¹ with hcdef
  intro hc0
  have key1 : ∀ v, σ v ≠ v → σ v = v * c := by
    intro v hv
    have h := hidx v v₀ hv hv₀
    rw [map_mul, map_inv] at h
    calc σ v = σ v * (σ v₀)⁻¹ * σ v₀ := by group
      _ = v * v₀⁻¹ * σ v₀ := by rw [h]
      _ = v * c := by rw [hcdef, mul_assoc, mul_comm v₀⁻¹]
  have key2 : ∀ v, σ v ≠ v → polarQ Q v c = 0 := by
    intro v hv
    have h := hσQ v
    rw [key1 v hv] at h
    unfold polarQ
    rw [h, hc0]
    ring
  have key3 : ∀ u, polarQ Q u c = 0 := by
    intro u
    by_cases hu : σ u = u
    · have huv : σ (u * v₀) ≠ u * v₀ := by
        rw [map_mul, hu]
        exact fun h => hv₀ (mul_left_cancel h)
      have h := key2 _ huv
      rw [hQ.1.1 u v₀ c, key2 v₀ hv₀, add_zero] at h
      exact h
    · exact key2 u hu
  have hc1 : c ≠ 1 := fun h => hv₀ (mul_inv_eq_one.1 h)
  obtain ⟨y, hy⟩ := hQ.2 c hc1
  apply hy
  have := key3 y
  unfold polarQ at this ⊢
  rw [mul_comm c y]
  linear_combination this

theorem s16c1_one_lt_betaN (D : Data G) (h41 : R16_41 D) (hkitB : OmegaKitB) (hkitC : OmegaKitC)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) : (1 : ℕ∞) < betaN 0 D.M V := by
  have h125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have pf := h125.pairFacts
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hVM : V ≤ D.M := pf.le_M
  have hMV : D.M ≤ normalizer (V : Set G) := pf.le_normalizer
  have hM0 : D.M ≤ normalizer (V₀ : Set G) := pf.le_normalizer₀
  refine lt_of_lt_of_le (b := 2) (by norm_num) (le_iInf₂ fun U hU => ?_)
  obtain ⟨hUV, t, ⟨htM, htC⟩, ⟨k, hk⟩, W, hWV, hmW, hUW, hWt, hP⟩ := hU
  have hWeq : W = V := (E3.mQuot_eq_zero_iff hV2 hWV).1 (Nat.le_zero.1 hmW)
  subst hWeq
  by_contra hlt
  push_neg at hlt
  have hm2 : E3.mQuot W U < 2 := by exact_mod_cast hlt
  have hm1 : E3.mQuot W U ≤ 1 := by omega
  apply hP
  suffices hsuff : ∃ c ∈ commElt W t, centralizer ({c} : Set G) ≤ D.M by
    obtain ⟨c, hcm, hcM⟩ := hsuff
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hcm)).trans hcM
  by_cases hct : CentralizesMod V₀ W t
  · obtain ⟨w, hwW, hwt⟩ := SetLike.not_le_iff_exists.1 hWt
    have hwM : w ∈ D.M := hVM hwW
    have hz1 : w⁻¹ * t⁻¹ * w * t ≠ 1 := by
      intro hz
      apply hwt
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc y * w = y * w * (w⁻¹ * y⁻¹ * w * y) := by rw [hz, mul_one]
        _ = w * y := by group
    have hc' : t * w * t⁻¹ * w⁻¹ ∈ V₀ := hct w hwW
    have hc1 : t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t ∈ V₀ :=
      (Subgroup.mem_normalizer_iff''.1 (hM0 htM) _).1 (V₀.inv_mem hc')
    have hc2 : w⁻¹ * (t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t) * w ∈ V₀ :=
      (Subgroup.mem_normalizer_iff''.1 (hM0 hwM) _).1 hc1
    have hzV₀ : w⁻¹ * t⁻¹ * w * t ∈ V₀ := by
      have e : w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t) * w := by group
      rw [e]
      exact hc2
    have hzW : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
    have hXV : Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) ≤ V₀ := Subgroup.zpowers_le.2 hzV₀
    have hX1 : Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
    have hN := h125.hyp62.normalizer_le _ hXV hX1
    have hcent_eq : centralizer ({w⁻¹ * t⁻¹ * w * t} : Set G) =
        centralizer (Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact ⟨_, hzW, ((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN⟩
  · have htinvM : t⁻¹ ∈ D.M := D.M.inv_mem htM
    have hst : t⁻¹ ∈ stabTil V₀ W := le_stabTil hMV hM0 htinvM
    have hstt : t ∈ stabTil V₀ W := le_stabTil hMV hM0 htM
    set σ := actTil V₀ W hV ⟨t⁻¹, hst⟩ with hσdef
    obtain ⟨⟨Q, hQm, hQinv⟩, h41'⟩ := h41 V₀ W L hV hS hc
    have hσN : σ ∈ normalizer (lBar V₀ W hV L : Set (MulAut (Vtil V₀ W hV))) :=
      s16c1_Mbar_le_normalizer hkitB hS hc (actTil_mem_barSub V₀ W hV htinvM hst)
    have hσQ : ∀ x, Q (σ x) = Q x := (hkitC _ _ hc.2.1).2.1 Q hQm hQinv σ hσN
    have hfixU : ∀ x : IntMod W hV, x.val ∈ U → σ (mkTil V₀ W hV x) = mkTil V₀ W hV x := by
      intro x hx
      rw [hσdef, actTil_mk]
      congr 1
      apply IntMod.val_injective
      rw [actStab_apply_val]
      have hcomm : x.val * t = t * x.val := Subgroup.mem_centralizer_iff.1 htC x.val hx
      show t⁻¹ * x.val * t⁻¹⁻¹ = x.val
      rw [inv_inv, mul_assoc, hcomm]
      group
    have hidx : ∀ a b, σ a ≠ a → σ b ≠ b → σ (a * b⁻¹) = a * b⁻¹ := by
      intro a b ha hb
      obtain ⟨x, rfl⟩ := mkTil_surjective V₀ W hV a
      obtain ⟨y, rfl⟩ := mkTil_surjective V₀ W hV b
      have hxU : x.val ∉ U := fun h => ha (hfixU x h)
      have hyU : y.val ∉ U := fun h => hb (hfixU y h)
      have hxy := mul_inv_mem_of_mQuot_le_one hV2 hUV hm1 x.val_mem y.val_mem hxU hyU
      rw [← map_inv, ← map_mul]
      exact hfixU (x * y⁻¹) (by rw [IntMod.val_mul, IntMod.val_inv]; exact hxy)
    have hσ1 : σ ≠ 1 := by
      intro h
      apply hct
      have e : (⟨t⁻¹, hst⟩ : stabTil V₀ W) = (⟨t, hstt⟩ : stabTil V₀ W)⁻¹ := rfl
      rw [hσdef, e, map_inv, inv_eq_one] at h
      exact (actTil_eq_one_iff V₀ W hV _).1 h
    obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
      by_contra h
      push_neg at h
      exact hσ1 (MulEquiv.ext h)
    have hQne := quad_ne_zero_of_transvection hQm.1 σ hσQ hidx ha
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ W hV a
    have hxinv : t⁻¹ * (x.val)⁻¹ * t ∈ W :=
      (Subgroup.mem_normalizer_iff''.1 (hMV htM) _).1 (W.inv_mem x.val_mem)
    have hcV : x.val * t⁻¹ * (x.val)⁻¹ * t ∈ W := by
      have e : x.val * t⁻¹ * (x.val)⁻¹ * t = x.val * (t⁻¹ * (x.val)⁻¹ * t) := by group
      rw [e]
      exact W.mul_mem x.val_mem hxinv
    have hcm : x.val * t⁻¹ * (x.val)⁻¹ * t ∈ commElt W t :=
      Subgroup.subset_closure ⟨(x.val)⁻¹, W.inv_mem x.val_mem, by rw [inv_inv]⟩
    refine ⟨_, hcm, ?_⟩
    set y : IntMod W hV := IntMod.mk hV ⟨_, hcV⟩ with hydef
    have hyeq : y = x * actStab V₀ W hV ⟨t⁻¹, hst⟩ x⁻¹ := by
      apply IntMod.val_injective
      rw [IntMod.val_mul, actStab_apply_val, IntMod.val_inv]
      show x.val * t⁻¹ * (x.val)⁻¹ * t = x.val * (t⁻¹ * (x.val)⁻¹ * t⁻¹⁻¹)
      rw [inv_inv]
      group
    have hinv : ∀ z : Vtil V₀ W hV, z⁻¹ = z :=
      fun z => (eq_inv_of_mul_eq_one_left (s16c1_vTil_mul_self hV z)).symm
    have hmk : mkTil V₀ W hV y = σ (mkTil V₀ W hV x) * (mkTil V₀ W hV x)⁻¹ := by
      rw [hyeq, map_mul, map_inv, hσdef, actTil_mk, map_inv, hinv, hinv, mul_comm]
    have hQy : Q (mkTil V₀ W hV y) ≠ 0 := by rw [hmk]; exact hQne
    exact ((h41' Q hQm hQinv).2 _ hQy).2 y rfl

theorem s16c1_le_conj_of_conj_le (D : Data G) (h42 : R16_42 D) (h43 : R16_43_1 D)
    (hkitC : OmegaKitC)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) (h0 : V₀ = ⊥) {g : G} (hg : conjSubgroup V g ≤ D.M) :
    V ≤ conjSubgroup D.M g := by
  subst h0
  by_contra hnot
  have hy : Hyp1643 D ⊥ V 0 (conjSubgroup V g) g :=
    ⟨Or.inl rfl, ⟨hg, g, le_rfl, E3.mQuot_self _⟩, le_rfl⟩
  have h32 := s16c1G43_rank h42 hS hc hy hnot
  have hMstab : D.M ≤ stabTil ⊥ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hA_stab : conjSubgroup V g ≤ stabTil ⊥ V := hg.trans hMstab
  have hAel2 : IsElemAbelian2 (barSub ⊥ V hV (conjSubgroup V g)) :=
    s16c1G44_isElemAbelian2_barSub le_rfl hA_stab
  have hbarNorm : barSub ⊥ V hV (conjSubgroup V g) ≤
      normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) :=
    (h43 ⊥ V L hV hS hc 0 (conjSubgroup V g) g hy).trans (Subgroup.le_normalizer)
  have hcard := (hkitC (Vtil ⊥ V hV) (lBar ⊥ V hV L) hc.2.1).2.2.2.1
    (barSub ⊥ V hV (conjSubgroup V g)) hbarNorm hAel2
  simp only [pow_zero, one_mul] at h32
  omega

theorem s16c1_exists_A_K_not_le (D : Data G) (h126 : R126 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) :
    ∃ H A K : Subgroup G, IsSylowIn 2 D.T H ∧ A ∈ E3.gammaSet V 0 D.T ∧
      E1.IsE D.k H D.T A K ∧ ¬ K ≤ D.M := by
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
  have hTH₀ : D.T ≤ H₀ := hmin.1.1
  have hH₀M : ¬ H₀ ≤ D.M := hmin.1.2.1
  have hS : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hTH₀
  have hEF : E1.InEFor D.k H₀ D.T := (E1.inE_iff_inEFor hS).1 (h126 H₀ hmin)
  let Ω : Set (Subgroup G) := {A | ∃ g : G, A = conjSubgroup V g ∧ A ≤ H₀}
  have hΩ : E1.IsInvColl H₀ Ω := by
    refine ⟨fun A hA => by obtain ⟨g, -, hAH⟩ := hA; exact hAH, fun A hA => ?_,
      fun A hA h hh => ?_⟩
    · obtain ⟨g, rfl, -⟩ := hA
      exact E3.isElemAbelian_conjSubgroup hV g
    · obtain ⟨g, hAg, hAH⟩ := hA
      refine ⟨g * h⁻¹, ?_, ?_⟩
      · rw [conjSub_eq_conjSubgroup_inv', hAg, conjSubgroup_conjSubgroup]
      · rw [conjSub_eq_conjSubgroup_inv', hAg]
        intro x hx
        rw [mem_conjSubgroup_iff] at hx
        rw [inv_inv, ← hAg] at hx
        have hxH : h⁻¹ * x * h ∈ H₀ := hAH hx
        have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
        rw [← e]
        exact H₀.mul_mem (H₀.mul_mem hh hxH) (H₀.inv_mem hh)
  have hweak : E1.weakClosure D.T Ω = E3.wClos V 0 D.T := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
      obtain ⟨g, rfl, -⟩ := hA
      exact E3.le_wClos ⟨hAT, g, le_rfl, E3.mQuot_self (conjSubgroup V g)⟩
    · refine E3.wClos_le_of_forall fun A hA => ?_
      obtain ⟨hAT, g, hAg, hmg⟩ := hA
      have hVg2 : IsPGroup 2 (conjSubgroup V g) :=
        E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g
      have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg2 hAg).1 hmg
      rw [hAeq]
      refine le_iSup₂_of_le (conjSubgroup V g) ⟨g, rfl, (hAeq ▸ hAT).trans hTH₀⟩ ?_
      exact le_iSup_of_le (hAeq ▸ hAT) le_rfl
  have hgen := hEF Ω hΩ
  rw [hweak] at hgen
  have hN' : H₀ ⊓ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := inf_le_right.trans hN
  have hgen_not : ¬ E1.eGen D.k H₀ D.T Ω ≤ D.M := by
    intro hle
    apply hH₀M
    rw [← hgen]
    exact sup_le hle hN'
  have hex : ∃ A K : Subgroup G, A ∈ Ω ∧ A ≤ D.T ∧ E1.IsE D.k H₀ D.T A K ∧ ¬ K ≤ D.M := by
    by_contra hcon
    apply hgen_not
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    by_contra hKM
    exact hcon ⟨A, K, hA, hAT, hK, hKM⟩
  obtain ⟨A, K, hAΩ, hAT, hK, hKM⟩ := hex
  obtain ⟨g, hAg, -⟩ := hAΩ
  exact ⟨H₀, A, K, hS, ⟨hAT, g, le_of_eq hAg, by rw [hAg, E3.mQuot_self]⟩, hK, hKM⟩

theorem s16c1_exists_conj_of_isE (D : Data G) {V H A K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : IsSylowIn 2 D.T H) (hA : A ∈ E3.gammaSet V 0 D.T) (hK : E1.IsE 1 H D.T A K)
    (hKM : ¬ K ≤ D.M) :
    ∃ g : G, ¬ conjSubgroup V g ≤ D.M ∧ conjSubgroup V g ⊓ D.M ∈ E3.gammaSet V 1 D.M := by
  have hTS : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hTM : D.T ≤ D.M := hTS.le
  obtain ⟨hAT, x, hAx, hmx⟩ := hA
  have hVx : IsElemAbelian 2 (conjSubgroup V x) := E3.isElemAbelian_conjSubgroup hV x
  have hVx2 : IsPGroup 2 (conjSubgroup V x) := B2F.isPGroup_of_isElemAbelian hVx
  have hAeq : A = conjSubgroup V x := (E3.mQuot_eq_zero_iff hVx2 hAx).1 hmx
  have hAab : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAx hVx
  have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAab
  obtain ⟨-, hcard⟩ := E3.card_le_of_isE hS hAT hAab hK
  have hmA : E3.mQuot A (A ⊓ pCoreOf 2 K) ≤ 1 := by
    have e := E3.card_eq_two_pow_mul hA2 (inf_le_left : A ⊓ pCoreOf 2 K ≤ A)
    rw [e] at hcard
    have := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
  have hPT : pCoreOf 2 K ≤ D.T := (E1.pCoreOf_two_le_of_isSylowIn hK.2.2.1).trans inf_le_left
  have hPM : pCoreOf 2 K ≤ D.M := hPT.trans hTM
  have hex : ∃ k ∈ K, ¬ conjSubgroup A k⁻¹ ≤ D.M := by
    by_contra hcon
    push_neg at hcon
    apply hKM
    have hcc : CFSG.Quasithin.conjClosure A K ≤ D.M := by
      refine (Subgroup.closure_le _).2 ?_
      rintro y ⟨h, hh, z, hz, rfl⟩
      refine hcon h hh ?_
      rw [mem_conjSubgroup_iff]
      have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
      rw [e]
      exact hz
    have h2 : twoResidual K ≤ D.M := (E1.twoResidual_le_conjClosure ⟨1, hK⟩).trans hcc
    rw [← sup_twoResidual_eq hK.2.2.1]
    exact sup_le (inf_le_left.trans hTM) h2
  obtain ⟨k, hkK, hkM⟩ := hex
  have hBeq : conjSubgroup A k⁻¹ = conjSubgroup V (x * k⁻¹) := by
    rw [hAeq, conjSubgroup_conjSubgroup]
  have hB2 : IsPGroup 2 (conjSubgroup A k⁻¹) := E3.isPGroup_conjSubgroup hA2 k⁻¹
  have hC : conjSubgroup (A ⊓ pCoreOf 2 K) k⁻¹ ≤ conjSubgroup A k⁻¹ ⊓ D.M := by
    refine le_inf ((E3.conjSubgroup_le_conjSubgroup_iff _).2 inf_le_left) ?_
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hg := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hkK
    have h3 := (Subgroup.mem_normalizer_iff.1 hg (k⁻¹ * y * k⁻¹⁻¹)).1 hy.2
    have e : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y := by group
    rw [e] at h3
    exact hPM h3
  have hm1 : E3.mQuot (conjSubgroup A k⁻¹) (conjSubgroup A k⁻¹ ⊓ D.M) ≤ 1 :=
    (E3.mQuot_mono hC).trans (by rw [E3.mQuot_conjSubgroup]; exact hmA)
  have hm0 : E3.mQuot (conjSubgroup A k⁻¹) (conjSubgroup A k⁻¹ ⊓ D.M) ≠ 0 := by
    intro h0
    apply hkM
    have := (E3.mQuot_eq_zero_iff hB2 inf_le_left).1 h0
    rw [← this]
    exact inf_le_right
  refine ⟨x * k⁻¹, by rw [← hBeq]; exact hkM, inf_le_right, x * k⁻¹, ?_, ?_⟩
  · rw [← hBeq]; exact inf_le_left
  · rw [← hBeq]; omega

theorem s16c1_cent_cClos_le (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (h0 : V₀ ≠ ⊥)
    (k : ℕ) :
    centralizer (E3.cClos V k D.T : Set G) ≤ D.M := by
  have pf := h.pairFacts
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hVn : (V.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer pf.le_M).2 pf.le_normalizer
  have hVT : V ≤ D.T := hT.le_of_normal pf.le_M hVn pf.elemAbelian.isPGroup
  have hTM : D.T ≤ D.M := hT.le
  have hT2 : IsPGroup 2 D.T := hT.isPGroup
  have hne := CFSG.Goldschmidt.Sec8.inf_center_ne_bot' hT2 (pf.le.trans hVT)
    (hTM.trans pf.le_normalizer₀) h0
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht1' : t ≠ 1 := fun e => ht1 (Subtype.ext e)
  have hWle : E3.wClos V k D.T ≤ D.T := by
    unfold E3.wClos
    exact iSup₂_le fun A hA => hA.1
  have htc : t ∈ E3.cClos V k D.T := by
    refine ⟨ht.2.1, ?_⟩
    exact Subgroup.centralizer_le (fun x hx => hWle hx) ht.2.2
  have hXV : Subgroup.zpowers t ≤ V₀ := Subgroup.zpowers_le.2 ht.1
  have hX1 : Subgroup.zpowers t ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr ht1'
  have hN := h.hyp62.normalizer_le _ hXV hX1
  have hcent_eq : centralizer ({t} : Set G) = centralizer (Subgroup.zpowers t : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  refine (Subgroup.centralizer_le (Set.singleton_subset_iff.2 htc)).trans ?_
  exact ((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN

theorem r16_47_O1_ne_holds (D : Data G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h41 : R16_41 D) (h42 : R16_42 D) (h43 : R16_43_1 D)
    (h434 : R16_43_4 D) (hkitB : OmegaKitB) (hkitC : OmegaKitC) : R16_47_O1_ne D := by
  intro V₀ V L hV hS hc _ _
  have h125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hk : D.k = 1 :=
    Data.k_eq_one_of_three_mem D hSg h1219 (by rw [hc.2.2.1]; exact Set.mem_singleton 3)
  have hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    r16_43_3_of D hSg h1219 h21 h22 h61 h42 h43 hkitB V₀ V L hV hS hc
  by_cases h0 : V₀ = ⊥
  · obtain ⟨H, A, K, hSyl, hA, hK, hKM⟩ := s16c1_exists_A_K_not_le D h126 h125 hN
    rw [hk] at hK
    obtain ⟨g, hgM, hgam⟩ := s16c1_exists_conj_of_isE D hV hSyl hA hK hKM
    rcases h434 V₀ V L hV hS hc 1 (conjSubgroup V g ⊓ D.M) g
        ⟨Or.inr ⟨h0, rfl⟩, hgam, inf_le_left⟩ h0 with hle | ⟨hO, -⟩
    · exfalso
      apply hgM
      have hinv : conjSubgroup V g⁻¹ ≤ D.M := by
        rw [conjSubgroup_inv_le_iff]
        exact hle
      have := s16c1_le_conj_of_conj_le D h42 h43 hkitC hS hc h0 hinv
      rwa [← conjSubgroup_inv_le_iff, inv_inv] at this
    · obtain ⟨g', hX, hg'⟩ := hO
      exact ⟨_, g', hX, hg'.1⟩
  · have hr : (D.k : ℕ∞) < E3.rParam V := Sixteen24.k_lt_rParam_of_hyp125 D hSg h1219 hx h61 h125
    have hβ : (D.k : ℕ∞) < betaN 0 D.M V := by
      rw [hk]; exact_mod_cast s16c1_one_lt_betaN D h41 hkitB hkitC hS hc
    rcases trichotomy_of_lt D h126 h125 hr hβ with h1 | h2 | ⟨X, g, hX, hg⟩
    · exact absurd hN h1
    · exact absurd (s16c1_cent_cClos_le D h125 h0 D.k) h2
    · rw [hk] at hg
      exact ⟨X, g, hX, hg.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
