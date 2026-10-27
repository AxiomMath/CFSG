module

public import CFSG.Quasithin.EmptyFaithful.S153Syl
public import CFSG.Quasithin.EmptyFaithful.S153YCases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section ModelSwap

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem OfourStruct.swap_apply_mem (h : OfourStruct X L₁ L₂ t) {x : MulAut W} (hX : x ∈ X)
    (hxN : x ∉ L₁ ⊔ L₂) :
    (∀ u ∈ commV L₁, x u ∈ commV L₂) ∧ (∀ u ∈ commV L₂, x u ∈ commV L₁) := by
  have hxt : x * t ∈ L₁ ⊔ L₂ := (h.mem_or_mul_t_mem hX).resolve_left hxN
  have htt : ∀ u : W, t (t u) = u := fun u => by
    have := congrArg (fun φ : MulAut W => φ u) h.tsq
    simpa using this
  have hx_eq : ∀ u : W, x u = (x * t) (t u) := fun u => by rw [MulAut.mul_apply, htt]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [hx_eq]
    exact (mem_stabSub.1 (h.sup_le_stab₂ hxt) (t u)).2 (h.swap₁ u hu)
  · rw [hx_eq]
    exact (mem_stabSub.1 (h.sup_le_stab₁ hxt) (t u)).2 (h.swap₂ u hu)

end ModelSwap

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem pow_three_mem_pCoreOf_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {y : G}
    (hy : y ∈ Y153 Mc M) : y ^ 3 ∈ pCoreOf 2 (Y153 Mc M) := by
  obtain ⟨φ, -⟩ := exists_mulEquiv_imageOTwoQuot (Y153_le Mc M) (le_normalizer_Y153 Mc M)
  have h3 := (h.Ystar_structure h113).1.2.2 (φ (QuotientGroup.mk ⟨y, hy⟩))
  have h4 : φ ((QuotientGroup.mk ⟨y, hy⟩ : OTwoQuot (Y153 Mc M)) ^ 3) = 1 := by
    rw [map_pow]
    exact h3
  have h5 : (QuotientGroup.mk ⟨y, hy⟩ : OTwoQuot (Y153 Mc M)) ^ 3 = 1 :=
    φ.injective (by rw [h4, map_one])
  have h6 : (QuotientGroup.mk (⟨y, hy⟩ ^ 3 : ↥(Y153 Mc M)) : OTwoQuot (Y153 Mc M)) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact h5
  have h7 := (mk_eq_one_iff_mem_pCoreOf (⟨y, hy⟩ ^ 3 : ↥(Y153 Mc M))).1 h6
  simpa using h7

theorem pCoreOf_Y153_le_Sgp153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) : pCoreOf 2 (Y153 Mc M) ≤ Sgp153 T V₁ := by
  have hYT : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 _)
      (h.T_le.trans ((le_normalizer_Y153 Mc M).trans (normalizer_le_normalizer_pCoreOf 2 _)))
  have h1 : pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 (Y153 Mc M ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) hYT (pCoreOf_isPGroup 2 _)
  rw [h.lemma_15_3_7_pCore h113] at h1
  exact h1.trans (inf_le_inf_left T
    ((Subgroup.centralizer_le D.le₁).trans (Subgroup.centralizer_le_normalizer _)))

theorem card_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    Nat.card (Y153 Mc M) =
      9 * Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hV := h.elemAbelian
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans h.le_normalizer
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  have h9 : Nat.card (autI hV (Y153 Mc M)) = 9 := by
    rw [e]
    exact hS.card_oTwoUpper h.isSylowTwoOf_autI
  have := card_autI_mul_card_inf hV hYN
  rw [h9] at this
  exact this.symm

theorem card_Yplus_base (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) =
      3 * Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  have hYM := Y153_le Mc M
  have hKN : Y153 Mc M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (VZ T M : Set G) := inf_le_left.trans (hYM.trans h.le_normalizer)
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  have hKeq : autI hV (Y153 Mc M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) = oTwoUpper (autI hV M) ⊓ L₂ := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨g, ⟨hgY, hgC⟩, rfl⟩ := (mem_autI hV).1 hφ
      refine ⟨?_, ?_⟩
      · rw [← e]
        exact convI_mem_autI hV hgY g.2
      · have hgM : convI hV g ∈ autI hV M := convI_mem_autI hV (hYM hgY) g.2
        refine (hS.symm.mem_L₁_iff hgM).2 ?_
        exact (mem_centralizer_map_inclMod_iff hV g.2 (commV L₁)).1 hgC
    · rintro ⟨hφY, hφL⟩
      have hφY' : φ ∈ autI hV (Y153 Mc M) := by rw [e]; exact hφY
      obtain ⟨g, hgY, rfl⟩ := (mem_autI hV).1 hφY'
      refine (mem_autI hV).2 ⟨g, ⟨hgY, ?_⟩, rfl⟩
      refine (mem_centralizer_map_inclMod_iff hV g.2 (commV L₁)).2 fun u hu => ?_
      exact hS.L₂_fix₁ hφL hu
  have hcard3 : Nat.card ↥(oTwoUpper (autI hV M) ⊓ L₂) = 3 := by
    obtain ⟨x₂, hx₂L, hx₂3, hx₂1⟩ := exists_orderThree hS.nat₂
    obtain ⟨x₁, hx₁L, hx₁3, hx₁1⟩ := exists_orderThree hS.nat₁
    have hodd : ∀ {y : MulAut (IntMod (VZ T M) hV)}, y ^ 3 = 1 → Odd (orderOf y) := fun hy =>
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy)
    have hord₂ : orderOf x₂ = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hx₂3 hx₂1
    have hx₂B : x₂ ∈ oTwoUpper (autI hV M) ⊓ L₂ :=
      ⟨mem_oTwoUpper_of_odd (hS.L₂_le hx₂L) (hodd hx₂3), hx₂L⟩
    have hdvd3 : 3 ∣ Nat.card ↥(oTwoUpper (autI hV M) ⊓ L₂) := by
      rw [← hord₂]
      exact Subgroup.orderOf_dvd_natCard _ hx₂B
    have h9 : Nat.card (oTwoUpper (autI hV M)) = 9 := hS.card_oTwoUpper h.isSylowTwoOf_autI
    have hdvd9 : Nat.card ↥(oTwoUpper (autI hV M) ⊓ L₂) ∣ 9 := by
      rw [← h9]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne9 : Nat.card ↥(oTwoUpper (autI hV M) ⊓ L₂) ≠ 9 := by
      intro h9'
      have heq : oTwoUpper (autI hV M) ⊓ L₂ = oTwoUpper (autI hV M) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, h9'])
      have hx₁A : x₁ ∈ oTwoUpper (autI hV M) :=
        mem_oTwoUpper_of_odd (hS.L₁_le hx₁L) (hodd hx₁3)
      have hx₁L₂ : x₁ ∈ L₂ := by
        have : x₁ ∈ oTwoUpper (autI hV M) ⊓ L₂ := by rw [heq]; exact hx₁A
        exact this.2
      have : x₁ ∈ L₁ ⊓ L₂ := ⟨hx₁L, hx₁L₂⟩
      rw [hS.Linf, Subgroup.mem_bot] at this
      exact hx₁1 this
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hdvd9 :
      Nat.card ↥(oTwoUpper (autI hV M) ⊓ L₂) ∣ 3 ^ 2)
    interval_cases k
    · rw [hkeq] at hdvd3
      norm_num at hdvd3
    · simpa using hkeq
    · exact absurd (by simpa using hkeq) hne9
  have hinf : (Y153 Mc M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) ⊓
        Subgroup.centralizer (VZ T M : Set G) =
      Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    ext y
    constructor
    · rintro ⟨⟨hyY, -⟩, hyC⟩
      exact ⟨hyY, hyC⟩
    · rintro ⟨hyY, hyC⟩
      exact ⟨⟨hyY, Subgroup.centralizer_le D.le₁ hyC⟩, hyC⟩
  have hKcard := card_autI_mul_card_inf hV hKN
  rw [hKeq, hcard3, hinf] at hKcard
  exact hKcard.symm

theorem Yplus_base_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) ≤
      oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ pCoreOf 2 (Y153 Mc M) := by
  intro c hc
  obtain ⟨a, ha⟩ := exists_pow_mem_oTwoUpper _ hc
  have h4 : c ^ 4 ^ a ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := by
    have e : c ^ 4 ^ a = (c ^ 2 ^ a) ^ 2 ^ a := by
      rw [← pow_mul]
      congr 1
      rw [← mul_pow]
      norm_num
    rw [e]
    exact Subgroup.pow_mem _ ha _
  have key : ∀ a : ℕ, ∃ m, 4 ^ a = 3 * m + 1 := by
    intro a
    induction a with
    | zero => exact ⟨0, by norm_num⟩
    | succ a ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨4 * m + 1, by rw [pow_succ, hm]; ring⟩
  obtain ⟨m, hm⟩ := key a
  have hc3 : (c ^ 3) ^ m ∈ pCoreOf 2 (Y153 Mc M) :=
    Subgroup.pow_mem _ (h.pow_three_mem_pCoreOf_Y153 h113 hc.1) m
  have e3 : c ^ (3 * m + 1) = (c ^ 3) ^ m * c := by
    rw [pow_succ c (3 * m), pow_mul c 3 m]
  have e2 : c = ((c ^ 3) ^ m)⁻¹ * c ^ 4 ^ a := by
    rw [hm, e3]
    group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc3))
    (Subgroup.mem_sup_left h4)

theorem inf_eq_Yplus_base (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) (hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M) {I : Subgroup G}
    (hI : IsHPlus (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) (Sgp153 T V₁) M I) :
    Y153 Mc M ⊓ I = Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) := by
  set K : Subgroup G := Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) with hK
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans hI.1.1
  have hYpI : oTwoUpper K ≤ I := le_sup_left.trans hI.1.1
  have hYI : ¬ Y153 Mc M ≤ I := fun hYI =>
    hI.2 (le_of_isUniqueM hU ⟨sup_le hYI hSI, hI.1.2⟩)
  have hKI : K ≤ Y153 Mc M ⊓ I := by
    refine le_inf inf_le_left (fun c hc => ?_)
    exact sup_le hYpI ((h.pCoreOf_Y153_le_Sgp153 h113 D).trans hSI) (h.Yplus_base_le h113 hc)
  have hpos : 0 < Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) := Nat.card_pos
  set c₀ := Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) with hc₀
  have hY : Nat.card (Y153 Mc M) = 9 * c₀ := h.card_Y153 h113
  have hKc : Nat.card K = 3 * c₀ := h.card_Yplus_base h113 D
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hKI
  have hd2 : Nat.card ↥(Y153 Mc M ⊓ I) ∣ Nat.card (Y153 Mc M) :=
    Subgroup.card_dvd_of_le inf_le_left
  have hd3 : d ∣ 3 := by
    rw [hd, hKc, hY] at hd2
    have e : 9 * c₀ = 3 * c₀ * 3 := by ring
    rw [e] at hd2
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) hd2
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h1
  · exact (Subgroup.eq_of_le_of_card_ge hKI (le_of_eq (by rw [hd, h1, mul_one]))).symm
  · exfalso
    apply hYI
    have heq : Y153 Mc M ⊓ I = Y153 Mc M :=
      Subgroup.eq_of_le_of_card_ge inf_le_left
        (le_of_eq (by rw [hd, h1, hKc, hY]; ring))
    exact (le_of_eq heq.symm).trans inf_le_right

theorem exists_mem_T_not_mem_normalizer (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ∃ s ∈ T, s ∉ Subgroup.normalizer (V₁ : Set G) := by
  by_contra hcon
  push Not at hcon
  have hle : T ≤ Sgp153 T V₁ := fun s hs => ⟨hs, hcon s hs⟩
  have h1 : (Sgp153 T V₁).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hle
  have h2 : (Sgp153 T V₁).relIndex T = 2 := D.relIndex_nS h
  omega

theorem V₂_le_conjClosure_Yplus (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    V₂ ≤ conjClosure (quasithinOmegaOneCenter T)
      (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) := by
  obtain ⟨s, hsT, hsV₁⟩ := h.exists_mem_T_not_mem_normalizer D
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, y, hy, hyY, hyL, hyord⟩ :=
    h.exists_mem_Yplus_acts h113 D
  subst hV₁ hV₂
  set U := conjClosure (quasithinOmegaOneCenter T)
    (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G))) with hU
  set x' : MulAut (IntMod (VZ T M) hV) := convI hV ⟨y, hy⟩ with hx'
  have hx'odd : Odd (orderOf x') := by rw [hyord]; decide
  have hx'1 : x' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyord
    exact absurd hyord (by norm_num)
  have hfpf : ∀ u ∈ commV L₂, u ≠ 1 → x' u ≠ u := fun u hu hu1 hxu =>
    hx'1 (eq_one_of_odd_of_fixed hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hyL hx'odd hu hu1
      hxu)
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h.qtfe.omegaOneCenter_ne_bot ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hzV : z ∈ VZ T M := h.Z_le_VZ hzZ
  set zw : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, hzV⟩ with hzw
  obtain ⟨a, ha, b, hb, hab⟩ := hS.exists_decomp_W zw
  have hsN : s ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer (h.T_le hsT)
  set sb : MulAut (IntMod (VZ T M) hV) := convI hV ⟨s, hsN⟩ with hsb
  have hsbX : sb ∈ autI hV M := convI_mem_autI hV (h.T_le hsT) hsN
  have hsbN : sb ∉ L₁ ⊔ L₂ := fun hmem =>
    hsV₁ ((mem_normalizer_map_inclMod_iff hV hsN (commV L₁)).2 (hS.sup_le_stab₁ hmem))
  have hsfix : sb zw = zw := by
    apply IntMod.val_injective
    rw [hsb, convI_apply_val]
    have hc := Subgroup.mem_centralizer_iff.mp (h.T_le_centralizer_Z hsT) z hzZ
    show s * z * s⁻¹ = z
    rw [← hc]
    group
  obtain ⟨hsw1, -⟩ := hS.swap_apply_mem hsbX hsbN
  have hb1 : b ≠ 1 := by
    intro hb1
    rw [hb1, mul_one] at hab
    have h1 : sb a ∈ commV L₂ := hsw1 a ha
    have h2 : sb a = a := by rw [← hab]; exact hsfix
    have h3 : a ∈ commV L₁ ⊓ commV L₂ := ⟨ha, h2 ▸ h1⟩
    rw [hS.inf, Subgroup.mem_bot] at h3
    apply hz1
    have h4 : zw = 1 := hab.trans h3
    have h5 := congrArg IntMod.val h4
    exact h5
  set Uw : Subgroup (IntMod (VZ T M) hV) := U.comap (inclMod hV) with hUw
  have hmemUw : ∀ w, w ∈ Uw ↔ w.val ∈ U := fun w => by
    rw [hUw, Subgroup.mem_comap, inclMod_apply]
  have hstab : ∀ w ∈ Uw, x' w ∈ Uw := by
    intro w hw
    rw [hmemUw] at hw ⊢
    rw [hx', convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hyY) w.val).mp hw
  have hzwUw : zw ∈ Uw := by
    rw [hmemUw]
    exact le_conjClosure _ _ hzZ
  have hx'a : x' a = a := hS.L₂_fix₁ hyL ha
  set u₀ : IntMod (VZ T M) hV := zw⁻¹ * x' zw with hu₀
  have hu₀Uw : u₀ ∈ Uw := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzwUw) (hstab _ hzwUw)
  have hu₀eq : u₀ = b⁻¹ * x' b := by
    rw [hu₀, hab, map_mul, hx'a]
    group
  have hu₀L : u₀ ∈ commV L₂ := by
    rw [hu₀eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) (commV_stable L₂ hyL hb)
  have hu₀1 : u₀ ≠ 1 := by
    intro h1
    rw [hu₀eq] at h1
    exact hfpf b hb hb1 (inv_mul_eq_one.mp h1).symm
  have hx'u₀ : x' u₀ ∈ Uw := hstab _ hu₀Uw
  have hx'u₀L : x' u₀ ∈ commV L₂ := commV_stable L₂ hyL hu₀L
  have hne1 : x' u₀ ≠ u₀ := hfpf u₀ hu₀L hu₀1
  have hne2 : x' u₀ ≠ 1 := fun h1 => hu₀1 (x'.injective (by rw [h1, map_one]))
  have hB : commV L₂ ≤ Uw := by
    set B : Subgroup (IntMod (VZ T M) hV) := Uw ⊓ commV L₂ with hBdef
    have hBle : B ≤ commV L₂ := inf_le_right
    have hcard4 : Nat.card (commV L₂) = 4 := (card_of_actsAsNaturalL2 hS.nat₂).2
    have hBcard : 3 ≤ Nat.card B := by
      have hsub : ({1, u₀, x' u₀} : Set (IntMod (VZ T M) hV)) ⊆ (B : Set _) := by
        intro w hw
        rcases hw with rfl | rfl | rfl
        · exact B.one_mem
        · exact ⟨hu₀Uw, hu₀L⟩
        · exact ⟨hx'u₀, hx'u₀L⟩
      have h3 : ({1, u₀, x' u₀} : Set (IntMod (VZ T M) hV)).ncard = 3 := by
        rw [Set.ncard_eq_three]
        exact ⟨1, u₀, x' u₀, hu₀1.symm, hne2.symm, hne1.symm, rfl⟩
      calc 3 = ({1, u₀, x' u₀} : Set (IntMod (VZ T M) hV)).ncard := h3.symm
        _ ≤ (B : Set (IntMod (VZ T M) hV)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card B := (Nat.card_coe_set_eq _).symm
    have hdvd : Nat.card B ∣ 4 := hcard4 ▸ Subgroup.card_dvd_of_le hBle
    have hB4 : Nat.card B = 4 := by
      have hle4 : Nat.card B ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      rcases (by omega : Nat.card B = 3 ∨ Nat.card B = 4) with h3 | h4
      · rw [h3] at hdvd
        norm_num at hdvd
      · exact h4
    have hBeq : B = commV L₂ := Subgroup.eq_of_le_of_card_ge hBle (by rw [hcard4, hB4])
    intro w hw
    have : w ∈ B := by rw [hBeq]; exact hw
    exact this.1
  intro v hv
  obtain ⟨w, hw, hwv⟩ := (mem_map_inclMod_iff hV).1 hv
  have hwUw := (hmemUw w).1 (hB hw)
  rw [← hwv]
  exact hwUw

end Hyp153

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem lemma_15_3_11_two_case_two (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (h2 : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))
    {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    I ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) I : Set G) ≤ M ⊓ I := by
  obtain ⟨hU, hY⟩ := h2
  subst hY
  have h3 := h.hyp.normalizer_V_le h113 h.decomp hU
  have hYpI : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ≤ I :=
    le_sup_left.trans hI.1.1
  have hV₂ : V₂ ≤ conjClosure (quasithinOmegaOneCenter T) I :=
    (h.hyp.V₂_le_conjClosure_Yplus h113 h.decomp).trans (conjClosure_mono le_rfl hYpI)
  intro x hx
  exact ⟨h3.2 (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hV₂ hx.2)), hx.1⟩

theorem lemma_15_3_11_two (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    I ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) I : Set G) ≤ M ⊓ I := by
  rcases h.cases with hY | h2
  · exact h.lemma_15_3_11_two_case_one h113 hY hI
  · exact h.lemma_15_3_11_two_case_two h113 h2 hI

theorem lemma_15_3_11_three (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (h2 : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))
    {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    Yp = oTwoUpper (Y153 Mc M ⊓ I) ∧ Subgroup.normalizer (V₁ : Set G) ≤ M ∧
      Subgroup.normalizer (V₂ : Set G) ≤ M ∧ Subgroup.normalizer (Yp : Set G) ≤ M := by
  obtain ⟨hU, hY⟩ := h2
  subst hY
  obtain ⟨hV₁, hV₂⟩ := h.hyp.normalizer_V_le h113 h.decomp hU
  refine ⟨?_, hV₁, hV₂, h.hyp.normalizer_Yplus_le h113 h.decomp hU⟩
  rw [h.hyp.inf_eq_Yplus_base h113 h.decomp hU hI]

theorem lemma_15_3_11_four (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I := by
  rcases h.cases with hY | h2
  · exact h.lemma_15_3_11_four_case_one h113 hY
  · have h3 := h.lemma_15_3_11_three h113 h2 hI
    apply le_antisymm
    · exact fun g hg => ⟨h3.2.2.2 hg.2, hg.1⟩
    · intro g hg
      refine ⟨hg.2, ?_⟩
      have hg' : g ∈ Subgroup.normalizer ((Y153 Mc M ⊓ I : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_Y153 Mc M hg.1, Subgroup.le_normalizer hg.2⟩
      have := normalizer_le_normalizer_oTwoUpper _ hg'
      rw [← h3.1] at this
      exact this

end Hyp15310

end CFSG.Quasithin
