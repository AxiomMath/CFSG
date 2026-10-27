module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenTenP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15_Thirteen_pRank_five_le_one_of_permutes
    {U : Type} [CommGroup U] [Finite U] {Y : Set (Subgroup U)} (hsup : sSup Y = ⊤)
    {X : Subgroup (MulAut U)}
    (hperm : ∀ ψ ∈ X, ∀ W ∈ Y, W.map ψ.toMonoidHom ∈ Y)
    (hcard : ∀ W ∈ Y, Nat.card W = 4) (hn : Y.ncard ≤ 6) :
    CFSG.Open.pRank 5 X ≤ 1 := by
  classical
  haveI : Finite ↥Y := Set.toFinite _
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : MulAction X (Subgroup U) := MulAction.compHom (α := Subgroup U) X.subtype
  letI : MulAction X ↥Y :=
    { smul := fun ψ W => ⟨ψ • (W : Subgroup U), hperm ψ ψ.2 W W.2⟩
      one_smul := fun W => Subtype.ext (one_smul X (W : Subgroup U))
      mul_smul := fun ψ χ W => Subtype.ext (mul_smul ψ χ (W : Subgroup U)) }
  refine CFSG.SectionRank.pRank_le (G := MulAut U) (p := 5) (k := 1) (by norm_num) ?_
  intro E hEX hEab
  have hP : IsPGroup 5 E := fun g => ⟨1, by
    show g ^ 5 = 1
    exact Subtype.ext (by simpa using hEab.2 (g : MulAut U) g.2)⟩
  obtain ⟨n, hn5⟩ := (IsPGroup.iff_card (p := 5)).1 hP
  set ρ : E →* Equiv.Perm ↥Y :=
    (MulAction.toPermHom X ↥Y).comp (Subgroup.inclusion hEX) with hρdef
  have hker : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    have hfixY : ∀ W : ↥Y, (⟨(k : MulAut U), hEX k.2⟩ : X) • W = W := by
      intro W
      have h2 := congrArg (fun σ : Equiv.Perm ↥Y => σ W) (MonoidHom.mem_ker.1 hk)
      rw [hρdef] at h2
      simp only [MonoidHom.comp_apply, MulAction.toPermHom_apply] at h2
      exact h2
    set κ : MulAut U := (k : MulAut U) with hκdef
    have hκ5 : κ ^ 5 = 1 := by
      have h := hEab.2 (k : MulAut U) k.2
      simpa [hκdef] using h
    have hmapW : ∀ W : ↥Y, (W : Subgroup U).map κ.toMonoidHom = (W : Subgroup U) := by
      intro W
      have h1 : (⟨(k : MulAut U), hEX k.2⟩ : X) • (W : Subgroup U) =
          (W : Subgroup U).map κ.toMonoidHom := by
        rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
        rfl
      have h2 : (⟨(k : MulAut U), hEX k.2⟩ : X) • (W : Subgroup U) = (W : Subgroup U) :=
        congrArg Subtype.val (hfixY W)
      rw [h1] at h2
      exact h2
    have hκfix : ∀ W ∈ Y, ∀ w ∈ W, κ w = w := by
      intro W hW w hw
      set H : Subgroup (MulAut U) := Subgroup.zpowers κ with hHdef
      letI : MulAction H U := MulAction.compHom (α := U) H.subtype
      have hH5 : Nat.card H ∣ 5 := by
        rw [hHdef, Nat.card_zpowers]
        exact orderOf_dvd_iff_pow_eq_one.2 hκ5
      have hκstab : κ ∈ MulAction.stabilizer (MulAut U) (W : Subgroup U) := by
        rw [MulAction.mem_stabilizer_iff, Subgroup.pointwise_smul_def]
        exact hmapW ⟨W, hW⟩
      have hHstab : H ≤ MulAction.stabilizer (MulAut U) (W : Subgroup U) :=
        Subgroup.zpowers_le.mpr hκstab
      have horbit_dvd : (MulAction.orbit H w).ncard ∣ Nat.card H := by
        have hidx : (MulAction.stabilizer H w).index = (MulAction.orbit H w).ncard :=
          MulAction.index_stabilizer H w
        rw [← hidx]
        exact ⟨Nat.card (MulAction.stabilizer H w),
          (Subgroup.index_mul_card (H := MulAction.stabilizer H w)).symm⟩
      have horbit_le : (MulAction.orbit H w).ncard ≤ 4 := by
        have hsub : MulAction.orbit H w ⊆ (W : Set U) := by
          rintro x ⟨h, rfl⟩
          have hh : (h : MulAut U) • (W : Subgroup U) = (W : Subgroup U) :=
            MulAction.mem_stabilizer_iff.1 (hHstab h.2)
          have : (h : MulAut U) w ∈ ((h : MulAut U) • (W : Subgroup U) : Subgroup U) :=
            Subgroup.mem_map_of_mem _ hw
          rw [hh] at this
          exact this
        calc (MulAction.orbit H w).ncard ≤ (W : Set U).ncard := Set.ncard_le_ncard hsub
          _ = Nat.card W := by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
          _ = 4 := hcard W hW
      have horbit1 : (MulAction.orbit H w).ncard = 1 := by
        have hdvd5 : (MulAction.orbit H w).ncard ∣ 5 := horbit_dvd.trans hH5
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd5 with h | h
        · exact h
        · omega
      obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 horbit1
      have hw_orbit : w ∈ MulAction.orbit H w := ⟨1, one_smul _ _⟩
      have hxw : x = w := by rw [hx] at hw_orbit; exact hw_orbit.symm
      have hκw : κ • w ∈ MulAction.orbit H w :=
        ⟨⟨κ, Subgroup.mem_zpowers κ⟩, rfl⟩
      rw [hx, hxw] at hκw
      simpa using hκw
    have hκ1 : κ = 1 := by
      refine MulEquiv.ext fun u => ?_
      have hle : sSup Y ≤ fixV (Subgroup.zpowers κ) :=
        sSup_le fun W hW => fun w hw => by
          rw [mem_fixV]
          intro x hx
          have hκstabw : κ ∈ MulAction.stabilizer (MulAut U) w := by
            rw [MulAction.mem_stabilizer_iff]; exact hκfix W hW w hw
          have hxstab : x ∈ MulAction.stabilizer (MulAut U) w :=
            (Subgroup.zpowers_le.mpr hκstabw) hx
          exact MulAction.mem_stabilizer_iff.1 hxstab
      have hu : u ∈ sSup Y := hsup ▸ Subgroup.mem_top u
      have hfix := hle hu
      rw [mem_fixV] at hfix
      exact hfix κ (Subgroup.mem_zpowers κ)
    exact Subtype.ext (by rw [← hκdef]; exact hκ1)
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  have hcardE : Nat.card E ∣ Nat.card (Equiv.Perm ↥Y) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hdvd720 : Nat.card E ∣ 720 := by
    have h1 : Nat.card (Equiv.Perm ↥Y) = Nat.factorial Y.ncard := by
      rw [Nat.card_perm, Nat.card_coe_set_eq]
    rw [h1] at hcardE
    have hfac : Nat.factorial Y.ncard ∣ 720 := by
      have h : Nat.factorial 6 = 720 := by norm_num
      rw [← h]
      exact Nat.factorial_dvd_factorial hn
    exact hcardE.trans hfac
  rw [hn5] at hdvd720 ⊢
  have hn1 : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have h25 : 25 ∣ 720 := (pow_dvd_pow 5 h2).trans hdvd720
    norm_num at h25
  calc 5 ^ n ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 5 := by norm_num

private theorem s15_Thirteen_gap1_mbar_five_rank (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal]
    (hs : s15 D.M V₀ V hV L ≤ 6) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) ≤ 1 := by
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hpf := h125.pairFacts
  have hMs : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil hpf.le_normalizer (s15_Infra_le_normalizer_v1Sub h125 hV)
  let ψ : ↥D.M →* MulAut (vStar D.M V₀ V hV L) :=
    (actTil (v1Sub D.M V₀ V hV L) V hV).comp (Subgroup.inclusion hMs)
  have hkerψ : ψ.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf D.M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hpf.le_normalizer]
    constructor
    · intro hψ
      refine ⟨m.2, hMs m.2, ?_⟩
      change (actTil (v1Sub D.M V₀ V hV L) V hV) (Subgroup.inclusion hMs m) = 1
      simpa [ψ] using hψ
    · rintro ⟨-, hst, hact⟩
      show actTil (v1Sub D.M V₀ V hV L) V hV
        (Subgroup.inclusion hMs m) = 1
      rw [show Subgroup.inclusion hMs m = (⟨(m : G), hst⟩ : stabTil
        (v1Sub D.M V₀ V hV L) V) from Subtype.ext rfl]
      exact hact
  have hN : (F11.CTilde D.M V₀ V).subgroupOf D.M =
      (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf D.M := by
    rw [fifteen_two_cent D h1217 h151 hV]
  let f : F11.MBar11 D.M V₀ V →* MulAut (vStar D.M V₀ V hV L) :=
    QuotientGroup.lift ((F11.CTilde D.M V₀ V).subgroupOf D.M) ψ (by
      rw [hkerψ]
      exact le_of_eq hN)
  have hf_inj : Function.Injective f := by
    rw [QuotientGroup.injective_lift_iff]
    exact hN.trans hkerψ.symm
  have hrange : f.range = Mbar D.M (v1Sub D.M V₀ V hV L) V hV := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H m => exact ⟨⟨(m : G), hMs m.2⟩, m.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨QuotientGroup.mk ⟨(g : G), hg⟩, ?_⟩
      show actTil (v1Sub D.M V₀ V hV L) V hV
        (Subgroup.inclusion hMs ⟨(g : G), hg⟩) =
        actTil (v1Sub D.M V₀ V hV L) V hV g
      exact congrArg (actTil (v1Sub D.M V₀ V hV L) V hV) (Subtype.ext rfl)
  have hle : CFSG.Open.pRank 5 (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) ≤
      CFSG.Open.pRank 5 f.range := by
    have h1 := CFSG.SectionRank.pRank_le_map (p := 5) (by norm_num) f hf_inj
      (⊤ : Subgroup (F11.MBar11 D.M V₀ V))
    rwa [Subgroup.map_top f] at h1
  have hsmall : CFSG.Open.pRank 5 f.range ≤ 1 :=
    s15_Thirteen_pRank_five_le_one_of_permutes
      (U := vStar D.M V₀ V hV L) (Y := wStarConj D.M V₀ V hV L) (X := f.range)
      (fifteen_two_directSum D h1217 h151 hV hL).2
      (fun φ hφ W hW => by
        rw [hrange] at hφ
        exact s15_Six_map_mem_wStarConj h125 hV hφ hW)
      (fun W hW => by
        have hpg : IsPGroup 2 ↥W := isPGroup_two_of_sq_eq_one fun a => Subtype.ext (by
          simpa [pow_two] using
            s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV a.1)
        rw [card_eq_two_pow_mSub hpg]
        change 2 ^ rk ↥W = 4
        rw [s15_Two_rk_wStarConj h151 hV hW, hγ]
        norm_num)
      (by rw [ncard_wStarConj D h151 hV]; exact hs)
  exact hle.trans hsmall

theorem s15_Thirteen_gap1_small (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h1217 : R1217 D) (h127 : R127 D) (h1111 : R1111 D)
    (h115 : F11.R115 D) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2) (hk : D.k = 2)
    (h5 : 5 ∈ D.sig) (hs : s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6)
    (hcard : Nat.card V₀ ≤ 4) : False := by
  have hpf := h.hyp151.hyp125.pairFacts
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    WeakClosure81.cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp151.hyp125
  obtain ⟨-, hle, hge⟩ := h115 V₀ V hH11 hcard 5 h5
  have hle' : CFSG.Open.pRank 5 D.M - 1 ≤
      CFSG.Open.pRank 5 (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := hle
  have hrank := s15_Thirteen_gap1_mbar_five_rank D h1217 h hV hL hγ
    (by rcases hs with h | h <;> omega)
  omega

theorem s15_Thirteen_false_of_gamma_two_of_eight_le_card (D : Data G)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) (h1217 : R1217 D) (h127 : R127 D)
    (h1110 : R1110G D) (h77 : F07.R77Eq D) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hγ : gamma15 D.M V₀ V hV L = 2) (hs : 3 ≤ s15 D.M V₀ V hV L)
    (hcard : 8 ≤ Nat.card V₀) : False := by
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    intro hL
    have h0 := s15_Three_wStar_eq_bot h hV hL
    have hγ0 : gamma15 D.M V₀ V hV L = 0 := by
      unfold gamma15
      rw [h0]
      exact rk_bot
    omega
  have hpf := h.hyp125.pairFacts
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    WeakClosure81.cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨n, hsn, Xbar, hXn, hXe, hXc, hXd⟩ := s15_Thirteen_exists_xbar D h1217 h hV hL hγ
  have h11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hlt := s11_TenP_card_lt_eight D hSg h1219 h1110 h77 h11 Nat.prime_three (by norm_num)
    (n := n) (by omega) Xbar hXn hXe hXc hXd
  omega

theorem s15_Thirteen_gap1_large (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h1217 : R1217 D) (h127 : R127 D) (h1111 : R1111 D)
    (h115 : F11.R115 D) (h1110 : R1110G D) (h77 : F07.R77Eq D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2) (hk : D.k = 2)
    (h5 : 5 ∈ D.sig) (hs : s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6)
    (hcard : 4 < Nat.card V₀) : False := by
  have hs3 : 3 ≤ s15 D.M V₀ V hV L := by rcases hs with hs | hs <;> omega
  obtain ⟨k, hk2⟩ := IsPGroup.iff_card.mp h.hyp151.hyp125.pairFacts.elemAbelian₀.isPGroup
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hk2] at hcard ⊢
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  exact s15_Thirteen_false_of_gamma_two_of_eight_le_card D hSg h1219 h1217 h127 h1110 h77
    h.hyp151 hV hγ hs3 h8

theorem s15_Thirteen_gap1 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1217 : R1217 D) (h127 : R127 D) (h1111 : R1111 D) (h115 : F11.R115 D)
    (h1110 : R1110G D) (h77 : F07.R77Eq D) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2) (hk : D.k = 2)
    (h5 : 5 ∈ D.sig) (hs : s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6) : False := by
  by_cases hcard : Nat.card V₀ ≤ 4
  · exact s15_Thirteen_gap1_small D hSg h1219 h1217 h127 h1111 h115 h hV hL hγ hk h5 hs hcard
  · exact s15_Thirteen_gap1_large D hSg h1219 h1217 h127 h1111 h115 h1110 h77 h hV hL hγ hk h5
      hs (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
