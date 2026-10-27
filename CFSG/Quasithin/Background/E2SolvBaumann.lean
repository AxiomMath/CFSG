module

public import CFSG.Quasithin.Background.E2SolvStruct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}
  {H T M : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem le_normalizer_alpha (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    H ≤ Subgroup.normalizer
      (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))) : Set G) := by
  rw [h.inf_centralizer_eq_pCoreOf hred (not_le_centralizer h hJ)]
  exact (le_normalizer_pCoreOf 2 H).trans
    (normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf (thompsonJ X))
      (fun φ X => by rw [omegaOneCenterOf_map_mulEquiv, thompsonJ_map_mulEquiv]) _)

theorem not_strong (hred : IsTwoReducedIn H V) (hsolv : Group.IsSolvable H)
    (hT : IsSylowTwoOf T H) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h)
  obtain ⟨hFF, -⟩ := B2_7_of_not_le hV hred.1 hHN hJH
  have hsolvX := isSolvable_autI hV hHN hsolv
  have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 => eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
  have hq := (B1_8_3 hW hsolvX hO2 hFF).2
  exact fun B hB => hq B (isStrongFFStarOffender_mono (autI_mono hV hT.1) hB)

theorem commutator_alpha_mem_of_isMaxElemAbelian (hred : IsTwoReducedIn H V)
    (hsolv : Group.IsSolvable H) (hT : IsSylowTwoOf T H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) {x a : G}
    (hx : x ∈ omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))))
    (ha : a ∈ A) : x * a * x⁻¹ * a⁻¹ ∈ V := by
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hred.2.1
  obtain ⟨-, -, -, h4⟩ := alpha_facts hred.2.2.1 hVT hTN
    (not_strong (hV := hred.2.2.1) hred hsolv hT hJ)
  have hxA := h4 A hA hx
  have hAN : A ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (hA.1.trans hTN)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hxA
  obtain ⟨c, hc, v, hv, rfl⟩ := hxA
  have hca : c * a = a * c := isElemAbelian_comm hA.2.1 hc.1 ha
  have hcv : ∀ w ∈ V, c * w = w * c := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hav : a * v⁻¹ * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hTN (hA.1 ha)) _).mp (V.inv_mem hv)
  have hw : v * (a * v⁻¹ * a⁻¹) ∈ V := V.mul_mem hv hav
  have e : c * v * a * (c * v)⁻¹ * a⁻¹ = c * (v * (a * v⁻¹ * a⁻¹)) * c⁻¹ := by
    calc c * v * a * (c * v)⁻¹ * a⁻¹ = c * v * a * v⁻¹ * (c⁻¹ * a⁻¹) := by group
      _ = c * v * a * v⁻¹ * (a⁻¹ * c⁻¹) := by
          rw [← mul_inv_rev, ← mul_inv_rev, hca]
      _ = c * (v * (a * v⁻¹ * a⁻¹)) * c⁻¹ := by group
  rw [e, hcv _ hw, mul_inv_cancel_right]
  exact hw

omit [Finite G] in
@[expose] def commCentralizer (Y V : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (V : Set G) ∧ ∀ x ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ V}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hy₁ hy₂, fun x hx => ?_⟩
    have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
        (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
    rw [e]
    exact V.mul_mem (h₁ x hx) ((Subgroup.mem_normalizer_iff.mp hy₁ _).mp (h₂ x hx))
  inv_mem' := by
    rintro y ⟨hy, h₁⟩
    refine ⟨Subgroup.inv_mem _ hy, fun x hx => ?_⟩
    have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) _).mp (V.inv_mem (h₁ x hx))

omit [Finite G] in
theorem mem_commCentralizer {Y : Subgroup G} {y : G} :
    y ∈ commCentralizer Y V ↔
      y ∈ Subgroup.normalizer (V : Set G) ∧ ∀ x ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ V := Iff.rfl

omit [Finite G] in
theorem conj_mem_commCentralizer {Y : Subgroup G} {h y : G}
    (hhY : h ∈ Subgroup.normalizer (Y : Set G)) (hhV : h ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ commCentralizer Y V) : h * y * h⁻¹ ∈ commCentralizer Y V := by
  obtain ⟨hyN, hyc⟩ := hy
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hhV hyN) (Subgroup.inv_mem _ hhV),
    fun x hx => ?_⟩
  have hx' : h⁻¹ * x * h ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhY) x).mp hx
    simpa [mul_assoc] using this
  have e : x * (h * y * h⁻¹) * x⁻¹ * (h * y * h⁻¹)⁻¹ =
      h * ((h⁻¹ * x * h) * y * (h⁻¹ * x * h)⁻¹ * y⁻¹) * h⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hhV _).mp (hyc _ hx')

theorem cjSub_thompsonJ_le_commCentralizer (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hsolv : Group.IsSolvable H) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    {y : G} (hy : y ∈ H) :
    cjSub y (thompsonJ T) ≤
      commCentralizer (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)))) V := by
  have hT := h.isSylow
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hred.2.1
  have hJle : thompsonJ T ≤
      commCentralizer (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)))) V := by
    refine iSup₂_le fun A hA a ha => ⟨hTN (hA.1 ha), fun x hx => ?_⟩
    exact commutator_alpha_mem_of_isMaxElemAbelian hred hsolv hT hJ hA hx ha
  intro z hz
  rw [mem_cjSub] at hz
  have := conj_mem_commCentralizer (le_normalizer_alpha h hred hJ hy) (hred.2.1 hy) (hJle hz)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {M' : Type*} [Group M'] {t x : M'} (ht : t ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨q, r, hr, hk⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ k = 2 * q + r :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  have h2 : t ^ (2 : ℤ) = 1 := by simpa [zpow_two, pow_two] using ht
  rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases hr with rfl | rfl
  · left
    simp
  · right
    simp

theorem Blocks.le_sup_zpowers (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) {t t' : MulAut (IntMod V hV)} (ht : t ∈ L) (ht' : t' ∈ L)
    (ht2 : orderOf t = 2) (ht'2 : orderOf t' = 2) (hne : t ≠ t') :
    L ≤ Subgroup.zpowers t ⊔ Subgroup.zpowers t' := by
  set Z := Subgroup.zpowers t ⊔ Subgroup.zpowers t' with hZ
  have hZL : Z ≤ L := sup_le (Subgroup.zpowers_le.2 ht) (Subgroup.zpowers_le.2 ht')
  have h2 : 2 ∣ Nat.card Z := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers t ≤ Z)
    rwa [Nat.card_zpowers, ht2] at this
  have h6 : Nat.card Z ∣ 6 := by
    have := Subgroup.card_dvd_of_le hZL
    rwa [B.card_eq hL] at this
  have hgt : 2 < Nat.card Z := by
    by_contra hle
    push Not at hle
    have heq : Subgroup.zpowers t = Z :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, ht2]; exact hle)
    have hmem : t' ∈ Subgroup.zpowers t := heq ▸ (le_sup_right : Subgroup.zpowers t' ≤ Z)
      (Subgroup.mem_zpowers t')
    have htsq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    rcases eq_one_or_eq_of_mem_zpowers htsq hmem with h1 | h1
    · rw [h1, orderOf_one] at ht'2
      norm_num at ht'2
    · exact hne h1.symm
  have hZ6 : Nat.card Z = 6 := by
    have hle : Nat.card Z ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    interval_cases hc : Nat.card Z <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hZL (by rw [hZ6, B.card_eq hL])).ge

theorem Blocks.conj_ne (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) {t f : MulAut (IntMod V hV)} (ht : t ∈ L) (hf : f ∈ L) (ht2 : orderOf t = 2)
    (hf3 : orderOf f = 3) :
    f * t * f⁻¹ ∈ L ∧ orderOf (f * t * f⁻¹) = 2 ∧ t ≠ f * t * f⁻¹ := by
  refine ⟨L.mul_mem (L.mul_mem hf ht) (L.inv_mem hf), ?_, fun he => ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]
  · apply B.mul_ne_mul hL ht hf ht2 hf3
    calc t * f = f * t * f⁻¹ * f := by rw [← he]
      _ = f * t := by group

theorem Blocks.exists_twoResidual_le (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set G) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T) := by
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  obtain ⟨gs, hgsK, hgsL⟩ : ∃ gs ∈ autI hV (twoResidual H), ∀ L ∈ I,
      L ≤ autI hV (thompsonJ T) ⊔ (autI hV (thompsonJ T)).map (MulAut.conj gs).toMonoidHom := by
    have hloc : ∀ {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) {t f : MulAut (IntMod V hV)},
        t ∈ L → t ∈ autI hV (thompsonJ T) → orderOf t = 2 → f ∈ L → orderOf f = 3 →
        ∀ gs : MulAut (IntMod V hV), gs * t * gs⁻¹ = f * t * f⁻¹ →
          L ≤ autI hV (thompsonJ T) ⊔
            (autI hV (thompsonJ T)).map (MulAut.conj gs).toMonoidHom := by
      intro L hL t f htL htJ ht2 hfL hf3 gs hgs
      obtain ⟨hcL, hc2, hne⟩ := B.conj_ne hL htL hfL ht2 hf3
      refine (B.le_sup_zpowers hL htL hcL ht2 hc2 hne).trans (sup_le_sup
        (Subgroup.zpowers_le.2 htJ) (Subgroup.zpowers_le.2 ?_))
      rw [← hgs]
      exact ⟨t, htJ, rfl⟩
    rcases B.eq_singleton_or_pair h hsolv hSQT hred hJ with ⟨L₁, hL₁, hI⟩ |
      ⟨L₁, hL₁, L₂, hL₂, hne, hI⟩
    · obtain ⟨t₁, ht₁L, -, ht₁J, ht₁2⟩ := B.exists_orderOf_eq_two hred hT hL₁
      obtain ⟨f₁, hf₁L, hf₁K, hf₁3⟩ := B.exists_orderOf_eq_three hL₁
      refine ⟨f₁, hf₁K, fun L hL => ?_⟩
      rw [hI L hL]
      exact hloc hL₁ ht₁L ht₁J ht₁2 hf₁L hf₁3 f₁ rfl
    · obtain ⟨t₁, ht₁L, -, ht₁J, ht₁2⟩ := B.exists_orderOf_eq_two hred hT hL₁
      obtain ⟨f₁, hf₁L, hf₁K, hf₁3⟩ := B.exists_orderOf_eq_three hL₁
      obtain ⟨t₂, ht₂L, -, ht₂J, ht₂2⟩ := B.exists_orderOf_eq_two hred hT hL₂
      obtain ⟨f₂, hf₂L, hf₂K, hf₂3⟩ := B.exists_orderOf_eq_three hL₂
      refine ⟨f₁ * f₂, Subgroup.mul_mem _ hf₁K hf₂K, fun L hL => ?_⟩
      have c12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := fun a ha b hb => B.comm hL₁ hL₂ hne ha hb
      rcases hI L hL with rfl | rfl
      · refine hloc hL₁ ht₁L ht₁J ht₁2 hf₁L hf₁3 (f₁ * f₂) ?_
        have e : f₂ * t₁ = t₁ * f₂ := (c12 t₁ ht₁L f₂ hf₂L).symm
        calc f₁ * f₂ * t₁ * (f₁ * f₂)⁻¹ = f₁ * (f₂ * t₁) * f₂⁻¹ * f₁⁻¹ := by group
          _ = f₁ * (t₁ * f₂) * f₂⁻¹ * f₁⁻¹ := by rw [e]
          _ = f₁ * t₁ * f₁⁻¹ := by group
      · refine hloc hL₂ ht₂L ht₂J ht₂2 hf₂L hf₂3 (f₁ * f₂) ?_
        have hc : f₂ * t₂ * f₂⁻¹ ∈ L := L.mul_mem (L.mul_mem hf₂L ht₂L) (L.inv_mem hf₂L)
        have e : f₁ * (f₂ * t₂ * f₂⁻¹) = (f₂ * t₂ * f₂⁻¹) * f₁ := c12 f₁ hf₁L _ hc
        calc f₁ * f₂ * t₂ * (f₁ * f₂)⁻¹ = f₁ * (f₂ * t₂ * f₂⁻¹) * f₁⁻¹ := by group
          _ = (f₂ * t₂ * f₂⁻¹) * f₁ * f₁⁻¹ := by rw [e]
          _ = f₂ * t₂ * f₂⁻¹ := by group
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hgsK
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := g.2
  set I₀ := thompsonJ T ⊔ cjSub (g : G) (thompsonJ T) with hI₀
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hT.1
  have hI₀H : I₀ ≤ H := by
    refine sup_le hJTH fun z hz => ?_
    rw [mem_cjSub] at hz
    have := H.mul_mem (H.mul_mem (hKH hgK) (hJTH hz)) (H.inv_mem (hKH hgK))
    simpa [mul_assoc] using this
  have hKI : autI hV (twoResidual H) ≤ autI hV I₀ := by
    rw [hI₀, autI_sup hV ((thompsonJ_le_self T).trans (hT.1.trans hHN))
      (fun z hz => hHN (hI₀H (Subgroup.mem_sup_right hz))), ← autI_cjSub hV hgN]
    calc autI hV (twoResidual H) ≤ autI hV (thompsonJ H) :=
          autI_mono hV (twoResidual_le_thompsonJ h hred hJ)
      _ = ⨆ L ∈ I, L := B.eq
      _ ≤ _ := iSup₂_le fun L hL => hgsL L hL
  have hKIJ : twoResidual H ≤ I₀ ⊔ kerIn M H := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := hHN (hKH hk)
    obtain ⟨i, hiI, hik⟩ := (mem_autI hV).1 (hKI (convI_mem_autI hV hk hkN))
    have hc : (i : G)⁻¹ * k ∈ Subgroup.centralizer (V : Set G) := by
      have := (convI_eq_one_iff hV (i⁻¹ * ⟨k, hkN⟩)).1 (by rw [map_mul, map_inv, hik,
        inv_mul_cancel])
      simpa using this
    have hiH : (i : G) ∈ H := hI₀H hiI
    have hcJ : (i : G)⁻¹ * k ∈ kerIn M H :=
      h.inf_centralizer_le_kerIn hred (not_le_centralizer h hJ)
        ⟨H.mul_mem (H.inv_mem hiH) (hKH hk), hc⟩
    have : k = (i : G) * ((i : G)⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hiI) (Subgroup.mem_sup_right hcJ)
  have hKIQ := h.twoResidual_le_sup_pCoreOf hsolv hI₀H hKIJ
  have hI₀N : I₀ ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hI₀H.trans (le_normalizer_pCoreOf 2 H)
  have hcl : conjClosure (thompsonJ T) H ≤ I₀ := by
    refine conjClosure_le fun y hy z hz => ?_
    have hH : H = twoResidual H ⊔ T := by rw [sup_comm]; exact (sup_twoResidual_eq hT).symm
    have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
      hT.1.trans (le_normalizer_twoResidual H)
    have hy' : y ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by rw [← hH]; exact hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hy'
    obtain ⟨k, hk, t, ht, rfl⟩ := hy'
    have hk' : k ∈ ((I₀ ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hKIQ hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hI₀N] at hk'
    obtain ⟨i, hi, q, hq, rfl⟩ := hk'
    have hqT : q ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT hq
    have hJTN : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    have hz' : (q * t) * z * (q * t)⁻¹ ∈ thompsonJ T :=
      (Subgroup.mem_normalizer_iff.mp (hJTN (T.mul_mem hqT ht)) z).mp hz
    have e : i * q * t * z * (i * q * t)⁻¹ = i * ((q * t) * z * (q * t)⁻¹) * i⁻¹ := by group
    rw [e]
    exact I₀.mul_mem (I₀.mul_mem hi (Subgroup.mem_sup_left hz')) (I₀.inv_mem hi)
  have hclJ : ¬ conjClosure (thompsonJ T) H ≤ kerIn M H := by
    intro hle
    apply hJ
    have h1 : thompsonJ T ≤ pCoreOf 2 H :=
      h.le_pCoreOf_of_isPGroup_of_le_kerIn (hT.2.1.to_le (thompsonJ_le_self T))
        ((le_conjClosure _ _).trans hle)
    exact h1.trans (MinParabolic.pCoreOf_le_centralizer hred)
  have hclH : conjClosure (thompsonJ T) H ≤ H :=
    conjClosure_le fun y hy z hz => H.mul_mem (H.mul_mem hy (hJTH hz)) (H.inv_mem hy)
  have hKcl := (h.le_kerIn_or_twoResidual_le hclH (le_normalizer_conjClosure _ _)).resolve_left
    hclJ
  exact ⟨g, hgK, hgN, hKcl.trans hcl⟩

theorem Blocks.exists_fix_thompsonJ (B : Blocks hV H 𝓗 I) (hT : IsSylowTwoOf T H)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ c : Subgroup (MulAut (IntMod V hV)) → IntMod V hV, ∀ L ∈ I,
      c L ∈ commSub ⊤ L ∧ c L ≠ 1 ∧ c L ∈ fixV (autI hV (thompsonJ T)) := by
  classical
  have hex : ∀ L, ∃ t : MulAut (IntMod V hV), L ∈ I →
      t ∈ L ∧ t ∈ autI hV (thompsonJ T) ∧ orderOf t = 2 := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨t, htL, -, htJ, ht2⟩ := B.exists_orderOf_eq_two hred hT hL
      exact ⟨t, fun _ => ⟨htL, htJ, ht2⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose t ht using hex
  have hexc : ∀ L, ∃ c : IntMod V hV, L ∈ I → c ∈ commSub ⊤ L ∧ c ≠ 1 ∧ t L c = c := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨c, hc, hc1, htc⟩ := B.exists_fix hL (ht L hL).1 (ht L hL).2.2
      exact ⟨c, fun _ => ⟨hc, hc1, htc⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose c hc using hexc
  have hJTeq := B.autI_thompsonJ_eq hT hsolv hred hJ t (fun L hL => ht L hL)
  refine ⟨c, fun L hL => ⟨(hc L hL).1, (hc L hL).2.1, fun y hy => ?_⟩⟩
  rw [hJTeq] at hy
  have hle : (⨆ L' ∈ I, Subgroup.zpowers (t L')) ≤
      MulAction.stabilizer (MulAut (IntMod V hV)) (c L) := by
    refine iSup₂_le fun L' hL' => Subgroup.zpowers_le.2 ?_
    rw [MulAction.mem_stabilizer_iff]
    by_cases hLL : L' = L
    · subst hLL
      exact (hc L' hL).2.2
    · exact B.hb.triv L' (B.sub hL') L (B.sub hL) hLL (t L') (ht L' hL').1 (c L) (hc L hL).1
  exact hle hy

theorem Blocks.two_mul_rkIdx_le (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤ rkIdx (fixV (autI hV (twoResidual H))) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hT := h.isSylow
  set F := fixV (autI hV (twoResidual H)) with hF
  set C := fixV (autI hV (thompsonJ T)) with hC
  obtain ⟨c, hc⟩ := B.exists_fix_thompsonJ hT hsolv hred hJ
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq, ← B.fixV_twoResidual h hsolv hSQT hred hJ] at hdec
  have hrk4 : ∀ L ∈ I, rk ↥(commSub (⊤ : Subgroup (IntMod V hV)) L) = 2 := fun L hL => by
    unfold rk
    rw [B.hb.card_comm L (B.sub hL), show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hrkc : ∀ L ∈ I, rk ↥(Subgroup.zpowers (c L)) = 1 := fun L hL => by
    unfold rk
    rw [Nat.card_zpowers, orderOf_eq_prime (hW _) (hc L hL).2.1]
    simp
  have hFC : F ≤ C := by
    rw [hF, B.fixV_twoResidual h hsolv hSQT hred hJ]
    exact B1.fixV_le_fixV (autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT))
  have h1 := rk_add_rkIdx F
  have h2 := rk_add_rkIdx C
  rcases B.eq_singleton_or_pair h hsolv hSQT hred hJ with ⟨L₁, hL₁, hI⟩ |
    ⟨L₁, hL₁, L₂, hL₂, hne, hI⟩
  · rw [iSup_eq_of_singleton hL₁ hI] at hdec
    have e1 := rk_sup_add_rk_inf F (commSub ⊤ L₁)
    rw [hdec.1, hdec.2, rk_top, rk_bot, hrk4 L₁ hL₁] at e1
    have hcV : Subgroup.zpowers (c L₁) ≤ commSub ⊤ L₁ := Subgroup.zpowers_le.2 (hc L₁ hL₁).1
    have hinf : F ⊓ Subgroup.zpowers (c L₁) = ⊥ :=
      le_bot_iff.1 (hdec.2 ▸ inf_le_inf_left F hcV)
    have e2 := rk_sup_add_rk_inf F (Subgroup.zpowers (c L₁))
    rw [hinf, rk_bot, hrkc L₁ hL₁] at e2
    have e3 : rk ↥(F ⊔ Subgroup.zpowers (c L₁)) ≤ rk ↥C :=
      rk_mono (sup_le hFC (Subgroup.zpowers_le.2 (hc L₁ hL₁).2.2))
    omega
  · rw [iSup_eq_of_pair hL₁ hL₂ hI] at hdec
    have h12 : commSub (⊤ : Subgroup (IntMod V hV)) L₁ ⊓ commSub ⊤ L₂ = ⊥ := by
      refine le_bot_iff.1 ((inf_le_inf_left _ ?_).trans
        (B.hb.commSub_inf_biSup_ne_eq_bot hW (B.sub hL₁)).le)
      exact le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut (IntMod V hV))) (_ : H' ∈ 𝓗) =>
        ⨆ (_ : H' ≠ L₁), commSub (⊤ : Subgroup (IntMod V hV)) H') L₂ (B.sub hL₂)
        (le_iSup_of_le (Ne.symm hne) le_rfl)
    have e1 := rk_sup_add_rk_inf F (commSub ⊤ L₁ ⊔ commSub ⊤ L₂)
    rw [hdec.1, hdec.2, rk_top, rk_bot] at e1
    have e1' := rk_sup_add_rk_inf (commSub (⊤ : Subgroup (IntMod V hV)) L₁) (commSub ⊤ L₂)
    rw [h12, rk_bot, hrk4 L₁ hL₁, hrk4 L₂ hL₂] at e1'
    have hc₁ : Subgroup.zpowers (c L₁) ≤ commSub ⊤ L₁ := Subgroup.zpowers_le.2 (hc L₁ hL₁).1
    have hc₂ : Subgroup.zpowers (c L₂) ≤ commSub ⊤ L₂ := Subgroup.zpowers_le.2 (hc L₂ hL₂).1
    have hinf : F ⊓ (Subgroup.zpowers (c L₁) ⊔ Subgroup.zpowers (c L₂)) = ⊥ :=
      le_bot_iff.1 (hdec.2 ▸ inf_le_inf_left F (sup_le_sup hc₁ hc₂))
    have hinf' : Subgroup.zpowers (c L₁) ⊓ Subgroup.zpowers (c L₂) = ⊥ :=
      le_bot_iff.1 (h12 ▸ inf_le_inf hc₁ hc₂)
    have e2 := rk_sup_add_rk_inf F (Subgroup.zpowers (c L₁) ⊔ Subgroup.zpowers (c L₂))
    have e2' := rk_sup_add_rk_inf (Subgroup.zpowers (c L₁)) (Subgroup.zpowers (c L₂))
    rw [hinf', rk_bot, hrkc L₁ hL₁, hrkc L₂ hL₂] at e2'
    rw [hinf, rk_bot] at e2
    have e3 : rk ↥(F ⊔ (Subgroup.zpowers (c L₁) ⊔ Subgroup.zpowers (c L₂))) ≤ rk ↥C :=
      rk_mono (sup_le hFC (sup_le (Subgroup.zpowers_le.2 (hc L₁ hL₁).2.2)
        (Subgroup.zpowers_le.2 (hc L₂ hL₂).2.2)))
    omega

omit [Finite G] in
@[expose] def valHom (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' := fun a b => IntMod.val_mul a b

omit [Finite G] in
theorem map_valHom_top : (⊤ : Subgroup (IntMod V hV)).map (valHom hV) = V := by
  ext x
  constructor
  · rintro ⟨v, -, rfl⟩
    exact v.val_mem
  · intro hx
    exact ⟨IntMod.mk hV ⟨x, hx⟩, trivial, rfl⟩

omit [Finite G] in
theorem map_valHom_fixV {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    (fixV (autI hV A)).map (valHom hV) = V ⊓ Subgroup.centralizer (A : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.val_mem, (mem_fixV_autI hV hA v).1 hv⟩
  · rintro ⟨hxV, hxC⟩
    exact ⟨IntMod.mk hV ⟨x, hxV⟩, (mem_fixV_autI hV hA _).2 hxC, rfl⟩

omit [Finite G] in
theorem map_valHom_commSub_le {A : Subgroup G} :
    (commSub ⊤ (autI hV A)).map (valHom hV) ≤ ⁅V, A⁆ := by
  rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
  rintro _ ⟨φ, hφ, w, -, rfl⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  show (convI hV g w * w⁻¹).val ∈ ⁅V, A⁆
  rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, Subgroup.commutator_comm,
    ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hg w.val_mem

theorem W_decomp_two {W X₁ X₂ L J : Subgroup G} (hW : IsElemAbelian 2 W) (hVW : V ≤ W)
    (hIW : X₁ ⊔ X₂ ≤ Subgroup.normalizer (W : Set G))
    (hIV : X₁ ⊔ X₂ ≤ Subgroup.normalizer (V : Set G)) (hLI : L ≤ X₁ ⊔ X₂)
    (hd : rkIdx (fixV (autI hV X₁)) + rkIdx (fixV (autI hV X₂)) ≤ rkIdx (fixV (autI hV L)))
    (hX₁ : ∃ g ∈ X₁ ⊔ X₂, cjSub g X₁ ≤ J) (hX₂ : ∃ g ∈ X₁ ⊔ X₂, cjSub g X₂ ≤ J)
    (hWJ : W ≤ (W ⊓ Subgroup.centralizer (J : Set G)) ⊔ V) :
    W ⊓ Subgroup.centralizer (L : Set G) =
        W ⊓ Subgroup.centralizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) ∧
      W = V ⊔ (W ⊓ Subgroup.centralizer (L : Set G)) := by
  set I := X₁ ⊔ X₂ with hI
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => isElemAbelian_comm hW ha hb
  have hrank : ∀ {X : Subgroup G}, X ≤ I → (∃ g ∈ I, cjSub g X ≤ J) →
      rkIdx (fixV (autI hW X)) = rkIdx (fixV (autI hV X)) := by
    rintro X hXI ⟨g, hg, hgX⟩
    have e1 := rkIdx_fixV_autI hW (hXI.trans hIW)
    have e2 := rkIdx_fixV_autI hV (hXI.trans hIV)
    have e4 := rk_inf_centralizer_cjSub (hIW hg) X
    have e5 := rk_inf_centralizer_cjSub (hIV hg) X
    have hWY : W = (W ⊓ Subgroup.centralizer (cjSub g X : Set G)) ⊔ V :=
      le_antisymm (hWJ.trans (sup_le_sup_right
        (inf_le_inf_left W (Subgroup.centralizer_le hgX)) V)) (sup_le inf_le_left hVW)
    have e3 := rk_sup_add_rk_inf_of_commute (A := W ⊓ Subgroup.centralizer (cjSub g X : Set G))
      (B := V) (fun a ha b hb => hcommW a ha.1 b (hVW hb))
    have hinf : (W ⊓ Subgroup.centralizer (cjSub g X : Set G)) ⊓ V =
        V ⊓ Subgroup.centralizer (cjSub g X : Set G) := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hVW h.1, h.2⟩, h.1⟩⟩
    rw [← hWY, hinf] at e3
    omega
  have hX₁I : X₁ ≤ I := le_sup_left
  have hX₂I : X₂ ≤ I := le_sup_right
  have hLNW : L ≤ Subgroup.normalizer (W : Set G) := hLI.trans hIW
  have f1 := rkIdx_fixV_autI hW hLNW
  have f2 := rkIdx_fixV_autI hV (hLI.trans hIV)
  have f3 := rk_sup_add_rk_inf_of_commute (A := V) (B := W ⊓ Subgroup.centralizer (L : Set G))
    (fun a ha b hb => hcommW a (hVW ha) b hb.1)
  have f4 : V ⊓ (W ⊓ Subgroup.centralizer (L : Set G)) =
      V ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hVW h.1, h.2⟩⟩
  have f5 : rk ↥(V ⊔ (W ⊓ Subgroup.centralizer (L : Set G))) ≤ rk ↥W :=
    rk_mono (sup_le hVW inf_le_left)
  rw [f4] at f3
  have r1 := hrank hX₁I hX₁
  have r2 := hrank hX₂I hX₂
  have hle2 : rkIdx (fixV (autI hV L)) ≤ rkIdx (fixV (autI hW L)) := by omega
  set X : Bool → Subgroup (MulAut (IntMod W hW)) := fun b => cond b (autI hW X₁) (autI hW X₂)
    with hX
  have hsup : (⨆ b, X b) = autI hW I := by
    rw [iSup_bool_eq, hI, autI_sup hW (hX₁I.trans hIW) (hX₂I.trans hIW)]
    rfl
  have hL' : autI hW L ≤ ⨆ b, X b := by
    rw [hsup]
    exact autI_mono hW hLI
  have hsum : ∑ b, rkIdx (fixV (X b)) ≤ rkIdx (fixV (autI hW L)) := by
    rw [Fintype.sum_bool]
    show rkIdx (fixV (autI hW X₁)) + rkIdx (fixV (autI hW X₂)) ≤ _
    omega
  obtain ⟨h17a, h17b⟩ := B2_17_aut (fun v : IntMod W hW => IntMod.sq_eq_one v) X hL' hsum
  rw [hsup] at h17a
  rw [Fintype.sum_bool] at h17b
  change rkIdx (fixV (autI hW L)) = rkIdx (fixV (autI hW X₁)) + rkIdx (fixV (autI hW X₂))
    at h17b
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxW, hxL⟩
      refine ⟨hxW, ?_⟩
      have h1 := (mem_fixV_autI hW hLNW (IntMod.mk hW ⟨x, hxW⟩)).2 hxL
      rw [h17a] at h1
      exact (mem_fixV_autI hW hIW (IntMod.mk hW ⟨x, hxW⟩)).1 h1
    · rintro ⟨hxW, hxI⟩
      refine ⟨hxW, ?_⟩
      have h1 := (mem_fixV_autI hW hIW (IntMod.mk hW ⟨x, hxW⟩)).2 hxI
      rw [← h17a] at h1
      exact (mem_fixV_autI hW hLNW (IntMod.mk hW ⟨x, hxW⟩)).1 h1
  · symm
    refine eq_of_le_of_rk_le_of_isPGroup (isPGroup_of_isElemAbelian hW)
      (sup_le hVW inf_le_left) ?_
    omega

end E2

end CFSG.Quasithin
