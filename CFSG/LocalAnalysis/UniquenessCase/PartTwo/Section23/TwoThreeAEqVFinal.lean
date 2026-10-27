module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVInvolN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVOmegaBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeLNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreePackage
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeUZero
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveInst
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Holds
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem Ctx23L.barSub_L_ne_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hVne : c.V ≠ ⊥) :
    barSub (⊥ : Subgroup G) c.V (Ctx23L.isElemAbelian_V_basic c) c.L ≠ ⊥ := by
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) c.V :=
    le_inf ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  intro hbot
  have hLcent : c.L ≤ Subgroup.centralizer (c.V : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hmem : actTil (⊥ : Subgroup G) c.V hV ⟨l, hLstab hl⟩ ∈
        barSub (⊥ : Subgroup G) c.V hV c.L :=
      actTil_mem_barSub (⊥ : Subgroup G) c.V hV hl (hLstab hl)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : l * v * l⁻¹ * v⁻¹ = 1 :=
      (actTil_eq_one_iff (⊥ : Subgroup G) c.V hV ⟨l, hLstab hl⟩).1 hmem v hv
    have h2 : l * v * l⁻¹ = v := mul_inv_eq_one.1 h1
    calc v * l = (l * v * l⁻¹) * l := by rw [h2]
      _ = l * v := by group
  have hVle : c.V ≤ c.V ⊓ Subgroup.centralizer (c.L : Set G) := by
    refine le_inf le_rfl fun v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLcent hl) v hv).symm
  rw [Ctx23L.fixed_L_eq_bot c] at hVle
  exact hVne (le_bot_iff.mp hVle)

private theorem Ctx23L.even_card_Mbar_V {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hVne : c.V ≠ ⊥) :
    Even (Nat.card (Mbar c.N (⊥ : Subgroup G) c.V (Ctx23L.isElemAbelian_V_basic c))) := by
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  let H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) c.V hV)) :=
    barSub (⊥ : Subgroup G) c.V hV c.L
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) c.V :=
    le_inf ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hHcomm : ⁅H, H⁆ = H := barSub_commutator hV hLstab c.hL.1.2.1
  have hHne : H ≠ ⊥ := Ctx23L.barSub_L_ne_bot c hVne
  have hHnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHne
  haveI : Group.IsPerfect (H : Type) := Subgroup.isPerfect_iff.mpr hHcomm
  have hHnotodd : ¬ Odd (Nat.card ↥H) :=
    CFSG.CGT.PushingUpLit.LIT.Foote.not_odd_card_of_perfect (Q := ↥H)
  have hHeven : Even (Nat.card ↥H) := Nat.not_odd_iff_even.mp hHnotodd
  have hHM : H ≤ Mbar c.N (⊥ : Subgroup G) c.V hV := by
    rw [Mbar_eq_barSub hV c.N]
    exact barSub_mono (⊥ : Subgroup G) c.V hV (Ctx23L.L_le_N c)
  exact even_iff_two_dvd.mpr
    ((even_iff_two_dvd.mp hHeven).trans (Subgroup.card_dvd_of_le hHM))

private theorem Ctx23L.exists_actN_involution_rkIdx_eq_mBar {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hVne : c.V ≠ ⊥) :
    ∃ x : c.N, orderOf (actN c x) = 2 ∧
      rkIdx (fixV (Subgroup.zpowers (actN c x))) =
        mBar c.N (⊥ : Subgroup G) c.V (Ctx23L.isElemAbelian_V_basic c) := by
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  have hEven : Even (Nat.card (Mbar c.N (⊥ : Subgroup G) c.V hV)) :=
    Ctx23L.even_card_Mbar_V c hVne
  obtain ⟨s, hsMbar, hs2, hsrk⟩ :=
    CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam
      (Mbar c.N (⊥ : Subgroup G) c.V hV) hEven
  obtain ⟨x, hxN, hxeq⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV c.N s).1 hsMbar
  let xn : c.N := ⟨x, hxN⟩
  have hsx : actN c xn = s := by
    simpa [Ctx23L.actN, xn] using hxeq
  exact ⟨xn, by rw [hsx]; exact hs2, by rw [hsx]; exact hsrk⟩

private theorem Ctx23L.W23_1_le_V {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    W23_1 c ≤ c.V :=
  uc22p22v_conjClosure_le
    (c.hL0L.trans ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c)))
    (uc22p22v_le_conjClosure c.N D.Z)

private theorem Ctx23L.omega_bound_of_irrL {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h209 : S20_9 D)
    (hIrrL : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A),
      c.L ≤ Subgroup.normalizer (A : Set G) → ∀ {k : ℕ},
        NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k → IrrOn c.L A)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) {k : ℕ}
    (hnat : IsNaturalClassicalModule (barSub ⊥ A hA c.L) k)
    (h2k : 2 * k = c.n) (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k)
    (hNat : NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k) :
    ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k := by
  let hW : IsElemAbelian 2 (W23_1 c) :=
    IsElemAbelian.mono (Ctx23L.isElemAbelian_V_basic c) (Ctx23L.W23_1_le_V c)
  exact ⟨hW, Ctx23L.aBar_W23_1_le_of_omegaMinus c h1930 h209 hA hAV hAne hAN
    (hIrrL hA ((Ctx23L.L_le_N c).trans hAN) hNat) hOm hNat hW⟩

private theorem Ctx23L.normal_L_N_of_isNaturalClassicalModule {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {k : ℕ}
    (hnat : IsNaturalClassicalModule (barSub ⊥ A hA c.L) k)
    (hnorm : ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal) :
    (c.L.subgroupOf c.N).Normal := by
  refine Ctx23L.normal_L_N_of_barSub_normal c h208 h1930 hA hAN ?_ ?_
  · exact Ctx23L.not_le_centralizer_of_barSub_ne_bot c hA
      (Ctx23L.barSub_ne_bot_of_isNaturalClassicalModule c hA hnat)
  · simpa [Mbar_eq_barSub hA c.N] using hnorm

private theorem Ctx23L.false_of_involution_min {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1A : S23_1A D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (hE : UC22P20gExcFacts) (hDeg : KMinDegLow) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) {k : ℕ}
    (hnat : IsNaturalClassicalModule (barSub ⊥ A hA c.L) k)
    (hk : k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k ∧
      NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k))
    (hnorm : ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal)
    (hW : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
      (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
      (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
        B = ⊥ ∨ B = A) {k : ℕ},
      IsNaturalClassicalModule (barSub ⊥ A hA c.L) k → 2 * k = c.n →
      IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k →
      NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k →
      ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k)
    {x : c.N} (hs2x : orderOf (actN c x) = 2)
    (hsrkx : rkIdx (fixV (Subgroup.zpowers (actN c x))) =
      mBar c.N (⊥ : Subgroup G) c.V (Ctx23L.isElemAbelian_V_basic c))
    (hCA : ∀ h : ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L),
      (h : MulAut (Vtil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c))) ∈
        centSub (imgTil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) A) →
      h ∈ Subgroup.center ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L))
    (hCW : ∀ h : ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L),
      (h : MulAut (Vtil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c))) ∈
        centQuot (imgTil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) A) →
      h ∈ Subgroup.center ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L)) :
    False := by
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  have hVne : c.V ≠ ⊥ := fun h => hAne (le_bot_iff.mp (h ▸ hAV))
  have hn3 : 3 ≤ c.n := uc22p20g_three_le_of_nparam hE h207 h1930 c.hL0 c.hn
  have hk' : 3 ≤ k ∨ 2 ≤ k ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k := by
    rcases hk with hk | ⟨h2k, hOm, -⟩
    exacts [Or.inl (by omega), Or.inr ⟨by omega, hOm⟩]
  by_cases hcent : ∀ h ∈ barSub (⊥ : Subgroup G) c.V hV c.L, Commute h (actN c x)
  · have hs1 : actN c x ≠ 1 := by
      intro h1
      simpa [h1] using hs2x
    have hlt := Ctx23L.n_lt_rkIdx_fixV_of_mem_N c hDeg h207 h208 h209 hE h1930
      (x := x) hs1 hs2x hcent
    have hle := Ctx23L.mParam_V_le c h1A h1930 hVne
    rw [hsrkx] at hlt
    omega
  · push Not at hcent
    obtain ⟨h, hh, hnc⟩ := hcent
    have hnotcent : ∃ h ∈ barSub (⊥ : Subgroup G) c.V hV c.L,
        actN c x * h * (actN c x)⁻¹ ≠ h := by
      refine ⟨h, hh, fun heq => hnc ?_⟩
      have hcomm : actN c x * h = h * actN c x := by
        calc actN c x * h = (actN c x * h * (actN c x)⁻¹) * actN c x := by group
          _ = h * actN c x := by rw [heq]
      exact hcomm.symm
    have hLN := Ctx23L.normal_L_N_of_isNaturalClassicalModule c h208 h1930 hA hAV hAne hAN
      hnat hnorm
    have hge := Ctx23L.k_add_two_le_rkIdx_fixV_of_mem_N c (kNoTransv_holds) hLN hA hAV hAN
      hnat hk' hCA hCW hs2x hnotcent
    rw [hsrkx] at hge
    rcases hk with hk | ⟨h2k, hOm, hNat⟩
    · have hle := Ctx23L.mParam_V_le c h1A h1930 hVne
      omega
    · obtain ⟨hW23, hW23le⟩ := hW hA hAV hAne hAN hmin hnat h2k hOm hNat
      have hle := mBar_V_le_of_omegaMinus c h1A h1930 hVne (hV := hV) (k := k) hW23le
      omega

private theorem Ctx23L.a_eq_V_of_natural_of_omega_bound {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1A : S23_1A D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (hE : UC22P20gExcFacts) (hDeg : KMinDegLow) (h1930 : H1930 D)
    (hnatA : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A), A ≤ c.V → A ≠ ⊥ →
      c.N ≤ Subgroup.normalizer (A : Set G) →
      (∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) → B = ⊥ ∨ B = A) →
      ∃ k : ℕ, IsNaturalClassicalModule (barSub ⊥ A hA c.L) k ∧
        (k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k ∧
          NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k)) ∧
        ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal)
    (hW : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
      (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
      (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
        B = ⊥ ∨ B = A) {k : ℕ},
      IsNaturalClassicalModule (barSub ⊥ A hA c.L) k → 2 * k = c.n →
      IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k →
      NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k →
      ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    A = c.V := by
  classical
  obtain ⟨k, hnat, hk, hnorm⟩ := hnatA hA hAV hAne hAN hmin
  by_contra hAVne
  have hVL : ¬ ⁅c.V, c.L⁆ ≤ A := fun h =>
    hAVne (Ctx23L.A_eq_V_of_commutator_le c hA hAV hAN h)
  obtain ⟨xn, hs2x, hsrkx⟩ := Ctx23L.exists_actN_involution_rkIdx_eq_mBar c
    (fun h => hAne (le_bot_iff.mp (h ▸ hAV)))
  have hCA := Ctx23L.centSub_le_center c h208 h1930 hAV hAne hAN
  have hCW := Ctx23L.centQuot_le_center c h208 h1930 hAV hAN hVL
  exact Ctx23L.false_of_involution_min c h1A h207 h208 h209 hE hDeg h1930 hA hAV hAne
    hAN hmin hnat hk hnorm hW hs2x hsrkx hCA hCW

private theorem Ctx23L.exists_aBar_W23_le_of_natural {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1A : S23_1A D Ch) (h1930 : H1930 D) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) {k : ℕ}
    (hnat : IsNaturalClassicalModule (barSub ⊥ A hA c.L) k)
    (hk : k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k ∧
      NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k))
    (hW : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
      (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
      (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
        B = ⊥ ∨ B = A) {k : ℕ},
      IsNaturalClassicalModule (barSub ⊥ A hA c.L) k → 2 * k = c.n →
      IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k →
      NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k →
      ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) :
    ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k := by
  rcases hk with hk | ⟨h2k, hOm, hNat⟩
  · have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
    have heq : c.V = conjClosure c.N (c.V ⊓ D.Z) := by
      rw [inf_eq_right.mpr hZleV]
      rfl
    obtain ⟨hW', -, haBar⟩ :=
      h1A h1930 c c.V (Ctx23L.isElemAbelian_V_basic c) le_rfl heq
        (fun h => hAne (le_bot_iff.mp (h ▸ hAV)))
    have hWe : conjClosure c.L0 (c.V ⊓ D.Z) = W23_1 c := by
      rw [inf_eq_right.mpr hZleV]
      rfl
    exact ⟨hWe ▸ hW', by
      rw [← aBar_congr_subgroup hWe hW' (hWe ▸ hW'), hk]
      exact haBar⟩
  · exact hW hA hAV hAne hAN hmin hnat h2k hOm hNat

private theorem Ctx23L.conclusions23_2_of_natural_of_omega_bound {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1A : S23_1A D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (hE : UC22P20gExcFacts) (hDeg : KMinDegLow) (h1930 : H1930 D)
    (hnatA : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A), A ≤ c.V → A ≠ ⊥ →
      c.N ≤ Subgroup.normalizer (A : Set G) →
      (∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) → B = ⊥ ∨ B = A) →
      ∃ k : ℕ, IsNaturalClassicalModule (barSub ⊥ A hA c.L) k ∧
        (k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k ∧
          NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k)) ∧
        ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal)
    (hW : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
      (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
      (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
        B = ⊥ ∨ B = A) {k : ℕ},
      IsNaturalClassicalModule (barSub ⊥ A hA c.L) k → 2 * k = c.n →
      IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k →
      NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k →
      ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) :
    c.Conclusions23_2 := by
  classical
  obtain ⟨A, hAV, hAne, hAN, hmin⟩ := Ctx23L.exists_irreducible_submodule c
  have hA : IsElemAbelian 2 A := IsElemAbelian.mono (Ctx23L.isElemAbelian_V_basic c) hAV
  obtain ⟨k, hnat, hk, -⟩ := hnatA hA hAV hAne hAN hmin
  have hAeq : A = c.V :=
    Ctx23L.a_eq_V_of_natural_of_omega_bound c h1A h207 h208 h209 hE hDeg h1930
      hnatA hW hA hAV hAne hAN hmin
  subst A
  have hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  have hnatV : IsNaturalClassicalModule (c.H hV) k := by
    change IsNaturalClassicalModule (barSub ⊥ c.V hA c.L) k
    exact hnat
  have hn3 : 3 ≤ c.n := uc22p20g_three_le_of_nparam hE h207 h1930 c.hL0 c.hn
  have hk2 : 2 ≤ k := by
    rcases hk with hk | ⟨h2k, -, -⟩
    · omega
    · omega
  have hk' : k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(c.H hV) 4 k) := by
    rcases hk with hk | ⟨h2k, hOm, -⟩
    · exact Or.inl hk
    · exact Or.inr ⟨h2k, by
        change IsOmegaMinus ↥(barSub ⊥ c.V hA c.L) 4 k
        exact hOm⟩
  obtain ⟨hcard, hU0, hUinf, hirr⟩ := Ctx23L.package_U0 c hV h207 h208 h209 h1930 hnatV
  refine ⟨hV, k, hk2, hnatV, hk', hcard, hU0, hUinf, hirr, ?_⟩
  exact Ctx23L.exists_aBar_W23_le_of_natural c h1A h1930 hA hAV hAne hAN hmin hnat hk hW

private theorem s23_2_natural_of_omega_bound (D : Data G) (Ch : Choice2011 G)
    (h1A : S23_1A D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (hE : UC22P20gExcFacts) (hDeg : KMinDegLow)
    (hnatA : H1930 D → ∀ c : Ctx23L D Ch, ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A),
      A ≤ c.V → A ≠ ⊥ → c.N ≤ Subgroup.normalizer (A : Set G) →
      (∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) → B = ⊥ ∨ B = A) →
      ∃ k : ℕ, IsNaturalClassicalModule (barSub ⊥ A hA c.L) k ∧
        (k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k ∧
          NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k)) ∧
        ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal)
    (hW : ∀ (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
      (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
      (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
        B = ⊥ ∨ B = A) {k : ℕ},
      IsNaturalClassicalModule (barSub ⊥ A hA c.L) k → 2 * k = c.n →
      IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k →
      NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k →
      ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) :
    S23_2_natural D Ch := by
  intro h1930 c
  obtain ⟨A, hAV, hAne, hAN, hmin⟩ := Ctx23L.exists_irreducible_submodule c
  have hA : IsElemAbelian 2 A := IsElemAbelian.mono (Ctx23L.isElemAbelian_V_basic c) hAV
  obtain ⟨k, hnat, hk, -⟩ := hnatA h1930 c hA hAV hAne hAN hmin
  have hAeq : A = c.V :=
    Ctx23L.a_eq_V_of_natural_of_omega_bound c h1A h207 h208 h209 hE hDeg h1930
      (hnatA h1930 c) (hW c) hA hAV hAne hAN hmin
  subst A
  have hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  have hnatV : IsNaturalClassicalModule (c.H hV) k := by
    change IsNaturalClassicalModule (barSub ⊥ c.V hA c.L) k
    exact hnat
  exact ⟨hV, k, (Ctx23L.package_U0 c hV h207 h208 h209 h1930 hnatV).1, hnatV⟩

theorem Ctx23L.conclusions23_2_of_natural {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1A : S23_1A D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (hE : UC22P20gExcFacts) (hDeg : KMinDegLow) (h1930 : H1930 D)
    (hnatA : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A), A ≤ c.V → A ≠ ⊥ →
      c.N ≤ Subgroup.normalizer (A : Set G) →
      (∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) → B = ⊥ ∨ B = A) →
      ∃ k : ℕ, IsNaturalClassicalModule (barSub ⊥ A hA c.L) k ∧
        (k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k ∧
          NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k)) ∧
        ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal)
    (hIrrL : ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A),
      c.L ≤ Subgroup.normalizer (A : Set G) → ∀ {k : ℕ},
        NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k → IrrOn c.L A) :
    c.Conclusions23_2 :=
  Ctx23L.conclusions23_2_of_natural_of_omega_bound c h1A h207 h208 h209 hE hDeg h1930
    hnatA (Ctx23L.omega_bound_of_irrL c h1930 h209 hIrrL)

theorem s23_2_natural_of_natural {D : Data G} {Ch : Choice2011 G} (h1A : S23_1A D Ch)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (hE : UC22P20gExcFacts)
    (hDeg : KMinDegLow)
    (hnatA : H1930 D → ∀ c : Ctx23L D Ch, ∀ {A : Subgroup G} (hA : IsElemAbelian 2 A),
      A ≤ c.V → A ≠ ⊥ → c.N ≤ Subgroup.normalizer (A : Set G) →
      (∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) → B = ⊥ ∨ B = A) →
      ∃ k : ℕ, IsNaturalClassicalModule (barSub ⊥ A hA c.L) k ∧
        (k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k ∧
          NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k)) ∧
        ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal)
    (hIrrL : ∀ (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A),
      c.L ≤ Subgroup.normalizer (A : Set G) → ∀ {k : ℕ},
        NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k → IrrOn c.L A) :
    S23_2_natural D Ch :=
  fun h1930 => (s23_2_natural_of_omega_bound D Ch h1A h207 h208 h209 hE hDeg hnatA
    (fun c => Ctx23L.omega_bound_of_irrL c h1930 h209 (hIrrL c))) h1930

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
