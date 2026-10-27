module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenPerm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveNineteen

theorem inP11_P1 (D : Data G) (hstd : Sigma23Std D) (h613 : UC6.R6_13 D) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 D p P P₀) :
    F11.InP11 D (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) := by
  obtain ⟨⟨hp3, hsolv, hwc, hΓ, hL, hfrob⟩, -, -, ⟨-, h4b, -⟩, -⟩ := h613 p P P₀ hH
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨n, hn, hE, hcard⟩ := uc22p22q_P1_elem D hstd hH hwc hL hp2
  have hP₁M : P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) ≤ D.M :=
    inf_le_left.trans hH.sylow.le
  have hsq : p ^ 2 ≤ Nat.card (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) := by
    rw [hcard]
    exact Nat.pow_le_pow_right hpP.pos hn
  have hnc := uc22p22n_not_isCyclic_of_card hpP hE hsq
  refine ⟨p, hpP, hp2, hP₁M, uc22p22e_isPGroup_of_elem hE, hE.2, hnc, ?_, hΓ, Or.inr ⟨_, hnc,
    ⟨P, hH.sylow, inf_le_left, le_normalizer_P1 hpP hH.sylow.isPGroup hH.le hH.card hwc⟩, hΓ⟩⟩
  exact permutes_of_le_normalizer_sup (uc22p22e_pCoreOf_le_T D) (D.sylowM.le.trans h4b)
    (hP₁M.trans (uc22p22qu_M_le_normalizer_R D.M))

theorem mem_pCoreOf_of_centralizes (D : Data G) (h613 : UC6.R6_13 D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) {m : G} (hm : m ∈ D.M)
    (hmc : ∀ y ∈ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)), m * y * m⁻¹ * y⁻¹ ∈ pCoreOf 2 D.M)
    (hm2 : m * m ∈ pCoreOf 2 D.M) : m ∈ pCoreOf 2 D.M := by
  obtain ⟨-, -, -, ⟨-, h4b, h4c⟩, -⟩ := h613 p P P₀ hH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₁ : Subgroup G := P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) with hP₁def
  set R : Subgroup G := pCoreOf 2 D.M with hRdef
  have hP₁M : P₁ ≤ D.M := inf_le_left.trans hH.sylow.le
  have hMR : D.M ≤ normalizer (R : Set G) := uc22p22qu_M_le_normalizer_R D.M
  obtain ⟨k, hk⟩ := uc22p22qh_isPGroup_pCoreOf D.M ⟨m * m, hm2⟩
  have hmk : m ^ 2 ^ (k + 1) = 1 := by
    have h1 : (m * m) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [pow_succ', pow_mul, sq]
    exact h1
  have hmp : IsPGroup 2 (zpowers m) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨k + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hmk, one_zpow]
  obtain ⟨x, hxM, hx⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM (zpowers_le.2 hm) hmp
  have ht : x⁻¹ * m * x ∈ D.T := hx m (mem_zpowers m)
  have hsetPR : ((P₁ ⊔ R : Subgroup G) : Set G) = (P₁ : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P₁ R (hP₁M.trans hMR)
  have hcomm : ∀ y ∈ P₁, (x⁻¹ * m * x) * y * (x⁻¹ * m * x)⁻¹ * y⁻¹ ∈ R := by
    intro y hy
    have hxy : x * y * x⁻¹ ∈ ((P₁ ⊔ R : Subgroup G) : Set G) :=
      (mem_normalizer_iff.1 (h4b hxM) y).1 (mem_sup_left hy)
    rw [hsetPR] at hxy
    obtain ⟨y', hy', r, hr, hyr⟩ := Set.mem_mul.1 hxy
    have hy'M : y' ∈ D.M := hP₁M hy'
    have hrM : m * r * m⁻¹ * r⁻¹ ∈ R :=
      R.mul_mem (uc22p22qh_conj_mem_pCoreOf hm hr) (R.inv_mem hr)
    have hc : m * (y' * r) * m⁻¹ * (y' * r)⁻¹ ∈ R := by
      have e : m * (y' * r) * m⁻¹ * (y' * r)⁻¹ =
          (m * y' * m⁻¹ * y'⁻¹) * (y' * (m * r * m⁻¹ * r⁻¹) * y'⁻¹) := by group
      rw [e]
      exact R.mul_mem (hmc y' hy') (uc22p22qh_conj_mem_pCoreOf hy'M hrM)
    have e : (x⁻¹ * m * x) * y * (x⁻¹ * m * x)⁻¹ * y⁻¹ =
        x⁻¹ * (m * (y' * r) * m⁻¹ * (y' * r)⁻¹) * x⁻¹⁻¹ := by
      have hy2 : y = x⁻¹ * (y' * r) * x := by
        rw [hyr]
        group
      rw [hy2]
      group
    rw [e]
    exact uc22p22qh_conj_mem_pCoreOf (D.M.inv_mem hxM) hc
  have htR : x⁻¹ * m * x ∈ R := h4c _ ht hcomm
  have e : m = x * (x⁻¹ * m * x) * x⁻¹ := by group
  rw [e]
  exact uc22p22qh_conj_mem_pCoreOf hxM htR

theorem card_barSub_of_inf_eq_bot {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) {X : Subgroup G}
    (hXM : X ≤ M) (hX : X ⊓ F11.CTilde M V₀ V = ⊥) :
    Nat.card (barSub V₀ V hV X) = Nat.card X := by
  have hXs : X ≤ stabTil V₀ V := hXM.trans (le_stabTil hM hM₀)
  set f := (actTil V₀ V hV).domRestrict (X.subgroupOf (stabTil V₀ V)) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hg1 : actTil V₀ V hV (g : stabTil V₀ V) = 1 := hg
    have hgX : ((g : stabTil V₀ V) : G) ∈ X := g.2
    have hgC : ((g : stabTil V₀ V) : G) ∈ F11.CTilde M V₀ V :=
      (mem_cTilde_iff hV hM).2 ⟨hXM hgX, (g : stabTil V₀ V).2, hg1⟩
    have h1 : ((g : stabTil V₀ V) : G) = 1 := by
      have : ((g : stabTil V₀ V) : G) ∈ X ⊓ F11.CTilde M V₀ V := ⟨hgX, hgC⟩
      rw [hX] at this
      exact this
    exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext h1))
  have hrange : f.range = barSub V₀ V hV X := by
    rw [hf, MonoidHom.domRestrict_range]
    rfl
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXs).toEquiv

private theorem barSub_le_normalizer {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {X Y : Subgroup G} (hXY : X ≤ normalizer (Y : Set G)) :
    barSub V₀ V hV X ≤ normalizer ((barSub V₀ V hV Y : Subgroup _) : Set _) := by
  refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map _)
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  rw [mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.1 (hXY hg) h

private theorem barSub_sup_eq {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) {Y C : Subgroup G}
    (hYM : Y ≤ M) (hC : C ≤ F11.CTilde M V₀ V) (hYC : Y ≤ normalizer (C : Set G)) :
    barSub V₀ V hV (Y ⊔ C) = barSub V₀ V hV Y := by
  refine le_antisymm (fun φ hφ => ?_) (barSub_mono V₀ V hV le_sup_left)
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
  have hset : ((Y ⊔ C : Subgroup G) : Set G) = (Y : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Y C hYC
  have hg' : (g : G) ∈ ((Y ⊔ C : Subgroup G) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨y, hy, c, hc, hyc⟩ := Set.mem_mul.1 hg'
  have hcC := (mem_cTilde_iff hV hM).1 (hC hc)
  obtain ⟨hcM, hcs, hc1⟩ := hcC
  have hys : y ∈ stabTil V₀ V := le_stabTil hM hM₀ (hYM hy)
  have hgeq : g = ⟨y, hys⟩ * ⟨c, hcs⟩ := Subtype.ext hyc.symm
  rw [hgeq, map_mul, hc1, mul_one]
  exact actTil_mem_barSub V₀ V hV hy hys

theorem mBarGT_three (D : Data G) (hstd : Sigma23Std D) (h613 : UC6.R6_13 D) (h112 : F11.R112 D)
    (h127 : R127 D) {p : ℕ} {P P₀ : Subgroup G} (hH : UC6.Hyp612 D p P P₀) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) : MBarGT D.M V₀ V 3 := by
  obtain ⟨⟨hp3, -, hwc, hΓ, hL, hfrob⟩, -, -, ⟨-, h4b, -⟩, -⟩ := h613 p P P₀ hH
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · interval_cases p
      exact absurd hpP (by norm_num)
    · exact h5
  have h11 : F11.Hyp11 D V₀ V := h.hyp11 h127
  obtain ⟨hVV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D h11
  have hMV : D.M ≤ normalizer (V : Set G) := hVV.2.2.1
  have hV : IsElemAbelian 2 V := hVV.2.2.2
  have hC : F11.CTilde D.M V₀ V = pCoreOf 2 D.M := h112 V₀ V h11 ⟨p, hH.mem_sig2⟩
  rw [mBarGT_iff_lt_mParam D.M V₀ V hV hV₀V hMV hMV₀]
  set L : Subgroup G := UC6.inftyOf (centralizer (P₀ : Set G)) with hLdef
  set P₁ : Subgroup G := P ⊓ L with hP₁def
  set R : Subgroup G := pCoreOf 2 D.M with hRdef
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  obtain ⟨n, hn, hE, hcard⟩ := uc22p22q_P1_elem D hstd hH hwc hL hp2
  have hP₁ne : P₁ ≠ ⊥ := uc22p22q_P1_ne_bot D hstd hH hwc hL hp2
  have hNM : normalizer (P₁ : Set G) ≤ D.M := uc22p22q_normalizer_P1_le D hH hP₁ne hΓ
  obtain ⟨m, -, hLm⟩ := hL
  obtain ⟨Dt, hDtL, hDtN, hDtc, hDtf⟩ :=
    exists_torus hpP hp2 hLm (uc22p22q_isSylowOf_P1 D hstd hH hwc)
  have hP₁M : P₁ ≤ D.M := inf_le_left.trans hH.sylow.le
  have hDtM : Dt ≤ D.M := hDtN.trans hNM
  have hMR : D.M ≤ normalizer (R : Set G) := uc22p22qu_M_le_normalizer_R D.M
  have hRC : R ≤ F11.CTilde D.M V₀ V := hC.ge
  have hP₁R : P₁ ⊓ R = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne p 2 hp2 P₁ R
      (hH.sylow.isPGroup.to_le inf_le_left) (uc22p22qh_isPGroup_pCoreOf D.M))
  have hP₀ne : P₀ ≠ ⊥ := by
    intro hb
    have hc := hH.card
    rw [hb, Subgroup.card_bot] at hc
    exact hpP.one_lt.ne hc
  have hLR := uc22p22qu_L_inf_R D hP₀ne (Subgroup.map_subtype_le _) hfrob
  have hDtR : Dt ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyR⟩
    exact Subgroup.mem_bot.2 (hLR y (hDtL hyD) hyR)
  have hcP : Nat.card (barSub V₀ V hV P₁) = Nat.card P₁ :=
    card_barSub_of_inf_eq_bot hV hMV hMV₀ hP₁M (by rw [hC]; exact hP₁R)
  have hcD : Nat.card (barSub V₀ V hV Dt) = Nat.card Dt :=
    card_barSub_of_inf_eq_bot hV hMV hMV₀ hDtM (by rw [hC]; exact hDtR)
  have hW : ∀ w : Vtil V₀ V hV, w * w = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H x => rw [← pow_two, ← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]
  have hA : IsElemAbelian p (barSub V₀ V hV P₁) :=
    (hE.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
  have hAc : p ^ 2 ≤ Nat.card (barSub V₀ V hV P₁) := by
    rw [hcP, hcard]
    exact Nat.pow_le_pow_right hpP.pos hn
  have hSA := barSub_le_normalizer (V₀ := V₀) hV hDtN
  have hSf : ∀ s ∈ barSub V₀ V hV Dt, s ≠ 1 → ∀ x ∈ barSub V₀ V hV P₁, s * x = x * s →
      x = 1 := by
    intro s hs hs1 x hx hsx
    obtain ⟨d, hd, rfl⟩ := (mem_barSub V₀ V hV Dt s).1 hs
    obtain ⟨y, hy, rfl⟩ := (mem_barSub V₀ V hV P₁ x).1 hx
    have hc1 : actTil V₀ V hV (d * y * d⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hsx]
      group
    have hcC : ((d * y * d⁻¹ * y⁻¹ : stabTil V₀ V) : G) ∈ F11.CTilde D.M V₀ V :=
      (mem_cTilde_iff hV hMV).2 ⟨D.M.mul_mem (D.M.mul_mem (D.M.mul_mem (hDtM hd) (hP₁M hy))
        (D.M.inv_mem (hDtM hd))) (D.M.inv_mem (hP₁M hy)), (d * y * d⁻¹ * y⁻¹).2, hc1⟩
    rw [hC] at hcC
    have hcP₁ : ((d * y * d⁻¹ * y⁻¹ : stabTil V₀ V) : G) ∈ P₁ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact P₁.mul_mem ((mem_normalizer_iff.1 (hDtN hd) _).1 hy) (P₁.inv_mem hy)
    have hc : ((d * y * d⁻¹ * y⁻¹ : stabTil V₀ V) : G) = 1 := by
      have : ((d * y * d⁻¹ * y⁻¹ : stabTil V₀ V) : G) ∈ P₁ ⊓ R := ⟨hcP₁, hcC⟩
      rw [hP₁R] at this
      exact this
    have hdy : (d : G) * y = y * d := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
      calc (d : G) * y = ((d : G) * y * (d : G)⁻¹ * (y : G)⁻¹) * (y * d) := by group
        _ = y * d := by rw [hc, one_mul]
    have hd1 : (d : G) ≠ 1 := by
      intro hd1
      apply hs1
      rw [show d = 1 from Subtype.ext hd1, map_one]
    rw [show y = 1 from Subtype.ext (hDtf d hd hd1 y hy hdy), map_one]
  have hSc : Nat.card (barSub V₀ V hV P₁) ≤ 2 * Nat.card (barSub V₀ V hV Dt) + 1 := by
    rw [hcP, hcD, hDtc]
  have hAX : barSub V₀ V hV P₁ ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hP₁M
  have hXA : Mbar D.M V₀ V hV ≤ normalizer ((barSub V₀ V hV P₁ : Subgroup _) : Set _) := by
    rw [← barSub_sup_eq hV hMV hMV₀ hP₁M hRC (hP₁M.trans hMR)]
    exact barSub_le_normalizer hV h4b
  have hinv : ∀ t ∈ Mbar D.M V₀ V hV, orderOf t = 2 →
      ∃ b ∈ barSub V₀ V hV P₁, t * b * t⁻¹ ≠ b := by
    intro t ht ht2
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V hV D.M t).1 ht
    have hg1 : actTil V₀ V hV g ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have hR' : ∀ c : stabTil V₀ V, (c : G) ∈ D.M → actTil V₀ V hV c = 1 → (c : G) ∈ R := by
      intro c hcM hc1
      rw [← hC]
      exact (mem_cTilde_iff hV hMV).2 ⟨hcM, c.2, hc1⟩
    have hsq : actTil V₀ V hV g ^ 2 = 1 := ht2 ▸ pow_orderOf_eq_one (actTil V₀ V hV g)
    have hg2 : (g : G) * g ∈ R := by
      have := hR' (g * g) (D.M.mul_mem hgM hgM) (by rw [map_mul, ← pow_two]; exact hsq)
      simpa using this
    have hgc : ∀ y ∈ P₁, (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ R := by
      intro y hy
      have hys : y ∈ stabTil V₀ V := hMs (hP₁M hy)
      have h1 := hcon (actTil V₀ V hV ⟨y, hys⟩) (actTil_mem_barSub V₀ V hV hy hys)
      have := hR' (g * ⟨y, hys⟩ * g⁻¹ * ⟨y, hys⟩⁻¹)
        (D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hgM (hP₁M hy)) (D.M.inv_mem hgM))
          (D.M.inv_mem (hP₁M hy)))
        (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, mul_inv_cancel])
      simpa using this
    have hgR : (g : G) ∈ R := mem_pCoreOf_of_centralizes D h613 hH hgM hgc hg2
    have hgC : (g : G) ∈ F11.CTilde D.M V₀ V := by
      rw [hC]
      exact hgR
    exact hg1 ((mem_cTilde_iff hV hMV).1 hgC).2.2
  exact three_lt_mParam hW hpP hp5 hA hAc hSA hSf hSc hAX hXA hinv

end TwelveNineteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
