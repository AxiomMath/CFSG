module

public import CFSG.Quasithin.H13.AS91Sec4EightLift
public import CFSG.Quasithin.Background.A1cTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour

namespace Two

theorem sOK48_spec :
    gensOKb sGens48 = true ∧ (∀ g ∈ sGens48, g ∈ enumGrp pRows) ∧ idR ∈ enumGrp sGens48 ∧
      closedCheck sGens48 (enumGrp sGens48) = true ∧ (enumGrp sGens48).dedup.length = 16 ∧
      ∀ x ∈ enumGrp sGens48, x = idR ∨ (enumGrp ebRows).contains x = false := by
  have h := splitOK48_parts.1
  simp only [sOK48, Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem uOK48_spec :
    uList48.dedup.length = 64 ∧ (∀ u ∈ uList48, u < 4096) ∧ 0 ∈ uList48 ∧
      (∀ x ∈ uList48, ∀ y ∈ uList48, x ^^^ y ∈ uList48) ∧ (∀ u ∈ uList48, q0b u = false) ∧
      (∀ u ∈ uList48, appN omegaRows u ∈ uList48) ∧
      (∀ g ∈ sGens48, ∀ u ∈ uList48, appN g u ∈ uList48) ∧
      ∀ u ∈ uList48, u = 0 ∨ w1List.contains u = false := by
  have h := splitOK48_parts.2.2.1
  simp only [uOK48, Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem cjOK48_spec :
    conjOK gamGensI cjA48 aRows48 = true ∧ cjA48.2.2 ∈ enumGrp ebRows ∧
      conjOK gamGensI cjB48 bRows48 = true ∧ cjB48.2.2 ∈ enumGrp ebRows ∧
      conjOK gamGensI cjAB48 (mulR (mulR aRows48 bRows48) (mulR aRows48 bRows48)) = true ∧
      cjAB48.2.2 ∈ enumGrp ebRows ∧
      conjOK nGensI cjC48 cRows48 = true ∧ cjC48.2.2 ∈ coreList48 () ∧ cjC48.2.2 ≠ idR ∧
      conjOK nGensI cjAC48 (mulR aRows48 cRows48) = true ∧ cjAC48.2.2 ∈ coreList48 () ∧
      cjAC48.2.2 ≠ idR ∧
      conjOK nGensI cjBC48 (mulR bRows48 cRows48) = true ∧ cjBC48.2.2 ∈ coreList48 () ∧
      cjBC48.2.2 ≠ idR ∧
      ∀ t ∈ [cRows48, mulR aRows48 cRows48, mulR bRows48 cRows48],
        mulR t t = idR ∧ mulR (mulR t omegaRows) t = mulR omegaRows omegaRows := by
  have h := splitOK48_parts.2.2.2
  simp only [cjOK48, Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

end Two

theorem conj_of_conjOK {gs : List (Array ℕ)} (hgs : GensOK gs) {d : List ℕ × List ℕ × Array ℕ}
    {t : Array ℕ} (h : Two.conjOK gs d t = true) :
    ∃ W ∈ genGrp gs, ∀ x, linOfRows t x = W (linOfRows d.2.2 (W⁻¹ x)) := by
  simp only [Two.conjOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨-, W, hW, hWx⟩ := rep_word hgs d.1 h1
  obtain ⟨-, Wi, -, hWix⟩ := rep_word hgs d.2.1 h2
  have hWWi : ∀ x, W (Wi x) = x := fun x => by
    rw [hWx, hWix, ← linOfRows_mulR, h3, linOfRows_idR]
  have hinv : ∀ x, W⁻¹ x = Wi x := fun x => by
    calc W⁻¹ x = W⁻¹ (W (Wi x)) := by rw [hWWi]
      _ = Wi x := by simp
  refine ⟨W, hW, fun x => ?_⟩
  rw [← h4, linOfRows_mulR, linOfRows_mulR, hinv, hWx, hWix]

theorem card_zpowers_le_of_pow {X : Type} [Group X] [Finite X] {a : X} {n : ℕ} (hn : 0 < n)
    (ha : a ^ n = 1) : Nat.card (zpowers a) ≤ n := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one hn ha

theorem card_closure_le_sixteen {X : Type} [Group X] [Finite X] {a b c : X} (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hab : (a * b) ^ 4 = 1) (hac : a * c = c * a)
    (hbc : b * c = c * b) : Nat.card (closure ({a, b, c} : Set X)) ≤ 16 := by
  set H : Subgroup X := zpowers (a * b) ⊔ zpowers a with hH
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hanorm : zpowers a ≤ normalizer (zpowers (a * b) : Set X) := by
    rw [zpowers_le]
    refine mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    have e : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
      rw [mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]
    rw [e]
    exact zpow_mem (inv_mem (mem_zpowers _)) k
  have hH8 : Nat.card H ≤ 8 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hanorm
    rw [sup_comm] at h1
    have h2 : Nat.card (zpowers a) ≤ 2 :=
      card_zpowers_le_of_pow (by norm_num) (by rw [pow_two]; exact ha)
    have h3 : Nat.card (zpowers (a * b)) ≤ 4 := card_zpowers_le_of_pow (by norm_num) hab
    have h4 : 0 < Nat.card (zpowers a ⊓ zpowers (a * b) : Subgroup X) := Nat.card_pos
    calc Nat.card H ≤ Nat.card H * Nat.card (zpowers a ⊓ zpowers (a * b) : Subgroup X) :=
          Nat.le_mul_of_pos_right _ h4
      _ = Nat.card (zpowers a) * Nat.card (zpowers (a * b)) := h1
      _ ≤ 2 * 4 := Nat.mul_le_mul h2 h3
      _ = 8 := by norm_num
  have hcen : H ≤ centralizer ({c} : Set X) := by
    rw [hH]
    refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
    · rw [mul_assoc, hbc, ← mul_assoc, hac, mul_assoc]
    · exact hac
  have hcnorm : zpowers c ≤ normalizer (H : Set X) := by
    rw [zpowers_le]
    refine mem_normalizer_fintype fun n hn => ?_
    have e : n * c = c * n := mem_centralizer_singleton_iff.mp (hcen hn)
    rw [← e, mul_inv_cancel_right]
    exact hn
  have hclo : closure ({a, b, c} : Set X) = zpowers c ⊔ H := by
    apply le_antisymm
    · rw [closure_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      refine ⟨mem_sup_right (mem_sup_right (mem_zpowers _)), ?_, mem_sup_left (mem_zpowers _)⟩
      have e : b = a * (a * b) := by rw [← mul_assoc, ha, one_mul]
      rw [e]
      exact mem_sup_right (mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _)))
    · refine sup_le ?_ (sup_le ?_ ?_) <;> rw [zpowers_le]
      · exact subset_closure (by simp)
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · exact subset_closure (by simp)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hcnorm
  have h2 : Nat.card (zpowers c) ≤ 2 :=
    card_zpowers_le_of_pow (by norm_num) (by rw [pow_two]; exact hc)
  have h4 : 0 < Nat.card (zpowers c ⊓ H : Subgroup X) := Nat.card_pos
  rw [hclo]
  calc Nat.card (zpowers c ⊔ H : Subgroup X)
      ≤ Nat.card (zpowers c ⊔ H : Subgroup X) * Nat.card (zpowers c ⊓ H : Subgroup X) :=
        Nat.le_mul_of_pos_right _ h4
    _ = Nat.card (zpowers c) * Nat.card H := h1
    _ ≤ 2 * 8 := Nat.mul_le_mul h2 hH8
    _ = 16 := by norm_num

namespace Two

@[expose] def U48 : Set V12 := {v | codeOf v ∈ uList48}

theorem mem_U48 {v : V12} : v ∈ U48 ↔ codeOf v ∈ uList48 := Iff.rfl

theorem vecOf_mem_U48 {n : ℕ} (hn : n ∈ uList48) :
    vecOf n ∈ U48 := by
  rw [mem_U48, codeOf_vecOf (uOK48_spec.2.1 n hn)]
  exact hn

@[expose] def U48sub : Submodule (ZMod 2) V12 where
  carrier := U48
  add_mem' {v w} hv hw := by
    show codeOf (v + w) ∈ uList48
    rw [← vecOf_codeOf v, ← vecOf_codeOf w, ← vecOf_xor,
      codeOf_vecOf (Nat.xor_lt_two_pow (n := 12) (codeOf_lt v) (codeOf_lt w))]
    exact uOK48_spec.2.2.2.1 _ hv _ hw
  zero_mem' := by
    show codeOf 0 ∈ uList48
    rw [← vecOf_zero, codeOf_vecOf (by norm_num)]
    exact uOK48_spec.2.2.1
  smul_mem' c v hv := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]
      show codeOf 0 ∈ uList48
      rw [← vecOf_zero, codeOf_vecOf (by norm_num)]
      exact uOK48_spec.2.2.1
    · rw [one_smul]
      exact hv

theorem card_U48sub : Nat.card U48sub = 64 := by
  have e : Nat.card ↥(U48sub : Submodule (ZMod 2) V12) = (U48 : Set V12).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [e]
  have hU : U48 = vecOf '' {c | c ∈ uList48} := by
    ext v
    constructor
    · intro hv
      exact ⟨codeOf v, hv, vecOf_codeOf v⟩
    · rintro ⟨c, hc, rfl⟩
      exact vecOf_mem_U48 hc
  have hinj : Set.InjOn vecOf {c | c ∈ uList48} := fun a ha b hb he =>
    vecOf_inj (uOK48_spec.2.1 a ha) (uOK48_spec.2.1 b hb) he
  have e2 : {c | c ∈ uList48} = (uList48.toFinset : Set ℕ) := by
    ext c
    simp
  rw [hU, hinj.ncard_image, e2, Set.ncard_coe_finset, List.card_toFinset, uOK48_spec.1]

theorem q0_of_mem_U48 {v : V12} (hv : v ∈ U48) : q0 v = 0 := by
  rw [← vecOf_codeOf v, q0_vecOf, uOK48_spec.2.2.2.2.1 _ hv]
  rfl

theorem eq_zero_of_mem_U48_W1
    {v : V12} (hv : v ∈ U48) (hw : v ∈ W1) : v = 0 := by
  rcases uOK48_spec.2.2.2.2.2.2.2 _ hv with h0 | h0
  · rw [← vecOf_codeOf v, h0, vecOf_zero]
  · have := mem_W1_iff.mp hw
    rw [← List.contains_iff_mem, h0] at this
    exact absurd this (by decide)

theorem theta0_mem_U48 {v : V12} (hv : v ∈ U48) :
    theta0 v ∈ U48 := by
  rw [← vecOf_codeOf v, ← linOfRows_omegaRows, ← vecOf_appN]
  exact vecOf_mem_U48 (uOK48_spec.2.2.2.2.2.1 _ hv)

theorem linOfRows_mem_U48 {g : Array ℕ} (hg : g ∈ sGens48)
    {v : V12} (hv : v ∈ U48) : linOfRows g v ∈ U48 := by
  rw [← vecOf_codeOf v, ← vecOf_appN]
  exact vecOf_mem_U48 (uOK48_spec.2.2.2.2.2.2.1 g hg _ hv)

end Two

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

local notation "Xc" => (zpowers ((D.c : h.setting.M) : G))

section Lifts

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw

theorem exists_lift_of_mem_enum_p {r : Array ℕ} (hr : r ∈ enumGrp Two.pRows) :
    ∃ y : h.setting.M, (y : G) ∈ normalizer (Xc : Set G) ∧ (y : G) ∈ D.T ∧
      ∀ x, D.Φo (h.setting.ρ y) x = linOfRows r x := by
  obtain ⟨-, U, hUP, hUr⟩ := enumGrp_sound Two.gensOK_pRows r hr
  have hUN := Two.pGrp_le_nGrp hUP
  rw [← D.map_Mbar_Φo hOut hTw] at hUN
  obtain ⟨p, hpM, rfl⟩ := hUN
  obtain ⟨y, hyN, hyp⟩ := D.exists_nx_lift hpM
  refine ⟨y, hyN, mem_pre_of_rho y ?_, fun x => by rw [hyp, hUr]⟩
  show D.Φo (h.setting.ρ y) ∈ Two.pGrp
  rw [hyp]
  exact hUP

omit hOut hTw
  in
theorem inv_θ_of_rows {y : h.setting.M} {t : Array ℕ}
    (hy : ∀ x, D.Φo (h.setting.ρ y) x = linOfRows t x) (ht2 : mulR t t = idR)
    (htθ : mulR (mulR t omegaRows) t = mulR omegaRows omegaRows) :
    h.setting.ρ y * D.θ * (h.setting.ρ y)⁻¹ = D.θ⁻¹ := by
  set Y := D.Φo (h.setting.ρ y) with hYdef
  have hYY : ∀ v, Y (Y v) = v := fun v => by
    rw [hy, hy, ← linOfRows_mulR, ht2, linOfRows_idR]
  have hY2 : Y * Y = 1 := LinearEquiv.ext fun v => hYY v
  have hYi : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hY2
  have hYθ : ∀ v, Y (theta0 (Y v)) = theta0 (theta0 v) := fun v => by
    rw [hy, hy, ← linOfRows_omegaRows, ← linOfRows_mulR, ← linOfRows_mulR, htθ, linOfRows_mulR,
      linOfRows_omegaRows, linOfRows_omegaRows]
  have hθY : ∀ v, theta0 (Y v) = Y (theta0 (theta0 v)) := fun v => by
    rw [← hYθ, hYY]
  rw [D.θ_inv]
  apply D.Φo_injective
  apply LinearEquiv.ext
  intro x
  rw [map_mul, map_mul, map_inv, ← hYdef, hYi, map_mul]
  simp only [LinearEquiv.mul_apply]
  rw [Φo_apply]
  rcases D.Φ_θ with hθ | hθ
  · rw [hθ, hθ, hθ, hYθ]
  · rw [hθ, hθ, hθ, hθY, hθY, hYY, theta0_theta0_theta0]

include hHat

theorem sq_eq_one_of_conjOK_eb {y : h.setting.M} (hy : (y : G) ∈ normalizer (Xc : Set G))
    {t : Array ℕ} {d : List ℕ × List ℕ × Array ℕ} (hd : Two.conjOK Two.gamGensI d t = true)
    (hs : d.2.2 ∈ enumGrp Two.ebRows) (hyt : ∀ x, D.Φo (h.setting.ρ y) x = linOfRows t x) :
    (y : G) * y = 1 := by
  obtain ⟨W, hW, hWt⟩ := conj_of_conjOK Two.gensOK_gamGensI hd
  obtain ⟨-, e, he, her⟩ := enumGrp_sound Two.gensOK_eb _ hs
  refine D.sq_eq_one_of_conj_eb hOut hTw hHat hy (Two.genGrp_gamGensI_le hW) he
    (LinearEquiv.ext fun x => ?_)
  rw [hyt, hWt, LinearEquiv.mul_apply, LinearEquiv.mul_apply, her]

theorem sq_eq_one_of_conjOK_core {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) {y : h.setting.M}
    (hy : (y : G) ∈ normalizer (Xc : Set G)) {t : Array ℕ} {d : List ℕ × List ℕ × Array ℕ}
    (hd : Two.conjOK Two.nGensI d t = true) (hs : d.2.2 ∈ Two.coreList48 ()) (hs1 : d.2.2 ≠ idR)
    (hyt : ∀ x, D.Φo (h.setting.ρ y) x = linOfRows t x) (ht : mulR t t = idR ∧
      mulR (mulR t omegaRows) t = mulR omegaRows omegaRows) : (y : G) * y = 1 := by
  obtain ⟨W, hW, hWt⟩ := conj_of_conjOK Two.gensOK_nGensI hd
  exact D.sq_eq_one_of_conj_core hOut hTw hHat hg₁ hy hW hs hs1 (fun x => by rw [hyt, hWt])
    (D.inv_θ_of_rows hyt ht.1 ht.2)

theorem exists_sGens_lift : ∃ a b c : h.setting.M,
    (a : G) ∈ normalizer (Xc : Set G) ∧ (b : G) ∈ normalizer (Xc : Set G) ∧
    (c : G) ∈ normalizer (Xc : Set G) ∧ (a : G) ∈ D.T ∧ (b : G) ∈ D.T ∧ (c : G) ∈ D.T ∧
    (∀ x, D.Φo (h.setting.ρ a) x = linOfRows Two.aRows48 x) ∧
    (∀ x, D.Φo (h.setting.ρ b) x = linOfRows Two.bRows48 x) ∧
    (∀ x, D.Φo (h.setting.ρ c) x = linOfRows Two.cRows48 x) ∧
    (a : G) * a = 1 ∧ (b : G) * b = 1 ∧ (c : G) * c = 1 ∧ ((a : G) * b) ^ 4 = 1 ∧
    (a : G) * c = c * a ∧ (b : G) * c = c * b := by
  obtain ⟨-, hP, -⟩ := Two.sOK48_spec
  obtain ⟨hcA, hsA, hcB, hsB, hcAB, hsAB, hcC, hsC, hC1, hcAC, hsAC, hAC1, hcBC, hsBC, hBC1,
    hinvs⟩ := Two.cjOK48_spec
  obtain ⟨g₁, hg₁⟩ := D.exists_g₁ hOut hTw
  obtain ⟨a, haN, haT, ha⟩ :=
    D.exists_lift_of_mem_enum_p hOut hTw (hP Two.aRows48 (by simp [Two.sGens48]))
  obtain ⟨b, hbN, hbT, hb⟩ :=
    D.exists_lift_of_mem_enum_p hOut hTw (hP Two.bRows48 (by simp [Two.sGens48]))
  obtain ⟨c, hcN, hcT, hc⟩ :=
    D.exists_lift_of_mem_enum_p hOut hTw (hP Two.cRows48 (by simp [Two.sGens48]))
  have hmul : ∀ {y y' : h.setting.M} {r r' : Array ℕ},
      (∀ x, D.Φo (h.setting.ρ y) x = linOfRows r x) →
      (∀ x, D.Φo (h.setting.ρ y') x = linOfRows r' x) →
      ∀ x, D.Φo (h.setting.ρ (y * y')) x = linOfRows (mulR r r') x := by
    intro y y' r r' hy hy' x
    rw [map_mul, map_mul, LinearEquiv.mul_apply, hy, hy', linOfRows_mulR]
  have ha2 := D.sq_eq_one_of_conjOK_eb hOut hTw hHat haN hcA hsA ha
  have hb2 := D.sq_eq_one_of_conjOK_eb hOut hTw hHat hbN hcB hsB hb
  have hc2 := D.sq_eq_one_of_conjOK_core hOut hTw hHat hg₁ hcN hcC hsC hC1 hc
    (hinvs _ (by simp))
  have hab4 : (((a * b) * (a * b) : h.setting.M) : G) * ((a * b) * (a * b) : h.setting.M) = 1 :=
    D.sq_eq_one_of_conjOK_eb hOut hTw hHat
      (mul_mem (mul_mem haN hbN) (mul_mem haN hbN)) hcAB hsAB (hmul (hmul ha hb) (hmul ha hb))
  have hac2 : (((a * c) : h.setting.M) : G) * ((a * c) : h.setting.M) = 1 :=
    D.sq_eq_one_of_conjOK_core hOut hTw hHat hg₁ (mul_mem haN hcN) hcAC hsAC hAC1 (hmul ha hc)
      (hinvs _ (by simp))
  have hbc2 : (((b * c) : h.setting.M) : G) * ((b * c) : h.setting.M) = 1 :=
    D.sq_eq_one_of_conjOK_core hOut hTw hHat hg₁ (mul_mem hbN hcN) hcBC hsBC hBC1 (hmul hb hc)
      (hinvs _ (by simp))
  have comm_of : ∀ {x y : G}, x * x = 1 → y * y = 1 → x * y * (x * y) = 1 → x * y = y * x := by
    intro x y hx hy hxy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
      _ = y * x := by rw [mul_inv_rev, hxi, hyi]
  refine ⟨a, b, c, haN, hbN, hcN, haT, hbT, hcT, ha, hb, hc, ha2, hb2, hc2, ?_,
    comm_of ha2 hc2 (by simpa using hac2), comm_of hb2 hc2 (by simpa using hbc2)⟩
  have e : ((a : G) * b) ^ 4 = (a : G) * b * (a * b) * ((a : G) * b * (a * b)) := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
  rw [e]
  simpa using hab4

end Lifts

section U

@[expose] noncomputable def Uq : Submodule (ZMod 2) h.setting.Qt where
  carrier := {v | D.ψV v ∈ Two.U48}
  add_mem' {v w} hv hw := by
    show D.ψV (v + w) ∈ Two.U48
    rw [map_add]
    exact Two.U48sub.add_mem hv hw
  zero_mem' := by
    show D.ψV 0 ∈ Two.U48
    rw [map_zero]
    exact Two.U48sub.zero_mem
  smul_mem' c v hv := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]
      show D.ψV 0 ∈ Two.U48
      rw [map_zero]
      exact Two.U48sub.zero_mem
    · rw [one_smul]
      exact hv

theorem card_Uq : Nat.card D.Uq = 64 := by
  rw [← Two.card_U48sub]
  exact Nat.card_congr (D.ψV.toEquiv.subtypeEquiv fun _ => Iff.rfl)

@[expose] noncomputable def U1 : Subgroup G := h.setting.clPre D.Uq

theorem card_U1 : Nat.card D.U1 = 2 ^ 7 := by
  rw [U1, h.setting.card_clPre, D.card_Uq]
  norm_num

theorem U1_comm {x y : G} (hx : x ∈ D.U1) (hy : y ∈ D.U1) : x * y = y * x := by
  refine (h.setting.polar_cl_eq_zero_iff hx.1 hy.1).mp ?_
  rw [D.polar_ψV, QuadraticMap.polar, Two.q0_of_mem_U48 (Two.U48sub.add_mem hx.2 hy.2),
    Two.q0_of_mem_U48 hx.2, Two.q0_of_mem_U48 hy.2, sub_zero, sub_zero]

theorem U1_sq {x : G} (hx : x ∈ D.U1) : x * x = 1 := by
  rw [← pow_two, ← h.setting.q_cl_eq_zero_iff hx.1, ← D.q0_ψV]
  exact Two.q0_of_mem_U48 hx.2

theorem conj_mem_U1 {m : h.setting.M}
    (hm : ∀ v ∈ Two.U48, D.Φo (h.setting.ρ m) v ∈ Two.U48) {x : G} (hx : x ∈ D.U1) :
    (m : G) * x * (m : G)⁻¹ ∈ D.U1 := by
  refine ⟨h.setting.conj_mem_QG m.2 hx.1, ?_⟩
  show D.ψV (h.setting.cl ((m : G) * x * (m : G)⁻¹)) ∈ Two.U48
  rw [← h.setting.ρ_cl m hx.1, ← Φo_apply_ψV]
  exact hm _ hx.2

theorem c_preserves_U48 : ∀ v ∈ Two.U48, D.Φo (h.setting.ρ D.c) v ∈ Two.U48 := by
  intro v hv
  rw [D.ρ_c, Φo_apply]
  rcases D.Φ_θ with hθ | hθ
  · rw [hθ]
    exact Two.theta0_mem_U48 hv
  · rw [hθ]
    exact Two.theta0_mem_U48 (Two.theta0_mem_U48 hv)

@[expose] def nrm (u : G) : G :=
  u * ((D.c : G) * u * (D.c : G)⁻¹) * ((D.c : G) * ((D.c : G) * u * (D.c : G)⁻¹) * (D.c : G)⁻¹)

theorem conjc_mem_U1 {u : G} (hu : u ∈ D.U1) : (D.c : G) * u * (D.c : G)⁻¹ ∈ D.U1 :=
  D.conj_mem_U1 D.c_preserves_U48 hu

theorem nrm_mul {u v : G} (hu : u ∈ D.U1) (hv : v ∈ D.U1) : D.nrm (u * v) = D.nrm u * D.nrm v := by
  set c : G := (D.c : G) with hc
  have hB := D.conjc_mem_U1 hu
  have hB' := D.conjc_mem_U1 hv
  have hC := D.conjc_mem_U1 hB
  have hC' := D.conjc_mem_U1 hB'
  simp only [nrm]
  rw [← hc]
  set B := c * u * c⁻¹
  set B' := c * v * c⁻¹
  set C := c * B * c⁻¹
  set C' := c * B' * c⁻¹
  have e1 : c * (u * v) * c⁻¹ = B * B' := by simp only [B, B']; group
  have e2 : c * (B * B') * c⁻¹ = C * C' := by simp only [C, C']; group
  rw [e1, e2]
  calc u * v * (B * B') * (C * C') = u * (v * B) * B' * (C * C') := by group
    _ = u * (B * v) * B' * (C * C') := by rw [D.U1_comm hv hB]
    _ = u * B * v * (B' * C) * C' := by group
    _ = u * B * v * (C * B') * C' := by rw [D.U1_comm hB' hC]
    _ = u * B * (v * C) * B' * C' := by group
    _ = u * B * (C * v) * B' * C' := by rw [D.U1_comm hv hC]
    _ = u * B * C * (v * B' * C') := by group

@[expose] noncomputable def Ugrp : Subgroup G where
  carrier := {u | u ∈ D.U1 ∧ D.nrm u = 1}
  mul_mem' {u v} hu hv := ⟨mul_mem hu.1 hv.1, by rw [D.nrm_mul hu.1 hv.1, hu.2, hv.2, one_mul]⟩
  one_mem' := ⟨one_mem _, by simp [nrm]⟩
  inv_mem' {u} hu := by
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (D.U1_sq hu.1)
    rw [Set.mem_setOf_eq, hui]
    exact hu

theorem Ugrp_le_U1 : D.Ugrp ≤ D.U1 := fun _ hu => hu.1

theorem z_mem_U1 : z ∈ D.U1 := by
  have := h.setting.z_mem_clPre D.Uq
  rwa [h.setting_z] at this

theorem nrm_z : D.nrm z = z := by
  have hcz : (D.c : G) * z * (D.c : G)⁻¹ = z := by
    have := h.setting.z_comm D.c.2
    rw [h.setting_z] at this
    rw [this, mul_inv_cancel_right]
  simp only [nrm]
  rw [hcz, hcz, h.z_mul_z, one_mul]

theorem z_not_mem_Ugrp : z ∉ D.Ugrp := by
  intro hz
  have h2 := hz.2
  rw [D.nrm_z] at h2
  exact h.setting.z_ne_one (by rw [h.setting_z]; exact h2)

theorem eq_one_of_mem_Ugrp_E {u : G} (hu : u ∈ D.Ugrp)
    (huE : u ∈ D.E) : u = 1 := by
  have huQ := (D.Ugrp_le_U1 hu).1
  have hE1 : u ∈ D.E1 := by
    rw [← D.QG_inf_E]
    exact ⟨huQ, huE⟩
  have h0 : D.ψV (h.setting.cl u) = 0 := Two.eq_zero_of_mem_U48_W1 (D.Ugrp_le_U1 hu).2 hE1.2
  have hcl : h.setting.cl u = 0 := by
    rw [← map_zero D.ψV] at h0
    exact D.ψV.injective h0
  rcases (h.setting.cl_eq_zero_iff huQ).mp hcl with h1 | h1
  · exact h1
  · exfalso
    rw [h.setting_z] at h1
    exact D.z_not_mem_Ugrp (h1 ▸ hu)

include D in
theorem eq_one_or_z_of_mem_zpowers {x : G} (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h.z_mul_z
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.emod_add_mul_ediv k 2, hk, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

variable (hHat : HatM22SmallModules)

include hHat in
theorem nrm_mem_zpowers {u : G} (hu : u ∈ D.U1) : D.nrm u ∈ zpowers z := by
  set c : G := (D.c : G) with hc
  have hB := D.conjc_mem_U1 hu
  have hC := D.conjc_mem_U1 hB
  have hc3 : c * c * c = 1 := by
    have := congrArg Subtype.val D.c_pow
    simpa [pow_three, mul_assoc] using this
  have hN : D.nrm u ∈ D.U1 := mul_mem (mul_mem hu hB) hC
  have hcomm : c * D.nrm u * c⁻¹ = D.nrm u := by
    simp only [nrm]
    rw [← hc]
    have hCc : c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = u := by
      calc c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * u * (c * c * c)⁻¹ := by group
        _ = u := by rw [hc3]; group
    calc c * (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) * c⁻¹
        = (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) * (c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹) := by
          group
      _ = (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) * u := by rw [hCc]
      _ = u * ((c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) := D.U1_comm (mul_mem hB hC) hu
      _ = u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) := by group
  have hmem : D.nrm u ∈ h.setting.QG ⊓ centralizer (Xc : Set G) := by
    refine ⟨hN.1, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨j, rfl⟩
    have hcx : c * D.nrm u = D.nrm u * c := by
      calc c * D.nrm u = c * D.nrm u * c⁻¹ * c := by group
        _ = D.nrm u * c := by rw [hcomm]
    exact (Commute.zpow_left hcx j).eq
  rw [inf_centralizer_eq hHat h.setting_width D.ρ_c D.θ_mem D.θ_ne D.hat, h.setting_z] at hmem
  exact hmem

include hHat in
theorem card_Ugrp : Nat.card D.Ugrp = 2 ^ 6 := by
  have hzU := D.z_mem_U1
  have hzN : zpowers z ≤ normalizer (D.Ugrp : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_fintype fun n hn => ?_
    have e : z * n * z⁻¹ = n := by
      have h1 := h.setting.z_comm (h.setting.QG_le_M hn.1.1)
      rw [h.setting_z] at h1
      rw [← h1, mul_inv_cancel_right]
    rw [e]
    exact hn
  have h1 := card_sup_mul_card_inf_of_le_normalizer hzN
  have hinf : zpowers z ⊓ D.Ugrp = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rcases D.eq_one_or_z_of_mem_zpowers hx1 with e | e
    · rw [e]
      exact one_mem _
    · rw [e] at hx2
      exact absurd hx2 D.z_not_mem_Ugrp
  have hsup : zpowers z ⊔ D.Ugrp = D.U1 := by
    apply le_antisymm
    · exact sup_le (zpowers_le.mpr hzU) D.Ugrp_le_U1
    · intro u hu
      rcases D.eq_one_or_z_of_mem_zpowers (D.nrm_mem_zpowers hHat hu) with h0 | h0
      · exact mem_sup_right ⟨hu, h0⟩
      · have huz : u * z ∈ D.Ugrp :=
          ⟨mul_mem hu hzU, by rw [D.nrm_mul hu hzU, h0, D.nrm_z]; exact h.z_mul_z⟩
        have e : u = (u * z) * z := by rw [mul_assoc, h.z_mul_z, mul_one]
        rw [e]
        exact mul_mem (mem_sup_right huz) (mem_sup_left (mem_zpowers z))
  rw [hsup, hinf, card_bot, mul_one, Nat.card_zpowers, h.orderOf_z, D.card_U1] at h1
  omega

theorem zpow_c_cases (k : ℤ) :
    (D.c : G) ^ k = 1 ∨ (D.c : G) ^ k = D.c ∨ (D.c : G) ^ k = (D.c : G) * D.c := by
  have h3 : (D.c : G) ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact congrArg Subtype.val D.c_pow
  rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with hk | hk | hk <;> rw [hk]
  · left
    exact zpow_zero _
  · right; left
    exact zpow_one _
  · right; right
    rw [zpow_two]

include hHat in
theorem conj_mem_Ugrp {y : h.setting.M} (hyN : (y : G) ∈ normalizer (Xc : Set G))
    (hyU : ∀ v ∈ Two.U48, D.Φo (h.setting.ρ y) v ∈ Two.U48) {u : G} (hu : u ∈ D.Ugrp) :
    (y : G) * u * (y : G)⁻¹ ∈ D.Ugrp := by
  refine ⟨D.conj_mem_U1 hyU hu.1, ?_⟩
  set c : G := (D.c : G) with hc
  obtain ⟨d, hdd⟩ : ∃ d, d = (y : G)⁻¹ * c * y := ⟨_, rfl⟩
  have hdX : d ∈ Xc := by
    have := (mem_normalizer_iff.mp (inv_mem hyN) c).mp (mem_zpowers _)
    rw [hdd]
    simpa using this
  have hcd : c = (y : G) * d * (y : G)⁻¹ := by rw [hdd]; group
  have hexp : D.nrm ((y : G) * u * (y : G)⁻¹) =
      (y : G) * (u * (d * u * d⁻¹) * (d * (d * u * d⁻¹) * d⁻¹)) * (y : G)⁻¹ := by
    simp only [nrm]
    rw [← hc, hcd]
    group
  rw [hexp]
  have hc3 : c * c * c = 1 := by
    have := congrArg Subtype.val D.c_pow
    simpa [pow_three, mul_assoc] using this
  have hd1 : d ≠ 1 := by
    intro h1
    apply D.c_ne
    rw [← hc, hcd, h1]
    group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hdX
  have hB := D.conjc_mem_U1 hu.1
  have key : u * (d * u * d⁻¹) * (d * (d * u * d⁻¹) * d⁻¹) = D.nrm u := by
    rcases D.zpow_c_cases k with e | e | e
    · exact absurd (hk.symm.trans e) hd1
    · rw [← hk, e]
      rfl
    · rw [← hk, e]
      simp only [nrm]
      rw [← hc]
      have e1 : c * c * u * (c * c)⁻¹ = c * (c * u * c⁻¹) * c⁻¹ := by group
      have e2 : c * c * (c * c * u * (c * c)⁻¹) * (c * c)⁻¹ = c * u * c⁻¹ := by
        calc c * c * (c * c * u * (c * c)⁻¹) * (c * c)⁻¹
            = (c * c * c) * (c * u * c⁻¹) * (c * c * c)⁻¹ := by group
          _ = c * u * c⁻¹ := by rw [hc3]; group
      rw [e2, e1]
      calc u * (c * (c * u * c⁻¹) * c⁻¹) * (c * u * c⁻¹)
          = u * ((c * (c * u * c⁻¹) * c⁻¹) * (c * u * c⁻¹)) := by group
        _ = u * ((c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) := by
            rw [D.U1_comm (D.conjc_mem_U1 hB) hB]
        _ = u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) := by group
  rw [key, hu.2]
  group

end U

section Compl

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem exists_compl_T : ∃ K : Subgroup G, K ≤ D.T ∧ K ⊓ D.E = ⊥ ∧ Nat.card K = 2 ^ 10 := by
  obtain ⟨a, b, c, haN, hbN, hcN, haT, hbT, hcT, ha, hb, hc, ha2, hb2, hc2, hab4, hac, hbc⟩ :=
    D.exists_sGens_lift hOut hTw hHat
  obtain ⟨hgok, -, hid, hcl, hlen16, hEb⟩ := Two.sOK48_spec
  set S1M : Subgroup h.setting.M := closure {a, b, c} with hS1M
  have hS1le : Nat.card S1M ≤ 16 := card_closure_le_sixteen (Subtype.ext ha2) (Subtype.ext hb2)
    (Subtype.ext hc2) (Subtype.ext (by simpa using hab4)) (Subtype.ext hac) (Subtype.ext hbc)
  set f : h.setting.M →* (V12 ≃ₗ[ZMod 2] V12) := D.Φo.comp h.setting.ρ with hf
  have himg : S1M.map f = genGrp Two.sGens48 := by
    rw [hS1M, MonoidHom.map_closure]
    congr 1
    ext l
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, GenSet, Set.mem_setOf_eq, Two.sGens48, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, Or.inl rfl, ha⟩
      · exact ⟨_, Or.inr (Or.inl rfl), hb⟩
      · exact ⟨_, Or.inr (Or.inr rfl), hc⟩
    · rintro ⟨r, hr, hl⟩
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (LinearEquiv.ext fun x => (hl x).trans (ha x).symm)
      · exact Or.inr (Or.inl (LinearEquiv.ext fun x => (hl x).trans (hb x).symm))
      · exact Or.inr (Or.inr (LinearEquiv.ext fun x => (hl x).trans (hc x).symm))
  have hcard16 : Nat.card (S1M.map f) = 16 := by
    rw [himg, card_genGrp (enumGrp_sound (Two.gensOK_of_gensOKb hgok)) hid hcl, hlen16]
  set g : ↥S1M →* (V12 ≃ₗ[ZMod 2] V12) := f.comp S1M.subtype with hg
  have hgr : g.range = S1M.map f := by rw [hg, MonoidHom.range_comp, range_subtype]
  have hcardS1M : Nat.card S1M = 16 * Nat.card g.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hgr, hcard16] at h1
  have hker : Nat.card g.ker = 1 := by
    have := Nat.card_pos (α := g.ker)
    omega
  have hinj : ∀ y ∈ S1M, f y = 1 → y = 1 := by
    intro y hy hfy
    have hmem : (⟨y, hy⟩ : ↥S1M) ∈ g.ker := hfy
    rw [Subgroup.card_eq_one.mp hker, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  set S1 : Subgroup G := S1M.map h.setting.M.subtype with hS1
  have hS1card : Nat.card S1 = 16 := by
    rw [hS1, card_map_of_injective h.setting.M.subtype_injective, hcardS1M, hker]
  have hpres : ∀ {y : h.setting.M} {r : Array ℕ}, r ∈ Two.sGens48 →
      (∀ x, D.Φo (h.setting.ρ y) x = linOfRows r x) →
      ∀ v ∈ Two.U48, D.Φo (h.setting.ρ y) v ∈ Two.U48 := fun hr hy v hv => by
    rw [hy]
    exact Two.linOfRows_mem_U48 hr hv
  have hgen : ∀ y ∈ ({a, b, c} : Set h.setting.M), (y : G) ∈ normalizer (Xc : Set G) ∧
      (y : G) ∈ D.T ∧ ∀ v ∈ Two.U48, D.Φo (h.setting.ρ y) v ∈ Two.U48 := by
    rintro y (rfl | rfl | rfl)
    · exact ⟨haN, haT, hpres (by simp [Two.sGens48]) ha⟩
    · exact ⟨hbN, hbT, hpres (by simp [Two.sGens48]) hb⟩
    · exact ⟨hcN, hcT, hpres (by simp [Two.sGens48]) hc⟩
  have hS1N : S1 ≤ normalizer (D.Ugrp : Set G) := by
    rw [hS1, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyN, -, hyU⟩ := hgen y hy
    exact mem_normalizer_fintype fun n hn => D.conj_mem_Ugrp hHat hyN hyU hn
  have hS1T : S1 ≤ D.T := by
    rw [hS1, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (hgen y hy).2.1
  have hinf : S1 ⊓ D.Ugrp = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, hy, rfl⟩, hxU⟩
    have hyQ : (y : G) ∈ h.setting.QG := (D.Ugrp_le_U1 hxU).1
    have hfy : f y = 1 := by
      rw [hf, MonoidHom.comp_apply, (h.setting.ρ_eq_one_iff y).mpr hyQ, map_one]
    rw [hinj y hy hfy]
    exact one_mem _
  have hK := card_sup_mul_card_inf_of_le_normalizer hS1N
  rw [hinf, card_bot, mul_one, hS1card, D.card_Ugrp hHat] at hK
  refine ⟨S1 ⊔ D.Ugrp, sup_le hS1T (D.Ugrp_le_U1.trans ((h.setting.clPre_le_QG _).trans D.QG_le_T)),
    ?_, by rw [hK]; norm_num⟩
  obtain ⟨-, -, -, -, hidE, hcE, -⟩ := Two.ebOK46_spec
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxE⟩
  rw [sup_comm] at hxK
  obtain ⟨u, hu, s, hs, rfl⟩ := exists_mul_of_mem_sup hS1N hxK
  obtain ⟨y, hy, rfl⟩ := hs
  have huQ : u ∈ h.setting.QG := (D.Ugrp_le_U1 hu).1
  have hxM : u * (y : G) ∈ h.setting.M := mul_mem (h.setting.QG_le_M huQ) y.2
  have hρ : h.setting.ρ ⟨u * y, hxM⟩ = h.setting.ρ y := by
    have e : (⟨u * y, hxM⟩ : h.setting.M) = ⟨u, h.setting.QG_le_M huQ⟩ * y := rfl
    rw [e, map_mul, (h.setting.ρ_eq_one_iff ⟨u, h.setting.QG_le_M huQ⟩).mpr huQ, one_mul]
  have hEbar : D.Φo (h.setting.ρ y) ∈ Two.ebGrp := by
    rw [← hρ]
    exact D.Φo_mem_eb hOut hTw hxE hxM
  have hSbar : D.Φo (h.setting.ρ y) ∈ genGrp Two.sGens48 := by
    rw [← himg]
    exact ⟨y, hy, rfl⟩
  obtain ⟨r1, hr1, h1⟩ := complete hid hcl _ hSbar
  obtain ⟨r2, hr2, h2⟩ := complete hidE hcE _ hEbar
  have hok1 := (enumGrp_sound (Two.gensOK_of_gensOKb hgok) r1 hr1).1
  have hok2 := (enumGrp_sound Two.gensOK_eb r2 hr2).1
  have hr12 : r1 = r2 := (rowsOf_eq hok1 h1).symm.trans (rowsOf_eq hok2 h2)
  rcases hEb r1 hr1 with h0 | h0
  · have hy1 : f y = 1 := LinearEquiv.ext fun v => by
      rw [hf, MonoidHom.comp_apply, h1, h0, linOfRows_idR]
      rfl
    have hyy : y = 1 := hinj y hy hy1
    subst hyy
    simp only [map_one, mul_one] at hxE ⊢
    rw [mem_bot]
    exact D.eq_one_of_mem_Ugrp_E hu hxE
  · exfalso
    rw [hr12] at h0
    rw [List.contains_iff_mem.mpr hr2] at h0
    exact absurd h0 (by decide)

theorem exists_split : ∃ C : Subgroup G, C ≤ normalizer (D.E : Set G) ∧ C ⊓ D.E = ⊥ ∧
    C ⊔ D.E = normalizer (D.E : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKT, hKE, hKc⟩ := D.exists_compl_T hOut hTw hHat
  set M : Subgroup G := normalizer (D.E : Set G) with hMdef
  have hTM : D.T ≤ M := fun t ht =>
    mem_normalizer_fintype fun n hn => D.conj_mem_E (D.T_le_G13 ht) hn
  have hEM : D.E ≤ M := le_normalizer
  have hKM : K ≤ M := hKT.trans hTM
  have hEK : K ⊔ D.E = D.T := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (H := K) (N := D.E) hKM
    rw [hKE, card_bot, mul_one, hKc, D.card_E hOut hTw] at h1
    refine Subgroup.eq_of_le_of_card_ge (sup_le hKT (D.E_le_T hOut hTw)) ?_
    rw [D.card_T hOut hTw, h1]
    norm_num
  set V : Subgroup ↥M := D.E.subgroupOf M with hV
  haveI : V.Normal := Subgroup.normal_in_normalizer
  haveI : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (D.E_comm hOut hTw hHat (mem_subgroupOf.mp a.2) (mem_subgroupOf.mp b.2)))⟩⟩
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 11) (by
    rw [hV, Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv, D.card_E hOut hTw])
  let P : Sylow 2 ↥M := (D.sylowT hOut hTw).subtype hTM
  have hP : (P : Subgroup ↥M) = D.T.subgroupOf M := Sylow.coe_subtype _ hTM
  have hKP : K.subgroupOf M ≤ (P : Subgroup ↥M) := by
    rw [hP]
    exact fun x hx => mem_subgroupOf.mpr (hKT (mem_subgroupOf.mp hx))
  have hVK : V ⊓ K.subgroupOf M = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxK⟩
    have hx : (x : G) ∈ K ⊓ D.E := ⟨mem_subgroupOf.mp hxK, mem_subgroupOf.mp hxE⟩
    rw [hKE, mem_bot] at hx
    exact mem_bot.mpr (Subtype.ext hx)
  have hVKP : V ⊔ K.subgroupOf M = (P : Subgroup ↥M) := by
    rw [hP, hV, ← subgroupOf_sup hEM hKM, sup_comm, hEK]
  obtain ⟨C', hVC, hVC'⟩ := (CFSG.Quasithin.gaschutz hVp P).mpr ⟨K.subgroupOf M, hKP, hVK, hVKP⟩
  refine ⟨C'.map M.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxE⟩
    have hxV : x ∈ V ⊓ C' := ⟨mem_subgroupOf.mpr hxE, hx⟩
    rw [hVC, mem_bot] at hxV
    rw [hxV]
    exact one_mem _
  · have h1 : (V ⊔ C').map M.subtype = M := by
      rw [hVC', ← MonoidHom.range_eq_map, range_subtype]
    rw [Subgroup.map_sup, hV, subgroupOf_map_subtype, inf_of_le_left hEM] at h1
    rw [sup_comm]
    exact h1

end Compl

end Data41

end CFSG.Quasithin.H13.AS91
