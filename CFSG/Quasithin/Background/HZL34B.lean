module

public import CFSG.Quasithin.Background.HZL34

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H13.Ch9.L34M
open scoped commutatorElement

abbrev W0 : Subgroup W9 := maskSub 9 w0Basis

theorem card_W0 : Nat.card W0 = 2 ^ 5 :=
  card_maskSub w0_lt (nodup_of_nodupB _ _ w0_nodup).1

theorem z0_mem_W0 : z0 ∈ W0 := toW_mem_maskSub z0_mem_w0

theorem toW_inv (m : ℕ) : (toW 9 m)⁻¹ = toW 9 m := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h := toW_xor 9 m m
  rw [Nat.xor_self, toW_zero] at h
  exact h.symm

theorem xorLin_comm (c : List ℕ) : XorLin fun m => actM c m ^^^ m := fun x y => by
  show actM c (x ^^^ y) ^^^ (x ^^^ y) = actM c x ^^^ x ^^^ (actM c y ^^^ y)
  rw [actM_xor c x y]
  ac_rfl

theorem rho9_uG_toW {t : ℕ} (ht : t < 16) {m : ℕ} (hm : m < 512) :
    rho9 (uG t) (toW 9 m) = toW 9 (actM (colsU.getD t []) m) :=
  rho9_toW_cols (uG t) (cols_uG ht) hm

theorem rho9_uG_mem_moveSub {t : ℕ} (ht : t < 16) : rho9 (uG t) ∈ moveSub W0 := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 v
  have hm' : m < 512 := lt_of_lt_of_eq hm (by norm_num)
  have e : rho9 (uG t) (toW 9 m) * (toW 9 m)⁻¹ = toW 9 (actM (colsU.getD t []) m ^^^ m) := by
    rw [rho9_uG_toW ht hm', toW_inv, toW_xor]
  have hmem : toW 9 (actM (colsU.getD t []) m ^^^ m) ∈ W0 :=
    toW_mem_maskSub (mem_combos_of_xorLin (xorLin_comm _)
      (fun j hj => u_comm_mem_w0 t ht j hj) m hm)
  exact (congrArg (· ∈ W0) e).mpr hmem

theorem Rbar_le_moveSub : Rbar ≤ moveSub W0 := fun φ hφ => by
  obtain ⟨t, ht, rfl⟩ := mem_Rbar.1 hφ
  exact rho9_uG_mem_moveSub ht

theorem comm_mem_commV (t : ℕ) (ht : t < 16) (j : ℕ) (hj : j < 9) :
    toW 9 (actM (colsU.getD t []) (2 ^ j) ^^^ 2 ^ j) ∈ commV Rbar := by
  have hj' : 2 ^ j < 512 := lt_of_lt_of_eq (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num)
  have h := mem_commV (rho9_uG_mem_Rbar ht) (toW 9 (2 ^ j))
  have e1 : toW 9 (actM (colsU.getD t []) (2 ^ j) ^^^ 2 ^ j) =
      rho9 (uG t) (toW 9 (2 ^ j)) * (toW 9 (2 ^ j))⁻¹ := by
    rw [rho9_uG_toW ht hj', toW_inv, toW_xor]
  rw [e1]
  exact h

theorem commV_Rbar : commV Rbar = W0 := by
  refine le_antisymm (commV_le_iff.2 Rbar_le_moveSub) ?_
  rintro _ ⟨m, hm, rfl⟩
  refine mem_of_combos (fun m => toW 9 m ∈ commV Rbar) ?_ ?_ w0Basis ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    rw [w0Basis_eq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      exact comm_mem_commV _ (by norm_num) _ (by norm_num)

@[expose] def kcG (i : ℕ) : GL (Fin 3) F4 :=
  if i < 4 then ⁅uG (2 ^ i), xG⁆ else ⁅uG (2 ^ (i - 4)), yG⁆

theorem coe_kcG (i : ℕ) : ((kcG i : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = kcM i := by
  show ((if i < 4 then ⁅uG (2 ^ i), xG⁆ else ⁅uG (2 ^ (i - 4)), yG⁆ : GL (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4) = if i < 4 then uM (2 ^ i) * xM * uM (2 ^ i) * xMi
      else uM (2 ^ (i - 4)) * yM * uM (2 ^ (i - 4)) * yMi
  split_ifs
  · show ((uG (2 ^ i) * xG * (uG (2 ^ i))⁻¹ * xG⁻¹ : GL (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = _
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    rfl
  · show ((uG (2 ^ (i - 4)) * yG * (uG (2 ^ (i - 4)))⁻¹ * yG⁻¹ : GL (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = _
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    rfl

theorem coe_kcGs : ((List.range 8).map kcG).map Units.val = (List.range 8).map kcM := by
  rw [List.map_map]
  exact List.map_congr_left fun i _ => coe_kcG i

theorem commutator_Rbar_L34 : ⁅Rbar, L34⁆ = Rbar := by
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro k hk l hl
    have h1 : l * k⁻¹ * l⁻¹ ∈ Rbar :=
      (Subgroup.mem_normalizer_iff.1 (L34_le_normalizer_Rbar hl) k⁻¹).1 (Rbar.inv_mem hk)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact Rbar.mul_mem hk (by simpa [mul_assoc] using h1)
  · intro φ hφ
    obtain ⟨t, ht, rfl⟩ := mem_Rbar.1 hφ
    have hw : wGL ((List.range 8).map kcG) (koComm t) = uG t := by
      apply Units.ext
      rw [coe_wGL, coe_kcGs]
      exact koComm_ok t ht
    rw [← hw]
    refine rho9_wGL_mem (fun g hg => ?_) _
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    unfold kcG
    split_ifs with h4
    · rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator
        (rho9_uG_mem_Rbar (by interval_cases i <;> norm_num)) x_mem_L34
    · rw [map_commutatorElement]
      by_cases h8 : i - 4 < 4
      · exact Subgroup.commutator_mem_commutator
          (rho9_uG_mem_Rbar (by interval_cases (i - 4) <;> norm_num)) y_mem_L34
      · have h16 : 16 ≤ 2 ^ (i - 4) := by
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ (i - 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hu : uG (2 ^ (i - 4)) = uG ((2 ^ (i - 4)) % 16) := by
          apply Units.ext
          show um (fc (2 ^ (i - 4))) (fc (2 ^ (i - 4) / 4)) 0 =
            um (fc (2 ^ (i - 4) % 16)) (fc (2 ^ (i - 4) % 16 / 4)) 0
          congr 1
          · exact f4_eq_of_code (by show _ % 4 = _ % 4; omega)
          · exact f4_eq_of_code (by show _ % 4 = _ % 4; omega)
        rw [hu]
        exact Subgroup.commutator_mem_commutator
          (rho9_uG_mem_Rbar (Nat.mod_lt _ (by norm_num))) y_mem_L34

theorem rho9_uG_mul {c d : ℕ} (hc : c < 16) (hd : d < 16) :
    rho9 (uG c) * rho9 (uG d) = rho9 (uG (c ^^^ d)) := by
  rw [← map_mul]
  exact congrArg rho9 (Units.ext (uM_mul c hc d hd))

theorem rho9_uG_zero : rho9 (uG 0) = 1 := by
  rw [show uG 0 = 1 from Units.ext uM_zero, map_one]

theorem koAct_lt (g : ℕ) {d : ℕ} (hd : d < 16) : koAct g d < 16 := by
  unfold koAct
  split_ifs
  · exact (actM_u_lt d hd).1
  · exact (actM_u_lt d hd).2

theorem rho_conj_uG (g : ℕ) {c : ℕ} (hc : c < 16) :
    ∃ x ∈ L34, x * rho9 (uG c) * x⁻¹ = rho9 (uG (koAct g c)) := by
  by_cases hg : g = 0
  · refine ⟨_, x_mem_L34, ?_⟩
    rw [conj_uG_x hc]
    congr 2
    simp [koAct, hg]
  · refine ⟨_, y_mem_L34, ?_⟩
    rw [conj_uG_y hc]
    congr 2
    simp [koAct, hg]

theorem eq_of_le_Rbar {N : Subgroup (MulAut W9)} (hN : N ≤ Rbar) (h1 : N ≠ ⊥)
    (hP : L34 ≤ Subgroup.normalizer (N : Set (MulAut W9))) : N = Rbar := by
  obtain ⟨⟨φ, hφ⟩, hφ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h1
  have hφ1 : φ ≠ 1 := fun h => hφ1' (Subtype.ext h)
  obtain ⟨c, hc16, hc⟩ := mem_Rbar.1 (hN hφ)
  let P : ℕ → Prop := fun d => d < 16 ∧ rho9 (uG d) ∈ N
  have P0 : P 0 := ⟨by norm_num, by rw [rho9_uG_zero]; exact N.one_mem⟩
  have Pxor : ∀ a b, P a → P b → P (a ^^^ b) := by
    rintro a b ⟨ha, hNa⟩ ⟨hb, hNb⟩
    refine ⟨Nat.xor_lt_two_pow (n := 4) ha hb, ?_⟩
    have := N.mul_mem hNa hNb
    rwa [rho9_uG_mul ha hb] at this
  have Pact : ∀ g d, P d → P (koAct g d) := by
    rintro g d ⟨hd, hNd⟩
    obtain ⟨x, hx, hxe⟩ := rho_conj_uG g hd
    refine ⟨koAct_lt g hd, ?_⟩
    rw [← hxe]
    exact (Subgroup.mem_normalizer_iff.1 (hP hx) _).1 hNd
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hφ1 (by rw [← hc, rho9_uG_zero])
  obtain ⟨e, he, he1⟩ := List.mem_map.1 (irrK_cover c hc16 hc0)
  have hall : ∀ d ∈ derivB koAct [e.1] e.2, P d := by
    refine mem_of_derivB koAct P Pact P0 e.2 [e.1] fun d hd => ?_
    rw [List.mem_singleton] at hd
    rw [hd, he1]
    exact ⟨hc16, hc ▸ hφ⟩
  refine le_antisymm hN fun ψ hψ => ?_
  obtain ⟨d, hd, rfl⟩ := mem_Rbar.1 hψ
  exact (mem_of_combos P P0 Pxor _ hall d (irrK_ok e he d hd)).2

theorem rho_lAct (g : ℕ) {m : ℕ} (hm : m < 512) :
    ∃ x ∈ L34, x (toW 9 m) = toW 9 (lAct g m) := by
  by_cases hg : g = 0
  · refine ⟨_, x_mem_L34, ?_⟩
    rw [rho9_toW_cols xG cols_x hm, lAct, ite_eq_left hg]
  · refine ⟨_, y_mem_L34, ?_⟩
    rw [rho9_toW_cols yG cols_y hm, lAct, ite_eq_right hg]

theorem lAct_lt (g m : ℕ) (hm : m < 512) : lAct g m < 512 := by
  unfold lAct
  split_ifs
  · rw [← cols_x]
    exact actM_cols_lt _ hm
  · rw [← cols_y]
    exact actM_cols_lt _ hm

theorem eq_W0_of_lt {Y : Subgroup W9} (h1 : Subgroup.zpowers z0 < Y) (h2 : Y ≤ W0)
    (h3 : L34 ≤ stabSub Y) : Y = W0 := by
  obtain ⟨y, hyY, hyz⟩ := IsConcreteLE.exists_of_lt h1
  obtain ⟨m, hm, rfl⟩ := h2 hyY
  have hm0 : m ≠ 0 := fun h => hyz (by rw [h, toW_zero]; exact Subgroup.one_mem _)
  have hm1 : m ≠ 1 := fun h => hyz (by rw [h]; exact Subgroup.mem_zpowers _)
  obtain ⟨e, he, he1⟩ := List.mem_map.1 (irrW_cover m hm hm0 hm1)
  let P : ℕ → Prop := fun k => k < 2 ^ 9 ∧ toW 9 k ∈ Y
  have Pact : ∀ g k, P k → P (lAct g k) := by
    rintro g k ⟨hk9, hk⟩
    have hk' : k < 512 := lt_of_lt_of_eq hk9 (by norm_num)
    refine ⟨lt_of_lt_of_eq (lAct_lt g k hk') (by norm_num), ?_⟩
    obtain ⟨x, hx, hxe⟩ := rho_lAct g hk'
    rw [← hxe]
    exact ((h3 hx) _).2 hk
  have P0 : P 0 := ⟨by norm_num, by rw [toW_zero]; exact Y.one_mem⟩
  have hstart : ∀ k ∈ [e.1, 1], P k := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · rw [he1]
      exact ⟨combos_lt w0_lt _ hm, hyY⟩
    · exact ⟨by norm_num, h1.le (Subgroup.mem_zpowers _)⟩
  have hall := mem_of_derivB lAct P Pact P0 e.2 _ hstart
  have hcard := (MaskCoords.std 9).pow_le_card Y (derivB lAct [e.1, 1] e.2)
    (nodup_of_nodupB _ _ (irrW_ok e he).1).1 (fun a ha => (hall a ha).1)
    (fun a ha => (hall a ha).2)
  rw [(irrW_ok e he).2] at hcard
  exact Subgroup.eq_of_le_of_card_ge h2 (by rw [card_W0]; exact hcard)

theorem fix_Rbar (w : W9) (hw : w ∈ fixV Rbar) : w = 1 ∨ w = z0 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 w
  have hm' : m < 512 := lt_of_lt_of_eq hm (by norm_num)
  have key : ∀ t, t < 16 → actM (colsU.getD t []) m = m := fun t ht =>
    toW_inj (lt_of_lt_of_eq (by rw [← cols_u t ht]; exact actM_cols_lt _ hm') (by norm_num)) hm
      ((rho9_uG_toW ht hm').symm.trans (hw _ (rho9_uG_mem_Rbar ht)))
  rcases u_fix m hm' ⟨key 1 (by norm_num), key 2 (by norm_num), key 4 (by norm_num),
    key 8 (by norm_num)⟩ with rfl | rfl
  · exact Or.inl (toW_zero 9)
  · exact Or.inr rfl

theorem W0_inf_fixV : W0 ⊓ fixV Rbar = Subgroup.zpowers z0 := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨-, hv⟩
    rcases fix_Rbar v hv with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨z0_mem_W0, fun φ hφ => ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_Rbar.1 hφ
    exact (rho9_uG_toW ht (by norm_num)).trans (congrArg (toW 9) (u_fix1 t ht))

theorem commV_L34 : commV L34 = ⊤ := by
  have hcv : ∀ e ∈ cvData, e.2 < 9 := by decide
  have hl : ∀ a ∈ cvData.map (fun e => lAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2),
      (MaskCoords.std 9).vm a ∈ commV L34 := by
    intro a ha
    obtain ⟨⟨g, j⟩, hgj, rfl⟩ := List.mem_map.1 ha
    have hj : 2 ^ j < 512 :=
      lt_of_lt_of_eq (Nat.pow_lt_pow_right (by norm_num) (hcv _ hgj)) (by norm_num)
    obtain ⟨x, hx, hxe⟩ := rho_lAct g hj
    have h := mem_commV hx (toW 9 (2 ^ j))
    show toW 9 (lAct g (2 ^ j) ^^^ 2 ^ j) ∈ commV L34
    have e1 : toW 9 (lAct g (2 ^ j) ^^^ 2 ^ j) = x (toW 9 (2 ^ j)) * (toW 9 (2 ^ j))⁻¹ := by
      rw [hxe, toW_inv, toW_xor]
    rw [e1]
    exact h
  have hlt : ∀ a ∈ cvData.map (fun e => lAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2), a < 2 ^ 9 := by
    intro a ha
    obtain ⟨⟨g, j⟩, hgj, rfl⟩ := List.mem_map.1 ha
    have hj : 2 ^ j < 512 :=
      lt_of_lt_of_eq (Nat.pow_lt_pow_right (by norm_num) (hcv _ hgj)) (by norm_num)
    exact Nat.xor_lt_two_pow (lt_of_lt_of_eq (lAct_lt g _ hj) (by norm_num))
      (lt_of_lt_of_eq hj (by norm_num))
  have hcard := (MaskCoords.std 9).pow_le_card _ _ (nodup_of_nodupB _ _ cv_ok.1).1 hlt hl
  rw [List.length_map, cv_ok.2] at hcard
  refine Subgroup.eq_top_of_le_card _ ?_
  rw [Nat.card_eq_fintype_card, card_Wn]
  exact hcard

theorem parZ_std : parZ img9 z0 = L34 :=
  perfectCore_stab

theorem radZ_std : radZ img9 z0 = Rbar := by
  show pCoreOf 2 (parZ img9 z0) = _
  rw [parZ_std]
  exact pCoreOf_L34

theorem vZ_std : vZ img9 z0 = W0 := by
  show commV (radZ img9 z0) = _
  rw [radZ_std]
  exact commV_Rbar

theorem hzConcl_std : HZConcl img9 z0 4 := by
  unfold HZConcl
  rw [vZ_std, radZ_std, parZ_std]
  exact ⟨card_W0, card_Rbar, commutator_Rbar_L34,
    fun N h1 h2 h3 => eq_of_le_Rbar h1 h2 h3, fun Y h1 h2 h3 => eq_W0_of_lt h1 h2 h3,
    W0_inf_fixV, commV_L34⟩

theorem exists_equiv_z0 {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    (h : BinaryNineTensor H ⊤ ⊥ 1) {z : V} (hz1 : z ≠ 1) {S : Subgroup (MulAut V)}
    (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hzS : z ∈ fixV S) :
    ∃ e : V ≃* W9, H.map (congrHom e) = img9 ∧ e z = z0 := by
  obtain ⟨e₀, he₀⟩ := exists_equiv_w9 h
  have hcH : Nat.card ↥img9 = Nat.card ↥H := by
    rw [← he₀]
    exact card_map_congrHom e₀ H
  have hS' : Nat.card ↥(S.map (congrHom e₀)) = 2 ^ (Nat.card ↥img9).factorization 2 := by
    rw [hcH, ← hS]
    exact card_map_congrHom e₀ S
  have hSH' : S.map (congrHom e₀) ≤ img9 := by
    rw [← he₀]
    exact Subgroup.map_mono hSH
  have hz' : e₀ z ∈ fixV (S.map (congrHom e₀)) := by
    rintro _ ⟨y, hy, rfl⟩
    show e₀ (y (e₀.symm (e₀ z))) = e₀ z
    rw [MulEquiv.symm_apply_apply, hzS y hy]
  have hz1' : e₀ z ≠ 1 := fun h' => hz1 (e₀.injective (h'.trans (map_one e₀).symm))
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_of_fixV hSH' hS' (Rbar_le_L34.trans L34_le_img9)
    isPGroup_Rbar fix_Rbar hz' hz1'
  exact exists_equiv_std e₀ he₀ hg hgz

theorem hzConcl_of_binaryNine {V : Type} [CommGroup V]
    [Finite V] {H : Subgroup (MulAut V)} (h : BinaryNineTensor H ⊤ ⊥ 1) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) : HZConcl H z 4 := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  have key : ∀ (A : Subgroup (MulAut W9)) (w : W9), A = img9 → w = z0 → HZConcl A w 4 := by
    rintro A w rfl rfl
    exact hzConcl_std
  exact HZConcl.of_map e (key _ _ he hez)

end CFSG.Quasithin.H.L34Z
