module

public import CFSG.Quasithin.Background.HZCoc24

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans
open scoped commutatorElement

theorem pCoreOf_subgroupOf {G : Type*} [Group G] {X A : Subgroup G} (h : X ≤ A) (p : ℕ) :
    pCoreOf p (X.subgroupOf A) = (pCoreOf p X).subgroupOf A := by
  have h1 := pCoreOf_map_of_injective p A.subtype A.subtype_injective (X.subgroupOf A)
  rw [Subgroup.map_subgroupOf_eq_of_le h] at h1
  apply Subgroup.map_injective A.subtype_injective
  rw [← h1, Subgroup.map_subgroupOf_eq_of_le
    ((CFSG.LieType.BorelTits.pCoreOf_le p X).trans h)]

theorem KSp_le_autPerm : KSp ≤ AutPerm := KSp_le_Lz.trans Lz_le

theorem pCoreOf_img11_Lz :
    pCoreOf 2 (img11 Lz) = img11 KSp := by
  rw [img11, pCoreOf_map_of_injective 2 _ (rho11_injective AutPerm le_rfl),
    pCoreOf_subgroupOf Lz_le, pCoreOf_Lz]
  rfl

theorem card_img11_KSp : Nat.card ↥(img11 KSp) = 2 ^ 6 := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe KSp_le_autPerm).toEquiv, card_KSp]
  norm_num

theorem ksP_mul_ksPerm (c : Fin 64) (i : Fin 6) :
    ksP c * ksPerm i = ksP ⟨c ^^^ 2 ^ (i : ℕ), Nat.xor_lt_two_pow (n := 6) c.2 (by
      have := i.2
      interval_cases (i : ℕ) <;> norm_num)⟩ := by
  refine perm_eq_of_hasArr (hasArr_mul (hasArr_ksP c) (hasArr_permOfArr (ksArr_ok i).1)) ?_
  rw [ksC_mulR c c.2 i i.2]
  exact hasArr_ksP _

@[expose] def ksL : List (Equiv.Perm (Fin 24)) :=
  (List.range 6).map fun i => if h : i < 6 then ksPerm ⟨i, h⟩ else 1

theorem hasArr_ksL : ∀ i, HasArr (ksL.getD i 1) (((List.range 6).map ksArr).getD i idArr) := by
  intro i
  by_cases hi : i < 6
  · rw [ksL, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range, hi, ↓reduceDIte]
    exact hasArr_permOfArr _
  · rw [ksL, List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by simpa using hi)]
    exact hasArr_one

@[expose] def xorOf (w : List ℕ) : ℕ := (w.map (2 ^ ·)).foldr (· ^^^ ·) 0

theorem ksP_mul_wPerm : ∀ (w : List ℕ), (∀ i ∈ w, i < 6) → ∀ (c : Fin 64)
    (hc : c.val ^^^ xorOf w < 64), ksP c * wPerm ksL w = ksP ⟨c.val ^^^ xorOf w, hc⟩
  | [], _hw, c, hc => by
    rw [wPerm, mul_one]
    congr 1
    exact Fin.ext (by simp [xorOf])
  | i :: w, hw, c, hc => by
    have hi := hw i List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 6 := fun j hj => hw j (List.mem_cons_of_mem i hj)
    have hgi : ksL.getD i 1 = ksPerm ⟨i, hi⟩ := by
      rw [ksL, List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_map, List.getElem_range, hi, ↓reduceDIte]
    rw [wPerm, hgi, ← mul_assoc, ksP_mul_ksPerm]
    have hc' : (c.val ^^^ 2 ^ i) ^^^ xorOf w < 64 := by
      rw [Nat.xor_assoc]
      exact hc
    rw [ksP_mul_wPerm w hw' _ hc']
    congr 1
    exact Fin.ext (by simp only [xorOf, List.map_cons, List.foldr_cons, Nat.xor_assoc])

theorem ksP_mul (c d : Fin 64) :
    ksP c * ksP d = ksP ⟨c.val ^^^ d.val, Nat.xor_lt_two_pow (n := 6) c.2 d.2⟩ := by
  have hb : ∀ i ∈ (List.range 6).filter (fun i => d.val.testBit i), i < 6 := fun i hi =>
    List.mem_range.1 (List.mem_filter.1 hi).1
  have hd : xorOf ((List.range 6).filter fun i => d.val.testBit i) = d.val := bits_xor d d.2
  have h := hasArr_wPerm hasArr_ksL ((List.range 6).filter fun i => d.val.testBit i)
  rw [ksC_word d d.2] at h
  rw [perm_eq_of_hasArr (hasArr_ksP d) h,
    ksP_mul_wPerm _ hb c (by rw [hd]; exact Nat.xor_lt_two_pow (n := 6) c.2 d.2)]
  congr 1
  exact Fin.ext (congrArg (c.val ^^^ ·) hd)

abbrev W0 : Subgroup W11 := maskSub 11 w0Basis

theorem card_W0 : Nat.card W0 = 2 ^ 7 :=
  card_maskSub w0_lt (nodup_of_nodupB _ _ w0_nodup).1

theorem z0_mem_W0 : z0 ∈ W0 := toW_mem_maskSub z0_mem_w0

theorem toW_inv (m : ℕ) : (toW 11 m)⁻¹ = toW 11 m := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h := toW_xor 11 m m
  rw [Nat.xor_self, toW_zero] at h
  exact h.symm

theorem xorLin_comm (a : Array ℕ) : XorLin fun m => act11 a m ^^^ m := fun x y => by
  show act11 a (x ^^^ y) ^^^ (x ^^^ y) = act11 a x ^^^ x ^^^ (act11 a y ^^^ y)
  rw [xorLin_act11 a x y]
  ac_rfl

theorem ksPerm_mem_commSub (i : Fin 6) :
    rho11 AutPerm le_rfl ⟨ksPerm i, ksPerm_mem i⟩ ∈ moveSub W0 := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
  show (rho11 AutPerm le_rfl ⟨ksPerm i, ksPerm_mem i⟩) (toW 11 m) * (toW 11 m)⁻¹ ∈ W0
  have e : (rho11 AutPerm le_rfl ⟨ksPerm i, ksPerm_mem i⟩) (toW 11 m) * (toW 11 m)⁻¹ =
      toW 11 (act11 (ksArr i) m ^^^ m) := by
    rw [rho11_toW AutPerm le_rfl ⟨ksPerm i, ksPerm_mem i⟩ (hasArr_permOfArr (ksArr_ok i).1) m,
      toW_inv, toW_xor]
  rw [e]
  exact toW_mem_maskSub (mem_combos_of_xorLin (xorLin_comm (ksArr i))
    (fun j hj => ks_comm_mem_w0 i i.2 j hj) m hm)

theorem img11_KSp_le_commSub : img11 KSp ≤ moveSub W0 := by
  have hQ : KSp ≤ ((moveSub W0).comap (rho11 AutPerm le_rfl)).map AutPerm.subtype := by
    rw [KSp, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨ksPerm i, ksPerm_mem i⟩, ksPerm_mem_commSub i, rfl⟩
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτ, hτσ⟩ := hQ (Subgroup.mem_subgroupOf.1 hσ)
  rw [show σ = τ from Subtype.ext hτσ.symm]
  exact hτ

theorem ksRho_mem_img11_KSp (i : Fin 6) :
    rho11 AutPerm le_rfl ⟨ksPerm i, ksPerm_mem i⟩ ∈ img11 KSp :=
  ⟨⟨ksPerm i, ksPerm_mem i⟩, Subgroup.mem_subgroupOf.2 (ksPerm_mem_KSp i), rfl⟩

theorem comm_mem_commV (i : ℕ) (hi : i < 6) (j : ℕ) :
    toW 11 (act11 (ksArr i) (2 ^ j) ^^^ 2 ^ j) ∈ commV (img11 KSp) := by
  have h := mem_commV (ksRho_mem_img11_KSp ⟨i, hi⟩) (toW 11 (2 ^ j))
  have e1 : toW 11 (act11 (ksArr i) (2 ^ j) ^^^ 2 ^ j) =
      (rho11 AutPerm le_rfl ⟨ksPerm ⟨i, hi⟩, ksPerm_mem _⟩) (toW 11 (2 ^ j)) *
        (toW 11 (2 ^ j))⁻¹ := by
    rw [rho11_toW AutPerm le_rfl _ (hasArr_permOfArr (ksArr_ok ⟨i, hi⟩).1), toW_inv, toW_xor]
  rw [e1]
  exact h

theorem commV_img11_KSp : commV (img11 KSp) = W0 := by
  refine le_antisymm (commV_le_iff.2 img11_KSp_le_commSub) ?_
  rintro _ ⟨m, hm, rfl⟩
  refine mem_of_combos (fun m => toW 11 m ∈ commV (img11 KSp)) ?_ ?_ w0Basis ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    rw [w0Basis_eq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact comm_mem_commV _ (by norm_num) _

theorem hasArr_ksL_inv (k : ℕ) (hk : k < 6) : HasArr (ksPerm ⟨k, hk⟩)⁻¹ (ksArr k) := by
  have h : (ksPerm ⟨k, hk⟩)⁻¹ = ksPerm ⟨k, hk⟩ :=
    inv_eq_of_mul_eq_one_right (permOfArr_mul_self _)
  rw [h]
  exact hasArr_permOfArr _

@[expose] def kcL : List (Equiv.Perm (Fin 24)) :=
  (List.range 12).map fun i => if h : i < 6 then ⁅ksPerm ⟨i, h⟩, lzX⁆ else
    if h' : i - 6 < 6 then ⁅ksPerm ⟨i - 6, h'⟩, lzY⁆ else 1

theorem hasArr_kcL : ∀ i, HasArr (kcL.getD i 1) (((List.range 12).map kcArr).getD i idArr) := by
  intro i
  by_cases hi : i < 12
  · rw [kcL, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range]
    unfold kcArr
    by_cases h6 : i < 6
    · simp only [h6, ↓reduceDIte, ↓reduceIte]
      rw [commutatorElement_def, mul_assoc (ksPerm ⟨i, h6⟩ * lzX)]
      exact hasArr_mul (hasArr_mul (hasArr_permOfArr _) hasArr_lzX)
        (hasArr_mul (hasArr_ksL_inv i h6) hasArr_lzXinv)
    · have h' : i - 6 < 6 := by omega
      simp only [h6, h', ↓reduceDIte, ↓reduceIte]
      rw [commutatorElement_def, mul_assoc (ksPerm ⟨i - 6, h'⟩ * lzY)]
      exact hasArr_mul (hasArr_mul (hasArr_permOfArr _) hasArr_lzY)
        (hasArr_mul (hasArr_ksL_inv (i - 6) h') hasArr_lzYinv)
  · rw [kcL, List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by simpa using hi)]
    exact hasArr_one

theorem commutator_KSp_Lz : ⁅KSp, Lz⁆ = KSp := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro k hk l hl
    have h1 : l * k⁻¹ * l⁻¹ ∈ KSp :=
      (Subgroup.mem_normalizer_iff.1 (Lz_le_normalizer_KSp hl) k⁻¹).1 (KSp.inv_mem hk)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact KSp.mul_mem hk (by simpa [mul_assoc] using h1)
  · show Subgroup.closure (Set.range ksPerm) ≤ ⁅KSp, Lz⁆
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have h := hasArr_wPerm hasArr_kcL (ksComm i)
    rw [ksComm_ok i i.2] at h
    have e : ksPerm i = wPerm kcL (ksComm i) :=
      perm_eq_of_hasArr (hasArr_permOfArr (ksArr_ok i).1) h
    rw [e]
    refine wPerm_mem (fun p hp => ?_) _
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    by_cases h6 : k < 6
    · simp only [h6, ↓reduceDIte]
      exact Subgroup.commutator_mem_commutator (ksPerm_mem_KSp _) lzX_mem_Lz
    · by_cases h' : k - 6 < 6
      · simp only [h6, h', ↓reduceDIte]
        exact Subgroup.commutator_mem_commutator (ksPerm_mem_KSp _) lzY_mem_Lz
      · simp only [h6, h', ↓reduceDIte]
        exact Subgroup.one_mem _

theorem commutator_img11_KSp_Lz : ⁅img11 KSp, img11 Lz⁆ = img11 KSp := by
  have h : ⁅KSp.subgroupOf AutPerm, Lz.subgroupOf AutPerm⁆ = KSp.subgroupOf AutPerm := by
    apply Subgroup.map_injective AutPerm.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le Lz_le,
      Subgroup.map_subgroupOf_eq_of_le KSp_le_autPerm, commutator_KSp_Lz]
  rw [img11, img11, ← Subgroup.map_commutator, h]

theorem ksP_mem_autPerm (c : Fin 64) : ksP c ∈ AutPerm := KSp_le_autPerm (ksP_mem_KSp c)

theorem mem_img11_KSp {φ : MulAut W11} :
    φ ∈ img11 KSp ↔ ∃ c, rho11 AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ = φ := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨c, hc⟩ := mem_KSp_iff.1 (Subgroup.mem_subgroupOf.1 hσ)
    exact ⟨c, congrArg _ (Subtype.ext hc)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨ksP c, ksP_mem_autPerm c⟩, Subgroup.mem_subgroupOf.2 (ksP_mem_KSp c), rfl⟩

theorem rho_ksP_mul (c d : Fin 64) :
    rho11 AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ *
      rho11 AutPerm le_rfl ⟨ksP d, ksP_mem_autPerm d⟩ =
    rho11 AutPerm le_rfl ⟨ksP ⟨c.val ^^^ d.val, Nat.xor_lt_two_pow (n := 6) c.2 d.2⟩,
      ksP_mem_autPerm _⟩ := by
  rw [← map_mul]
  exact congrArg _ (Subtype.ext (ksP_mul c d))

theorem rho_lzX_mem : rho11 AutPerm le_rfl ⟨lzX, lzX_mem⟩ ∈ img11 Lz :=
  ⟨⟨lzX, lzX_mem⟩, Subgroup.mem_subgroupOf.2 lzX_mem_Lz, rfl⟩

theorem rho_lzY_mem : rho11 AutPerm le_rfl ⟨lzY, lzY_mem⟩ ∈ img11 Lz :=
  ⟨⟨lzY, lzY_mem⟩, Subgroup.mem_subgroupOf.2 lzY_mem_Lz, rfl⟩

theorem ksAct_lt (g : ℕ) {d : ℕ} (hd : d < 64) : ksAct g d < 64 := by
  unfold ksAct
  split_ifs
  · exact (actM_ks_lt d hd).1
  · exact (actM_ks_lt d hd).2

theorem rho_conj_ksP (g : ℕ) (c : Fin 64) :
    ∃ x ∈ img11 Lz, x * rho11 AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ * x⁻¹ =
      rho11 AutPerm le_rfl ⟨ksP ⟨ksAct g c, ksAct_lt g c.2⟩, ksP_mem_autPerm _⟩ := by
  by_cases hg : g = 0
  · refine ⟨_, rho_lzX_mem, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg _ (Subtype.ext ?_)
    show lzX * ksP c * lzX⁻¹ = _
    rw [conj_ksP_x]
    congr 1
    exact Fin.ext (by simp [ksAct, hg])
  · refine ⟨_, rho_lzY_mem, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg _ (Subtype.ext ?_)
    show lzY * ksP c * lzY⁻¹ = _
    rw [conj_ksP_y]
    congr 1
    exact Fin.ext (by simp [ksAct, hg])

theorem eq_of_le_img11_KSp {N : Subgroup (MulAut W11)} (hN : N ≤ img11 KSp) (h1 : N ≠ ⊥)
    (hP : img11 Lz ≤ Subgroup.normalizer (N : Set (MulAut W11))) : N = img11 KSp := by
  obtain ⟨⟨φ, hφ⟩, hφ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h1
  have hφ1 : φ ≠ 1 := fun h => hφ1' (Subtype.ext h)
  obtain ⟨c, hc⟩ := mem_img11_KSp.1 (hN hφ)
  let P : ℕ → Prop := fun d =>
    ∃ hd : d < 64, rho11 AutPerm le_rfl ⟨ksP ⟨d, hd⟩, ksP_mem_autPerm _⟩ ∈ N
  have P0 : P 0 := ⟨by norm_num, by
    have h0 : (⟨ksP ⟨0, by norm_num⟩, ksP_mem_autPerm _⟩ : ↥AutPerm) = 1 :=
      Subtype.ext ksP_zero
    rw [h0, map_one]
    exact N.one_mem⟩
  have Pxor : ∀ a b, P a → P b → P (a ^^^ b) := by
    rintro a b ⟨ha, hNa⟩ ⟨hb, hNb⟩
    refine ⟨Nat.xor_lt_two_pow (n := 6) ha hb, ?_⟩
    have := N.mul_mem hNa hNb
    rwa [rho_ksP_mul] at this
  have Pact : ∀ g d, P d → P (ksAct g d) := by
    rintro g d ⟨hd, hNd⟩
    obtain ⟨x, hx, hxe⟩ := rho_conj_ksP g ⟨d, hd⟩
    refine ⟨ksAct_lt g hd, ?_⟩
    rw [← hxe]
    exact (Subgroup.mem_normalizer_iff.1 (hP hx) _).1 hNd
  have hc0 : c.val ≠ 0 := by
    intro h
    apply hφ1
    rw [← hc]
    have h0 : (⟨ksP c, ksP_mem_autPerm c⟩ : ↥AutPerm) = 1 :=
      Subtype.ext (by rw [show c = 0 from Fin.ext h]; exact ksP_zero)
    rw [h0, map_one]
  obtain ⟨e, he, he1⟩ := List.mem_map.1 (irrK_cover c c.2 hc0)
  have hall : ∀ d ∈ derivB ksAct [e.1] e.2, P d := by
    refine mem_of_derivB ksAct P Pact P0 e.2 [e.1] fun d hd => ?_
    rw [List.mem_singleton] at hd
    rw [hd, he1]
    exact ⟨c.2, hc ▸ hφ⟩
  refine le_antisymm hN fun ψ hψ => ?_
  obtain ⟨d, rfl⟩ := mem_img11_KSp.1 hψ
  obtain ⟨_, h⟩ := mem_of_combos P P0 Pxor _ hall d (irrK_ok e he d d.2)
  exact h

theorem rho_lzAct (g m : ℕ) : ∃ x ∈ img11 Lz, x (toW 11 m) = toW 11 (lzAct g m) := by
  by_cases hg : g = 0
  · refine ⟨_, rho_lzX_mem, ?_⟩
    rw [rho11_toW AutPerm le_rfl ⟨lzX, lzX_mem⟩ hasArr_lzX m, lzAct, ite_eq_left hg]
  · refine ⟨_, rho_lzY_mem, ?_⟩
    rw [rho11_toW AutPerm le_rfl ⟨lzY, lzY_mem⟩ hasArr_lzY m, lzAct, ite_eq_right hg]

theorem eq_W0_of_lt {Y : Subgroup W11} (h1 : Subgroup.zpowers z0 < Y) (h2 : Y ≤ W0)
    (h3 : img11 Lz ≤ stabSub Y) : Y = W0 := by
  obtain ⟨y, hyY, hyz⟩ := IsConcreteLE.exists_of_lt h1
  obtain ⟨m, hm, rfl⟩ := h2 hyY
  have hm0 : m ≠ 0 := fun h => hyz (by rw [h, toW_zero]; exact Subgroup.one_mem _)
  have hm31 : m ≠ 31 := fun h => hyz (by rw [h]; exact Subgroup.mem_zpowers _)
  obtain ⟨e, he, he1⟩ := List.mem_map.1 (irrW_cover m hm hm0 hm31)
  let P : ℕ → Prop := fun k => k < 2 ^ 11 ∧ toW 11 k ∈ Y
  have Pact : ∀ g k, P k → P (lzAct g k) := by
    rintro g k ⟨-, hk⟩
    refine ⟨by unfold lzAct; exact act11_lt _ _, ?_⟩
    obtain ⟨x, hx, hxe⟩ := rho_lzAct g k
    rw [← hxe]
    exact ((h3 hx) _).2 hk
  have P0 : P 0 := ⟨by norm_num, by rw [toW_zero]; exact Y.one_mem⟩
  have hstart : ∀ k ∈ [e.1, 31], P k := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · rw [he1]
      exact ⟨combos_lt w0_lt _ hm, hyY⟩
    · exact ⟨by norm_num, h1.le (Subgroup.mem_zpowers _)⟩
  have hall := mem_of_derivB lzAct P Pact P0 e.2 _ hstart
  have hcard := (MaskCoords.std 11).pow_le_card Y (derivB lzAct [e.1, 31] e.2)
    (nodup_of_nodupB _ _ (irrW_ok e he).1).1 (fun a ha => (hall a ha).1)
    (fun a ha => (hall a ha).2)
  rw [(irrW_ok e he).2] at hcard
  exact Subgroup.eq_of_le_of_card_ge h2 (by rw [card_W0]; exact hcard)

theorem W0_inf_fixV : W0 ⊓ fixV (img11 KSp) = Subgroup.zpowers z0 := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨-, hv⟩
    rcases fix_ksRho v (fun i => hv _ (ksRho_mem_img11_KSp i)) with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨z0_mem_W0, fun φ hφ => ?_⟩
    obtain ⟨c, rfl⟩ := mem_img11_KSp.1 hφ
    exact (rho11_toW AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ (hasArr_ksP c) 31).trans
      (congrArg (toW 11) (ksC_fix c c.2))

theorem commV_img11_Lz : commV (img11 Lz) = ⊤ := by
  have hl : ∀ a ∈ cvData.map (fun e => lzAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2),
      (MaskCoords.std 11).vm a ∈ commV (img11 Lz) := by
    intro a ha
    obtain ⟨⟨g, j⟩, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨x, hx, hxe⟩ := rho_lzAct g (2 ^ j)
    have h := mem_commV hx (toW 11 (2 ^ j))
    show toW 11 (lzAct g (2 ^ j) ^^^ 2 ^ j) ∈ commV (img11 Lz)
    have e1 : toW 11 (lzAct g (2 ^ j) ^^^ 2 ^ j) = x (toW 11 (2 ^ j)) * (toW 11 (2 ^ j))⁻¹ := by
      rw [hxe, toW_inv, toW_xor]
    rw [e1]
    exact h
  have hlt : ∀ a ∈ cvData.map (fun e => lzAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2), a < 2 ^ 11 := by
    intro a ha
    obtain ⟨⟨g, j⟩, hgj, rfl⟩ := List.mem_map.1 ha
    have hcv : ∀ e ∈ cvData, e.2 < 11 := by decide
    have hj : j < 11 := hcv _ hgj
    exact Nat.xor_lt_two_pow (by unfold lzAct; exact act11_lt _ _)
      (Nat.pow_lt_pow_right (by norm_num) hj)
  have hcard := (MaskCoords.std 11).pow_le_card _ _ (nodup_of_nodupB _ _ cv_ok.1).1 hlt hl
  rw [List.length_map, cv_ok.2] at hcard
  refine Subgroup.eq_top_of_le_card _ ?_
  rw [Nat.card_eq_fintype_card, card_Wn]
  exact hcard

theorem exists_fus : ∃ φ ∈ img11 AutPerm, φ z0 ≠ z0 ∧ φ z0 ∈ W0 := by
  obtain ⟨⟨e, he, he1⟩, hW⟩ := fus_ok
  obtain ⟨φ, hφ, hφz⟩ := orbTree_mem e he
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hφz, he1]
    intro h
    have := toW_inj (by norm_num) (by norm_num) h
    norm_num at this
  · rw [hφz, he1]
    exact toW_mem_maskSub hW

end CFSG.Quasithin.H.Coc24
