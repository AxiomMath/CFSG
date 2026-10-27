module

public import CFSG.Quasithin.Background.B3Four2
public import CFSG.Quasithin.Background.B3Named6
public import CFSG.Quasithin.Background.B3Two

public section

namespace CFSG.Quasithin.B3

open scoped commutatorElement

variable {k : Mod}

theorem subsetT_iff {A B : List Tab} : subsetT A B = true ↔ ∀ t ∈ A, t ∈ B := by
  simp only [subsetT, List.all_eq_true, List.contains_iff_mem]

theorem seteqT_iff {A B : List Tab} : seteqT A B = true ↔ ∀ t, t ∈ A ↔ t ∈ B := by
  simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun h t => ⟨h.1 t, h.2 t⟩, fun h => ⟨fun t ht => (h t).1 ht, fun t ht => (h t).2 ht⟩⟩

theorem subOf_le_of_subsetT {n : ℕ} {A B : List Tab} (hA : subOK n A = true)
    (hB : subOK n B = true) (h : subsetT A B = true) : subOf n A ≤ subOf n B := by
  intro x hx
  rw [mem_subOf hA] at hx
  rw [mem_subOf hB]
  exact subsetT_iff.1 h _ hx

theorem subOK_id (n : ℕ) : subOK n [idT n] = true := by
  have h1 : isTab n (idT n) = true := by
    rw [← tab_one (n := n)]
    exact isTab_tab 1
  have h2 : mulT (idT n) (idT n) = idT n := by
    rw [← tab_one (n := n), ← tab_mul, mul_one]
  have h3 : invT (idT n) = idT n := by
    rw [← tab_one (n := n), ← tab_inv, inv_one]
  simp [subOK, h1, h2, h3]

theorem subOf_id (n : ℕ) : subOf n [idT n] = ⊥ := by
  ext x
  rw [mem_subOf (subOK_id n), Subgroup.mem_bot, List.mem_singleton]
  constructor
  · intro h
    exact tab_injective (h.trans tab_one.symm)
  · intro h
    rw [h, tab_one]

theorem subOf_eq_bot_of_seteq {n : ℕ} {J : List Tab} (hJ : subOK n J = true)
    (h : seteqT J [idT n] = true) : subOf n J = ⊥ :=
  (subOf_congr hJ (subOK_id n) h).trans (subOf_id n)

theorem rk_subOf {n : ℕ} {K : List Tab} (hK : subOK n K = true) :
    rk (subOf n K) = padicValNat 2 K.length := by
  unfold rk
  rw [card_subOf hK]

structure StructOK (k : Mod) (b : Bool) (e : ℕ) : Prop where
  hTl : subOK 6 (Tl 6) = true
  hEA : chkEA 6 (Tl 6) (Dl 6) = true
  hT0 : subOK 6 (Tgl 6 b) = true
  hTlen : (Tgl 6 b).length = 2 ^ e
  hsub : ∀ t ∈ Tgl 6 b, t ∈ Tl 6
  hTHl : subsetT (Tgl 6 b) (Hl 6 b) = true
  hflag : flagOK 6 k b = true
  hH1 : subOK 6 (H1tab 6 k b) = true
  hH2 : subOK 6 (H2tab 6 k b) = true
  hTH1 : subsetT (Tgl 6 b) (H1tab 6 k b) = true
  hTH2 : subsetT (Tgl 6 b) (H2tab 6 k b) = true
  hH1len : (H1tab 6 k b).length = 3 * 2 ^ e
  hH2len : (H2tab 6 k b).length = 3 * 2 ^ e
  hR1 : subOK 6 (rTab (H1tab 6 k b) (Tgl 6 b)) = true
  hR2 : subOK 6 (rTab (H2tab 6 k b) (Tgl 6 b)) = true

theorem structOK_of_chk {b : Bool} {e : ℕ} (h : chkStruct6 k b e = true) : StructOK k b e := by
  simp only [chkStruct6, fourD, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem card_Hg6 (b : Bool) : Nat.card (Hg 6 b) = if b then 720 else 360 := by
  cases b
  · have h := card_alternatingGroup (α := Fin 6)
    rw [Fintype.card_fin] at h
    simp only [Hg, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.card_eq_fintype_card, h]
    decide
  · simp only [Hg, ↓reduceIte]
    rw [Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

theorem std6 {b : Bool} {e m : ℕ} (hs : StructOK k b e) (hH : Nat.card (Hg 6 b) = 2 ^ e * m)
    (hm : m % 2 = 1) : Std 6 b := by
  have hTH : Tgrp 6 b ≤ Hg 6 b := by
    intro x hx
    have h1 : tab x ∈ Tgl 6 b := (mem_Tgrp b hs.hT0).1 hx
    exact ((Hl_spec b).1 x).2 (subsetT_iff.1 hs.hTHl _ h1)
  have hcard : Nat.card (Tgrp 6 b) = 2 ^ e := by
    unfold Tgrp
    rw [card_subOf hs.hT0, hs.hTlen]
  obtain ⟨hp, hidx⟩ := sylow_of_cards hTH hcard hH hm
  exact ⟨by norm_num, hs.hTl, hs.hEA, hs.hT0, hs.hsub, hTH, hp, hidx⟩

theorem std6_G (h : chkStruct6 k true 4 = true) : Std 6 true :=
  std6 (structOK_of_chk h) (m := 45) (by rw [card_Hg6]; norm_num) (by norm_num)

theorem std6_L (h : chkStruct6 k false 3 = true) : Std 6 false :=
  std6 (structOK_of_chk h) (m := 45) (by rw [card_Hg6]; norm_num) (by norm_num)

theorem subOf_le_Tgrp {n : ℕ} {b : Bool} {B : List Tab} (hT0 : subOK n (Tgl n b) = true)
    (hB : subOK n B = true) (hBT : subsetT B (Tgl n b) = true) : subOf n B ≤ Tgrp n b := by
  intro x hx
  rw [mem_subOf hB] at hx
  rw [mem_Tgrp b hT0]
  exact subsetT_iff.1 hBT _ hx

theorem subsetT_of_le {n : ℕ} {K B : List Tab} (hK : subOK n K = true) (hB : subOK n B = true)
    (h : subOf n K ≤ subOf n B) : subsetT K B = true := by
  refine subsetT_iff.2 fun t ht => ?_
  obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hK).1 t ht)
  exact (mem_subOf hB).1 (h ((mem_subOf hK).2 ht))

theorem subsetT_rTab (X T : List Tab) : subsetT (rTab X T) T = true := by
  refine subsetT_iff.2 fun t ht => ?_
  simp only [rTab, List.mem_filter] at ht
  exact ht.1

theorem subsetT_refl (T : List Tab) : subsetT T T = true := subsetT_iff.2 fun _ ht => ht

theorem stab1_eq {b : Bool} {e : ℕ} (hs : StructOK k b e) :
    stabW (Hg 6 b) (flagF1V 6 k b) = subOf 6 (H1tab 6 k b) := by
  rw [H1tab_eq]
  exact stabW_eq_subOf b (fun m hm => mask_F1 b hs.hT0 hm) (by rw [← H1tab_eq]; exact hs.hH1)

theorem stab2_eq {b : Bool} {e : ℕ} (hs : StructOK k b e) :
    stabW (Hg 6 b) (flagF2V 6 k b) = subOf 6 (H2tab 6 k b) := by
  rw [H2tab_eq]
  exact stabW_eq_subOf b (fun m hm => mask_F2 b hs.hT0 hm) (by rw [← H2tab_eq]; exact hs.hH2)

theorem O2_stab1_eq {b : Bool} {e : ℕ} (hs : StructOK k b e) :
    O2s (stabW (Hg 6 b) (flagF1V 6 k b)) = subOf 6 (rTab (H1tab 6 k b) (Tgl 6 b)) := by
  rw [stab1_eq hs]
  exact O2s_subOf hs.hH1 hs.hT0 hs.hTH1 (e := e) (m := 3) hs.hTlen
    (by rw [hs.hH1len]; ring) (by norm_num) hs.hR1

theorem O2_stab2_eq {b : Bool} {e : ℕ} (hs : StructOK k b e) :
    O2s (stabW (Hg 6 b) (flagF2V 6 k b)) = subOf 6 (rTab (H2tab 6 k b) (Tgl 6 b)) := by
  rw [stab2_eq hs]
  exact O2s_subOf hs.hH2 hs.hT0 hs.hTH2 (e := e) (m := 3) hs.hTlen
    (by rw [hs.hH2len]; ring) (by norm_num) hs.hR2

theorem rAV_lt_iff {n : ℕ} (hn : 5 ≤ n) (k : Mod) {K : List Tab} (hK : subOK n K = true)
    (hoff : IsOffG n k (subOf n K)) :
    rAV ((subOf n K).map (Mod.act n k)) < 1 ↔ cntF n k [idT n] < Fval n k K := by
  rw [rAV_lt_one_iff (V_sq' k) (IsFFStarOffender.isA2 hoff), ← cntF_id (n := n) k,
    ← fval_eq hn k hK (K := subOf n K) (fun x => mem_subOf hK)]
  exact (Nat.mul_lt_mul_right (cN_pos k)).symm

theorem strong_coded {n : ℕ} {b : Bool} (hS : Std n b) {B : List Tab} (hB : subOK n B = true)
    (hBT : subsetT B (Tgl n b) = true) {A : Subgroup (MulAut (Mod.V n k))}
    (hA : A ≤ (subOf n B).map (Mod.act n k))
    (hstr : IsStrongFFStarOffender ((Hg n b).map (Mod.act n k)) A) :
    ∃ K ∈ offsH n k b, subsetT K B = true ∧ cntF n k [idT n] < Fval n k K ∧
      A = (subOf n K).map (Mod.act n k) := by
  obtain ⟨A', hA'B, hmap⟩ := exists_pullback_le hS.five k hA
  have hBle : subOf n B ≤ Tgrp n b := subOf_le_Tgrp hS.hT0 hB hBT
  have hAH : A' ≤ Hg n b := hA'B.trans (hBle.trans hS.hTH)
  have hoff : IsOffG n k A' := (isFFStar_iff_offG hAH).1 (by rw [hmap]; exact hstr.1)
  obtain ⟨K, hKo, hK⟩ := exists_offsH hS hoff (hA'B.trans hBle)
  obtain ⟨-, hKok, -, -⟩ := offsH_spec hS hKo
  have hoffK : IsOffG n k (subOf n K) := by rw [hK]; exact hoff
  refine ⟨K, hKo, subsetT_of_le hKok hB (by rw [hK]; exact hA'B), ?_, by rw [hK, hmap]⟩
  rw [← rAV_lt_iff hS.five k hKok hoffK, hK, hmap]
  exact hstr.2

theorem four_L_std (hchk : chkL6 k = true)
    {P : Set (Subgroup (MulAut (Mod.V 6 k)))} (hP : IsStableFF ((Hg 6 false).map (Mod.act 6 k)) P) :
    ffJP P ((Tgrp 6 false).map (Mod.act 6 k)) =
        (O2s (stabW (Hg 6 false) (flagF2V 6 k false))).map (Mod.act 6 k) ∧
      rk (O2s (stabW (Hg 6 false) (flagF2V 6 k false))) = 2 ∧
      (∀ A : Subgroup (MulAut (Mod.V 6 k)),
        A ≤ (O2s (stabW (Hg 6 false) (flagF2V 6 k false))).map (Mod.act 6 k) →
          ¬ IsStrongFFStarOffender ((Hg 6 false).map (Mod.act 6 k)) A) ∧
      ffJP P ((O2s (stabW (Hg 6 false) (flagF1V 6 k false))).map (Mod.act 6 k)) = ⊥ := by
  simp only [chkL6, Bool.and_eq_true] at hchk
  obtain ⟨⟨hstruct, hsubL⟩, hRL⟩ := hchk
  have hs := structOK_of_chk hstruct
  have hS : Std 6 false := std6_L hstruct
  have hne := SP_ne_nil hS hP
  have hstab := stableB_SP hS hP
  have hclaims : claimsL (fourD k false) (SP 6 k false P) = true := by
    simp only [chkSubL6, List.all_eq_true, List.mem_filter] at hsubL
    have h := hsubL (SP 6 k false P) ⟨List.mem_sublists.2 (SP_sublist false P), hstab⟩
    rwa [List.isEmpty_eq_false_iff.2 hne, Bool.false_or] at h
  simp only [claimsL, Bool.and_eq_true] at hclaims
  obtain ⟨⟨⟨hJT, hJR1⟩, hJe⟩, hJ1⟩ := hclaims
  have hJTok := (chkGenTabs_spec hJT).1
  have hJR1ok := (chkGenTabs_spec hJR1).1
  have hR2 : O2s (stabW (Hg 6 false) (flagF2V 6 k false)) = subOf 6 (fourD k false).R2 :=
    O2_stab2_eq hs
  have hR1 : O2s (stabW (Hg 6 false) (flagF1V 6 k false)) = subOf 6 (fourD k false).R1 :=
    O2_stab1_eq hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ffJP_SP hS hP (B := Tgl 6 false) hs.hT0 (subsetT_refl _) hJT
    rw [hR2]
    exact this.trans (congrArg (Subgroup.map (Mod.act 6 k)) (subOf_congr hJTok hs.hR2 hJe))
  · rw [hR2]
    simp only [chkRL6, Bool.and_eq_true, beq_iff_eq] at hRL
    have h4 : (fourD k false).R2.length = 4 := hRL.1
    rw [rk_subOf (n := 6) (K := (fourD k false).R2) hs.hR2, h4, show (4 : ℕ) = 2 ^ 2 by norm_num,
      padicValNat.prime_pow]
  · intro A hA hstr
    rw [hR2] at hA
    obtain ⟨K, hKo, hKR, hKw, -⟩ := strong_coded hS (B := (fourD k false).R2) hs.hR2
      (subsetT_rTab _ _) hA hstr
    simp only [chkRL6, Bool.and_eq_true, List.all_eq_true] at hRL
    have h := hRL.2 K hKo
    rw [hKR] at h
    simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true', decide_eq_false_iff_not,
      not_lt] at h
    exact absurd hKw (not_lt.2 h)
  · have := ffJP_SP hS hP (B := (fourD k false).R1) hs.hR1 (subsetT_rTab _ _) hJR1
    rw [hR1, this]
    rw [show subOf 6 (jOf 6 (fourD k false).R1 (SP 6 k false P)) = ⊥ from
      subOf_eq_bot_of_seteq hJR1ok hJ1, Subgroup.map_bot]

theorem tab_commutator {n : ℕ} (a b : Gp n) : tab ⁅a, b⁆ = commT (tab a) (tab b) := by
  have h : ⁅a, b⁆ = (a * b) * (a⁻¹ * b⁻¹) := by
    simp [commutatorElement_def, mul_assoc]
  rw [h, tab_mul, tab_mul, tab_mul, tab_inv, tab_inv]
  rfl

theorem commutator_subOf {n : ℕ} {A B : List Tab} (hA : subOK n A = true) (hB : subOK n B = true)
    (h : chkGenTabs n (commGens A B) = true) :
    ⁅subOf n A, subOf n B⁆ = subOf n (commSub n A B) := by
  obtain ⟨-, -, hcl⟩ := chkGenTabs_spec h
  rw [Subgroup.commutator_def]
  have hset : {g : Gp n | ∃ g₁ ∈ subOf n A, ∃ g₂ ∈ subOf n B, ⁅g₁, g₂⁆ = g} =
      {x : Gp n | tab x ∈ commGens A B} := by
    ext x
    constructor
    · rintro ⟨g₁, h₁, g₂, h₂, rfl⟩
      show tab ⁅g₁, g₂⁆ ∈ commGens A B
      rw [tab_commutator]
      simp only [commGens, List.mem_flatMap, List.mem_map]
      exact ⟨tab g₁, (mem_subOf hA).1 h₁, tab g₂, (mem_subOf hB).1 h₂, rfl⟩
    · intro hx
      have hx' : tab x ∈ commGens A B := hx
      simp only [commGens, List.mem_flatMap, List.mem_map] at hx'
      obtain ⟨a, ha, b, hb, hab⟩ := hx'
      obtain ⟨a', rfl⟩ := exists_tab_eq ((subOK_spec hA).1 a ha)
      obtain ⟨b', rfl⟩ := exists_tab_eq ((subOK_spec hB).1 b hb)
      refine ⟨a', (mem_subOf hA).2 ha, b', (mem_subOf hB).2 hb, ?_⟩
      apply tab_injective
      rw [tab_commutator]
      exact hab
  rw [hset]
  exact hcl

theorem normalizes_spec {n : ℕ} {X J : List Tab} (hX : subOK n X = true) (hJ : subOK n J = true)
    (h : normalizesT X J = true) :
    ∀ x ∈ subOf n X, ∀ j ∈ subOf n J, x * j * x⁻¹ ∈ subOf n J := by
  intro x hx j hj
  rw [mem_subOf hX] at hx
  rw [mem_subOf hJ] at hj
  rw [mem_subOf hJ]
  have h1 : cjT (tab x) (tab j) ∈ J := by
    simp only [normalizesT, List.all_eq_true, List.contains_iff_mem] at h
    exact h _ hx _ hj
  rwa [cjT_tab] at h1

theorem normal_subgroupOf_of_conj {G : Type*} [Group G] {J Y : Subgroup G}
    (h : ∀ x ∈ Y, ∀ j ∈ J, x * j * x⁻¹ ∈ J) : (J.subgroupOf Y).Normal := by
  refine ⟨fun j hj x => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hj ⊢
  simpa using h x x.2 j hj

theorem seteq_id_of_bot {n : ℕ} {J : List Tab} (hJ : subOK n J = true) (h : subOf n J = ⊥) :
    seteqT J [idT n] = true := by
  rw [seteqT_iff]
  intro t
  constructor
  · intro ht
    obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hJ).1 t ht)
    have hx : x ∈ subOf n J := (mem_subOf hJ).2 ht
    rw [h, Subgroup.mem_bot] at hx
    rw [hx, tab_one]
    simp
  · intro ht
    rw [List.mem_singleton] at ht
    rw [ht]
    exact (subOK_spec hJ).2.1

theorem subOf_le_cj {n : ℕ} {B K : List Tab} (hB : subOK n B = true) (hK : subOK n K = true)
    {γ : Gp n} (h : subsetT B (conjT (tab γ) K) = true) : subOf n B ≤ cj γ (subOf n K) := by
  intro x hx
  rw [mem_subOf hB] at hx
  have hx' := subsetT_iff.1 h _ hx
  simp only [conjT, List.mem_map] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  obtain ⟨y', rfl⟩ := exists_tab_eq ((subOK_spec hK).1 y hy)
  rw [cjT_tab] at hyx
  have hxe : x = γ * y' * γ⁻¹ := tab_injective hyx.symm
  rw [mem_cj, hxe]
  have h2 : γ⁻¹ * (γ * y' * γ⁻¹) * γ = y' := by group
  rw [h2]
  exact (mem_subOf hK).2 hy

theorem L1_eq {b : Bool} {e : ℕ} (hs : StructOK k b e) (hL1 : subOK 6 (fourD k b).L1 = true) :
    stabW (Hg 6 b) (flagF1V 6 k b) ⊓ alternatingGroup (Fin 6) = subOf 6 (fourD k b).L1 := by
  apply subOf_eq hL1
  intro x
  rw [Subgroup.mem_inf, stab1_eq hs, mem_subOf hs.hH1, mem_alternatingGroup_iff]
  show _ ↔ tab x ∈ (H1tab 6 k b).filter isEvenT
  rw [List.mem_filter]

theorem L2_eq {b : Bool} {e : ℕ} (hs : StructOK k b e)
    (hL2 : subOK 6 ((fourD k b).H2.filter isEvenT) = true) :
    stabW (Hg 6 b) (flagF2V 6 k b) ⊓ alternatingGroup (Fin 6) =
      subOf 6 ((fourD k b).H2.filter isEvenT) := by
  apply subOf_eq hL2
  intro x
  rw [Subgroup.mem_inf, stab2_eq hs, mem_subOf hs.hH2, mem_alternatingGroup_iff]
  show _ ↔ tab x ∈ (H2tab 6 k b).filter isEvenT
  rw [List.mem_filter]

theorem L2T_eq {b : Bool} {e : ℕ} (hs : StructOK k b e)
    (hL2 : subOK 6 ((fourD k b).H2.filter isEvenT) = true)
    (h : chkGenTabs 6 ((fourD k b).H2.filter isEvenT ++ (fourD k b).T) = true) :
    (stabW (Hg 6 b) (flagF2V 6 k b) ⊓ alternatingGroup (Fin 6)) ⊔ Tgrp 6 b =
      subOf 6 (fourD k b).L2T := by
  obtain ⟨-, -, hcl⟩ := chkGenTabs_spec h
  rw [L2_eq hs hL2]
  have hset : {x : Gp 6 | tab x ∈ (fourD k b).H2.filter isEvenT ++ (fourD k b).T} =
      (subOf 6 ((fourD k b).H2.filter isEvenT) : Set (Gp 6)) ∪ (Tgrp 6 b : Set (Gp 6)) := by
    ext x
    rw [Set.mem_union, SetLike.mem_coe, SetLike.mem_coe, mem_subOf hL2, mem_Tgrp b hs.hT0]
    exact List.mem_append
  have hcl' : (subOf 6 ((fourD k b).H2.filter isEvenT)) ⊔ Tgrp 6 b =
      Subgroup.closure {x : Gp 6 | tab x ∈ (fourD k b).H2.filter isEvenT ++ (fourD k b).T} := by
    rw [hset, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hcl', hcl]
  rfl

theorem zpowers_ti_eq (h : chkGenTabs 6 [tab (ti 6 2)] = true) :
    Subgroup.zpowers (ti 6 2) = subOf 6 (closeT 6 [tab (ti 6 2)]) := by
  obtain ⟨-, -, hcl⟩ := chkGenTabs_spec h
  rw [← hcl, Subgroup.zpowers_eq_closure]
  congr 1
  ext x
  constructor
  · intro hx
    have hx' : x = ti 6 2 := hx
    rw [hx']
    exact List.mem_singleton_self _
  · intro hx
    have hx' : tab x ∈ [tab (ti 6 2)] := hx
    exact tab_injective (List.mem_singleton.1 hx')

theorem isStrong_mono {V : Type*} [CommGroup V] {X Y A : Subgroup (MulAut V)} (hXY : X ≤ Y)
    (hAX : A ≤ X) : IsStrongFFStarOffender Y A ↔ IsStrongFFStarOffender X A :=
  ⟨fun h => ⟨⟨hAX, h.1.2⟩, h.2⟩, fun h => ⟨⟨h.1.1.trans hXY, h.1.2⟩, h.2⟩⟩

theorem strong_Tl6 (hk : k = Mod.u0 ∨ k = Mod.ut0) :
    ∀ A : Subgroup (Gp 6), A ≤ subOf 6 (Tl 6) →
      (IsStrongFFStarOffender ((subOf 6 (Tl 6)).map (Mod.act 6 k)) (A.map (Mod.act 6 k)) ↔
        A = Dsub 6) :=
  strongTl6_of hk

theorem G_parts (hchk : chkG6 k = true) :
    chkStruct6 k true 4 = true ∧ chkGenG6 k = true ∧ chkSubG6 k = true ∧ chkWitG6 k = true ∧
      chkRG6 k = true := by
  simp only [chkG6, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hchk
  exact ⟨h1, h2, h3, h4, h5⟩

theorem G_claims (hchk : chkG6 k = true) {P : Set (Subgroup (MulAut (Mod.V 6 k)))}
    (hP : IsStableFF ((Hg 6 true).map (Mod.act 6 k)) P) :
    claimsG k (fourD k true) (SP 6 k true P) = true := by
  obtain ⟨hst, -, hsub, -, -⟩ := G_parts hchk
  have hS : Std 6 true := std6_G hst
  have hne := SP_ne_nil hS hP
  have hstab := stableB_SP hS hP
  simp only [chkSubG6, List.all_eq_true, List.mem_filter] at hsub
  have h := hsub (SP 6 k true P) ⟨List.mem_sublists.2 (SP_sublist true P), hstab⟩
  rwa [List.isEmpty_eq_false_iff.2 hne, Bool.false_or] at h

theorem G_gen_spec (h : chkGenG6 k = true) :
    subOK 6 (fourD k true).L1 = true ∧ subOK 6 ((fourD k true).H2.filter isEvenT) = true ∧
      chkGenTabs 6 ((fourD k true).H2.filter isEvenT ++ (fourD k true).T) = true ∧
      chkGenTabs 6 (commGens (fourD k true).L1 (fourD k true).L1) = true ∧
      chkGenTabs 6 [tab (ti 6 2)] = true := by
  simp only [chkGenG6, Bool.and_eq_true, and_assoc] at h
  exact h

theorem G_R2_eq_D (hchk : chkG6 k = true) :
    O2s (stabW (Hg 6 true) (flagF2V 6 k true)) = Dsub 6 := by
  obtain ⟨hst, -, -, -, hRG⟩ := G_parts hchk
  have hs := structOK_of_chk hst
  obtain ⟨-, hg, -⟩ := chkNamed_spec chkNamed_six
  simp only [chkRG6, Bool.and_eq_true] at hRG
  rw [O2_stab2_eq hs, Dsub_eq hg]
  exact subOf_congr hs.hR2 (subOK_Dc hg) hRG.1

theorem G_i (hk : k = Mod.u0 ∨ k = Mod.ut0) (hchk : chkG6 k = true) :
    rk (O2s (stabW (Hg 6 true) (flagF2V 6 k true))) = 3 ∧
      ∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ (Tgrp 6 true).map (Mod.act 6 k) →
        (IsStrongFFStarOffender ((Hg 6 true).map (Mod.act 6 k)) A ↔
          A = (O2s (stabW (Hg 6 true) (flagF2V 6 k true))).map (Mod.act 6 k)) := by
  have hR2 := G_R2_eq_D hchk
  have hn : 5 ≤ 6 := by norm_num
  refine ⟨?_, fun A hA => ?_⟩
  · rw [hR2]
    exact (B3_2_1 (n := 6) (Or.inr (Or.inl rfl)) k (m := 3) (by norm_num) (by norm_num)).1
  · rw [hR2]
    obtain ⟨A', hA'T, hmap⟩ := exists_pullback_le hn k hA
    subst hmap
    have hmono : (Tgrp 6 true).map (Mod.act 6 k) ≤ (Hg 6 true).map (Mod.act 6 k) :=
      Subgroup.map_mono le_top
    rw [isStrong_mono hmono hA]
    exact (strong_Tl6 hk A' hA'T).trans (Subgroup.map_injective (act_injective hn k)).eq_iff.symm

theorem G_ii
    (hk : k = Mod.u0 ∨ k = Mod.ut0) (hchk : chkG6 k = true) :
    ∀ A : Subgroup (MulAut (Mod.V 6 k)),
      A ≤ (O2s (stabW (Hg 6 true) (flagF1V 6 k true))).map (Mod.act 6 k) →
        ¬ IsStrongFFStarOffender ((Hg 6 true).map (Mod.act 6 k)) A := by
  obtain ⟨hst, -, -, -, hRG⟩ := G_parts hchk
  have hs := structOK_of_chk hst
  have hn : 5 ≤ 6 := by norm_num
  intro A hA hstr
  have hR1 := O2_stab1_eq hs
  have hR1T : O2s (stabW (Hg 6 true) (flagF1V 6 k true)) ≤ Tgrp 6 true := by
    rw [hR1]
    exact subOf_le_Tgrp hs.hT0 hs.hR1 (subsetT_rTab _ _)
  have hAT : A ≤ (Tgrp 6 true).map (Mod.act 6 k) := hA.trans (Subgroup.map_mono hR1T)
  have hA2 := ((G_i hk hchk).2 A hAT).1 hstr
  rw [hA2] at hA
  have hle := (Subgroup.map_le_map_iff_of_injective (act_injective hn k)).1 hA
  rw [G_R2_eq_D hchk] at hle
  obtain ⟨-, hg, -⟩ := chkNamed_spec chkNamed_six
  simp only [chkRG6, Bool.and_eq_true, Bool.not_eq_true'] at hRG
  obtain ⟨hDR2, hDR1⟩ := hRG
  rw [hR1, Dsub_eq hg] at hle
  have h1 : subsetT (Dc 6) (fourD k true).R1 = true := subsetT_of_le (subOK_Dc hg) hs.hR1 hle
  rw [h1] at hDR1
  exact Bool.noConfusion hDR1

theorem G_core (hchk : chkG6 k = true) {P : Set (Subgroup (MulAut (Mod.V 6 k)))}
    (hP : IsStableFF ((Hg 6 true).map (Mod.act 6 k)) P)
    {T H₁ H₂ R₁ R₂ L₁ L₂ : Subgroup (Gp 6)} {J J₁ : Subgroup (MulAut (Mod.V 6 k))}
    (hT : T = Tgrp 6 true) (hH₁ : H₁ = stabW (Hg 6 true) (flagF1V 6 k true))
    (hH₂ : H₂ = stabW (Hg 6 true) (flagF2V 6 k true)) (hR₁ : R₁ = O2s H₁) (hR₂ : R₂ = O2s H₂)
    (hL₁ : L₁ = H₁ ⊓ alternatingGroup (Fin 6)) (hL₂ : L₂ = H₂ ⊓ alternatingGroup (Fin 6))
    (hJ : J = ffJP P (T.map (Mod.act 6 k))) (hJ₁ : J₁ = ffJP P (R₁.map (Mod.act 6 k))) :
    ((∀ A ∈ P, IsStrongFFStarOffender ((Hg 6 true).map (Mod.act 6 k)) A) →
        J₁ = ⊥ ∧ J = R₂.map (Mod.act 6 k)) ∧
      (J₁ = ⊥ →
        (J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧
          (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal) ∧
        ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆) ∧
      (J₁ ≠ ⊥ →
        ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆ ∧
        ((J₁ = (Subgroup.zpowers (ti 6 2)).map (Mod.act 6 k) ∧
            (J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧
              (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal)) ∨
          (J₁ = R₁.map (Mod.act 6 k) ∧ J = T.map (Mod.act 6 k)))) := by
  obtain ⟨hst, hgen, -, -, -⟩ := G_parts hchk
  have hs := structOK_of_chk hst
  have hS : Std 6 true := std6_G hst
  have hinj := act_injective (n := 6) (by norm_num) k
  obtain ⟨hL1ok, hL2ok, hL2Tgen, hL1dgen, hA1gen⟩ := G_gen_spec hgen
  have hclaims := G_claims hchk hP
  have eT : T = subOf 6 (fourD k true).T := by rw [hT]; rfl
  have eR₁ : R₁ = subOf 6 (fourD k true).R1 := by rw [hR₁, hH₁]; exact O2_stab1_eq hs
  have eR₂ : R₂ = subOf 6 (fourD k true).R2 := by rw [hR₂, hH₂]; exact O2_stab2_eq hs
  have eL₁ : L₁ = subOf 6 (fourD k true).L1 := by rw [hL₁, hH₁]; exact L1_eq hs hL1ok
  have eL₂T : L₂ ⊔ T = subOf 6 (fourD k true).L2T := by
    rw [hL₂, hH₂, hT]; exact L2T_eq hs hL2ok hL2Tgen
  simp only [claimsG, Bool.and_eq_true] at hclaims
  obtain ⟨⟨⟨⟨⟨⟨hjT, hjR⟩, hgenLJ⟩, hsubJ⟩, h3⟩, h4⟩, h5⟩ := hclaims
  have hJTok := (chkGenTabs_spec hjT).1
  have hJRok := (chkGenTabs_spec hjR).1
  have hL2Tok := (chkGenTabs_spec hL2Tgen).1
  have eJ : J = (subOf 6 (jOf 6 (fourD k true).T (SP 6 k true P))).map (Mod.act 6 k) := by
    rw [hJ, eT]
    exact ffJP_SP hS hP hs.hT0 (subsetT_refl _) hjT
  have eJ₁ : J₁ = (subOf 6 (jOf 6 (fourD k true).R1 (SP 6 k true P))).map (Mod.act 6 k) := by
    rw [hJ₁, eR₁]
    exact ffJP_SP hS hP hs.hR1 (subsetT_rTab _ _) hjR
  have hnorm : normalizesT (fourD k true).L2T (jOf 6 (fourD k true).T (SP 6 k true P)) = true →
      J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧ (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal := by
    intro hn
    rw [eL₂T, eJ]
    refine ⟨Subgroup.map_mono (subOf_le_of_subsetT hJTok hL2Tok hsubJ), ?_⟩
    apply normal_subgroupOf_of_conj
    rintro _ ⟨x, hx, rfl⟩ _ ⟨j, hj, rfl⟩
    refine ⟨x * j * x⁻¹, normalizes_spec hL2Tok hJTok hn x hx j hj, ?_⟩
    simp [map_mul, map_inv]
  have hcomm : seteqT (commSub 6 (fourD k true).L1 (jOf 6 (fourD k true).T (SP 6 k true P)))
      (fourD k true).L1d = true →
      ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆ := by
    intro hse
    have h1 : ⁅subOf 6 (fourD k true).L1, subOf 6 (jOf 6 (fourD k true).T (SP 6 k true P))⁆ =
        ⁅subOf 6 (fourD k true).L1, subOf 6 (fourD k true).L1⁆ := by
      refine (commutator_subOf hL1ok hJTok hgenLJ).trans ?_
      refine Eq.trans ?_ (commutator_subOf hL1ok hL1ok hL1dgen).symm
      exact subOf_congr (chkGenTabs_spec hgenLJ).1 (chkGenTabs_spec hL1dgen).1 hse
    rw [eJ, eL₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, h1]
  have hbot : J₁ = ⊥ ↔ seteqT (jOf 6 (fourD k true).R1 (SP 6 k true P)) [idT 6] = true := by
    rw [eJ₁]
    constructor
    · intro h
      exact seteq_id_of_bot hJRok ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h)
    · intro h
      have hb : subOf 6 (jOf 6 (fourD k true).R1 (SP 6 k true P)) = ⊥ :=
        subOf_eq_bot_of_seteq hJRok h
      rw [hb, Subgroup.map_bot]
  refine ⟨fun hall => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have hSall : (SP 6 k true P).all
        (fun K => decide ((fourD k true).w < Fval 6 k K)) = true := by
      simp only [List.all_eq_true, decide_eq_true_eq]
      intro K hK
      obtain ⟨hKo, hKP⟩ := mem_SP.1 hK
      obtain ⟨-, hKok, hKoff, -⟩ := offsH_spec hS hKo
      exact (rAV_lt_iff hS.five k hKok hKoff).1 (hall _ hKP).2
    rw [hSall] at h3
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h3
    refine ⟨hbot.2 h3.1, ?_⟩
    rw [eJ, eR₂]
    exact congrArg (Subgroup.map (Mod.act 6 k)) (subOf_congr hJTok hs.hR2 h3.2)
  · have hb := hbot.1 h1
    rw [hb] at h4
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h4
    exact ⟨hnorm h4.1, hcomm h4.2⟩
  · have hb : ¬ seteqT (jOf 6 (fourD k true).R1 (SP 6 k true P)) [idT 6] = true :=
      fun h => h1 (hbot.2 h)
    rw [Bool.not_eq_true] at hb
    rw [hb, Bool.false_or] at h5
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h5
    refine ⟨hcomm h5.1, ?_⟩
    rcases h5.2 with ⟨hA, hN⟩ | ⟨hR, hT'⟩
    · refine Or.inl ⟨?_, hnorm hN⟩
      rw [eJ₁, zpowers_ti_eq hA1gen]
      exact congrArg (Subgroup.map (Mod.act 6 k)) (subOf_congr hJRok (chkGenTabs_spec hA1gen).1 hA)
    · refine Or.inr ⟨?_, ?_⟩
      · rw [eJ₁, eR₁]
        exact congrArg (Subgroup.map (Mod.act 6 k)) (subOf_congr hJRok hs.hR1 hR)
      · rw [eJ, eT]
        exact congrArg (Subgroup.map (Mod.act 6 k)) (subOf_congr hJTok hs.hT0 hT')

theorem G_vi (hchk : chkG6 k = true) {P : Set (Subgroup (MulAut (Mod.V 6 k)))}
    (hP : IsStableFF ((Hg 6 true).map (Mod.act 6 k)) P)
    {T H₂ R₂ : Subgroup (Gp 6)} (hT : T = Tgrp 6 true)
    (hH₂ : H₂ = stabW (Hg 6 true) (flagF2V 6 k true)) (hR₂ : R₂ = O2s H₂) :
    (∀ A ∈ P, Nat.card A = 2) ∨
      ∃ A ∈ P, ∃ B : Subgroup (MulAut (Mod.V 6 k)), B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧
        B ≤ T.map (Mod.act 6 k) ∧ ¬ B ≤ R₂.map (Mod.act 6 k) := by
  obtain ⟨hst, -, -, hwit, -⟩ := G_parts hchk
  have hs := structOK_of_chk hst
  have hS : Std 6 true := std6_G hst
  have hinj := act_injective (n := 6) (by norm_num) k
  by_cases hall : ∀ A ∈ P, Nat.card A = 2
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨A, hAP, hAne⟩ := hall
    obtain ⟨A', hA'H, hmap⟩ := exists_pullback_le hS.five k (hP.2.1 A hAP).1
    rw [← hmap] at hAP hAne
    have hoff : IsOffG 6 k A' := isOffG_of_stable hP hAP
    have hA'p : IsPGroup 2 A' := isPGroup_of_sq (hoff.comm_sq hS.five).2
    obtain ⟨g, hgH, hg⟩ := exists_conj_le_sylow_sub hS.hTH hS.hp hS.hidx hA'H hA'p
    obtain ⟨K, hKo, hK⟩ := exists_offsH hS (hoff.cj g) hg
    obtain ⟨hKD, hKok, -, -⟩ := offsH_spec hS hKo
    have hKP : (subOf 6 K).map (Mod.act 6 k) ∈ P := by
      rw [hK, map_cj, conjAut_eq_map_conj]
      exact hP.2.2.1 _ hAP _ (Subgroup.mem_map_of_mem _ hgH)
    have hKlen : K.length ≠ 2 := by
      rw [← card_subOf hKok, hK]
      have h1 : Nat.card (cj g A') = Nat.card A' :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      have h2 : Nat.card (A'.map (Mod.act 6 k)) = Nat.card A' :=
        Subgroup.card_map_of_injective hinj
      rw [h1, ← h2]
      exact hAne
    simp only [chkWitG6, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hwit
    rcases hwit K hKo with hlen | hw
    · exact absurd hlen hKlen
    simp only [witB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw
    obtain ⟨g', hg', B, hB, ⟨⟨hBT, hBlen⟩, hBR⟩, hBc⟩ := hw
    obtain ⟨σ, hσ, rfl⟩ := (Hl_spec true).2 g' hg'
    obtain ⟨-, hmem, -⟩ := chkEA_spec hs.hEA
    have hBok : subOK 6 B = true := (hmem B hB).1
    have hBle : subOf 6 B ≤ cj σ (subOf 6 K) := subOf_le_cj hBok hKok hBc
    have hAw : (cj σ (subOf 6 K)).map (Mod.act 6 k) ∈ P := by
      rw [map_cj, conjAut_eq_map_conj]
      exact hP.2.2.1 _ hKP _ (Subgroup.mem_map_of_mem _ hσ)
    refine ⟨_, hAw, (subOf 6 B).map (Mod.act 6 k), Subgroup.map_mono hBle, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj,
        show Nat.card (cj σ (subOf 6 K)) = Nat.card (subOf 6 K) from
          Subgroup.card_map_of_injective (MulAut.conj σ).injective,
        card_subOf hKok, card_subOf hBok]
      omega
    · rw [hT]
      exact Subgroup.map_mono (subOf_le_Tgrp hs.hT0 hBok hBT)
    · intro hle
      have hR : R₂ = subOf 6 (fourD k true).R2 := by rw [hR₂, hH₂]; exact O2_stab2_eq hs
      rw [hR] at hle
      have h1 : subsetT B (fourD k true).R2 = true := subsetT_of_le hBok hs.hR2
        ((Subgroup.map_le_map_iff_of_injective hinj).1 hle)
      rw [hBR] at h1
      exact Bool.noConfusion h1

end CFSG.Quasithin.B3
