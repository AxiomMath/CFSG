module

public import CFSG.Quasithin.Background.RonanH155Chain
public import CFSG.Quasithin.Background.RonanH154Hyp
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.RonanH143ConjA
public import CFSG.Quasithin.Background.RonanH155Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.QuasithinUnique.Setup.X1
  CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH154

theorem toPerm_ko (t : Fin 16) : PG2.toPerm ⟨t, 0, 0⟩ = koPerm t := by
  show koPerm t * dPerm 0 * (if (0 : Fin 2) = 1 then ePerm else 1) = koPerm t
  rw [dPerm_zero]
  simp

theorem mem_koL155_of_toPerm_mem {s : PG2} (hs : PG2.toPerm s ∈ fixO) : s ∈ koL155 := by
  obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 hs
  have h2 : s = ⟨t, 0, 0⟩ := PG2.toPerm_injective (ht.trans (toPerm_ko t).symm)
  rw [h2]
  exact List.mem_map.2 ⟨t, List.mem_finRange t, rfl⟩

theorem mem_inf_fixO_chain {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) (x : P24) :
    x ∈ A ⊓ fixO ↔
      ∃ s ∈ (subprods l).filter (fun s => koL155.contains s), x = PG2.toPerm s := by
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxA, hxO⟩
    obtain ⟨s, hs, rfl⟩ := (hAeq x).1 hxA
    exact ⟨s, List.mem_filter.2 ⟨hs, List.contains_iff_mem.2 (mem_koL155_of_toPerm_mem hxO)⟩,
      rfl⟩
  · rintro ⟨s, hs, rfl⟩
    rcases List.mem_filter.1 hs with ⟨hs1, hs2⟩
    exact ⟨(hAeq _).2 ⟨s, hs1, rfl⟩, toPerm_koL155 (List.contains_iff_mem.1 hs2)⟩

@[expose] def WitOK (l : List PG2) (w : List (PG2 × ℕ)) : Prop :=
  (∀ p ∈ w, p.1 ∈ subprods l ∧ p.1 ≠ 1 ∧ p.2 < 2 ^ 10 ∧ actP2 p.1 p.2 = p.2) ∧
    nodupB (combos (w.map Prod.snd)) 0 = true

instance (l : List PG2) (w : List (PG2 × ℕ)) : Decidable (WitOK l w) := by
  unfold WitOK
  infer_instance

@[expose] def wit155 : List (List (PG2 × ℕ)) :=
  [[(⟨0, 0, 1⟩, 3), (⟨0, 0, 1⟩, 13), (⟨0, 0, 1⟩, 16), (⟨0, 0, 1⟩, 32), (⟨0, 0, 1⟩, 128), (⟨0, 0, 1⟩, 325), (⟨0, 0, 1⟩, 512), (⟨1, 2, 0⟩, 47), (⟨1, 2, 0⟩, 78), (⟨1, 2, 1⟩, 39)],
    [(⟨0, 2, 0⟩, 30), (⟨0, 2, 0⟩, 43), (⟨0, 2, 0⟩, 78), (⟨0, 2, 0⟩, 128), (⟨0, 2, 0⟩, 269), (⟨0, 2, 0⟩, 512), (⟨0, 5, 0⟩, 5), (⟨0, 5, 0⟩, 321), (⟨0, 7, 0⟩, 12), (⟨6, 2, 1⟩, 45)],
    [(⟨0, 2, 1⟩, 30), (⟨0, 2, 1⟩, 110), (⟨0, 2, 1⟩, 128), (⟨0, 2, 1⟩, 262), (⟨0, 2, 1⟩, 512), (⟨1, 0, 0⟩, 14), (⟨1, 0, 0⟩, 32), (⟨1, 2, 1⟩, 12), (⟨1, 2, 1⟩, 39), (⟨6, 2, 1⟩, 45)],
    [(⟨0, 4, 1⟩, 32), (⟨0, 4, 1⟩, 80), (⟨0, 4, 1⟩, 128), (⟨0, 4, 1⟩, 262), (⟨0, 4, 1⟩, 542), (⟨1, 0, 0⟩, 14), (⟨1, 0, 0⟩, 16), (⟨2, 0, 0⟩, 256), (⟨6, 4, 1⟩, 11), (⟨7, 4, 1⟩, 7)],
    [(⟨0, 6, 1⟩, 10), (⟨0, 6, 1⟩, 19), (⟨0, 6, 1⟩, 39), (⟨0, 6, 1⟩, 67), (⟨0, 6, 1⟩, 128), (⟨0, 6, 1⟩, 257), (⟨0, 6, 1⟩, 519), (⟨1, 0, 0⟩, 14), (⟨1, 0, 0⟩, 16), (⟨6, 6, 1⟩, 17)],
    [(⟨0, 5, 0⟩, 5), (⟨0, 5, 0⟩, 27), (⟨0, 5, 0⟩, 43), (⟨0, 5, 0⟩, 128), (⟨0, 5, 0⟩, 321), (⟨0, 5, 0⟩, 585), (⟨1, 2, 1⟩, 12), (⟨1, 2, 1⟩, 69), (⟨6, 7, 1⟩, 14), (⟨6, 2, 1⟩, 45)],
    [(⟨0, 7, 0⟩, 2), (⟨0, 7, 0⟩, 12), (⟨0, 7, 0⟩, 16), (⟨0, 7, 0⟩, 37), (⟨0, 7, 0⟩, 128), (⟨0, 7, 0⟩, 769), (⟨1, 2, 1⟩, 69), (⟨1, 2, 1⟩, 257), (⟨6, 5, 1⟩, 5), (⟨6, 2, 1⟩, 45)]]

@[expose] def witKO : List (PG2 × ℕ) :=
  [(⟨1, 0, 0⟩, 14), (⟨1, 0, 0⟩, 16), (⟨1, 0, 0⟩, 32), (⟨1, 0, 0⟩, 64), (⟨1, 0, 0⟩, 128), (⟨1, 0, 0⟩, 512), (⟨2, 0, 0⟩, 256), (⟨4, 0, 0⟩, 6), (⟨8, 0, 0⟩, 4)]

theorem card_xiV_wit {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) {w : List (PG2 × ℕ)}
    (hw : WitOK l w) : 2 ^ w.length ≤ Nat.card (xiV (rImg Rc A)) := by
  obtain ⟨hwa, hnd⟩ := hw
  have hltl : ∀ a ∈ w.map Prod.snd, a < 2 ^ 10 := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact (hwa p hp).2.2.1
  have hle : mS (w.map Prod.snd) ≤ xiV (rImg Rc A) := by
    apply ch_maskSub_le
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hs, hs1, hlt, hfix⟩ := hwa p hp
    have hmem : autP2 p.1 ∈ rImg Rc A := (isChainSub_rImg hAeq _).2 ⟨p.1, hs, rfl⟩
    have hne : autP2 p.1 ≠ 1 := fun h => hs1 (injective_autP2 (h.trans (map_one autP2).symm))
    have hfx : toW 10 p.2 ∈ fixV (Subgroup.zpowers (autP2 p.1)) :=
      (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).2
        ((autP2_toW p.1 p.2).trans (congrArg (toW 10) hfix))
    exact fixV_le_xiV hmem hne hfx
  have hcard := card_mS hltl (nodup_of_nodupB _ 0 hnd).1
  rw [List.length_map] at hcard
  calc 2 ^ w.length = Nat.card ↥(mS (w.map Prod.snd)) := hcard.symm
    _ ≤ Nat.card ↥(xiV (rImg Rc A)) := Subgroup.card_le_of_le hle

theorem xi_top_wit {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) {w : List (PG2 × ℕ)}
    (hw : WitOK l w) (hlen : w.length = 10) : xiV (rImg Rc A) = ⊤ := by
  have h := card_xiV_wit hAeq hw
  rw [hlen] at h
  exact (MaskCoords.std 10).eq_top_of_pow_le h

theorem xi_idx_wit {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) {w : List (PG2 × ℕ)}
    (hw : WitOK l w) (hlen : w.length = 9) : rkIdx (xiV (rImg Rc A)) ≤ 1 := by
  have h := card_xiV_wit hAeq hw
  rw [hlen] at h
  exact (MaskCoords.std 10).rkIdx_le_one_of_pow_le (by norm_num) h

@[expose] def Alt4Prop (l : List PG2) (w : List (PG2 × ℕ)) : Prop :=
  (fixMasks 10 actP2 l).length = 2 ^ 3 ∧ WitOK l w ∧ w.length = 9 ∧
    ((subprods l).filter (fun s => koL155.contains s)).Nodup ∧
    ((subprods l).filter (fun s => koL155.contains s)).length = 2 ^ 3

instance (l : List PG2) (w : List (PG2 × ℕ)) : Decidable (Alt4Prop l w) := by
  unfold Alt4Prop
  infer_instance

theorem alt4_chain {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) {w : List (PG2 × ℕ)}
    (h : Alt4Prop l w) :
    CFSG.Quasithin.rk ↥(A ⊓ fixO) = 3 ∧ CFSG.Quasithin.rk ↥(fixV (rImg Rc A)) = 3 ∧
      rkIdx (xiV (rImg Rc A)) ≤ 1 := by
  obtain ⟨hfix, hw, hwl, hnd, hlen⟩ := h
  refine ⟨rk_eq_of_card ?_, rk_fixV_chain hAeq hfix, xi_idx_wit hAeq hw hwl⟩
  rw [card_of_chain _ hnd _ (mem_inf_fixO_chain hAeq), hlen]

theorem xi_le_chain {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) (H : Subgroup W10)
    (h : ∀ s ∈ subprods l, s ≠ 1 → ∀ m < 2 ^ 10, actP2 s m = m → toW 10 m ∈ H) :
    xiV (rImg Rc A) ≤ H := by
  unfold xiV
  refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
  obtain ⟨s, hs, rfl⟩ := (isChainSub_rImg hAeq a).1 ha
  have hs1 : s ≠ 1 := fun e => ha1 (by subst e; exact map_one autP2)
  intro v hv
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  have hfix : autP2 s (toW 10 m) = toW 10 m := (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).1 hv
  rw [autP2_toW] at hfix
  exact h s hs hs1 m hm (toW_inj (act10_lt _ _) hm hfix)

@[expose] def lKO : List PG2 := [⟨8, 0, 0⟩, ⟨4, 0, 0⟩, ⟨2, 0, 0⟩, ⟨1, 0, 0⟩]

theorem lKO_all : ∀ t : Fin 16, (⟨t, 0, 0⟩ : PG2) ∈ subprods lKO := by decide +kernel

theorem lKO_ko : ∀ s ∈ subprods lKO, s ∈ koL155 := by decide +kernel

theorem lKO_spec : ∀ x : P24, x ∈ fixO ↔ ∃ s ∈ subprods lKO, x = PG2.toPerm s := by
  intro x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := (mem_fixO_iff _).1 hx
    exact ⟨⟨t, 0, 0⟩, lKO_all t, (toPerm_ko t).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact toPerm_koL155 (lKO_ko s hs)

@[expose] def evenBasis : List ℕ := [2, 4, 8, 16, 32, 64, 128, 256, 512]

theorem evenBasis_lt : ∀ a ∈ evenBasis, a < 2 ^ 10 := by decide +kernel

theorem evenBasis_nodup : nodupB (combos evenBasis) 0 = true := by decide +kernel

theorem evenBasis_even : ∀ m < 2 ^ 10, m % 2 = 0 → m ∈ combos evenBasis := by decide +kernel

theorem lKO_fixed_even : ∀ s ∈ subprods lKO, s ≠ 1 → ∀ m < 2 ^ 10, actP2 s m = m → m % 2 = 0 := by
  decide +kernel

theorem lKO_fix : (fixMasks 10 actP2 lKO).length = 2 ^ 5 := by decide +kernel

theorem lKO_wit : WitOK lKO witKO := by decide +kernel

theorem xi_KO_le : xiV (rImg Rc fixO) ≤ mS evenBasis :=
  xi_le_chain lKO_spec _ fun s hs hs1 m hm hfix =>
    toW_mem_mS (evenBasis_even m hm (lKO_fixed_even s hs hs1 m hm hfix))

theorem rk_W10 : CFSG.Quasithin.rk W10 = 10 := by
  unfold CFSG.Quasithin.rk
  rw [chc_card_W10, padicValNat.prime_pow]

theorem witKO_length : witKO.length = 9 := by decide +kernel

theorem alt1_KO : CFSG.Quasithin.rk ↥(fixV (rImg Rc fixO)) = 5 ∧
    rkIdx (xiV (rImg Rc fixO)) = 1 := by
  refine ⟨rk_fixV_chain lKO_spec lKO_fix, ?_⟩
  have hge : 2 ^ 9 ≤ Nat.card (xiV (rImg Rc fixO)) := by
    have h := card_xiV_wit lKO_spec lKO_wit
    rw [witKO_length] at h
    exact h
  have hH : Nat.card ↥(mS evenBasis) = 2 ^ 9 := by
    have := card_mS (l := evenBasis) evenBasis_lt (nodup_of_nodupB _ 0 evenBasis_nodup).1
    exact this
  have hle : Nat.card (xiV (rImg Rc fixO)) ≤ 2 ^ 9 :=
    hH ▸ Subgroup.card_le_of_le xi_KO_le
  have hrk : CFSG.Quasithin.rk ↥(xiV (rImg Rc fixO)) = 9 :=
    rk_eq_of_card (le_antisymm hle hge)
  have h3 : CFSG.Quasithin.rk ↥(xiV (rImg Rc fixO)) + rkIdx (xiV (rImg Rc fixO)) = 10 :=
    (rk_add_rkIdx (xiV (rImg Rc fixO))).trans rk_W10
  omega

@[expose] def Alt2bProp (l : List PG2) (w : List (PG2 × ℕ)) : Prop :=
  (fixMasks 10 actP2 l).length = 2 ^ 2 ∧ WitOK l w ∧ w.length = 10

instance (l : List PG2) (w : List (PG2 × ℕ)) : Decidable (Alt2bProp l w) := by
  unfold Alt2bProp
  infer_instance

theorem permOfArr_mem_mog22plus {a b : Array ℕ} (h : InvPairOK 24 a b = true)
    (hok : autArrOK a b = true) (h0 : a[0]! = 0) (h1 : a[1]! = 1) :
    permOfArr 24 a b h ∈ mog22plus :=
  mog22_le_mog22plus (mem_mog22_of_arr (mem_AutPerm_of_arr h hok) (hasArr_permOfArr h) h0 h1)

theorem alt2b_chain {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) {w : List (PG2 × ℕ)}
    (h : Alt2bProp l w)
    (gA gI : Array ℕ) (hinv : InvPairOK 24 gA gI = true) (hok : autArrOK gA gI = true)
    (h0 : gA[0]! = 0) (h1 : gA[1]! = 1)
    (hconj : ∀ s ∈ subprods l, ∃ u < 32, compA24 (compA24 gA (arrP2 s)) gI = nq2Arr u) :
    (∃ g ∈ mog22plus, conjSubg g A ≤ NQ2) ∧ CFSG.Quasithin.rk ↥(fixV (rImg Rc A)) = 2 ∧
      xiV (rImg Rc A) = ⊤ := by
  obtain ⟨hfix, hw, hwl⟩ := h
  refine ⟨⟨permOfArr 24 gA gI hinv, permOfArr_mem_mog22plus hinv hok h0 h1, ?_⟩,
    rk_fixV_chain hAeq hfix, xi_top_wit hAeq hw hwl⟩
  intro x hx
  rw [mem_conjSubg_iff] at hx
  set g := permOfArr 24 gA gI hinv with hg
  obtain ⟨s, hs, hxs⟩ := (hAeq _).1 hx
  obtain ⟨u, hu, hcu⟩ := hconj s hs
  have hx' : x = g * PG2.toPerm s * g⁻¹ := by
    rw [← hxs]
    group
  have harr : HasArr (g * PG2.toPerm s * g⁻¹) (compA24 (compA24 gA (arrP2 s)) gI) :=
    hasArr_compA24 (hasArr_compA24 (hasArr_permOfArr hinv) (hasArr_toPerm s))
      (hasArr_permOfArr_inv hinv)
  rw [hcu] at harr
  have heq : g * PG2.toPerm s * g⁻¹ = nq2Perm ⟨u, hu⟩ := eq_of_hasArr harr (hasArr_nq2 ⟨u, hu⟩)
  exact ⟨⟨u, hu⟩, hx'.trans heq⟩

theorem alt4_check2 : Alt4Prop (specials155.getD 2 []) ((wit155.getD 2 []).take 9) := by
  decide +kernel

theorem alt4_check3 : Alt4Prop (specials155.getD 3 []) ((wit155.getD 3 []).take 9) := by
  decide +kernel

theorem alt4_check4 : Alt4Prop (specials155.getD 4 []) ((wit155.getD 4 []).take 9) := by
  decide +kernel

theorem alt2b_check5 : Alt2bProp (specials155.getD 5 []) (wit155.getD 5 []) := by
  decide +kernel

theorem alt2b_check6 : Alt2bProp (specials155.getD 6 []) (wit155.getD 6 []) := by
  decide +kernel

end CFSG.Quasithin.RonanH155
