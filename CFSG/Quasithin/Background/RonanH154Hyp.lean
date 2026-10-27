module

public import CFSG.Quasithin.Background.RonanH154Chain
public import CFSG.Quasithin.Background.RonanH154Xor
import CFSG.Quasithin.Background.RonanH154HypK

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def hypFix : List (List ℕ) :=
  [[],
    [128, 374],
    [128, 544],
    [128, 854],
    [30, 128],
    [128, 360],
    [128, 574],
    [128, 840],
    [32, 128],
    [128, 342],
    [128, 512],
    [128, 886],
    [62, 128],
    [128, 328],
    [128, 542],
    [128, 872],
    [78, 128],
    [128, 312],
    [128, 622],
    [128, 792],
    [80, 128],
    [128, 294],
    [128, 624],
    [128, 774],
    [110, 128],
    [128, 280],
    [128, 590],
    [128, 824],
    [112, 128],
    [128, 262],
    [128, 592],
    [128, 806]]

@[expose] def hypWit : List (List (ℕ × ℕ)) :=
  [[],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (4, 13), (4, 512), (6, 15), (10, 43)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (4, 13), (4, 277), (5, 11), (9, 39)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (4, 13), (4, 277), (7, 7), (11, 47)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (2, 262), (8, 45), (9, 39), (10, 43)],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (5, 11), (5, 512), (7, 7), (8, 45)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (6, 15), (6, 279), (7, 7), (8, 45)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (5, 11), (5, 262), (6, 15), (8, 45)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (2, 262), (4, 13), (5, 11), (6, 15)],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (4, 13), (4, 512), (6, 15), (9, 39)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (4, 13), (4, 277), (5, 11), (11, 47)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (4, 13), (4, 277), (7, 7), (10, 43)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (2, 262), (12, 19), (13, 17), (14, 25)],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (5, 11), (5, 512), (7, 7), (11, 47)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (6, 15), (6, 279), (7, 7), (10, 43)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (5, 11), (5, 262), (6, 15), (9, 39)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (2, 262), (4, 13), (5, 11), (6, 15)],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (4, 13), (4, 512), (6, 15), (10, 43)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (4, 13), (4, 277), (5, 11), (9, 39)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (4, 13), (4, 277), (7, 7), (11, 47)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (2, 262), (8, 45), (9, 39), (10, 43)],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (5, 11), (5, 512), (7, 7), (8, 45)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (6, 15), (6, 279), (7, 7), (8, 45)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (5, 11), (5, 262), (6, 15), (8, 45)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (2, 262), (4, 13), (5, 11), (6, 15)],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (4, 13), (4, 512), (6, 15), (9, 39)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (4, 13), (4, 277), (5, 11), (11, 47)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (4, 13), (4, 277), (7, 7), (10, 43)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (2, 262), (12, 19), (13, 17), (14, 25)],
    [(2, 14), (2, 16), (2, 32), (2, 64), (2, 128), (2, 262), (5, 11), (5, 512), (7, 7), (11, 47)],
    [(1, 14), (1, 16), (1, 32), (1, 64), (1, 128), (1, 512), (6, 15), (6, 279), (7, 7), (10, 43)],
    [(3, 14), (3, 16), (3, 32), (3, 64), (3, 128), (3, 774), (5, 11), (5, 262), (6, 15), (9, 39)]]

@[expose] def e4Cover : List (ℕ × ℕ × ℕ) :=
  [(1, 2, 14), (1, 2, 16), (1, 2, 32), (1, 2, 64), (1, 2, 128), (1, 4, 512), (2, 4, 280), (4, 8, 45), (5, 10, 43), (6, 11, 47)]

theorem hyp_fix_lt : ∀ h < 32, ∀ x ∈ hypFix.getD h [], x < 2 ^ 10 := by decide +kernel

theorem hyp_fix_ok : ∀ h < 32, 1 ≤ h → ∀ x ∈ hypFix.getD h [],
    ∀ u < 32, dot5 h u = false → act10 (nq2Arr u) x = x := by
  decide +kernel

@[expose] def FixedOK (h : ℕ) (L : List ℕ) : Prop :=
  ∀ m < 2 ^ 10, (∀ u < 32, dot5 h u = false → act10 (nq2Arr u) m = m) → m ∈ combos L

instance (h : ℕ) (L : List ℕ) : Decidable (FixedOK h L) := by
  unfold FixedOK
  infer_instance

theorem hyp_fixed_masks : ∀ h < 32, 1 ≤ h → FixedOK h (hypFix.getD h []) := by
  have hG : ∀ h < 32, ∀ g ∈ HypK.genTab.getD h [], g < 32 ∧ dot5 h g = false := by decide +kernel
  have hc := HypK.allBelow_tt (m := 32) (hi := 1)
    (f := fun h => bIf(Nat.blt 0 h, HypK.fixGensB (hypFix.getD h []) (HypK.genTab.getD h []), true))
    (by decide +kernel)
  intro h hh h1
  exact HypK.fixed_of_gens (hG h hh) (HypK.bIf_tt (hc h hh (by omega)) (Nat.blt_eq.mpr h1))

@[expose] def mS (l : List ℕ) : Subgroup W10 := maskSub 10 l

theorem card_mS {l : List ℕ} (hl : ∀ a ∈ l, a < 2 ^ 10) (hnd : (combos l).Nodup) :
    Nat.card ↥(mS l) = 2 ^ l.length :=
  card_maskSub hl hnd

theorem toW_mem_mS {m : ℕ} {l : List ℕ} (hm : m ∈ combos l) : toW 10 m ∈ mS l :=
  toW_mem_maskSub hm

theorem mem_mS {l : List ℕ} {v : W10} : v ∈ mS l ↔ ∃ m ∈ combos l, toW 10 m = v := Iff.rfl

theorem hyp_fix_len : ∀ h < 32, 1 ≤ h → (hypFix.getD h []).length = 2 := by decide +kernel

theorem hyp_fix_nodup : ∀ h < 32, 1 ≤ h → nodupB (combos (hypFix.getD h [])) 0 = true := by
  decide +kernel

theorem hyp_wit_ok : ∀ h < 32, 1 ≤ h → ∀ p ∈ hypWit.getD h [],
    p.1 ≠ 0 ∧ p.1 < 32 ∧ dot5 h p.1 = false ∧ act10 (nq2Arr p.1) p.2 = p.2 := by
  decide +kernel

theorem hyp_wit_lt : ∀ h < 32, ∀ p ∈ hypWit.getD h [], p.2 < 2 ^ 10 := by decide +kernel

theorem hyp_wit_len : ∀ h < 32, 1 ≤ h → ((hypWit.getD h []).map Prod.snd).length = 10 := by
  decide +kernel

theorem hyp_wit_nodup : ∀ h < 32, 1 ≤ h →
    nodupB (combos ((hypWit.getD h []).map Prod.snd)) 0 = true := by
  decide +kernel

theorem nq2_faithful_mask : ∀ u < 32, u ≠ 0 → ∃ m < 2 ^ 10, act10 (nq2Arr u) m ≠ m := by
  decide +kernel

theorem nq2Elt_xor (u v : Fin 32) : nq2Elt (xor32 u v) = nq2Elt u * nq2Elt v :=
  Subtype.ext (nq2Perm_mul u v).symm

theorem nq2Elt_zero_eq : nq2Elt 0 = 1 := Subtype.ext nq2Perm_zero

theorem Rc_ne_one_of_ne_zero {u : Fin 32} (hu : u ≠ 0) : Rc (nq2Elt u) ≠ 1 := by
  intro h
  have hu' : (u : ℕ) ≠ 0 := fun h0 => hu (Fin.ext h0)
  obtain ⟨m, hm, hne⟩ := nq2_faithful_mask u u.2 hu'
  apply hne
  have h1 : Rc (nq2Elt u) (toW 10 m) = toW 10 m := by rw [h]; rfl
  rw [Rc_nq2] at h1
  exact toW_inj (act10_lt _ m) hm h1

theorem mem_rImg_A {A : Subgroup P24} {h : Fin 32}
    (hA : ∀ g : P24, g ∈ A ↔ ∃ u : Fin 32, g = nq2Perm u ∧ dot5 (h : ℕ) (u : ℕ) = false)
    {g : MulAut W10} :
    g ∈ rImg Rc A ↔ ∃ u : Fin 32, dot5 (h : ℕ) (u : ℕ) = false ∧ g = Rc (nq2Elt u) := by
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ :=
      Subgroup.mem_map.1 (show g ∈ Subgroup.map Rc (A.subgroupOf mog22plus) from hg)
    obtain ⟨u, hu, hd⟩ := (hA _).1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨u, hd, congrArg Rc (Subtype.ext hu)⟩
  · rintro ⟨u, hd, rfl⟩
    exact Subgroup.mem_map_of_mem Rc (Subgroup.mem_subgroupOf.2 ((hA _).2 ⟨u, rfl, hd⟩))

theorem fixV_A_eq {A : Subgroup P24} {h : Fin 32} (h0 : h ≠ 0)
    (hA : ∀ g : P24, g ∈ A ↔ ∃ u : Fin 32, g = nq2Perm u ∧ dot5 (h : ℕ) (u : ℕ) = false) :
    fixV (rImg Rc A) = mS (hypFix.getD (h : ℕ) []) := by
  have h1 : 1 ≤ (h : ℕ) := Nat.one_le_iff_ne_zero.2 (fun e => h0 (Fin.ext e))
  ext v
  rw [mem_fixV]
  constructor
  · intro hv
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
    have hfix : ∀ u < 32, dot5 (h : ℕ) u = false → act10 (nq2Arr u) m = m := by
      intro u hu hd
      have hmem : Rc (nq2Elt ⟨u, hu⟩) ∈ rImg Rc A :=
        (mem_rImg_A hA).2 ⟨⟨u, hu⟩, hd, rfl⟩
      have h2 := hv _ hmem
      have h3 : toW 10 (act10 (nq2Arr u) m) = toW 10 m := (Rc_nq2 ⟨u, hu⟩ m).symm.trans h2
      exact toW_inj (act10_lt _ m) hm h3
    exact toW_mem_mS (hyp_fixed_masks h h.2 h1 m hm hfix)
  · intro hv x hx
    obtain ⟨u, hd, rfl⟩ := (mem_rImg_A hA).1 hx
    obtain ⟨m, hm, rfl⟩ := mem_mS.1 hv
    refine (Rc_nq2 u m).trans ?_
    congr 1
    exact act10_fix_combos_of _ (fun x hx => hyp_fix_ok h h.2 h1 x hx u u.2 hd) m hm

theorem rk_of_card_X {X : Subgroup W10} {k : ℕ} (h : Nat.card ↥X = 2 ^ k) : rk ↥X = k := by
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem rk_fixV_A {A : Subgroup P24} {h : Fin 32} (h0 : h ≠ 0)
    (hA : ∀ g : P24, g ∈ A ↔ ∃ u : Fin 32, g = nq2Perm u ∧ dot5 (h : ℕ) (u : ℕ) = false) :
    rk ↥(fixV (rImg Rc A)) = 2 := by
  have h1 : 1 ≤ (h : ℕ) := Nat.one_le_iff_ne_zero.2 (fun e => h0 (Fin.ext e))
  have hc : Nat.card ↥(mS (hypFix.getD (h : ℕ) [])) = 2 ^ 2 := by
    have := card_mS (l := hypFix.getD (h : ℕ) [])
      (fun a ha => hyp_fix_lt h h.2 a ha) (nodup_of_nodupB _ 0 (hyp_fix_nodup h h.2 h1)).1
    rw [hyp_fix_len h h.2 h1] at this
    exact this
  exact rk_of_card_X (k := 2) ((congrArg (fun X : Subgroup W10 => Nat.card ↥X)
    (fixV_A_eq h0 hA)).trans hc)

theorem mS_eq_top_of_len {l : List ℕ} (hl : ∀ a ∈ l, a < 2 ^ 10)
    (hnd : (combos l).Nodup) (hlen : l.length = 10) : mS l = ⊤ :=
  Subgroup.eq_top_of_card_eq _ (by rw [card_mS hl hnd, hlen, chc_card_W10])

theorem fixV_le_xiV {G : Subgroup (MulAut W10)} {g : MulAut W10} (hg : g ∈ G) (hg1 : g ≠ 1) :
    fixV (Subgroup.zpowers g) ≤ xiV G := by
  unfold xiV
  exact le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hg1 le_rfl))

theorem xi_A_top {A : Subgroup P24} {h : Fin 32} (h0 : h ≠ 0)
    (hA : ∀ g : P24, g ∈ A ↔ ∃ u : Fin 32, g = nq2Perm u ∧ dot5 (h : ℕ) (u : ℕ) = false) :
    xiV (rImg Rc A) = ⊤ := by
  have h1 : 1 ≤ (h : ℕ) := Nat.one_le_iff_ne_zero.2 (fun e => h0 (Fin.ext e))
  have htop : mS ((hypWit.getD (h : ℕ) []).map Prod.snd) = ⊤ :=
    mS_eq_top_of_len
      (fun a ha => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
        exact hyp_wit_lt h h.2 p hp)
      (nodup_of_nodupB _ 0 (hyp_wit_nodup h h.2 h1)).1 (hyp_wit_len h h.2 h1)
  have hle : mS ((hypWit.getD (h : ℕ) []).map Prod.snd) ≤ xiV (rImg Rc A) := by
    apply ch_maskSub_le
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hp0, hp32, hpd, hpfix⟩ := hyp_wit_ok h h.2 h1 p hp
    have hu0 : (⟨p.1, hp32⟩ : Fin 32) ≠ 0 := fun e => hp0 (congrArg Fin.val e)
    have hmem : Rc (nq2Elt ⟨p.1, hp32⟩) ∈ rImg Rc A :=
      (mem_rImg_A hA).2 ⟨⟨p.1, hp32⟩, hpd, rfl⟩
    have hfix : toW 10 p.2 ∈ fixV (Subgroup.zpowers (Rc (nq2Elt ⟨p.1, hp32⟩))) :=
      (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).2
        ((Rc_nq2 ⟨p.1, hp32⟩ p.2).trans (congrArg (toW 10) hpfix))
    exact fixV_le_xiV hmem (Rc_ne_one_of_ne_zero hu0) hfix
  exact eq_top_iff.2 (htop.symm.trans_le hle)

theorem hyp3_std :
    ∀ A : Subgroup P24, A ≤ KY mog22plus Qstd →
      Nat.card A * 2 = Nat.card (KY mog22plus Qstd) →
        xiV (rImg Rc A) = ⊤ ∧ rk ↥(fixV (rImg Rc A)) = 2 := by
  intro A hA hcard
  rw [KY_Q_L2] at hA hcard
  obtain ⟨h, h0, hmem⟩ := exists_hyperplane A hA hcard
  exact ⟨xi_A_top h0 hmem, rk_fixV_A h0 hmem⟩

theorem e4_ok : ∀ t ∈ e4Cover, t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.1 ≠ t.2.1 ∧ t.1 < 32 ∧ t.2.1 < 32 ∧
    act10 (nq2Arr t.1) t.2.2 = t.2.2 ∧ act10 (nq2Arr t.2.1) t.2.2 = t.2.2 := by
  decide +kernel

theorem e4_lt : ∀ t ∈ e4Cover, t.2.2 < 2 ^ 10 := by decide +kernel

theorem e4_len : (e4Cover.map fun t => t.2.2).length = 10 := by decide +kernel

theorem e4_nodup : nodupB (combos (e4Cover.map fun t => t.2.2)) 0 = true := by decide +kernel

theorem e4_set_closed : ∀ u v : Fin 32, ∀ s ∈ ({0, u, v, xor32 u v} : Finset (Fin 32)),
    ∀ t ∈ ({0, u, v, xor32 u v} : Finset (Fin 32)),
      xor32 s t ∈ ({0, u, v, xor32 u v} : Finset (Fin 32)) := by
  intro u v s hs t ht
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hs ht ⊢
  exact HypK.xor32_closed4 u v s t hs ht

theorem e4_set_card : ∀ u v : Fin 32, u ≠ 0 → v ≠ 0 → u ≠ v →
    ({0, u, v, xor32 u v} : Finset (Fin 32)).card = 4 := by
  decide +kernel

@[expose] def E4 (u v : Fin 32) : Subgroup P24 :=
  xorSub {0, u, v, xor32 u v} (by simp) (e4_set_closed u v)

theorem E4_le_NQ2 (u v : Fin 32) : E4 u v ≤ NQ2 := xorSub_le_NQ2 _ _ _

theorem isE2k_E4 {u v : Fin 32} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) : IsE2k 2 (E4 u v) :=
  isE2k_xorSub _ _ _ (by rw [e4_set_card u v hu hv huv]; norm_num)

theorem fixV_E4 (u v : Fin 32) (m : ℕ) (hu : act10 (nq2Arr u) m = m)
    (hv : act10 (nq2Arr v) m = m) : toW 10 m ∈ fixV (rImg Rc (E4 u v)) := by
  rw [mem_fixV]
  intro g hg
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (show g ∈ Subgroup.map Rc ((E4 u v).subgroupOf mog22plus)
    from hg)
  obtain ⟨w, hw, hyw⟩ := (mem_xorSub_iff).1 (Subgroup.mem_subgroupOf.1 hy)
  have hy' : y = nq2Elt w := Subtype.ext hyw
  subst hy'
  have hu' : Rc (nq2Elt u) (toW 10 m) = toW 10 m := by rw [Rc_nq2, hu]
  have hv' : Rc (nq2Elt v) (toW 10 m) = toW 10 m := by rw [Rc_nq2, hv]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · have h10 : Rc (nq2Elt 0) = 1 := (congrArg Rc nq2Elt_zero_eq).trans (map_one Rc)
    exact (congrArg (fun f : MulAut W10 => f (toW 10 m)) h10).trans (MulAut.one_apply W10 _)
  · exact hu'
  · exact hv'
  · have h : Rc (nq2Elt (xor32 u v)) = Rc (nq2Elt u) * Rc (nq2Elt v) :=
      (congrArg Rc (nq2Elt_xor u v)).trans (map_mul Rc _ _)
    calc Rc (nq2Elt (xor32 u v)) (toW 10 m)
        = (Rc (nq2Elt u) * Rc (nq2Elt v)) (toW 10 m) := congrArg (fun f : MulAut W10 => f (toW 10 m)) h
      _ = Rc (nq2Elt u) (Rc (nq2Elt v) (toW 10 m)) := MulAut.mul_apply W10 _ _ _
      _ = toW 10 m := by rw [hv', hu']

theorem hyp4_std :
    (⨆ (B' : Subgroup P24) (_ : B' ≤ KY mog22plus Qstd) (_ : IsE2k 2 B'),
      fixV (rImg Rc B')) = ⊤ := by
  rw [KY_Q_L2]
  have htop : mS (e4Cover.map fun t => t.2.2) = ⊤ :=
    mS_eq_top_of_len
      (fun a ha => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
        exact e4_lt t ht)
      (nodup_of_nodupB _ 0 e4_nodup).1 e4_len
  have hle : mS (e4Cover.map fun t => t.2.2) ≤
      ⨆ (B' : Subgroup P24) (_ : B' ≤ NQ2) (_ : IsE2k 2 B'), fixV (rImg Rc B') := by
    apply ch_maskSub_le
    intro b hb
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6⟩ := e4_ok t ht
    have hu : (⟨t.1, ht3⟩ : Fin 32) ≠ 0 := fun e => ht0 (congrArg Fin.val e)
    have hv : (⟨t.2.1, ht4⟩ : Fin 32) ≠ 0 := fun e => ht1 (congrArg Fin.val e)
    have huv : (⟨t.1, ht3⟩ : Fin 32) ≠ ⟨t.2.1, ht4⟩ := fun e => ht2 (congrArg Fin.val e)
    have hfix := fixV_E4 ⟨t.1, ht3⟩ ⟨t.2.1, ht4⟩ t.2.2 ht5 ht6
    have hB : fixV (rImg Rc (E4 ⟨t.1, ht3⟩ ⟨t.2.1, ht4⟩)) ≤
        ⨆ (B' : Subgroup P24) (_ : B' ≤ NQ2) (_ : IsE2k 2 B'), fixV (rImg Rc B') :=
      le_iSup_of_le (E4 ⟨t.1, ht3⟩ ⟨t.2.1, ht4⟩) (le_iSup_of_le (E4_le_NQ2 _ _)
        (le_iSup_of_le (isE2k_E4 hu hv huv) le_rfl))
    exact hB hfix
  exact eq_top_iff.2 (htop.symm.trans_le hle)

end CFSG.Quasithin.RonanH154
