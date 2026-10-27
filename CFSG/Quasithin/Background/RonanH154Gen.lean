module

public import CFSG.Quasithin.Background.RonanH154Base
public import CFSG.Quasithin.Background.RonanH163Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem mask_lt_w1 : ∀ a ∈ w1, a < 2 ^ 10 := by decide +kernel

theorem mask_lt_w2 : ∀ a ∈ w2, a < 2 ^ 10 := by decide +kernel

theorem mask_lt_w6 : ∀ a ∈ w6, a < 2 ^ 10 := by decide +kernel

theorem mask_lt_w10 : ∀ a ∈ w10, a < 2 ^ 10 := by decide +kernel

theorem nodup_combos_w1 : (combos w1).Nodup :=
  (nodup_of_nodupB (combos w1) 0 (by decide +kernel)).1

theorem nodup_combos_w2 : (combos w2).Nodup :=
  (nodup_of_nodupB (combos w2) 0 (by decide +kernel)).1

theorem nodup_combos_w6 : (combos w6).Nodup :=
  (nodup_of_nodupB (combos w6) 0 (by decide +kernel)).1

theorem nodup_combos_w10 : (combos w10).Nodup :=
  (nodup_of_nodupB (combos w10) 0 (by decide +kernel)).1

theorem combos_w1_sub_w2 : ∀ m ∈ combos w1, m ∈ combos w2 := by decide +kernel

theorem combos_w2_sub_w6 : ∀ m ∈ combos w2, m ∈ combos w6 := by decide +kernel

theorem act10_mem_combos_of (a : Array ℕ) {l : List ℕ} (h : ∀ x ∈ l, act10 a x ∈ combos l) :
    ∀ m ∈ combos l, act10 a m ∈ combos l :=
  mem_of_combos (fun x => act10 a x ∈ combos l)
    (by
      show act10 a 0 ∈ combos l
      rw [XorLin.map_zero (xorLin_act10 a)]
      exact zero_mem_combos l)
    (fun x y hx hy => by
      show act10 a (x ^^^ y) ∈ combos l
      rw [xorLin_act10 a x y]
      exact xor_mem_combos l hx hy)
    l h

theorem act10_fix_combos_of (a : Array ℕ) {l : List ℕ} (h : ∀ x ∈ l, act10 a x = x) :
    ∀ m ∈ combos l, act10 a m = m :=
  mem_of_combos (fun x => act10 a x = x)
    (by
      show act10 a 0 = 0
      exact XorLin.map_zero (xorLin_act10 a))
    (fun x y hx hy => by
      have hx' : act10 a x = x := hx
      have hy' : act10 a y = y := hy
      show act10 a (x ^^^ y) = x ^^^ y
      rw [xorLin_act10 a x y, hx', hy'])
    l h

theorem g1_inv_w1 : ∀ x ∈ w1, act10 g1Arr x ∈ combos w1 := by decide +kernel

theorem g1_inv_w2 : ∀ x ∈ w2, act10 g1Arr x ∈ combos w2 := by decide +kernel

theorem g1_inv_w6 : ∀ x ∈ w6, act10 g1Arr x ∈ combos w6 := by decide +kernel

theorem g2_inv_w1 : ∀ x ∈ w1, act10 g2Arr x ∈ combos w1 := by decide +kernel

theorem g2_inv_w2 : ∀ x ∈ w2, act10 g2Arr x ∈ combos w2 := by decide +kernel

theorem g2_inv_w6 : ∀ x ∈ w6, act10 g2Arr x ∈ combos w6 := by decide +kernel

theorem nq2_inv_w1 : ∀ u < 32, ∀ x ∈ w1, act10 (nq2Arr u) x ∈ combos w1 := by decide +kernel

theorem nq2_inv_w2 : ∀ u < 32, ∀ x ∈ w2, act10 (nq2Arr u) x ∈ combos w2 := by decide +kernel

theorem nq2_inv_w6 : ∀ u < 32, ∀ x ∈ w6, act10 (nq2Arr u) x ∈ combos w6 := by decide +kernel

theorem nq2_fix_w1 : ∀ u < 32, ∀ x ∈ w1, act10 (nq2Arr u) x = x := by decide +kernel

theorem nq_fix_w2 : ∀ u < 16, ∀ x ∈ w2, act10 (nq2Arr u) x = x := by decide +kernel

theorem nq2_fixed_masks :
    ∀ m < 2 ^ 10, (∀ u < 32, act10 (nq2Arr u) m = m) → m ∈ combos w1 := by
  decide +kernel

theorem nq_fixed_masks :
    ∀ m < 2 ^ 10, (∀ u < 16, act10 (nq2Arr u) m = m) → m ∈ combos w2 := by
  decide +kernel

@[expose] noncomputable def stabPWc (l : List ℕ) : Subgroup P24 :=
  ((stabSub (maskSub 10 l)).comap Rc).map mog22plus.subtype

theorem coe_mem_stabPWc {l : List ℕ} (x : ↥mog22plus) (hx : Rc x ∈ stabSub (maskSub 10 l)) :
    (x : P24) ∈ stabPWc l := by
  unfold stabPWc
  exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem Rc_mem_of_mem_stabPWc {l : List ℕ} {x : ↥mog22plus} (hx : (x : P24) ∈ stabPWc l) :
    Rc x ∈ stabSub (maskSub 10 l) := by
  unfold stabPWc at hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
  have hzx' : z = x := Subtype.ext hzx
  subst hzx'
  exact hz

theorem card_X1 : Nat.card ↥X1 = 2 ^ 1 :=
  card_maskSub mask_lt_w1 nodup_combos_w1

theorem card_X2 : Nat.card ↥X2 = 2 ^ 2 :=
  card_maskSub mask_lt_w2 nodup_combos_w2

theorem card_X6 : Nat.card ↥X6 = 2 ^ 6 :=
  card_maskSub mask_lt_w6 nodup_combos_w6

theorem card_X10 : Nat.card ↥(maskSub 10 w10) = 2 ^ 10 :=
  card_maskSub mask_lt_w10 nodup_combos_w10

theorem rk_X1 : rk ↥X1 = 1 := by
  unfold rk
  rw [card_X1, padicValNat.prime_pow]

theorem rk_X2 : rk ↥X2 = 2 := by
  unfold rk
  rw [card_X2, padicValNat.prime_pow]

theorem rk_X6 : rk ↥X6 = 6 := by
  unfold rk
  rw [card_X6, padicValNat.prime_pow]

theorem X1_le_X2 : X1 ≤ X2 := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 w1 from hv)
  exact toW_mem_maskSub (combos_w1_sub_w2 m hm)

theorem X2_le_X6 : X2 ≤ X6 := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 w2 from hv)
  exact toW_mem_maskSub (combos_w2_sub_w6 m hm)

theorem toW_mem_X1_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ X1 ↔ m ∈ combos w1 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 w1 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_w1 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem toW_mem_X2_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ X2 ↔ m ∈ combos w2 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 w2 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_w2 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem toW_mem_X6_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ X6 ↔ m ∈ combos w6 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 w6 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_w6 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem inv_gen_maskc (l : List ℕ)
    (h1 : ∀ x ∈ l, act10 g1Arr x ∈ combos l) (h2 : ∀ x ∈ l, act10 g2Arr x ∈ combos l)
    (hn : ∀ u < 32, ∀ x ∈ l, act10 (nq2Arr u) x ∈ combos l) :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ maskSub 10 l, g u ∈ maskSub 10 l := by
  have stab_g1 : Rc g1Elt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (Rc_g1 m)).mpr
      (toW_mem_maskSub (act10_mem_combos_of g1Arr h1 m hm))
  have stab_g2 : Rc g2Elt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (Rc_g2 m)).mpr
      (toW_mem_maskSub (act10_mem_combos_of g2Arr h2 m hm))
  have stab_nq2 : ∀ u : Fin 32, Rc (nq2Elt u) ∈ stabSub (maskSub 10 l) := by
    intro u
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (Rc_nq2 u m)).mpr
      (toW_mem_maskSub (act10_mem_combos_of _ (hn u.1 u.2) m hm))
  have hgen : Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) ≤ stabPWc l := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨u, rfl⟩ := hx
      exact coe_mem_stabPWc (nq2Elt u) (stab_nq2 u)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact coe_mem_stabPWc g1Elt stab_g1
      · exact coe_mem_stabPWc g2Elt stab_g2
  have hMY : MY mog22plus Qstd ≤ stabPWc l := le_trans MQ_le_closure hgen
  intro g hg u hu
  obtain ⟨y, hy, rfl⟩ :=
    Subgroup.mem_map.1 (show g ∈ Subgroup.map Rc ((MY mog22plus Qstd).subgroupOf mog22plus) from hg)
  have hyR := Rc_mem_of_mem_stabPWc (hMY (Subgroup.mem_subgroupOf.1 hy))
  exact (mem_stabSub.1 hyR u).2 hu

theorem inv_X1 :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ X1, g u ∈ X1 :=
  inv_gen_maskc w1 g1_inv_w1 g2_inv_w1 nq2_inv_w1

theorem inv_X2 :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ X2, g u ∈ X2 :=
  inv_gen_maskc w2 g1_inv_w2 g2_inv_w2 nq2_inv_w2

theorem inv_X6 :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ X6, g u ∈ X6 :=
  inv_gen_maskc w6 g1_inv_w6 g2_inv_w6 nq2_inv_w6

theorem fixV_NQ2_X1 : fixV (rImg Rc NQ2) = X1 := by
  ext v
  rw [mem_fixV]
  constructor
  · intro hv
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
    have hfix : ∀ u < 32, act10 (nq2Arr u) m = m := by
      intro u hu
      have hnq : nq2Elt ⟨u, hu⟩ ∈ NQ2.subgroupOf mog22plus :=
        Subgroup.mem_subgroupOf.2 (mem_NQ2_iff.2 ⟨⟨u, hu⟩, rfl⟩)
      have h := hv _ (Subgroup.mem_map_of_mem Rc hnq)
      have h2 : toW 10 (act10 (nq2Arr u) m) = toW 10 m := (Rc_nq2 ⟨u, hu⟩ m).symm.trans h
      exact toW_inj (act10_lt _ m) hm h2
    exact (toW_mem_X1_iff hm).2 (nq2_fixed_masks m hm hfix)
  · intro hv x hx
    obtain ⟨y, hy, rfl⟩ :=
      Subgroup.mem_map.1 (show x ∈ Subgroup.map Rc (NQ2.subgroupOf mog22plus) from hx)
    obtain ⟨u, hu⟩ := mem_NQ2_iff.1 (Subgroup.mem_subgroupOf.1 hy)
    have hy' : y = nq2Elt u := Subtype.ext hu
    subst hy'
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 w1 from hv)
    refine (Rc_nq2 u m).trans ?_
    congr 1
    exact act10_fix_combos_of _ (nq2_fix_w1 u.1 u.2) m hm

theorem mem_NQ_iff_lt16 {g : P24} : g ∈ NQ ↔ ∃ u : Fin 32, (u : ℕ) < 16 ∧ g = nq2Perm u := by
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := hg
    refine ⟨⟨t, by omega⟩, t.2, ?_⟩
    have h : (t : ℕ) < 16 := t.2
    simp only [nq2Perm, h, ↓reduceIte]
    congr 1
    exact Fin.ext (by simp [Nat.mod_eq_of_lt h])
  · rintro ⟨u, hu, rfl⟩
    simp only [nq2Perm, hu, ↓reduceIte]
    exact ⟨⟨u % 16, by omega⟩, rfl⟩

theorem fixV_NQ_X2 : fixV (rImg Rc NQ) = X2 := by
  ext v
  rw [mem_fixV]
  constructor
  · intro hv
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
    have hfix : ∀ u < 16, act10 (nq2Arr u) m = m := by
      intro u hu
      have hnq : nq2Elt ⟨u, by omega⟩ ∈ NQ.subgroupOf mog22plus :=
        Subgroup.mem_subgroupOf.2 (mem_NQ_iff_lt16.2 ⟨⟨u, by omega⟩, hu, rfl⟩)
      have h := hv _ (Subgroup.mem_map_of_mem Rc hnq)
      have h2 : toW 10 (act10 (nq2Arr u) m) = toW 10 m :=
        (Rc_nq2 ⟨u, by omega⟩ m).symm.trans h
      exact toW_inj (act10_lt _ m) hm h2
    exact (toW_mem_X2_iff hm).2 (nq_fixed_masks m hm hfix)
  · intro hv x hx
    obtain ⟨y, hy, rfl⟩ :=
      Subgroup.mem_map.1 (show x ∈ Subgroup.map Rc (NQ.subgroupOf mog22plus) from hx)
    obtain ⟨u, hu16, hu⟩ := mem_NQ_iff_lt16.1 (Subgroup.mem_subgroupOf.1 hy)
    have hy' : y = nq2Elt u := Subtype.ext hu
    subst hy'
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 w2 from hv)
    refine (Rc_nq2 u m).trans ?_
    congr 1
    exact act10_fix_combos_of _ (fun x hx => nq_fix_w2 u.1 hu16 x hx) m hm

end CFSG.Quasithin.RonanH154
