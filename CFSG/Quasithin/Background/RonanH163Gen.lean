module

public import CFSG.Quasithin.Background.RonanH163Base
public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem mask_lt_b4 : ∀ a ∈ b4, a < 2 ^ 10 := by decide +kernel

theorem mask_lt_b8 : ∀ a ∈ b8, a < 2 ^ 10 := by decide +kernel

theorem mask_lt_b9 : ∀ a ∈ b9, a < 2 ^ 10 := by decide +kernel

theorem nodup_combos_b4 : (combos b4).Nodup :=
  (nodup_of_nodupB (combos b4) 0 (by decide +kernel)).1

theorem nodup_combos_b8 : (combos b8).Nodup :=
  (nodup_of_nodupB (combos b8) 0 (by decide +kernel)).1

theorem nodup_combos_b9 : (combos b9).Nodup :=
  (nodup_of_nodupB (combos b9) 0 (by decide +kernel)).1

theorem combos_b4_sub_b8 : ∀ m ∈ combos b4, m ∈ combos b8 := by decide +kernel

theorem combos_b8_sub_b9 : ∀ m ∈ combos b8, m ∈ combos b9 := by
  intro m hm
  show m ∈ combos (2 :: b8)
  exact List.mem_append_left _ hm

theorem actC10_mem_combos_of (a : Array ℕ) {l : List ℕ} (h : ∀ x ∈ l, actC10 a x ∈ combos l) :
    ∀ m ∈ combos l, actC10 a m ∈ combos l :=
  mem_of_combos (fun x => actC10 a x ∈ combos l)
    (by
      show actC10 a 0 ∈ combos l
      rw [XorLin.map_zero (xorLin_actC10 a)]
      exact zero_mem_combos l)
    (fun x y hx hy => by
      show actC10 a (x ^^^ y) ∈ combos l
      rw [xorLin_actC10 a x y]
      exact xor_mem_combos l hx hy)
    l h

theorem actC10_fix_combos_of (a : Array ℕ) {l : List ℕ} (h : ∀ x ∈ l, actC10 a x = x) :
    ∀ m ∈ combos l, actC10 a m = m :=
  mem_of_combos (fun x => actC10 a x = x)
    (by
      show actC10 a 0 = 0
      exact XorLin.map_zero (xorLin_actC10 a))
    (fun x y hx hy => by
      have hx' : actC10 a x = x := hx
      have hy' : actC10 a y = y := hy
      show actC10 a (x ^^^ y) = x ^^^ y
      rw [xorLin_actC10 a x y, hx', hy'])
    l h

theorem g1_inv_b4 : ∀ x ∈ b4, actC10 g1Arr x ∈ combos b4 := by decide +kernel

theorem g1_inv_b8 : ∀ x ∈ b8, actC10 g1Arr x ∈ combos b8 := by decide +kernel

theorem g1_inv_b9 : ∀ x ∈ b9, actC10 g1Arr x ∈ combos b9 := by decide +kernel

theorem g2_inv_b4 : ∀ x ∈ b4, actC10 g2Arr x ∈ combos b4 := by decide +kernel

theorem g2_inv_b8 : ∀ x ∈ b8, actC10 g2Arr x ∈ combos b8 := by decide +kernel

theorem g2_inv_b9 : ∀ x ∈ b9, actC10 g2Arr x ∈ combos b9 := by decide +kernel

theorem nq2_inv_b4 : ∀ u < 32, ∀ x ∈ b4, actC10 (nq2Arr u) x ∈ combos b4 := by
  decide +kernel

theorem nq2_inv_b8 : ∀ u < 32, ∀ x ∈ b8, actC10 (nq2Arr u) x ∈ combos b8 := by
  decide +kernel

theorem nq2_inv_b9 : ∀ u < 32, ∀ x ∈ b9, actC10 (nq2Arr u) x ∈ combos b9 := by
  decide +kernel

theorem nq2_fix_b4 : ∀ u < 32, ∀ x ∈ b4, actC10 (nq2Arr u) x = x := by decide +kernel

theorem nq2_fixed_masks :
    ∀ m < 2 ^ 10, (∀ u < 32, actC10 (nq2Arr u) m = m) → m ∈ combos b4 := by
  decide +kernel

theorem mem_stabSub_of_forward {V : Type*} [CommGroup V] [Finite V] {U : Subgroup V}
    {g : MulAut V} (h : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U := by
  refine mem_stabSub.2 fun v => ⟨fun hv => ?_, h v⟩
  have hf : Function.Injective (fun u : U => (⟨g u, h u u.2⟩ : U)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hf ⟨g v, hv⟩
  have hgv : g u = g v := congrArg Subtype.val hu
  rw [← g.injective hgv]
  exact u.2

@[expose] noncomputable def stabPW (l : List ℕ) : Subgroup P24 :=
  ((stabSub (maskSub 10 l)).comap R).map mog22plus.subtype

theorem coe_mem_stabPW {l : List ℕ} (x : ↥mog22plus) (hx : R x ∈ stabSub (maskSub 10 l)) :
    (x : P24) ∈ stabPW l := by
  unfold stabPW
  exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem R_mem_of_mem_stabPW {l : List ℕ} {x : ↥mog22plus} (hx : (x : P24) ∈ stabPW l) :
    R x ∈ stabSub (maskSub 10 l) := by
  unfold stabPW at hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
  have hzx' : z = x := Subtype.ext hzx
  subst hzx'
  exact hz

theorem g1Perm_mem_gen :
    g1Perm ∈ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) :=
  Subgroup.subset_closure (Or.inr (Set.mem_insert _ _))

theorem g2Perm_mem_gen :
    g2Perm ∈ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) :=
  Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem nq2_le_gen : NQ2 ≤ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem card_U4 : Nat.card ↥U4 = 2 ^ 4 :=
  card_maskSub mask_lt_b4 nodup_combos_b4

theorem card_U8 : Nat.card ↥U8 = 2 ^ 8 :=
  card_maskSub mask_lt_b8 nodup_combos_b8

theorem card_U9 : Nat.card ↥U9 = 2 ^ 9 :=
  card_maskSub mask_lt_b9 nodup_combos_b9

theorem rk_U4 : rk ↥U4 = 4 := by
  unfold rk
  rw [card_U4, padicValNat.prime_pow]

theorem rk_U8 : rk ↥U8 = 8 := by
  unfold rk
  rw [card_U8, padicValNat.prime_pow]

theorem rk_U9 : rk ↥U9 = 9 := by
  unfold rk
  rw [card_U9, padicValNat.prime_pow]

theorem U4_le_U8 : U4 ≤ U8 := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 b4 from hv)
  exact toW_mem_maskSub (combos_b4_sub_b8 m hm)

theorem U8_le_U9 : U8 ≤ U9 := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 b8 from hv)
  exact toW_mem_maskSub (combos_b8_sub_b9 m hm)

theorem toW_mem_U4_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ U4 ↔ m ∈ combos b4 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 b4 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_b4 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem toW_mem_U8_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ U8 ↔ m ∈ combos b8 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 b8 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_b8 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem toW_mem_U9_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ U9 ↔ m ∈ combos b9 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 b9 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_b9 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem MQ_le_closure :
    MY mog22plus Qstd ≤ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) := by
  set H : Subgroup P24 := Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) with hH
  set H' : Subgroup ↥(MY mog22plus Qstd) := H.subgroupOf (MY mog22plus Qstd) with hH'
  have hg1 : (⟨g1Perm, g1Perm_mem_MY g1Perm_mem_mog22plus⟩ : ↥(MY mog22plus Qstd)) ∈ H' :=
    Subgroup.mem_subgroupOf.2 g1Perm_mem_gen
  have hg2 : (⟨g2Perm, g2Perm_mem_MY g2Perm_mem_mog22plus⟩ : ↥(MY mog22plus Qstd)) ∈ H' :=
    Subgroup.mem_subgroupOf.2 g2Perm_mem_gen
  have hm := map_closure_eq_top_of_cycle_swap (piQ mog22plus) sig1 sig1_isCycle sig1_support 3
    ⟨g1Perm, g1Perm_mem_MY g1Perm_mem_mog22plus⟩ ⟨g2Perm, g2Perm_mem_MY g2Perm_mem_mog22plus⟩
    (piQ_eq_of_smul _ _ g1_smul_Zq) (by rw [← sig2_eq]; exact piQ_eq_of_smul _ _ g2_smul_Zq)
  have hsig : H'.map (piQ mog22plus) = ⊤ := by
    rw [eq_top_iff, ← hm]
    apply Subgroup.map_mono
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hg1
    · exact hg2
  intro g hg
  have h1 : piQ mog22plus ⟨g, hg⟩ ∈ H'.map (piQ mog22plus) := by
    rw [hsig]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hgh⟩ := h1
  have h2 : (⟨g, hg⟩ : ↥(MY mog22plus Qstd)) * h⁻¹ ∈ (piQ mog22plus).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
  rw [ker_piQ_L2, Subgroup.mem_subgroupOf] at h2
  have h3 : g * (h : P24)⁻¹ ∈ H := nq2_le_gen h2
  have h4 : (h : P24) ∈ H := Subgroup.mem_subgroupOf.1 hh
  simpa using H.mul_mem h3 h4

theorem inv_gen_mask (l : List ℕ)
    (h1 : ∀ x ∈ l, actC10 g1Arr x ∈ combos l) (h2 : ∀ x ∈ l, actC10 g2Arr x ∈ combos l)
    (hn : ∀ u < 32, ∀ x ∈ l, actC10 (nq2Arr u) x ∈ combos l) :
    ∀ g ∈ rImg R (MY mog22plus Qstd), ∀ u ∈ maskSub 10 l, g u ∈ maskSub 10 l := by
  have stab_g1 : R g1Elt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (R_g1 m)).mpr
      (toW_mem_maskSub (actC10_mem_combos_of g1Arr h1 m hm))
  have stab_g2 : R g2Elt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (R_g2 m)).mpr
      (toW_mem_maskSub (actC10_mem_combos_of g2Arr h2 m hm))
  have stab_nq2 : ∀ u : Fin 32, R (nq2Elt u) ∈ stabSub (maskSub 10 l) := by
    intro u
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (R_nq2 u m)).mpr
      (toW_mem_maskSub (actC10_mem_combos_of _ (hn u.1 u.2) m hm))
  have hgen : Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) ≤ stabPW l := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨u, rfl⟩ := hx
      exact coe_mem_stabPW (nq2Elt u) (stab_nq2 u)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact coe_mem_stabPW g1Elt stab_g1
      · exact coe_mem_stabPW g2Elt stab_g2
  have hMY : MY mog22plus Qstd ≤ stabPW l := le_trans MQ_le_closure hgen
  intro g hg u hu
  obtain ⟨y, hy, rfl⟩ :=
    Subgroup.mem_map.1 (show g ∈ Subgroup.map R ((MY mog22plus Qstd).subgroupOf mog22plus) from hg)
  have hyR := R_mem_of_mem_stabPW (hMY (Subgroup.mem_subgroupOf.1 hy))
  exact (mem_stabSub.1 hyR u).2 hu

theorem inv_U4 :
    ∀ g ∈ rImg R (MY mog22plus Qstd), ∀ u ∈ U4, g u ∈ U4 :=
  inv_gen_mask b4 g1_inv_b4 g2_inv_b4 nq2_inv_b4

theorem inv_U8 :
    ∀ g ∈ rImg R (MY mog22plus Qstd), ∀ u ∈ U8, g u ∈ U8 :=
  inv_gen_mask b8 g1_inv_b8 g2_inv_b8 nq2_inv_b8

theorem inv_U9 :
    ∀ g ∈ rImg R (MY mog22plus Qstd), ∀ u ∈ U9, g u ∈ U9 :=
  inv_gen_mask b9 g1_inv_b9 g2_inv_b9 nq2_inv_b9

theorem fixV_NQ2 : fixV (rImg R NQ2) = U4 := by
  ext v
  rw [mem_fixV]
  constructor
  · intro hv
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
    have hfix : ∀ u < 32, actC10 (nq2Arr u) m = m := by
      intro u hu
      have hnq : nq2Elt ⟨u, hu⟩ ∈ NQ2.subgroupOf mog22plus :=
        Subgroup.mem_subgroupOf.2 (mem_NQ2_iff.2 ⟨⟨u, hu⟩, rfl⟩)
      have h := hv _ (Subgroup.mem_map_of_mem R hnq)
      have h2 : toW 10 (actC10 (nq2Arr u) m) = toW 10 m := (R_nq2 ⟨u, hu⟩ m).symm.trans h
      exact toW_inj (actC10_lt _ m) hm h2
    exact (toW_mem_U4_iff hm).2 (nq2_fixed_masks m hm hfix)
  · intro hv x hx
    obtain ⟨y, hy, rfl⟩ :=
      Subgroup.mem_map.1 (show x ∈ Subgroup.map R (NQ2.subgroupOf mog22plus) from hx)
    obtain ⟨u, hu⟩ := mem_NQ2_iff.1 (Subgroup.mem_subgroupOf.1 hy)
    have hy' : y = nq2Elt u := Subtype.ext hu
    subst hy'
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 b4 from hv)
    refine (R_nq2 u m).trans ?_
    congr 1
    exact actC10_fix_combos_of _ (nq2_fix_b4 u.1 u.2) m hm

end CFSG.Quasithin.RonanH163
