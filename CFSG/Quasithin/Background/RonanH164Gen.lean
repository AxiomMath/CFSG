module

public import CFSG.Quasithin.Background.RonanH164Base
public import CFSG.Quasithin.Background.RonanH143QH
public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem mask_lt_c1 : ∀ a ∈ c1, a < 2 ^ 10 := by decide +kernel

theorem mask_lt_c5 : ∀ a ∈ c5, a < 2 ^ 10 := by decide +kernel

theorem mask_lt_c6 : ∀ a ∈ c6, a < 2 ^ 10 := by decide +kernel

theorem nodup_combos_c1 : (combos c1).Nodup :=
  (nodup_of_nodupB (combos c1) 0 (by decide +kernel)).1

theorem nodup_combos_c5 : (combos c5).Nodup :=
  (nodup_of_nodupB (combos c5) 0 (by decide +kernel)).1

theorem nodup_combos_c6 : (combos c6).Nodup :=
  (nodup_of_nodupB (combos c6) 0 (by decide +kernel)).1

theorem combos_c1_sub_c5 : ∀ m ∈ combos c1, m ∈ combos c5 := by decide +kernel

theorem combos_c5_sub_c6 : ∀ m ∈ combos c5, m ∈ combos c6 := by
  intro m hm
  show m ∈ combos (18 :: c5)
  exact List.mem_append_left _ hm

private theorem actC10_mem_combos_of (a : Array ℕ) {l : List ℕ} (h : ∀ x ∈ l, actC10 a x ∈ combos l) :
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

private theorem actC10_fix_combos_of (a : Array ℕ) {l : List ℕ} (h : ∀ x ∈ l, actC10 a x = x) :
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

theorem ko_inv_c1 : ∀ t < 16, ∀ x ∈ c1, actC10 (koArr t) x ∈ combos c1 := by decide +kernel

theorem ko_inv_c5 : ∀ t < 16, ∀ x ∈ c5, actC10 (koArr t) x ∈ combos c5 := by decide +kernel

theorem ko_inv_c6 : ∀ t < 16, ∀ x ∈ c6, actC10 (koArr t) x ∈ combos c6 := by decide +kernel

theorem x6_inv_c1 : ∀ x ∈ c1, actC10 x6Arr x ∈ combos c1 := by decide +kernel

theorem x6_inv_c5 : ∀ x ∈ c5, actC10 x6Arr x ∈ combos c5 := by decide +kernel

theorem x6_inv_c6 : ∀ x ∈ c6, actC10 x6Arr x ∈ combos c6 := by decide +kernel

theorem tau_inv_c1 : ∀ x ∈ c1, actC10 tauArr x ∈ combos c1 := by decide +kernel

theorem tau_inv_c5 : ∀ x ∈ c5, actC10 tauArr x ∈ combos c5 := by decide +kernel

theorem tau_inv_c6 : ∀ x ∈ c6, actC10 tauArr x ∈ combos c6 := by decide +kernel

theorem ko_fix_c1 : ∀ t < 16, ∀ x ∈ c1, actC10 (koArr t) x = x := by decide +kernel

theorem ko_fixed_masks :
    ∀ m < 2 ^ 10, (∀ t < 16, actC10 (koArr t) m = m) → m ∈ combos c1 := by
  decide +kernel

theorem ko_comm_c5 : ∀ t < 16, ∀ m < 2 ^ 10, actC10 (koArr t) m ^^^ m ∈ combos c5 := by
  have hc : ∀ t < 16, ∀ j < 10, actC10 (koArr t) (2 ^ j) ^^^ 2 ^ j ∈ combos c5 := by
    decide +kernel
  intro t ht m hm
  have hf : XorLin fun m => actC10 (koArr t) m ^^^ m := fun a b => by
    change actC10 (koArr t) (a ^^^ b) ^^^ (a ^^^ b) =
      (actC10 (koArr t) a ^^^ a) ^^^ (actC10 (koArr t) b ^^^ b)
    rw [xorLin_actC10 (koArr t) a b, Nat.xor_assoc, ← Nat.xor_assoc (actC10 (koArr t) b) a b,
      Nat.xor_comm (actC10 (koArr t) b) a, Nat.xor_assoc a (actC10 (koArr t) b) b,
      ← Nat.xor_assoc (actC10 (koArr t) a) a]
  exact mem_combos_of_xorLin hf (fun j hj => hc t ht j hj) m hm

theorem c5_wit : ∀ a ∈ c5, ∃ t < 16, ∃ m < 2 ^ 10, actC10 (koArr t) m ^^^ m = a := by
  have hcases : ∀ a ∈ c5, a = 512 ∨ a = 256 ∨ a = 10 ∨ a = 6 ∨ a = 1 := by decide +kernel
  intro a ha
  rcases hcases a ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, by norm_num, 368, by norm_num, by decide +kernel⟩
  · exact ⟨1, by norm_num, 688, by norm_num, by decide +kernel⟩
  · exact ⟨1, by norm_num, 656, by norm_num, by decide +kernel⟩
  · exact ⟨1, by norm_num, 528, by norm_num, by decide +kernel⟩
  · exact ⟨1, by norm_num, 512, by norm_num, by decide +kernel⟩

theorem card_V1 : Nat.card ↥V1 = 2 ^ 1 :=
  card_maskSub mask_lt_c1 nodup_combos_c1

theorem card_V5 : Nat.card ↥V5 = 2 ^ 5 :=
  card_maskSub mask_lt_c5 nodup_combos_c5

theorem card_V6 : Nat.card ↥V6 = 2 ^ 6 :=
  card_maskSub mask_lt_c6 nodup_combos_c6

theorem rk_V1 : rk ↥V1 = 1 := by
  unfold rk
  rw [card_V1, padicValNat.prime_pow]

theorem rk_V5 : rk ↥V5 = 5 := by
  unfold rk
  rw [card_V5, padicValNat.prime_pow]

theorem rk_V6 : rk ↥V6 = 6 := by
  unfold rk
  rw [card_V6, padicValNat.prime_pow]

theorem V1_le_V5 : V1 ≤ V5 := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 c1 from hv)
  exact toW_mem_maskSub (combos_c1_sub_c5 m hm)

theorem V5_le_V6 : V5 ≤ V6 := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 c5 from hv)
  exact toW_mem_maskSub (combos_c5_sub_c6 m hm)

theorem toW_mem_V1_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ V1 ↔ m ∈ combos c1 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 c1 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_c1 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem toW_mem_V5_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ V5 ↔ m ∈ combos c5 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 c5 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_c5 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

theorem toW_mem_V6_iff {m : ℕ} (hm : m < 2 ^ 10) : toW 10 m ∈ V6 ↔ m ∈ combos c6 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := mem_maskSub.1 (show toW 10 m ∈ maskSub 10 c6 from h)
    rw [toW_inj (combos_lt (n := 10) mask_lt_c6 m' hm') hm he] at hm'
    exact hm'
  · intro h
    exact toW_mem_maskSub h

private theorem mem_stabSub_of_forward {V : Type*} [CommGroup V] [Finite V] {U : Subgroup V}
    {g : MulAut V} (h : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U := by
  refine mem_stabSub.2 fun v => ⟨fun hv => ?_, h v⟩
  have hf : Function.Injective (fun u : U => (⟨g u, h u u.2⟩ : U)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hf ⟨g v, hv⟩
  have hgv : g u = g v := congrArg Subtype.val hu
  rw [← g.injective hgv]
  exact u.2

private noncomputable def stabPW (l : List ℕ) : Subgroup P24 :=
  ((stabSub (maskSub 10 l)).comap R).map mog22plus.subtype

private theorem coe_mem_stabPW {l : List ℕ} (x : ↥mog22plus) (hx : R x ∈ stabSub (maskSub 10 l)) :
    (x : P24) ∈ stabPW l := by
  unfold stabPW
  exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩

private theorem R_mem_of_mem_stabPW {l : List ℕ} {x : ↥mog22plus} (hx : (x : P24) ∈ stabPW l) :
    R x ∈ stabSub (maskSub 10 l) := by
  unfold stabPW at hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
  have hzx' : z = x := Subtype.ext hzx
  subst hzx'
  exact hz

theorem MH_le_closure :
    MY mog22plus Hstd ≤ Subgroup.closure ((fixO : Set P24) ∪ {x6Perm, tauPerm}) := by
  set H : Subgroup P24 := Subgroup.closure ((fixO : Set P24) ∪ {x6Perm, tauPerm}) with hH
  set H' : Subgroup ↥(MY mog22plus Hstd) := H.subgroupOf (MY mog22plus Hstd) with hH'
  have hx6 : (⟨x6Perm, x6_mem_MY_H⟩ : ↥(MY mog22plus Hstd)) ∈ H' :=
    Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (Or.inr (Set.mem_insert _ _)))
  have htau : (⟨tauPerm, tau_mem_MY_H⟩ : ↥(MY mog22plus Hstd)) ∈ H' :=
    Subgroup.mem_subgroupOf.2
      (Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hm := map_closure_eq_top_of_cycle_swap piH2 sigX sigX_isCycle sigX_support 1
    ⟨x6Perm, x6_mem_MY_H⟩ ⟨tauPerm, tau_mem_MY_H⟩ (piH2_eq_of_smul _ _ x6_smul_Tot)
    (by rw [← sigT_eq]; exact piH2_eq_of_smul _ _ tau_smul_Tot)
  have hsig : H'.map piH2 = ⊤ := by
    rw [eq_top_iff, ← hm]
    apply Subgroup.map_mono
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hx6
    · exact htau
  have hfixO : fixO ≤ H := fun _ hx => Subgroup.subset_closure (Or.inl hx)
  intro g hg
  have h1 : piH2 ⟨g, hg⟩ ∈ H'.map piH2 := by
    rw [hsig]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hgh⟩ := h1
  have h2 : (⟨g, hg⟩ : ↥(MY mog22plus Hstd)) * h⁻¹ ∈ piH2.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
  rw [ker_piH2, Subgroup.mem_subgroupOf] at h2
  have h3 : g * (h : P24)⁻¹ ∈ H := hfixO h2
  have h4 : (h : P24) ∈ H := Subgroup.mem_subgroupOf.1 hh
  simpa using H.mul_mem h3 h4

theorem inv_gen_mask_H (l : List ℕ)
    (hk : ∀ t < 16, ∀ x ∈ l, actC10 (koArr t) x ∈ combos l)
    (h6 : ∀ x ∈ l, actC10 x6Arr x ∈ combos l) (ht : ∀ x ∈ l, actC10 tauArr x ∈ combos l) :
    ∀ g ∈ rImg R (MY mog22plus Hstd), ∀ u ∈ maskSub 10 l, g u ∈ maskSub 10 l := by
  have stab_ko : ∀ t : Fin 16, R (koElt t) ∈ stabSub (maskSub 10 l) := by
    intro t
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (R_ko t m)).mpr
      (toW_mem_maskSub (actC10_mem_combos_of (koArr t) (hk t.1 t.2) m hm))
  have stab_x6 : R x6Elt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (R_x6 m)).mpr
      (toW_mem_maskSub (actC10_mem_combos_of x6Arr h6 m hm))
  have stab_tau : R tauElt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (R_tau m)).mpr
      (toW_mem_maskSub (actC10_mem_combos_of tauArr ht m hm))
  have hgen : Subgroup.closure ((fixO : Set P24) ∪ {x6Perm, tauPerm}) ≤ stabPW l := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨t, rfl⟩ := (mem_fixO_iff x).1 hx
      exact coe_mem_stabPW (koElt t) (stab_ko t)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact coe_mem_stabPW x6Elt stab_x6
      · exact coe_mem_stabPW tauElt stab_tau
  have hMY : MY mog22plus Hstd ≤ stabPW l := le_trans MH_le_closure hgen
  intro g hg u hu
  obtain ⟨y, hy, rfl⟩ :=
    Subgroup.mem_map.1 (show g ∈ Subgroup.map R ((MY mog22plus Hstd).subgroupOf mog22plus) from hg)
  have hyR := R_mem_of_mem_stabPW (hMY (Subgroup.mem_subgroupOf.1 hy))
  exact (mem_stabSub.1 hyR u).2 hu

theorem inv_V1 :
    ∀ g ∈ rImg R (MY mog22plus Hstd), ∀ u ∈ V1, g u ∈ V1 :=
  inv_gen_mask_H c1 ko_inv_c1 x6_inv_c1 tau_inv_c1

theorem inv_V5 :
    ∀ g ∈ rImg R (MY mog22plus Hstd), ∀ u ∈ V5, g u ∈ V5 :=
  inv_gen_mask_H c5 ko_inv_c5 x6_inv_c5 tau_inv_c5

theorem inv_V6 :
    ∀ g ∈ rImg R (MY mog22plus Hstd), ∀ u ∈ V6, g u ∈ V6 :=
  inv_gen_mask_H c6 ko_inv_c6 x6_inv_c6 tau_inv_c6

private theorem toW_inv_self (m : ℕ) : (toW 10 m)⁻¹ = toW 10 m := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h0 : toW 10 (m ^^^ m) = 1 := (congrArg (toW 10) (Nat.xor_self m)).trans (toW_zero 10)
  exact (toW_xor 10 m m).symm.trans h0

theorem toW_mem_commV_of (t : Fin 16) (m : ℕ) :
    toW 10 (actC10 (koArr t) m ^^^ m) ∈ commV (rImg R fixO) := by
  have hmem : R (koElt t) ∈ rImg R fixO :=
    Subgroup.mem_map_of_mem R (Subgroup.mem_subgroupOf.2 ((mem_fixO_iff (koPerm t)).2 ⟨t, rfl⟩))
  have key : toW 10 (actC10 (koArr t) m ^^^ m) = R (koElt t) (toW 10 m) * (toW 10 m)⁻¹ := by
    rw [R_ko t m, toW_inv_self m, toW_xor]
  rw [key]
  exact Subgroup.subset_closure ⟨R (koElt t), hmem, toW 10 m, rfl⟩

theorem fixV_fixO : fixV (rImg R fixO) = V1 := by
  ext v
  rw [mem_fixV]
  constructor
  · intro hv
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
    have hfix : ∀ t < 16, actC10 (koArr t) m = m := by
      intro t ht
      have hk : koElt ⟨t, ht⟩ ∈ fixO.subgroupOf mog22plus :=
        Subgroup.mem_subgroupOf.2 ((mem_fixO_iff (koPerm ⟨t, ht⟩)).2 ⟨⟨t, ht⟩, rfl⟩)
      have h := hv _ (Subgroup.mem_map_of_mem R hk)
      have h2 : toW 10 (actC10 (koArr t) m) = toW 10 m := (R_ko ⟨t, ht⟩ m).symm.trans h
      exact toW_inj (actC10_lt _ m) hm h2
    exact (toW_mem_V1_iff hm).2 (ko_fixed_masks m hm hfix)
  · intro hv x hx
    obtain ⟨y, hy, rfl⟩ :=
      Subgroup.mem_map.1 (show x ∈ Subgroup.map R (fixO.subgroupOf mog22plus) from hx)
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hy)
    have hy' : y = koElt t := Subtype.ext ht
    subst hy'
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 c1 from hv)
    refine (R_ko t m).trans ?_
    congr 1
    exact actC10_fix_combos_of _ (ko_fix_c1 t.1 t.2) m hm

theorem commV_fixO : commV (rImg R fixO) = V5 := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨y, hy, rfl⟩ :=
      Subgroup.mem_map.1 (show x ∈ Subgroup.map R (fixO.subgroupOf mog22plus) from hx)
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hy)
    have hy' : y = koElt t := Subtype.ext ht
    subst hy'
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
    have hV5 : R (koElt t) (toW 10 m) * (toW 10 m)⁻¹ ∈ V5 := by
      rw [R_ko t m, toW_inv_self m, ← toW_xor]
      exact toW_mem_maskSub (ko_comm_c5 t.1 t.2 m hm)
    exact hV5
  · have hgen : ∀ a ∈ c5, toW 10 a ∈ commV (rImg R fixO) := by
      intro a ha
      obtain ⟨t, ht, m, -, hta⟩ := c5_wit a ha
      subst hta
      exact toW_mem_commV_of ⟨t, ht⟩ m
    have h0 : toW 10 0 ∈ commV (rImg R fixO) := by
      rw [toW_zero]
      exact Subgroup.one_mem _
    have hxor : ∀ a b, toW 10 a ∈ commV (rImg R fixO) → toW 10 b ∈ commV (rImg R fixO) →
        toW 10 (a ^^^ b) ∈ commV (rImg R fixO) := by
      intro a b ha hb
      rw [toW_xor]
      exact Subgroup.mul_mem _ ha hb
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show v ∈ maskSub 10 c5 from hv)
    exact mem_of_combos (fun a => toW 10 a ∈ commV (rImg R fixO)) h0 hxor c5 hgen m hm

end CFSG.Quasithin.RonanH163
