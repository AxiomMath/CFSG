module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.E2SolvBaumann

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F
open scoped commutatorElement

section Module

variable {W : Type*} [CommGroup W]

theorem commSub_top_le_of_closure {S : Set (MulAut W)} {N : Subgroup W}
    (h : ∀ s ∈ S, ∀ w : W, s w * w⁻¹ ∈ N) :
    commSub (⊤ : Subgroup W) (Subgroup.closure S) ≤ N := by
  let K : Subgroup (MulAut W) :=
    { carrier := {x | ∀ w : W, x w * w⁻¹ ∈ N}
      one_mem' := fun w => by simp
      mul_mem' := fun {x y} hx hy w => by
        have e : (x * y) w * w⁻¹ = (x (y w) * (y w)⁻¹) * (y w * w⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [e]
        exact N.mul_mem (hx _) (hy _)
      inv_mem' := fun {x} hx w => by
        have e : x⁻¹ w * w⁻¹ = (x (x⁻¹ w) * (x⁻¹ w)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]
          group
        rw [e]
        exact N.inv_mem (hx _) }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr fun s hs w => h s hs w
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, -, rfl⟩
  exact hle hx w

theorem commSub_sup_le (A B : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (A ⊔ B) ≤ commSub ⊤ A ⊔ commSub ⊤ B := by
  rw [Subgroup.sup_eq_closure]
  refine commSub_top_le_of_closure fun s hs w => ?_
  rcases hs with hs | hs
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨s, hs, w, Subgroup.mem_top w, rfl⟩)
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨s, hs, w, Subgroup.mem_top w, rfl⟩)

theorem commSub_sup_eq (A B : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (A ⊔ B) = commSub ⊤ A ⊔ commSub ⊤ B :=
  le_antisymm (commSub_sup_le A B)
    (sup_le (commSub_mono le_rfl le_sup_left) (commSub_mono le_rfl le_sup_right))

theorem mem_fixV_zpowers {t : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers t) ↔ t w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem commSub_stable {X : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ X) {u : W}
    (hu : u ∈ commSub (⊤ : Subgroup W) X) : x u ∈ commSub (⊤ : Subgroup W) X := by
  have hmap := IsTransvectionBlocks.map_commSub_conjAut X x
  have hX : B1.conjAut x X = X := by
    rw [conjAut_eq_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
  rw [hX] at hmap
  rw [← hmap]
  exact ⟨u, hu, rfl⟩

variable [Finite W]

theorem fixV_inf_commSub_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) : fixV Y ⊓ commSub ⊤ Y = ⊥ := by
  have h := (B1.coprime_decomp hW hY (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)).2
  rwa [top_inf_eq] at h

theorem fixV_sup_commSub_eq_top (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) : fixV Y ⊔ commSub ⊤ Y = ⊤ := by
  have h := (B1.coprime_decomp hW hY (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)).1
  rwa [top_inf_eq] at h

theorem commSub_commSub_eq (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) : commSub (commSub ⊤ Y) Y = commSub ⊤ Y := by
  have h := (B1.coprime_decomp hW hY (M := commSub ⊤ Y)
    (fun y hy m hm => commSub_stable hy hm)).1
  have hbot : commSub (⊤ : Subgroup W) Y ⊓ fixV Y = ⊥ := by
    rw [inf_comm]
    exact fixV_inf_commSub_eq_bot hW hY
  rwa [hbot, bot_sup_eq] at h

theorem eq_one_of_fix_fixV_commSub (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) {x : MulAut W} (h1 : ∀ w ∈ fixV Y, x w = w)
    (h2 : ∀ w ∈ commSub (⊤ : Subgroup W) Y, x w = w) : x = 1 :=
  E2.eq_one_of_fix_sup (fixV_sup_commSub_eq_top hW hY) h1 h2

section Blocks

variable {J : Subgroup (MulAut W)} {𝓗 : Finset (Subgroup (MulAut W))} {L : Subgroup (MulAut W)}

theorem eq_one_of_orderOf_eq_three (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (hL : L ∈ 𝓗) {f : MulAut W} (hf : f ∈ L) (hf3 : orderOf f = 3) {w : W}
    (hw : w ∈ commSub ⊤ L) (hfw : f w = w) : w = 1 := by
  by_contra hw1
  have hsq : ∀ x : W, x * x = 1 := fun x => by rw [← pow_two]; exact hW x
  have hfix := E2.fix_of_orderOf_eq_three (hb.card_comm L hL) hsq hf3
    (fun u hu => hb.stab L hL f hf u hu) hw hw1 hfw
  have hfC : f ∈ L ⊓ centSub (commSub ⊤ L) := ⟨hf, mem_centSub.mpr hfix⟩
  rw [hb.inf_centSub hL, Subgroup.mem_bot] at hfC
  rw [hfC, orderOf_one] at hf3
  norm_num at hf3

theorem commSub_zpowers_eq (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (hL : L ∈ 𝓗) {f : MulAut W} (hfL : f ∈ L) (hf3 : orderOf f = 3) :
    commSub (⊤ : Subgroup W) (Subgroup.zpowers f) = commSub ⊤ L := by
  refine le_antisymm (commSub_mono le_rfl (Subgroup.zpowers_le.2 hfL)) ?_
  have hodd : Odd (Nat.card (Subgroup.zpowers f)) := by
    rw [Nat.card_zpowers, hf3]
    decide
  have hinv : ∀ y ∈ Subgroup.zpowers f, ∀ m ∈ commSub (⊤ : Subgroup W) L,
      y m ∈ commSub (⊤ : Subgroup W) L := fun y hy m hm =>
    hb.stab L hL y (Subgroup.zpowers_le.2 hfL hy) m hm
  obtain ⟨hd1, -⟩ := B1.coprime_decomp hW hodd hinv
  have hfix : commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers f) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hwf⟩
    exact eq_one_of_orderOf_eq_three hW hb hL hfL hf3 hw (hwf f (Subgroup.mem_zpowers f))
  rw [hfix, bot_sup_eq] at hd1
  rw [← hd1]
  exact commSub_mono le_top le_rfl

theorem exists_fix (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗) (hL : L ∈ 𝓗)
    {t : MulAut W} (ht : t ∈ L) (ht2 : orderOf t = 2) :
    ∃ c ∈ commSub ⊤ L, c ≠ 1 ∧ t c = c := by
  have hsq : ∀ x : W, x * x = 1 := fun x => by rw [← pow_two]; exact hW x
  have hU4 := hb.card_comm L hL
  obtain ⟨u, hu1⟩ : ∃ u : commSub (⊤ : Subgroup W) L, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (commSub (⊤ : Subgroup W) L) := ⟨fun a b => by rw [hcon a, hcon b]⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  have hu1' : (u : W) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have htt : ∀ x : W, t (t x) = x := fun x => by
    rw [← MulAut.mul_apply, ← pow_two, ← ht2, pow_orderOf_eq_one, MulAut.one_apply]
  by_cases htu : t u = u
  · exact ⟨u, u.2, hu1', htu⟩
  · refine ⟨u * t u, Subgroup.mul_mem _ u.2 (hb.stab L hL t ht u u.2), ?_, ?_⟩
    · intro h
      apply htu
      have := congrArg ((u : W) * ·) h
      simp only [← mul_assoc, hsq, one_mul, mul_one] at this
      exact this
    · rw [map_mul, htt, mul_comm]

omit [Finite W] in
theorem exists_ne_of_ne_one (hb : IsTransvectionBlocks J 𝓗) (hL : L ∈ 𝓗) {x : MulAut W}
    (hx : x ∈ L) (hx1 : x ≠ 1) : ∃ u ∈ commSub (⊤ : Subgroup W) L, x u ≠ u := by
  by_contra hcon
  push Not at hcon
  have hxC : x ∈ L ⊓ centSub (commSub ⊤ L) := ⟨hx, mem_centSub.mpr hcon⟩
  rw [hb.inf_centSub hL, Subgroup.mem_bot] at hxC
  exact hx1 hxC

theorem card_fixV_zpowers_inf (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (hL : L ∈ 𝓗) {t : MulAut W} (htL : t ∈ L) (ht2 : orderOf t = 2) :
    Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ commSub ⊤ L) = 2 := by
  set U := commSub (⊤ : Subgroup W) L with hU
  set F := fixV (Subgroup.zpowers t) ⊓ U with hF
  have hU4 : Nat.card U = 4 := hb.card_comm L hL
  have hFU : F ≤ U := inf_le_right
  have hdvd : Nat.card F ∣ 4 := hU4 ▸ Subgroup.card_dvd_of_le hFU
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  obtain ⟨u, huU, hu⟩ := exists_ne_of_ne_one hb hL htL ht1
  have hne4 : Nat.card F ≠ 4 := by
    intro h4
    have hFeq : F = U := Subgroup.eq_of_le_of_card_ge hFU (by rw [h4, hU4])
    have huF : u ∈ F := hFeq ▸ huU
    exact hu (mem_fixV_zpowers.mp huF.1)
  obtain ⟨c, hcU, hc1, htc⟩ := exists_fix hW hb hL htL ht2
  have hcF : c ∈ F := ⟨mem_fixV_zpowers.mpr htc, hcU⟩
  have hne1 : Nat.card F ≠ 1 := by
    intro h1
    have := (Subgroup.card_eq_one.mp h1)
    rw [this] at hcF
    exact hc1 hcF
  have hle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card F := Nat.card_pos
  interval_cases h : Nat.card F <;> simp_all

theorem fix_of_commute (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗) (hL : L ∈ 𝓗)
    {f : MulAut W} (hfL : f ∈ L) (hf3 : orderOf f = 3) {d : MulAut W}
    (hd : ∃ k : ℕ, d ^ 2 ^ k = 1) (hdf : d * f = f * d) :
    ∀ u ∈ commSub (⊤ : Subgroup W) L, d u = u := by
  have hsq : ∀ x : W, x * x = 1 := fun x => by rw [← pow_two]; exact hW x
  set U := commSub (⊤ : Subgroup W) L with hU
  have hU4 : Nat.card U = 4 := hb.card_comm L hL
  have hUf := commSub_zpowers_eq hW hb hL hfL hf3
  have hfU : ∀ u ∈ U, f u ∈ U := fun u hu => hb.stab L hL f hfL u hu
  have hdU : ∀ u ∈ U, d u ∈ U := by
    intro u hu
    have hmap := IsTransvectionBlocks.map_commSub_conjAut (Subgroup.zpowers f) d
    have hconj : B1.conjAut d (Subgroup.zpowers f) = Subgroup.zpowers f := by
      rw [conjAut_eq_map, MonoidHom.map_zpowers]
      congr 1
      show d * f * d⁻¹ = f
      rw [hdf, mul_inv_cancel_right]
    rw [hconj, hUf] at hmap
    change d u ∈ commSub ⊤ L
    rw [← hmap]
    exact ⟨u, hu, rfl⟩
  have hf3' : f ^ 3 = 1 := by rw [← hf3]; exact pow_orderOf_eq_one f
  have hfff : ∀ x : W, f (f (f x)) = x := fun x => by
    have : (f ^ 3) x = x := by rw [hf3', MulAut.one_apply]
    simpa [pow_succ, MulAut.mul_apply] using this
  have hfpf : ∀ u ∈ U, f u = u → u = 1 := fun u hu h =>
    eq_one_of_orderOf_eq_three hW hb hL hfL hf3 hu h
  obtain ⟨a, haU, ha1⟩ : ∃ a ∈ U, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr hcon
    rw [this, Subgroup.card_bot] at hU4
    norm_num at hU4
  have hfa : f a ≠ a := fun h => ha1 (hfpf a haU h)
  have hfaU : f a ∈ U := hfU a haU
  have hfa1 : f a ≠ 1 := fun h => ha1 (f.injective (by rw [h, map_one]))
  have hffa : f (f a) = a * f a := by
    have hxU : a * f a * f (f a) ∈ U := U.mul_mem (U.mul_mem haU hfaU) (hfU _ hfaU)
    have hx : f (a * f a * f (f a)) = a * f a * f (f a) := by
      rw [map_mul, map_mul, hfff]
      rw [mul_comm (f a * f (f a)) a, mul_assoc]
    have h1 := hfpf _ hxU hx
    have h2 : f (f a) = (a * f a)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    have h3 : (a * f a) * (a * f a) = 1 := hsq _
    exact inv_eq_of_mul_eq_one_right h3
  have hfour : ∀ x ∈ U, x = 1 ∨ x = a ∨ x = f a ∨ x = a * f a := fun x hx =>
    E2.mem_four hU4 hsq haU hfaU hx ha1 hfa1 hfa
  have hcomm : ∀ n : ℕ, ∀ x : W, (d ^ n) (f x) = f ((d ^ n) x) := by
    intro n x
    have hc : Commute (d ^ n) f := (Commute.pow_left (show Commute d f from hdf) n)
    rw [← MulAut.mul_apply, hc.eq, MulAut.mul_apply]
  have hda : d a = a := by
    by_contra hda
    have hdaU : d a ∈ U := hdU a haU
    have hda1 : d a ≠ 1 := fun h => ha1 (d.injective (by rw [h, map_one]))
    have hcases : d a = f a ∨ d a = f (f a) := by
      rcases hfour _ hdaU with h | h | h | h
      · exact absurd h hda1
      · exact absurd h hda
      · exact Or.inl h
      · exact Or.inr (h.trans hffa.symm)
    have hpow : ∀ n : ℕ, (d ^ 2 ^ n) a = f a ∨ (d ^ 2 ^ n) a = f (f a) := by
      intro n
      induction n with
      | zero => simpa using hcases
      | succ n ih =>
        have e : (d ^ 2 ^ (n + 1)) a = (d ^ 2 ^ n) ((d ^ 2 ^ n) a) := by
          rw [pow_succ, pow_mul, pow_two, MulAut.mul_apply]
        rw [e]
        rcases ih with h | h
        · right
          rw [h, hcomm, h]
        · left
          rw [h, hcomm, hcomm, h, hfff]
    obtain ⟨k, hk⟩ := hd
    rcases hpow k with h | h
    · rw [hk, MulAut.one_apply] at h
      exact hfa h.symm
    · rw [hk, MulAut.one_apply] at h
      apply hfa
      calc f a = f (f (f a)) := by rw [← h]
        _ = a := hfff a
  intro u hu
  rcases hfour u hu with rfl | rfl | rfl | rfl
  · exact map_one d
  · exact hda
  · have := hcomm 1 a
    rw [pow_one] at this
    rw [this, hda]
  · have := hcomm 1 a
    rw [pow_one] at this
    rw [map_mul, this, hda]

end Blocks

end Module

section Transfer

variable {G : Type*} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem valHom_injective : Function.Injective (E2.valHom hV) := IntMod.val_injective

theorem card_map_valHom (X : Subgroup (IntMod V hV)) :
    Nat.card (X.map (E2.valHom hV)) = Nat.card X :=
  Subgroup.card_map_of_injective (valHom_injective hV)

theorem map_valHom_inf (X Y : Subgroup (IntMod V hV)) :
    (X ⊓ Y).map (E2.valHom hV) = X.map (E2.valHom hV) ⊓ Y.map (E2.valHom hV) :=
  Subgroup.map_inf X Y _ (valHom_injective hV)

theorem commutator_map_valHom {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (X : Subgroup (IntMod V hV)) :
    ⁅X.map (E2.valHom hV), A⁆ = (commSub X (autI hV A)).map (E2.valHom hV) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro _ ⟨w, hw, rfl⟩ a ha
    set c : IntMod V hV := convI hV ⟨a, hA ha⟩ w * w⁻¹ with hc
    have hcmem : c ∈ commSub X (autI hV A) :=
      Subgroup.subset_closure ⟨_, convI_mem_autI hV ha (hA ha), w, hw, rfl⟩
    refine ⟨c⁻¹, (commSub X (autI hV A)).inv_mem hcmem, ?_⟩
    show (c⁻¹).val = ⁅w.val, a⁆
    rw [hc, IntMod.val_inv, IntMod.val_mul, IntMod.val_inv, convI_apply_val,
      commutatorElement_def]
    group
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, w, hw, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    show (convI hV g w * w⁻¹).val ∈ ⁅X.map (E2.valHom hV), A⁆
    rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, Subgroup.commutator_comm,
      ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hg ⟨w, hw, rfl⟩

theorem commutator_eq_map_commSub {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, A⁆ = (commSub ⊤ (autI hV A)).map (E2.valHom hV) := by
  rw [← commutator_map_valHom hV hA ⊤, E2.map_valHom_top]

end Transfer

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
