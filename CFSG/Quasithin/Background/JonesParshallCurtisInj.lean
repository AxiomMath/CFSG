module

public import CFSG.Quasithin.Background.JonesParshallCurtisBruhat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G5 V)

theorem two_dvd_card [Finite V] [Nontrivial V] : 2 ∣ Nat.card V := by
  have : Fintype V := Fintype.ofFinite V
  have hpos : 0 < Module.finrank (ZMod 2) V :=
    (Module.finrank_pos_iff_of_free (ZMod 2) V).mpr inferInstance
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  exact dvd_pow_self 2 hpos.ne'

theorem exists_fixed_ne {H : Subgroup G5} (hH : IsPGroup 2 ↥H) [Finite V] [Nontrivial V] :
    ∃ x : V, x ≠ 0 ∧ ∀ h ∈ H, ρ h x = x := by
  let _ : MulAction ↥H V :=
    { smul := fun h v => ρ h v
      one_smul := fun v => by
        change ρ ((1 : ↥H) : G5) v = v
        rw [Subgroup.coe_one, map_one]
        rfl
      mul_smul := fun a b v => by
        change ρ ((a * b : ↥H) : G5) v = ρ a (ρ b v)
        rw [Subgroup.coe_mul, map_mul]
        rfl }
  have h0 : (0 : V) ∈ MulAction.fixedPoints ↥H V := fun h => map_zero (ρ h)
  obtain ⟨b, hb, hne⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point V two_dvd_card h0
  exact ⟨b, hne.symm, fun h hh => hb ⟨h, hh⟩⟩

theorem exists_fixU_ne [Finite V] [Nontrivial V] : ∃ x ∈ fixU ρ, x ≠ 0 := by
  obtain ⟨x, hx, hfix⟩ := exists_fixed_ne ρ isPGroup_Ugrp
  exact ⟨x, fun u hu => hfix u hu, hx⟩

@[expose] def augL : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {z | ∃ q ∈ Lgrp, ∃ x : V, z = ρ q x - x}

@[expose] def augQ (s : Fin 4) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2)
    {z | ∃ q : G5, IsQm s (q : Matrix (Fin 5) (Fin 5) (ZMod 2)) ∧ ∃ x : V, z = ρ q x - x}

theorem sub_mem_augL {q : G5} (hq : q ∈ Lgrp) (x : V) : ρ q x - x ∈ augL ρ :=
  Submodule.subset_span ⟨q, hq, x, rfl⟩

theorem act_mem_augL {q : G5} (hq : q ∈ Lgrp) {z : V} (hz : z ∈ augL ρ) : ρ q z ∈ augL ρ := by
  have e : ρ q z = (ρ q z - z) + z := by abel
  rw [e]
  exact add_mem (sub_mem_augL ρ hq z) hz

@[expose] def dualRep : Representation (ZMod 2) G5 (Module.Dual (ZMod 2) V) where
  toFun g :=
    { toFun := fun f => f ∘ₗ ρ g⁻¹
      map_add' := fun f₁ f₂ => LinearMap.add_comp _ _ _
      map_smul' := fun c f => LinearMap.smul_comp _ _ _ }
  map_one' := by
    ext f v
    change f (ρ 1⁻¹ v) = f v
    rw [inv_one, map_one]
    rfl
  map_mul' g h := by
    ext f v
    change f (ρ (g * h)⁻¹ v) = f (ρ h⁻¹ (ρ g⁻¹ v))
    rw [_root_.mul_inv_rev, map_mul]
    rfl

theorem dualRep_apply (g : G5) (f : Module.Dual (ZMod 2) V) (v : V) :
    dualRep ρ g f v = f (ρ g⁻¹ v) := rfl

theorem augL_ne_top [Finite V] [Nontrivial V] : augL ρ ≠ ⊤ := by
  intro htop
  have : Finite (Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2))
      DFunLike.coe_injective
  obtain ⟨f, hf, hfix⟩ := exists_fixed_ne (V := Module.Dual (ZMod 2) V) (dualRep ρ) isPGroup_Lgrp
  apply hf
  have key : ∀ z ∈ augL ρ, f z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, w, rfl⟩ := hz
      have h1 := congrArg (fun φ : Module.Dual (ZMod 2) V => φ w) (hfix q⁻¹ (Lgrp.inv_mem hq))
      have h2 : f (ρ q w) = f w := by
        have h3 : dualRep ρ q⁻¹ f w = f w := h1
        rwa [dualRep_apply, inv_inv] at h3
      rw [map_sub, h2, sub_self]
    | zero => exact map_zero f
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  ext v
  exact key v (htop ▸ Submodule.mem_top)

theorem augQ_le (s : Fin 4) : augQ ρ s ≤ augL ρ := by
  rw [augQ, Submodule.span_le]
  rintro _ ⟨q, hq, x, rfl⟩
  exact sub_mem_augL ρ hq.1 x

theorem augQ_map {s : Fin 4} {g : G5}
    (hg : ∀ q : G5, IsQm s (q : Matrix (Fin 5) (Fin 5) (ZMod 2)) →
      IsQm s ((g * q * g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)))
    {z : V} (hz : z ∈ augQ ρ s) : ρ g z ∈ augQ ρ s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, w, rfl⟩ := hz
    have e : ρ g (ρ q w - w) = ρ (g * q * g⁻¹) (ρ g w) - ρ g w := by
      rw [map_sub, act_act, act_act, inv_mul_cancel_right]
    rw [e]
    exact Submodule.subset_span ⟨_, hg q hq, _, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem Qm_conj_xE
    {s : Fin 4} (q : G5) (hq : IsQm s (q : Matrix (Fin 5) (Fin 5) (ZMod 2))) :
    IsQm s ((xE s * q * (xE s)⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  rw [xE_inv]
  exact Qm_conj_x hq

theorem Qm_conj_yE
    {s : Fin 4} (q : G5) (hq : IsQm s (q : Matrix (Fin 5) (Fin 5) (ZMod 2))) :
    IsQm s ((yE s * q * (yE s)⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  rw [yE_inv]
  exact Qm_conj_y hq

theorem gen_mem_augQ {s : Fin 4} {q : G5} (hq : IsQm s (q : Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (x : V) : ρ q x - x ∈ augQ ρ s :=
  Submodule.subset_span ⟨q, hq, x, rfl⟩

theorem y_sub_mem_augQ
    (s : Fin 4) {z : V} (hz : z ∈ augL ρ) : ρ (yE s) z - z ∈ augQ ρ s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, w, rfl⟩ := hz
    rcases decomp_lo (s := s) (show IsLoU (q : Matrix (Fin 5) (Fin 5) (ZMod 2)) from hq) with
      h | h
    · have e : ρ (yE s) (ρ q w - w) - (ρ q w - w) =
          (ρ (yE s * q * (yE s)⁻¹) (ρ (yE s) w) - ρ (yE s) w) - (ρ q w - w) := by
        rw [map_sub, act_act, act_act, inv_mul_cancel_right]
      rw [e]
      exact sub_mem (gen_mem_augQ ρ (Qm_conj_yE q h) _) (gen_mem_augQ ρ h _)
    · set q₀ := yE s * q
      have hq0 : q = yE s * q₀ := by rw [← mul_assoc, yE_mul_self, one_mul]
      have e : ρ (yE s) (ρ q w - w) - (ρ q w - w) =
          (ρ q₀ w - w) - (ρ (yE s * q₀ * (yE s)⁻¹) (ρ (yE s) w) - ρ (yE s) w) +
            ((w - ρ (yE s) w) + (w - ρ (yE s) w)) := by
        rw [act_act, inv_mul_cancel_right, map_sub, act_act, hq0, ← mul_assoc, yE_mul_self,
          one_mul]
        abel
      rw [e, add_self_zmod2, add_zero]
      exact sub_mem (gen_mem_augQ ρ h _) (gen_mem_augQ ρ (Qm_conj_yE q₀ h) _)
  | zero => simp
  | add a b _ _ ha hb =>
    have e : ρ (yE s) (a + b) - (a + b) = (ρ (yE s) a - a) + (ρ (yE s) b - b) := by
      rw [map_add]; abel
    rw [e]
    exact add_mem ha hb
  | smul c a _ ha =>
    have e : ρ (yE s) (c • a) - c • a = c • (ρ (yE s) a - a) := by
      rw [map_smul, smul_sub]
    rw [e]
    exact Submodule.smul_mem _ c ha

theorem sE_mem_augL
    (s : Fin 4) {z : V} (hz : z ∈ augL ρ) (hx : ρ (xE s) z = z) :
    ρ (sE s) z ∈ augL ρ := by
  have h1 := y_sub_mem_augQ ρ s hz
  have h2 := augQ_map ρ (g := xE s) (Qm_conj_xE) h1
  have e : ρ (sE s) z = z + ρ (xE s) (ρ (yE s) z - z) := by
    rw [map_sub, hx, sE_def, ← act_act, ← act_act, hx]
    abel
  rw [e]
  exact add_mem hz (augQ_le ρ s h2)

@[expose] def IsSimpleRep : Prop :=
  Nontrivial V ∧ ∀ W : Submodule (ZMod 2) V, (∀ g : G5, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def orbitSpan (x : V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range fun g => ρ g x)

theorem orbitSpan_stable (x : V) (g : G5) (w : V) (hw : w ∈ orbitSpan ρ x) :
    ρ g w ∈ orbitSpan ρ x := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, rfl⟩ := hw
    rw [act_act]
    exact Submodule.subset_span ⟨g * h, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem mem_orbitSpan_self (x : V) : x ∈ orbitSpan ρ x :=
  Submodule.subset_span ⟨1, by
    show ρ 1 x = x
    rw [map_one]
    rfl⟩

theorem orbitSpan_eq_top {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) {x : V}
    (hx : x ≠ 0) : orbitSpan ρ x = ⊤ := by
  rcases hρ.2 _ (orbitSpan_stable ρ x) with h | h
  · exfalso
    apply hx
    have h' := mem_orbitSpan_self ρ x
    rw [h] at h'
    exact (Submodule.mem_bot _).mp h'
  · exact h

theorem canW_length_zero : ∀ j : Fin 120, (canW j).length = 0 → j = 0 := by decide +kernel

theorem canW_induction {P : Fin 120 → Prop} (h0 : P 0)
    (hstep : ∀ j : Fin 120, j ≠ 0 → P (tailIdx j) → P j) (j : Fin 120) : P j := by
  suffices ∀ n, ∀ j : Fin 120, (canW j).length = n → P j from this _ j rfl
  intro n
  induction n with
  | zero =>
    intro j hj
    rw [canW_length_zero j hj]
    exact h0
  | succ n ih =>
    intro j hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [canW_zero] at hj
      exact absurd hj (by simp)
    refine hstep j hj0 (ih _ ?_)
    have := length_tailIdx hj0
    omega

theorem xE_fix_tail
    {j : Fin 120} (hj : j ≠ 0) {v : V} (hv : v ∈ fixU ρ) :
    ρ (xE (headS j)) (ρ (wE (tailIdx j)) v) = ρ (wE (tailIdx j)) v := by
  rw [act_act]
  have e : xE (headS j) * wE (tailIdx j) =
      wE (tailIdx j) * ((wE (tailIdx j))⁻¹ * xE (headS j) * wE (tailIdx j)) := by group
  rw [e, ← act_act, hv _ (wE_tail_conj hj)]

theorem wE_act_mem_augL
    {k : V} (hk : k ∈ fixU ρ) (hka : k ∈ augL ρ) (j : Fin 120) :
    ρ (wE j) k ∈ augL ρ := by
  induction j using canW_induction with
  | h0 => rw [wE_zero, map_one, Module.End.one_apply]; exact hka
  | hstep j hj ih =>
    rw [wE_eq_cons hj, ← act_act]
    exact sE_mem_augL ρ _ ih (xE_fix_tail ρ hj hk)

theorem cell_act {g : G5} {q : G5} {j : Fin 120} {u : G5} (e : g = q * wE j * u) (x : V) :
    ρ g x = ρ q (ρ (wE j) (ρ u x)) := by
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]

theorem fixU_inf_augL
    {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) [Finite V]
    {k : V} (hk : k ∈ fixU ρ) (hka : k ∈ augL ρ) : k = 0 := by
  by_contra hne
  have := hρ.1
  apply augL_ne_top ρ
  rw [eq_top_iff, ← orbitSpan_eq_top hρ hne, orbitSpan, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  show ρ g k ∈ augL ρ
  obtain ⟨q, hq, j, u, hu, e⟩ := bruhat_cover g
  rw [cell_act ρ e, hk _ hu]
  exact act_mem_augL ρ hq (wE_act_mem_augL ρ hk hka j)

@[expose] def hW (l : List (Fin 4)) : V →ₗ[ZMod 2] V :=
  l.foldr (fun s f => (LinearMap.id + Th ρ s) ∘ₗ f) LinearMap.id

theorem hW_nil (x : V) : hW ρ [] x = x := rfl

theorem hW_cons (s : Fin 4) (l : List (Fin 4)) (x : V) :
    hW ρ (s :: l) x = hW ρ l x + Th ρ s (hW ρ l x) := rfl

theorem hW_mem_fixU
    (l : List (Fin 4)) {x : V} (hx : x ∈ fixU ρ) : hW ρ l x ∈ fixU ρ := by
  induction l with
  | nil => exact hx
  | cons s l ih =>
    rw [hW_cons]
    exact add_mem ih (Th_mem_fixU ρ s ih)

theorem sE_sub_mem_augL
    (s : Fin 4) {m : V} (hm : m ∈ fixU ρ) :
    ρ (sE s) m - (m + Th ρ s m) ∈ augL ρ := by
  have hxy : xE s * yE s = sE s * xE s := (order_three_checks s).2.2
  have e : ρ (xE s * yE s) m = ρ (sE s) m := by rw [hxy, ← act_act, hm _ (xE_mem s)]
  have e2 : ρ (sE s) m - (m + Th ρ s m) = -(ρ (yE s) m - m) - (m + m) := by
    rw [Th_apply, e]
    abel
  rw [e2, add_self_zmod2, sub_zero]
  exact neg_mem (sub_mem_augL ρ (yE_mem s) m)

theorem coinv_formula
    {v : V} (hv : v ∈ fixU ρ) (j : Fin 120) :
    ρ (wE j) v - hW ρ (canW j) v ∈ augL ρ := by
  induction j using canW_induction with
  | h0 =>
    rw [wE_zero, map_one, Module.End.one_apply, canW_zero, hW_nil, sub_self]
    exact zero_mem _
  | hstep j hj ih =>
    set n := ρ (wE (tailIdx j)) v
    set m := hW ρ (canW (tailIdx j)) v
    have hm : m ∈ fixU ρ := hW_mem_fixU ρ _ hv
    have hd : ρ (xE (headS j)) (n - m) = n - m := by
      rw [map_sub, xE_fix_tail ρ hj hv, hm _ (xE_mem _)]
    have h1 := sE_mem_augL ρ (headS j) ih hd
    have h2 := sE_sub_mem_augL ρ (headS j) hm
    have e : ρ (wE j) v - hW ρ (canW j) v =
        ρ (sE (headS j)) (n - m) + (ρ (sE (headS j)) m - (m + Th ρ (headS j) m)) := by
      rw [wE_eq_cons hj, canW_cons j hj, hW_cons, map_sub, ← act_act]
      abel
    rw [e]
    exact add_mem h1 h2

theorem fixU_le_span
    {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) [Finite V]
    {v : V} (hv : v ∈ fixU ρ) (hv0 : v ≠ 0) {x : V} (hx : x ∈ fixU ρ) :
    x ∈ Submodule.span (ZMod 2) (Set.range fun j => hW ρ (canW j) v) := by
  set S := Submodule.span (ZMod 2) (Set.range fun j => hW ρ (canW j) v)
  have hSU : S ≤ fixU ρ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hW_mem_fixU ρ _ hv
  have key : ∀ y ∈ orbitSpan ρ v, ∃ y' ∈ S, y - y' ∈ augL ρ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      obtain ⟨q, hq, j, u, hu, e⟩ := bruhat_cover g
      refine ⟨hW ρ (canW j) v, Submodule.subset_span ⟨j, rfl⟩, ?_⟩
      show ρ g v - _ ∈ _
      rw [cell_act ρ e, hv _ hu]
      have e2 : ρ q (ρ (wE j) v) - hW ρ (canW j) v =
          (ρ q (ρ (wE j) v) - ρ (wE j) v) + (ρ (wE j) v - hW ρ (canW j) v) := by abel
      rw [e2]
      exact add_mem (sub_mem_augL ρ hq _) (coinv_formula ρ hv j)
    | zero => exact ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      have e : a + b - (a' + b') = (a - a') + (b - b') := by abel
      rw [e]
      exact add_mem hda hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      rw [← smul_sub]
      exact Submodule.smul_mem _ c hda
  obtain ⟨y', hy', hd⟩ := key x (by rw [orbitSpan_eq_top hρ hv0]; exact Submodule.mem_top)
  have h0 := fixU_inf_augL hρ (sub_mem hx (hSU hy')) hd
  rw [sub_eq_zero] at h0
  rw [h0]
  exact hy'

end CFSG.Quasithin.JonesParshall.Curtis
