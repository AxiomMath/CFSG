module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuHecke
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuBruhat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix CFSG.Quasithin.SmithCurtis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G6 V)

theorem exists_fixU_ne [Finite V] [Nontrivial V] : ∃ x ∈ fixU ρ, x ≠ 0 := by
  obtain ⟨x, hx, hfix⟩ := exists_fixed_ne ρ isPGroup_Ugrp
  exact ⟨x, fun u hu => hfix u hu, hx⟩

abbrev augL : Submodule (ZMod 2) V := augSub ρ Lgrp

@[expose] def augQ (s : Fin 3) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {z | ∃ q : G6, IsQm s (gM q) ∧ ∃ x : V, z = ρ q x - x}

theorem sub_mem_augL {q : G6} (hq : q ∈ Lgrp) (x : V) : ρ q x - x ∈ augL ρ :=
  sub_mem_augSub ρ hq x

theorem act_mem_augL {q : G6} (hq : q ∈ Lgrp) {z : V} (hz : z ∈ augL ρ) : ρ q z ∈ augL ρ :=
  act_mem_augSub_self ρ hq hz

theorem augL_ne_top [Finite V] [Nontrivial V] : augL ρ ≠ ⊤ :=
  augSub_ne_top ρ isPGroup_Lgrp

theorem augQ_le (s : Fin 3) : augQ ρ s ≤ augL ρ := by
  rw [augQ, Submodule.span_le]
  rintro _ ⟨q, hq, x, rfl⟩
  exact sub_mem_augL ρ hq.1 x

theorem augQ_map {s : Fin 3} {g : G6}
    (hg : ∀ q : G6, IsQm s (gM q) → IsQm s (gM (g * q * g⁻¹))) {z : V} (hz : z ∈ augQ ρ s) :
    ρ g z ∈ augQ ρ s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, w, rfl⟩ := hz
    have e : ρ g (ρ q w - w) = ρ (g * q * g⁻¹) (ρ g w) - ρ g w := by
      rw [map_sub, act_mul, act_mul, inv_mul_cancel_right]
    rw [e]
    exact Submodule.subset_span ⟨_, hg q hq, _, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem Qm_conj_xE {s : Fin 3} (q : G6) (hq : IsQm s (gM q)) :
    IsQm s (gM (xE s * q * (xE s)⁻¹)) := by
  rw [xE_inv]
  exact Qm_conj_x hq

theorem Qm_conj_yE {s : Fin 3} (q : G6) (hq : IsQm s (gM q)) :
    IsQm s (gM (yE s * q * (yE s)⁻¹)) := by
  rw [yE_inv]
  exact Qm_conj_y hq

theorem gen_mem_augQ {s : Fin 3} {q : G6} (hq : IsQm s (gM q)) (x : V) :
    ρ q x - x ∈ augQ ρ s :=
  Submodule.subset_span ⟨q, hq, x, rfl⟩

theorem y_sub_mem_augQ (s : Fin 3) {z : V} (hz : z ∈ augL ρ) : ρ (yE s) z - z ∈ augQ ρ s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, w, rfl⟩ := hz
    rcases decomp_lo (s := s) (show IsLoU (gM q) from hq) with h | h
    · have e : ρ (yE s) (ρ q w - w) - (ρ q w - w) =
          (ρ (yE s * q * (yE s)⁻¹) (ρ (yE s) w) - ρ (yE s) w) - (ρ q w - w) := by
        rw [map_sub, act_mul, act_mul, inv_mul_cancel_right]
      rw [e]
      exact sub_mem (gen_mem_augQ ρ (Qm_conj_yE q h) _) (gen_mem_augQ ρ h _)
    · set q₀ := yE s * q
      have hq0 : q = yE s * q₀ := by rw [← mul_assoc, yE_mul_self, one_mul]
      have e : ρ (yE s) (ρ q w - w) - (ρ q w - w) =
          (ρ q₀ w - w) - (ρ (yE s * q₀ * (yE s)⁻¹) (ρ (yE s) w) - ρ (yE s) w) +
            ((w - ρ (yE s) w) + (w - ρ (yE s) w)) := by
        rw [act_mul, inv_mul_cancel_right, map_sub, act_mul, hq0, ← mul_assoc, yE_mul_self,
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

theorem sE_mem_augL (s : Fin 3) {z : V} (hz : z ∈ augL ρ) (hx : ρ (xE s) z = z) :
    ρ (sE s) z ∈ augL ρ := by
  have h1 := y_sub_mem_augQ ρ s hz
  have h2 := augQ_map ρ (g := xE s) (fun q hq => Qm_conj_xE q hq) h1
  have e : ρ (sE s) z = z + ρ (xE s) (ρ (yE s) z - z) := by
    rw [map_sub, hx, sE_def, ← act_mul, ← act_mul, hx]
    abel
  rw [e]
  exact add_mem hz (augQ_le ρ s h2)

theorem xE_fix_tail {j : Fin 48} (hj : j ≠ 0) {v : V} (hv : v ∈ fixU ρ) :
    ρ (xE (headS j)) (ρ (wE (tailIdx j)) v) = ρ (wE (tailIdx j)) v := by
  rw [act_mul]
  have e : xE (headS j) * wE (tailIdx j) =
      wE (tailIdx j) * ((wE (tailIdx j))⁻¹ * xE (headS j) * wE (tailIdx j)) := by group
  rw [e, ← act_mul, hv _ (wE_tail_conj hj)]

theorem wE_act_mem_augL {k : V} (hk : k ∈ fixU ρ) (hka : k ∈ augL ρ) (j : Fin 48) :
    ρ (wE j) k ∈ augL ρ := by
  induction j using canW_induction with
  | h0 => rw [wE_zero, map_one, Module.End.one_apply]; exact hka
  | hstep j hj ih =>
    rw [wE_eq_cons hj, ← act_mul]
    exact sE_mem_augL ρ _ ih (xE_fix_tail ρ hj hk)

theorem cell_act {g q : G6} {j : Fin 48} {u : G6} (e : g = q * wE j * u) (x : V) :
    ρ g x = ρ q (ρ (wE j) (ρ u x)) := by
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]

theorem fixU_inf_augL {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V]
    {k : V} (hk : k ∈ fixU ρ) (hka : k ∈ augL ρ) : k = 0 := by
  by_contra hne
  have := hρ.1
  apply augL_ne_top ρ
  rw [eq_top_iff, ← orbitSpan_eq_top hρ hne, orbitSpan, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  show ρ g k ∈ augL ρ
  obtain ⟨q, hq, j, u, hu, e⟩ := bruhat_cover g
  rw [cell_act ρ e, hk u hu]
  exact act_mem_augL ρ hq (wE_act_mem_augL ρ hk hka j)

@[expose] def hW (l : List (Fin 3)) : V →ₗ[ZMod 2] V :=
  l.foldr (fun s f => (LinearMap.id + Th ρ s) ∘ₗ f) LinearMap.id

theorem hW_nil (x : V) : hW ρ [] x = x := rfl

theorem hW_cons (s : Fin 3) (l : List (Fin 3)) (x : V) :
    hW ρ (s :: l) x = hW ρ l x + Th ρ s (hW ρ l x) := rfl

theorem hW_mem_fixU (l : List (Fin 3)) {x : V} (hx : x ∈ fixU ρ) : hW ρ l x ∈ fixU ρ := by
  induction l with
  | nil => exact hx
  | cons s l ih =>
    rw [hW_cons]
    exact add_mem ih (Th_mem_fixU ρ s ih)

theorem sE_sub_mem_augL (s : Fin 3) {m : V} (hm : m ∈ fixU ρ) :
    ρ (sE s) m - (m + Th ρ s m) ∈ augL ρ := by
  have hxy : xE s * yE s = sE s * xE s := xE_mul_yE' s
  have e : ρ (xE s * yE s) m = ρ (sE s) m := by rw [hxy, ← act_mul, hm _ (xE_mem s)]
  have e2 : ρ (sE s) m - (m + Th ρ s m) = -(ρ (yE s) m - m) - (m + m) := by
    rw [Th_apply, e]
    abel
  rw [e2, add_self_zmod2, sub_zero]
  exact neg_mem (sub_mem_augL ρ (yE_mem s) m)

theorem coinv_formula {v : V} (hv : v ∈ fixU ρ) (j : Fin 48) :
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
      rw [wE_eq_cons hj, canW_cons j hj, hW_cons, map_sub, ← act_mul]
      abel
    rw [e]
    exact add_mem h1 h2

theorem fixU_le_span {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V]
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
