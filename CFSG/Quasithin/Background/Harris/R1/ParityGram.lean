module

public import CFSG.Quasithin.Recognition.SzR1FamCenter

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

section Generic

variable {P : Type*} [Group P] {Ω : Type*} {z : P} {w : Ω → P}

theorem gramRel_exists_nodup [DecidableEq Ω] (h : GramRel z w) :
    ∀ (n : ℕ) (l : List Ω), l.length = n →
      ∃ (k : ℕ) (l' : List Ω), l'.Nodup ∧ gprod w l = z ^ k * gprod w l' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hn
    by_cases hnd : l.Nodup
    · exact ⟨0, l, hnd, by simp⟩
    · rw [List.nodup_iff_count_le_one] at hnd
      push Not at hnd
      obtain ⟨i, hi⟩ := hnd
      have hmem : i ∈ l := List.count_pos_iff.mp (by omega)
      have p1 : l.Perm (i :: l.erase i) := List.perm_cons_erase hmem
      have hcnt' : 0 < (l.erase i).count i := by
        rw [List.count_erase_self]
        omega
      have hmem' : i ∈ l.erase i := List.count_pos_iff.mp hcnt'
      have p2 : (l.erase i).Perm (i :: (l.erase i).erase i) := List.perm_cons_erase hmem'
      have p3 : l.Perm (i :: i :: (l.erase i).erase i) := p1.trans (List.Perm.cons i p2)
      obtain ⟨k, hk⟩ := h.gprod_perm p3
      rw [h.gprod_cons_cons] at hk
      have hlen : ((l.erase i).erase i).length < n := by
        rw [List.length_erase_of_mem hmem', List.length_erase_of_mem hmem]
        have : 0 < l.length := List.length_pos_of_mem hmem
        omega
      obtain ⟨k', l'', hl'', hk'⟩ := ih _ hlen ((l.erase i).erase i) rfl
      exact ⟨k + k', l'', hl'', by rw [hk, hk', pow_add, mul_assoc]⟩

end Generic


namespace FamCtxLemmas

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

include C

theorem sq_mem_Zs {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) {x : G} (hx : x ∈ vBeta K1 L2 S Zs) :
    x * x ∈ Zs := by
  have hcl := C.U_eq_closure (C.cm_mem i₀ j₀) (C.cm_ne_one hij)
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨j, rfl⟩
    · rw [C.Zs_sq (C.cm_mem i₀ j₀)]; exact Zs.one_mem
    · rw [C.Vf_sq (C.zf_mem j)]; exact Zs.one_mem
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxW : x ∈ vBeta K1 L2 S Zs := by rw [hcl]; exact hx
    have hyW : y ∈ vBeta K1 L2 S Zs := by rw [hcl]; exact hy
    have hc : y * x * y⁻¹ * x⁻¹ ∈ Zs := C.U_comm_mem hyW hxW
    have hxc : x * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * x := C.Zs_central hxW hc
    have e : x * y * (x * y) = (y * x * y⁻¹ * x⁻¹) * (x * x) * (y * y) := by
      calc x * y * (x * y) = x * ((y * x * y⁻¹ * x⁻¹) * x * y) * y := by group
        _ = (x * (y * x * y⁻¹ * x⁻¹)) * x * y * y := by simp only [mul_assoc]
        _ = ((y * x * y⁻¹ * x⁻¹) * x) * x * y * y := by rw [hxc]
        _ = _ := by simp only [mul_assoc]
    rw [e]
    exact Zs.mul_mem (Zs.mul_mem hc ihx) ihy
  | inv x hx ih =>
    have : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [this]
    exact Zs.inv_mem ih


variable [Fintype Ω] [DecidableEq Ω]

theorem gprod_univ_mem_Zs {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (hodd : Odd (Fintype.card Ω))
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀) :
    ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ∈ Zs := by
  have hG := C.gramRel hij
  have hclos : ∀ g : ↥(vBeta K1 L2 S Zs),
      g ∈ Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    intro g
    rw [C.closure_wU hij]
    exact Subgroup.mem_top g
  refine hcen _ (gprod C.wU l₀).2 fun u hu => ?_
  have := congrArg Subtype.val (hG.commute_gprod_univ_closure hodd l₀ hl₀ hall (hclos ⟨u, hu⟩))
  exact this.symm

theorem mem_Vf_pt_of_sq_eq_one (hΩ : Fintype.card Ω = 5)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {x : G} (hxW : x ∈ vBeta K1 L2 S Zs) (hxc : x * C.zf C.D.pt = C.zf C.D.pt * x)
    (hx2 : x * x = 1) : x ∈ C.D.Vf (conjClosure Zs L2) C.D.pt := by
  have hodd : Odd (Fintype.card Ω) := by rw [hΩ]; decide
  obtain ⟨i₀, j₀, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Ω)
  have hG := C.gramRel hij
  have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
  set pt := C.D.pt with hpt
  let l₀ : List Ω := Finset.univ.toList
  have hl₀ : l₀.Nodup := Finset.nodup_toList _
  have hall : ∀ i, i ∈ l₀ := fun i => by simp [l₀]
  have hy := gprod_univ_mem_Zs C hij hodd hcen l₀ hl₀ hall
  let x' : ↥(vBeta K1 L2 S Zs) := ⟨x, hxW⟩
  have hxcl : x' ∈ Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    rw [C.closure_wU hij]; exact Subgroup.mem_top _
  obtain ⟨a, l, hxl⟩ := hG.mem_closure_iff.mp hxcl
  obtain ⟨k, l', hnd, hl'⟩ := gramRel_exists_nodup hG _ l rfl
  have hx' : x' = C.zU i₀ j₀ ^ (a + k) * gprod C.wU l' := by
    rw [hxl, hl', pow_add, mul_assoc]
  have hxcP : C.wU pt * x' = x' * C.wU pt := Subtype.ext hxc.symm
  have hxxP : x' * x' = 1 := Subtype.ext hx2
  have hcnt : Even (l'.countP (fun i => decide (i ≠ pt))) := by
    have h1 := hG.mul_gprod pt l'
    have h2 : C.zU i₀ j₀ ^ (l'.countP (fun i => decide (i ≠ pt))) = 1 := by
      rw [hx'] at hxcP
      have e1 : C.wU pt * (C.zU i₀ j₀ ^ (a + k) * gprod C.wU l') =
          C.zU i₀ j₀ ^ (a + k) * (C.zU i₀ j₀ ^ (l'.countP (fun i => decide (i ≠ pt))) *
            (gprod C.wU l' * C.wU pt)) := by
        rw [← mul_assoc, hG.mul_zpow_comm (C.wU pt), mul_assoc, h1]
      have e2 : C.zU i₀ j₀ ^ (a + k) * gprod C.wU l' * C.wU pt =
          C.zU i₀ j₀ ^ (a + k) * (gprod C.wU l' * C.wU pt) := mul_assoc _ _ _
      rw [e1, e2] at hxcP
      exact mul_eq_right.mp (mul_left_cancel hxcP)
    exact (hG.z_pow_eq_one_iff hz _).mp h2
  have hsq : Even (Nat.choose l'.length 2) := by
    have h1 : gprod C.wU l' * gprod C.wU l' = 1 := by
      rw [hx'] at hxxP
      have e : C.zU i₀ j₀ ^ (a + k) * gprod C.wU l' * (C.zU i₀ j₀ ^ (a + k) * gprod C.wU l') =
          C.zU i₀ j₀ ^ ((a + k) + (a + k)) * (gprod C.wU l' * gprod C.wU l') := by
        calc _ = C.zU i₀ j₀ ^ (a + k) * (gprod C.wU l' * C.zU i₀ j₀ ^ (a + k)) *
              gprod C.wU l' := by simp only [mul_assoc]
          _ = C.zU i₀ j₀ ^ (a + k) * (C.zU i₀ j₀ ^ (a + k) * gprod C.wU l') *
              gprod C.wU l' := by rw [hG.mul_zpow_comm]
          _ = _ := by rw [pow_add _ (a + k) (a + k)]; simp only [mul_assoc]
      rw [e, hG.z_pow_add_self, one_mul] at hxxP
      exact hxxP
    have h2 := hG.gprod_sq hnd
    rw [h1] at h2
    exact (hG.z_pow_eq_one_iff hz _).mp h2.symm
  have hcc := countP_ne_add_count pt l'
  have hc1 : l'.count pt ≤ 1 := List.nodup_iff_count_le_one.mp hnd pt
  have hn5 : l'.length ≤ 5 := hΩ ▸ hnd.length_le_card
  let V' : Subgroup ↥(vBeta K1 L2 S Zs) := (C.D.Vf (conjClosure Zs L2) pt).subgroupOf (vBeta K1 L2 S Zs)
  have hzV : C.zU i₀ j₀ ∈ V' := C.Zs_le_Vf pt (C.cm_mem i₀ j₀)
  have hwV : C.wU pt ∈ V' := C.zf_mem pt
  have hyV : gprod C.wU l₀ ∈ V' := C.Zs_le_Vf pt hy
  show x' ∈ V'
  rw [hx']
  have hperm5 : ∀ m : List Ω, m.Nodup → m.length = 5 → ∃ k₂ : ℕ,
      gprod C.wU m = C.zU i₀ j₀ ^ k₂ * gprod C.wU l₀ := by
    intro m hm hlen
    have hT : m.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by
      rw [List.toFinset_card_of_nodup hm, hlen, hΩ])
    have hperm : m.Perm l₀ := List.perm_of_nodup_nodup_toFinset_eq hm hl₀ (by
      rw [hT]; ext i; simp [hall i])
    exact hG.gprod_perm hperm
  obtain ⟨n, hn⟩ : ∃ n, l'.length = n := ⟨_, rfl⟩
  rw [hn] at hsq hn5
  have hcc' := hcc
  rw [hn] at hcc'
  interval_cases n
  · rw [List.length_eq_zero_iff.mp hn]
    simpa using V'.pow_mem hzV (a + k)
  · obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hn
    by_cases hi : i = pt
    · subst hi
      simpa using V'.mul_mem (V'.pow_mem hzV (a + k)) hwV
    · exfalso
      have : [i].countP (fun i => decide (i ≠ pt)) = 1 := by simp [hi]
      rw [this] at hcnt
      exact absurd hcnt (by decide)
  · exact absurd hsq (by decide)
  · exact absurd hsq (by decide)
  · have hcount0 : l'.count pt = 0 := by
      obtain ⟨r, hr⟩ := hcnt
      omega
    have hnotin : pt ∉ l' := fun h => by
      have := List.count_pos_iff.mpr h
      omega
    obtain ⟨k₂, hk₂⟩ := hperm5 (pt :: l') (List.nodup_cons.2 ⟨hnotin, hnd⟩) (by simp [hn])
    rw [gprod_cons] at hk₂
    have e : gprod C.wU l' = C.wU pt * (C.zU i₀ j₀ ^ k₂ * gprod C.wU l₀) := by
      rw [← hk₂, ← mul_assoc, hG.w_sq, one_mul]
    rw [e]
    exact V'.mul_mem (V'.pow_mem hzV _) (V'.mul_mem hwV (V'.mul_mem (V'.pow_mem hzV _) hyV))
  · obtain ⟨k₂, hk₂⟩ := hperm5 l' hnd hn
    rw [hk₂]
    exact V'.mul_mem (V'.pow_mem hzV _) (V'.mul_mem (V'.pow_mem hzV _) hyV)

end FamCtxLemmas

end CFSG.Quasithin.Background.Harris.R1
