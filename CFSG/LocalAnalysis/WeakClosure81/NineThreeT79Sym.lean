module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Cfg
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem nine3_isSwap_of_isConj {α : Type*} [Fintype α] [DecidableEq α] {c d : Equiv.Perm α}
    (hc : c.IsSwap) (h : IsConj c d) : d.IsSwap := by
  rw [Equiv.Perm.isSwap_iff_cycleType] at hc ⊢
  rw [← Equiv.Perm.isConj_iff_cycleType_eq.1 h]
  exact hc

private theorem nine3_eq_of_support_eq_of_swap {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Equiv.Perm α}
    (hs : s.IsSwap) (ht : t.IsSwap) (h : s.support = t.support) : s = t := by
  obtain ⟨x, y, hxy, rfl⟩ := hs
  obtain ⟨z, w, hzw, rfl⟩ := ht
  rw [Equiv.Perm.support_swap hxy, Equiv.Perm.support_swap hzw] at h
  have hx : x ∈ ({z, w} : Finset α) := by rw [← h]; simp
  have hy : y ∈ ({z, w} : Finset α) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hxz | hxw <;> rcases hy with hyz | hyw
  · exact absurd (hxz.trans hyz.symm) hxy
  · rw [hxz, hyw]
  · rw [hxw, hyz]; exact Equiv.swap_comm w z
  · exact absurd (hxw.trans hyw.symm) hxy

private theorem nine3_swap_mul_swap_ne {α : Type*} [DecidableEq α] {a b d : α} (hab : a ≠ b)
    (had : a ≠ d) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap a d ≠ Equiv.swap a d * Equiv.swap a b := by
  intro h
  have h1 := congrArg (fun σ : Equiv.Perm α => σ a) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h1
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd),
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbd] at h1
  exact hbd h1.symm

private theorem nine3_disjoint_of_swap_commute {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hcd : c ≠ d) (hne : Equiv.swap a b ≠ Equiv.swap c d)
    (hc : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have key : ∀ {x y z : α}, x ≠ y → x ≠ z → Equiv.swap x y ≠ Equiv.swap x z →
      Equiv.swap x y * Equiv.swap x z ≠ Equiv.swap x z * Equiv.swap x y :=
    fun hxy hxz hne' => nine3_swap_mul_swap_ne hxy hxz fun h => hne' (by rw [h])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact key hab hcd hne hc
  · rintro rfl
    rw [Equiv.swap_comm c] at hne hc
    exact key hab (Ne.symm hcd) hne hc
  · rintro rfl
    rw [Equiv.swap_comm a] at hne hc
    exact key (Ne.symm hab) hcd hne hc
  · rintro rfl
    rw [Equiv.swap_comm a, Equiv.swap_comm c] at hne hc
    exact key (Ne.symm hab) (Ne.symm hcd) hne hc

private theorem nine3_disjoint_support_of_commute {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Equiv.Perm α}
    (hs : s.IsSwap) (ht : t.IsSwap) (hcomm : s * t = t * s) (hne : s ≠ t) :
    Disjoint s.support t.support := by
  obtain ⟨x, y, hxy, rfl⟩ := hs
  obtain ⟨z, w, hzw, rfl⟩ := ht
  obtain ⟨hxz, hxw, hyz, hyw⟩ := nine3_disjoint_of_swap_commute hxy hzw hne hcomm
  rw [Equiv.Perm.support_swap hxy, Equiv.Perm.support_swap hzw, Finset.disjoint_left]
  intro p hp hp'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hp'
  rcases hp with rfl | rfl
  · rcases hp' with h | h
    · exact hxz h
    · exact hxw h
  · rcases hp' with h | h
    · exact hyz h
    · exact hyw h

private theorem nine3_swap_comm_of_disjoint_supports {α : Type*} [DecidableEq α] {x y z w : α}
    (h1 : x ≠ z) (h2 : x ≠ w) (h3 : y ≠ z) (h4 : y ≠ w) :
    Equiv.swap x y * Equiv.swap z w = Equiv.swap z w * Equiv.swap x y := by
  ext t
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  grind

private theorem nine3_swap_mul_comm_of_not_mem_support {α : Type*} [Fintype α] [DecidableEq α]
    {s : Equiv.Perm α}
    {p u : α} (hs : s.IsSwap) (hp : p ∉ s.support) (hu : u ∉ s.support) :
    Equiv.swap p u * s = s * Equiv.swap p u := by
  obtain ⟨x, y, hxy, rfl⟩ := hs
  simp only [Equiv.Perm.support_swap hxy, Finset.mem_insert, Finset.mem_singleton, not_or] at hp hu
  exact nine3_swap_comm_of_disjoint_supports hp.1 hp.2 hu.1 hu.2

theorem nine3_prop710_sym {n : ℕ} {c a e a' v : Equiv.Perm (Fin n)} (hc : c.IsSwap)
    (h : Nine3Config c a e a' v) :
    ∃ d : Equiv.Perm (Fin n), IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  have ha : a.IsSwap := nine3_isSwap_of_isConj hc h.conj_a
  have he : e.IsSwap := nine3_isSwap_of_isConj hc h.conj_e
  have ha' : a'.IsSwap := nine3_isSwap_of_isConj hc h.conj_a'
  have hv : v.IsSwap := nine3_isSwap_of_isConj hc h.conj_v
  have hnc_ae : a * e ≠ e * a := h.not_comm_ae
  have hord_ea' : orderOf (e * a') = 3 := h.orderOf_ae.2
  have hne_ae : a ≠ e := fun hh => hnc_ae (by rw [hh])
  have hne_aa' : a ≠ a' := fun hh => h.ne_aa' (by rw [hh, h.sq_a'])
  have hnc_ea' : e * a' ≠ a' * e := by
    intro hcomm
    have h2 : (e * a') ^ 2 = 1 := by
      rw [pow_two]
      calc e * a' * (e * a') = e * (a' * e) * a' := by group
        _ = e * (e * a') * a' := by rw [← hcomm]
        _ = (e * e) * (a' * a') := by group
        _ = 1 := by rw [h.sq_e, h.sq_a', mul_one]
    have hdvd : orderOf (e * a') ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hord_ea'] at hdvd
    norm_num at hdvd
  have hne_ea' : e ≠ a' := by
    intro hh
    have h1 : orderOf (e * a') = 1 := by rw [hh, h.sq_a', orderOf_one]
    omega
  have hne_va : v ≠ a := by
    intro hh
    apply hnc_ae
    rw [← hh]
    exact h.comm_ve
  have hne_ve : v ≠ e := by
    intro hh
    apply hnc_ae
    rw [← hh]
    exact h.comm_va.symm
  have hne_va' : v ≠ a' := by
    intro hh
    apply hnc_ea'
    rw [← hh]
    exact h.comm_ve.symm
  have hdisj_aa' : Disjoint a.support a'.support :=
    nine3_disjoint_support_of_commute ha ha' h.comm_aa' hne_aa'
  have hdisj_va : Disjoint v.support a.support :=
    nine3_disjoint_support_of_commute hv ha h.comm_va hne_va
  have hdisj_ve : Disjoint v.support e.support :=
    nine3_disjoint_support_of_commute hv he h.comm_ve hne_ve
  have hdisj_va' : Disjoint v.support a'.support :=
    nine3_disjoint_support_of_commute hv ha' h.comm_va' hne_va'
  have hdiff : (a'.support \ e.support).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : a'.support ⊆ e.support := by
      intro p hp
      by_contra hpe
      exact Finset.notMem_empty p (hemp ▸ Finset.mem_sdiff.mpr ⟨hp, hpe⟩)
    have hcard : a'.support.card = e.support.card := by
      rw [Equiv.Perm.card_support_eq_two.mpr ha', Equiv.Perm.card_support_eq_two.mpr he]
    exact (Ne.symm hne_ea') (nine3_eq_of_support_eq_of_swap ha' he
      (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)))
  obtain ⟨p', hp'⟩ := hdiff
  rw [Finset.mem_sdiff] at hp'
  obtain ⟨hp'a', hp'e⟩ := hp'
  have hvu : v.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    exact h.ne_v (Equiv.Perm.support_eq_empty_iff.mp hemp)
  obtain ⟨u, hu⟩ := hvu
  have hp'_not_a : p' ∉ a.support := Finset.disjoint_left.mp hdisj_aa'.symm hp'a'
  have hp'_not_v : p' ∉ v.support := Finset.disjoint_left.mp hdisj_va'.symm hp'a'
  have hu_not_a : u ∉ a.support := Finset.disjoint_left.mp hdisj_va hu
  have hu_not_e : u ∉ e.support := Finset.disjoint_left.mp hdisj_ve hu
  have hp'u : p' ≠ u := fun hh => hp'_not_v (hh.symm ▸ hu)
  have hd_swap : (Equiv.swap p' u).IsSwap := ⟨p', u, hp'u, rfl⟩
  refine ⟨Equiv.swap p' u, ?_, ?_, ?_, ?_⟩
  · exact Equiv.Perm.isConj_iff_cycleType_eq.mpr (by
      rw [Equiv.Perm.isSwap_iff_cycleType.mp hc, Equiv.Perm.isSwap_iff_cycleType.mp hd_swap])
  · intro hdv
    have hmem : p' ∈ (Equiv.swap p' u).support := by
      rw [Equiv.Perm.mem_support, Equiv.swap_apply_left]
      exact fun h => hp'u h.symm
    rw [hdv] at hmem
    exact hp'_not_v hmem
  · exact nine3_swap_mul_comm_of_not_mem_support ha hp'_not_a hu_not_a
  · exact nine3_swap_mul_comm_of_not_mem_support he hp'e hu_not_e

end CFSG.LocalAnalysis.WeakClosure81
