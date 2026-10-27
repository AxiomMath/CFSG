module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartOne.CTP.Alt

open Equiv Equiv.Perm

theorem swap_mul_swap_rot {V : Type*} [DecidableEq V] {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : swap x y * swap y z = swap y z * swap z x := by
  have := hxy.symm
  have := hyz.symm
  have := hxz.symm
  ext v
  by_cases h1 : v = x
  · subst h1
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h2 : v = y
  · subst h2
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h3 : v = z
  · subst h3
    simp [swap_apply_of_ne_of_ne, *]
  simp [swap_apply_of_ne_of_ne, *]

theorem swap_mul_swap_inv {V : Type*} [DecidableEq V] {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : (swap x y * swap y z)⁻¹ = swap x z * swap z y := by
  have := hxy.symm
  have := hyz.symm
  have := hxz.symm
  ext v
  by_cases h1 : v = x
  · subst h1
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h2 : v = y
  · subst h2
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h3 : v = z
  · subst h3
    simp [swap_apply_of_ne_of_ne, *]
  simp [swap_apply_of_ne_of_ne, *]

theorem swap_commutator {V : Type*} [DecidableEq V] {p q r s u : V}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s)
    (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    (swap p q * swap q r) * (swap r s * swap s u) * (swap p q * swap q r)⁻¹ *
      (swap r s * swap s u)⁻¹ = swap p s * swap s r := by
  have := hpq.symm
  have := hpr.symm
  have := hps.symm
  have := hpu.symm
  have := hqr.symm
  have := hqs.symm
  have := hqu.symm
  have := hrs.symm
  have := hru.symm
  have := hsu.symm
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, mul_inv_rev, swap_inv]
  by_cases h1 : x = p
  · subst h1
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h2 : x = q
  · subst h2
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h3 : x = r
  · subst h3
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h4 : x = s
  · subst h4
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h5 : x = u
  · subst h5
    simp [swap_apply_of_ne_of_ne, *]
  simp [swap_apply_of_ne_of_ne, *]

section

variable {V : Type*} [DecidableEq V]

def Contains3 (N : Subgroup (Perm V)) (x y z : V) : Prop :=
  swap x y * swap y z ∈ N

variable {N : Subgroup (Perm V)} {x y z p q r s u : V}

theorem Contains3.rot (h : Contains3 N x y z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Contains3 N y z x := by
  unfold Contains3 at *
  rwa [swap_mul_swap_rot hxy hyz hxz] at h

theorem Contains3.flip (h : Contains3 N x y z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Contains3 N x z y := by
  have := N.inv_mem h
  unfold Contains3
  rwa [swap_mul_swap_inv hxy hyz hxz] at this

theorem Contains3.comm (h1 : Contains3 N p q r) (h2 : Contains3 N r s u)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s)
    (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) : Contains3 N p s r := by
  have := N.mul_mem (N.mul_mem (N.mul_mem h1 h2) (N.inv_mem h1)) (N.inv_mem h2)
  unfold Contains3
  rwa [swap_commutator hpq hpr hps hpu hqr hqs hqu hrs hru hsu] at this

structure TwoSetData (N : Subgroup (Perm V)) (W₁ W₂ : Finset V) : Prop where
  disjoint : Disjoint W₁ W₂
  three₁ : 3 ≤ W₁.card
  three₂ : 3 ≤ W₂.card
  outside : ∃ r, r ∉ W₁ ∧ r ∉ W₂
  good₁ : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∉ W₁ → y ∉ W₁ → z ∉ W₁ → Contains3 N x y z
  good₂ : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∉ W₂ → y ∉ W₂ → z ∉ W₂ → Contains3 N x y z

variable {W₁ W₂ : Finset V}

theorem TwoSetData.symm (D : TwoSetData N W₁ W₂) : TwoSetData N W₂ W₁ :=
  ⟨D.disjoint.symm, D.three₂, D.three₁, by simpa [and_comm] using D.outside, D.good₂, D.good₁⟩

theorem TwoSetData.mixed_outside (D : TwoSetData N W₁ W₂) {w₁ w₂ r : V} (hw₁ : w₁ ∈ W₁)
    (hw₂ : w₂ ∈ W₂) (hr₁ : r ∉ W₁) (hr₂ : r ∉ W₂) : Contains3 N w₁ w₂ r := by
  obtain ⟨s, hs, hsw⟩ := Finset.exists_mem_ne (by have := D.three₁; omega : 1 < W₁.card) w₁
  obtain ⟨t, ht, htw⟩ := Finset.exists_mem_ne (by have := D.three₂; omega : 1 < W₂.card) w₂
  have hn : ∀ x ∈ W₁, x ∉ W₂ := fun x hx => Finset.disjoint_left.mp D.disjoint hx
  have hn' : ∀ x ∈ W₂, x ∉ W₁ := fun x hx hx' => hn x hx' hx
  have e1 : Contains3 N w₁ s r :=
    D.good₂ _ _ _ hsw.symm (by rintro rfl; exact hr₁ hs) (by rintro rfl; exact hr₁ hw₁)
      (hn _ hw₁) (hn _ hs) hr₂
  have e2 : Contains3 N r w₂ t :=
    D.good₁ _ _ _ (by rintro rfl; exact hr₂ hw₂) htw.symm (by rintro rfl; exact hr₂ ht)
      hr₁ (hn' _ hw₂) (hn' _ ht)
  exact e1.comm e2 hsw.symm (by rintro rfl; exact hr₁ hw₁) (by rintro rfl; exact hn _ hw₁ hw₂)
    (by rintro rfl; exact hn _ hw₁ ht) (by rintro rfl; exact hr₁ hs)
    (by rintro rfl; exact hn _ hs hw₂) (by rintro rfl; exact hn _ hs ht)
    (by rintro rfl; exact hr₂ hw₂) (by rintro rfl; exact hr₂ ht) htw.symm

theorem TwoSetData.mixed_second (D : TwoSetData N W₁ W₂) {w₁ w₂ w₂' : V} (hw₁ : w₁ ∈ W₁)
    (hw₂ : w₂ ∈ W₂) (hw₂' : w₂' ∈ W₂) (hne : w₂ ≠ w₂') : Contains3 N w₁ w₂ w₂' := by
  obtain ⟨r, hr₁, hr₂⟩ := D.outside
  obtain ⟨e, he, hee⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {w₂, w₂'}) (t := W₂) (lt_of_le_of_lt Finset.card_le_two (by have := D.three₂; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hee
  have hn : ∀ x ∈ W₁, x ∉ W₂ := fun x hx => Finset.disjoint_left.mp D.disjoint hx
  have hn' : ∀ x ∈ W₂, x ∉ W₁ := fun x hx hx' => hn x hx' hx
  have e1 : Contains3 N w₁ r w₂' :=
    (D.mixed_outside hw₁ hw₂' hr₁ hr₂).flip (by rintro rfl; exact hn _ hw₁ hw₂')
      (by rintro rfl; exact hr₂ hw₂') (by rintro rfl; exact hr₁ hw₁)
  have e2 : Contains3 N w₂' w₂ e :=
    D.good₁ _ _ _ hne.symm (Ne.symm hee.1) (Ne.symm hee.2) (hn' _ hw₂') (hn' _ hw₂) (hn' _ he)
  exact e1.comm e2 (by rintro rfl; exact hr₁ hw₁) (by rintro rfl; exact hn _ hw₁ hw₂')
    (by rintro rfl; exact hn _ hw₁ hw₂) (by rintro rfl; exact hn _ hw₁ he)
    (by rintro rfl; exact hr₂ hw₂') (by rintro rfl; exact hr₂ hw₂) (by rintro rfl; exact hr₂ he)
    hne.symm (Ne.symm hee.2) (Ne.symm hee.1)

theorem TwoSetData.mixed_triple (D : TwoSetData N W₁ W₂) {w₁ w₂ t : V} (hw₁ : w₁ ∈ W₁)
    (hw₂ : w₂ ∈ W₂) (ht₁ : t ≠ w₁) (ht₂ : t ≠ w₂) : Contains3 N w₁ w₂ t := by
  have hw : w₁ ≠ w₂ := fun h => Finset.disjoint_left.mp D.disjoint hw₁ (h ▸ hw₂)
  by_cases htW₁ : t ∈ W₁
  · exact ((D.symm.mixed_second hw₂ hw₁ htW₁ ht₁.symm).rot hw.symm ht₁.symm ht₂.symm).flip
      ht₁.symm ht₂ hw
  · by_cases htW₂ : t ∈ W₂
    · exact D.mixed_second hw₁ hw₂ htW₂ ht₂.symm
    · exact D.mixed_outside hw₁ hw₂ htW₁ htW₂

theorem TwoSetData.contains3 (D : TwoSetData N W₁ W₂) {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : Contains3 N x y z := by
  have hn : ∀ a ∈ W₁, a ∉ W₂ := fun a ha => Finset.disjoint_left.mp D.disjoint ha
  by_cases hA : x ∈ W₁ ∨ y ∈ W₁ ∨ z ∈ W₁
  · by_cases hB : x ∈ W₂ ∨ y ∈ W₂ ∨ z ∈ W₂
    · rcases hA with hx | hy | hz <;> rcases hB with hx' | hy' | hz'
      · exact absurd hx' (hn _ hx)
      · exact D.mixed_triple hx hy' hxz.symm hyz.symm
      · exact (D.mixed_triple hx hz' hxy.symm hyz).flip hxz hyz.symm hxy
      · exact (((D.mixed_triple hy hx' hyz.symm hxz.symm).flip hxy.symm hxz hyz).rot hyz
          hxz.symm hxy.symm).rot hxz.symm hxy hyz.symm
      · exact absurd hy' (hn _ hy)
      · exact ((D.mixed_triple hy hz' hxy hxz).rot hyz hxz.symm hxy.symm).rot hxz.symm hxy
          hyz.symm
      · exact (D.mixed_triple hz hx' hyz hxy.symm).rot hxz.symm hxy hyz.symm
      · exact ((D.mixed_triple hz hy' hxz hxy).flip hyz.symm hxy.symm hxz.symm).rot hxz.symm hxy
          hyz.symm
      · exact absurd hz' (hn _ hz)
    · simp only [not_or] at hB
      exact D.good₂ x y z hxy hyz hxz hB.1 hB.2.1 hB.2.2
  · simp only [not_or] at hA
    exact D.good₁ x y z hxy hyz hxz hA.1 hA.2.1 hA.2.2

theorem contains3_of_commute [Fintype V] {a : Perm V}
    (hNa : ∀ k ∈ alternatingGroup V, k * a = a * k → k ∈ N)
    (hx : x ∉ a.support) (hy : y ∉ a.support) (hz : z ∉ a.support)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : Contains3 N x y z := by
  have hnd : [x, y, z].Nodup := by simp [hxy, hyz, hxz]
  have hsupp := Equiv.Perm.support_swap_mul_swap hnd
  apply hNa
  · have h3 : (swap x y * swap y z).IsThreeCycle := by
      rw [← card_support_eq_three_iff, hsupp]
      simp [hxy, hyz, hxz]
    exact h3.mem_alternatingGroup
  · have hd : Disjoint (swap x y * swap y z) a := by
      rw [disjoint_iff_disjoint_support, hsupp, Finset.disjoint_left]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    exact hd.commute.eq

theorem alternatingGroup_le_of_two_supports [Fintype V] {a b : Perm V}
    (hab : Disjoint a.support b.support) (ha3 : 3 ≤ a.support.card) (hb3 : 3 ≤ b.support.card)
    (hr : ∃ r, r ∉ a.support ∧ r ∉ b.support)
    (hNa : ∀ k ∈ alternatingGroup V, k * a = a * k → k ∈ N)
    (hNb : ∀ k ∈ alternatingGroup V, k * b = b * k → k ∈ N) :
    alternatingGroup V ≤ N := by
  have D : TwoSetData N a.support b.support :=
    ⟨hab, ha3, hb3, hr,
      fun _ _ _ hxy hyz hxz hx hy hz => contains3_of_commute hNa hx hy hz hxy hyz hxz,
      fun _ _ _ hxy hyz hxz hx hy hz => contains3_of_commute hNb hx hy hz hxy hyz hxz⟩
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hσ3 : σ.IsThreeCycle := hσ
  obtain ⟨c, hc⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ3.card_support]
    norm_num
  have h1 := (hσ3.eq_swap_mul_swap_iff_mem_support (a := c)).mpr hc
  obtain ⟨hc1, hc2⟩ := List.nodup_cons.mp (hσ3.nodup_iff_mem_support.mpr hc)
  obtain ⟨hc3, -⟩ := List.nodup_cons.mp hc2
  simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hc1 hc3
  have h3 := D.contains3 hc1.1 hc3 hc1.2
  unfold Contains3 at h3
  rw [← h1] at h3
  exact h3

end

end CFSG.RankThree.PartOne.CTP.Alt
