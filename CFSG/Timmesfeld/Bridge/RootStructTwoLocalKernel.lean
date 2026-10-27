module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalStruct

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace TwoLocalSetting

variable {G : Type} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem map_line_eq_of_mem_nCore {a g : G} (ha : a ∈ D) (hg : g ∈ nCore D a) {L : Subgroup G}
    (hL : L ∈ rootLines D a) : L.map (MulAut.conj g).toMonoidHom = L := by
  obtain ⟨x, hx, hax, hxa, rfl⟩ := (S.mem_rootLines_iff ha).1 hL
  refine (S.map_line_eq_iff ha hx hax hxa (commute_of_mem_nCore hg)).2 ?_
  rcases S.commutator_eq ha hg (S.mem_nCore ha hx hax.symm) with h | h
  · left
    rw [mul_inv_eq_one] at h
    exact h
  · right
    rw [← h]
    group

theorem pow_eq_self_of_odd {a : G} (ha : a ∈ D) {n : ℕ} (hn : Odd n) : a ^ n = a := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, sq, S.root.mul_self_eq_one ha, one_pow, one_mul]

theorem fix_rootLines_iff {a g : G} (ha : a ∈ D) (h5 : 5 ≤ (rootLines D a).ncard)
    (hg : Commute g a) :
    (∀ L ∈ rootLines D a, L.map (MulAut.conj g).toMonoidHom = L) ↔ g ∈ nCore D a := by
  classical
  have hD := S.root
  refine ⟨fun hfix => ?_, fun hg' L hL => S.map_line_eq_of_mem_nCore ha hg' hL⟩
  obtain ⟨P, hPk, hP, hnc, hcov⟩ := S.exists_transversal ha
  set l := P.toList
  have hlP : ∀ y ∈ l, y ∈ P := fun y hy => Finset.mem_toList.1 hy
  have hgy : ∀ y ∈ l, g * y * g⁻¹ = y ∨ g * y * g⁻¹ = a * y := by
    intro y hy
    obtain ⟨hyD, hay, hya⟩ := hP y (hlP y hy)
    exact (S.map_line_eq_iff ha hyD hay hya hg).1
      (hfix _ ((S.mem_rootLines_iff ha).2 ⟨y, hyD, hay, hya, rfl⟩))
  have hr : Even (l.countP fun y => g * y * g⁻¹ ≠ y) := by
    have ht := S.toList_prod_mem_zpowers ha h5 hPk hP hnc hcov
    have h1 := conj_list_prod l (fun y hy => (hP y (hlP y hy)).2.1) hgy
    have h2 : g * l.prod * g⁻¹ = l.prod := by
      rcases (mem_zpowers_iff_of_mul_self (hD.mul_self_eq_one ha)).1 ht with h | h <;> rw [h]
      · group
      · rw [hg.eq, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 : a ^ (l.countP fun y => g * y * g⁻¹ ≠ y) = 1 := by
      have := congrArg (· * l.prod⁻¹) h1
      simpa using this.symm
    exact (pow_eq_one_iff_even_of_mul_self (hD.ne_one ha) (hD.mul_self_eq_one ha)).1 h3
  set l' := l.filter fun y => g * y * g⁻¹ ≠ y
  have hl'P : ∀ y ∈ l', y ∈ P := fun y hy => hlP y (List.mem_of_mem_filter hy)
  have hnd' : l'.Nodup := P.nodup_toList.filter _
  have hlen : l'.length = l.countP fun y => g * y * g⁻¹ ≠ y := by
    rw [List.countP_eq_length_filter]
  set m₀ := l'.prod
  have hm₀M : m₀ ∈ nCore D a := (nCore D a).list_prod_mem fun y hy =>
    S.mem_nCore ha (hP y (hl'P y hy)).1 (hP y (hl'P y hy)).2.1.symm
  have hagree : ∀ x ∈ P, m₀ * x * m₀⁻¹ = g * x * g⁻¹ := by
    intro x hxP
    obtain ⟨hxD, hax, hxa⟩ := hP x hxP
    have h1 := list_prod_conj (a := a) (x := x) l' (fun y hy => (hP y (hl'P y hy)).2.1)
      fun y hy => S.conj_eq_or ha (hP y (hl'P y hy)).1 hxD (hP y (hl'P y hy)).2.1 hax
        (hP y (hl'P y hy)).2.2 hxa
    have hcount : (l'.countP fun y => y * x * y⁻¹ ≠ x) = l'.countP fun y => y ≠ x := by
      refine List.countP_congr fun y hy => ?_
      simp only [ne_eq, decide_eq_true_eq]
      constructor
      · rintro hmove rfl
        exact hmove (by rw [mul_inv_cancel_right])
      · intro hne hfix'
        exact hnc y (hl'P y hy) x hxP hne (mul_inv_eq_iff_eq_mul.1 hfix')
    rw [hcount, countP_ne_eq hnd', hlen] at h1
    change m₀ * x * m₀⁻¹ = _ at h1
    rcases hgy x (Finset.mem_toList.2 hxP) with h | h
    ·
      have hxl' : x ∉ l' := by
        intro hx'
        have := (List.mem_filter.1 hx').2
        simp [h] at this
      simp only [hxl', ↓reduceIte, Nat.sub_zero] at h1
      rw [(pow_eq_one_iff_even_of_mul_self (hD.ne_one ha) (hD.mul_self_eq_one ha)).2 hr,
        one_mul] at h1
      rw [h1, h]
    ·
      have hxne : g * x * g⁻¹ ≠ x := by
        rw [h]
        intro h'
        exact hD.ne_one ha (by simpa using h')
      have hxl' : x ∈ l' := List.mem_filter.2 ⟨Finset.mem_toList.2 hxP, by simpa using hxne⟩
      have hpos : 1 ≤ l.countP fun y => g * y * g⁻¹ ≠ y := by
        rw [← hlen]
        exact List.length_pos_of_mem hxl'
      have hodd : Odd ((l.countP fun y => g * y * g⁻¹ ≠ y) - 1) := by
        obtain ⟨k, hk⟩ := hr
        exact ⟨k - 1, by omega⟩
      simp only [hxl', ↓reduceIte] at h1
      rw [S.pow_eq_self_of_odd ha hodd] at h1
      rw [h1, h]
  set c' := m₀⁻¹ * g with hc'
  have hcen : c' ∈ Subgroup.centralizer (nCore D a : Set G) := by
    rw [Subgroup.mem_centralizer_iff, S.nCore_eq_closure_insert ha hP hcov]
    intro m hm
    induction hm using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · rw [hy]
        have hm₀a : Commute m₀ a := commute_of_mem_nCore hm₀M
        exact ((hm₀a.inv_left.mul_left hg).eq).symm
      · have h1 := hagree y hy
        have e : c' * y * c'⁻¹ = y := by
          calc c' * y * c'⁻¹ = m₀⁻¹ * (g * y * g⁻¹) * m₀ := by rw [hc']; group
            _ = m₀⁻¹ * (m₀ * y * m₀⁻¹) * m₀ := by rw [h1]
            _ = y := by group
        exact (mul_inv_eq_iff_eq_mul.1 e).symm
    | one => simp
    | mul x y _ _ ihx ihy => rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
    | inv x _ ihx => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ihx, mul_assoc, mul_inv_cancel,
        mul_one]
  rw [S.centralizer_nCore ha h5] at hcen
  have hgm : g = m₀ * c' := by rw [hc']; group
  rw [hgm]
  exact (nCore D a).mul_mem hm₀M (Subgroup.zpowers_le.2 (S.self_mem ha) hcen)

end TwoLocalSetting

end CFSG.Timmesfeld.Bridge
