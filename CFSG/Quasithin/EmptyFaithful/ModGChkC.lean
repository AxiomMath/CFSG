module

public import CFSG.Quasithin.EmptyFaithful.ModGBase

public section

namespace CFSG.Quasithin.ModG

open CFSG.Blueprint

theorem pow_five_eq {G : Type*} [Group G] (c : G) : c ^ 5 = (c * c) * (c * c) * c := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

@[expose] def zi (k : ℕ) : Mg := ev Lab (zWd.getD k [])

@[expose] def di (j : ℕ) : Mg := ev Lks8 (dWd.getD j [])

theorem cd_zi (k : ℕ) : cd (zi k) = zK.getD k kId := by
  have h := List.getD_map zWd [] (n := k) (fun w => cd (ev Lab w))
  have h2 : zWd.map (fun w => cd (ev Lab w)) = zK := by
    rw [← zEl_cd, zEl, List.map_map]
    rfl
  rw [h2] at h
  have h3 : cd (ev Lab []) = kId := by rw [ev_nil, cd_one]
  rw [h3] at h
  exact h.symm

theorem cd_zi_inv (k : ℕ) : cd (zi k)⁻¹ = zinvK.getD k kId := by
  have h := List.getD_map zWd [] (n := k) (fun w => cd ((ev Lab w)⁻¹))
  have h2 : zWd.map (fun w => cd ((ev Lab w)⁻¹)) = zinvK := by
    rw [← zinv_cd, List.map_map]
    rfl
  rw [h2] at h
  have h3 : cd ((ev Lab [])⁻¹) = kId := by rw [ev_nil, inv_one, cd_one]
  rw [h3] at h
  exact h.symm

theorem cd_di (j : ℕ) : cd (di j) = dK.getD j kId := by
  have h := List.getD_map dWd [] (n := j) (fun w => cd (ev Lks8 w))
  have h2 : dWd.map (fun w => cd (ev Lks8 w)) = dK := by
    rw [← dEl_cd, dEl, List.map_map]
    rfl
  rw [h2] at h
  have h3 : cd (ev Lks8 []) = kId := by rw [ev_nil, cd_one]
  rw [h3] at h
  exact h.symm

theorem cd_di_inv (j : ℕ) : cd (di j)⁻¹ = dinvK.getD j kId := by
  have h := List.getD_map dWd [] (n := j) (fun w => cd ((ev Lks8 w)⁻¹))
  have h2 : dWd.map (fun w => cd ((ev Lks8 w)⁻¹)) = dinvK := by
    rw [← dinv_cd, List.map_map]
    rfl
  rw [h2] at h
  have h3 : cd ((ev Lks8 [])⁻¹) = kId := by rw [ev_nil, inv_one, cd_one]
  rw [h3] at h
  exact h.symm

@[expose] def alph4 (y : Mg) : List Mg :=
  [Ls.getD 0 1, Ls.getD 1 1, Ls.getD 2 1, y, Ls.getD 3 1, Ls.getD 4 1, Ls.getD 5 1, y⁻¹]

@[expose] def alph4K (yK yiK : ℕ) : List ℕ :=
  [LsK.getD 0 kId, LsK.getD 1 kId, LsK.getD 2 kId, yK, LsK.getD 3 kId, LsK.getD 4 kId, LsK.getD 5 kId, yiK]

theorem Ls_getD_cd (i : ℕ) : cd (Ls.getD i 1) = LsK.getD i kId := by
  have := List.getD_map Ls 1 (n := i) cd
  rw [cd_one, Ls_cd] at this
  exact this.symm

theorem alph4_cd (y : Mg) : (alph4 y).map cd = alph4K (cd y) (cd y⁻¹) := by
  simp only [alph4, alph4K, List.map_cons, List.map_nil, Ls_getD_cd]

theorem alph4_inv (y : Mg) : ∀ l < 4, (alph4 y).getD (l + 4) 1 = ((alph4 y).getD l 1)⁻¹ := by
  intro l hl
  have h0 := Ls_inv 0 (by omega)
  have h1 := Ls_inv 1 (by omega)
  have h2 := Ls_inv 2 (by omega)
  interval_cases l
  · simpa [alph4] using h0
  · simpa [alph4] using h1
  · simpa [alph4] using h2
  · simp [alph4]

theorem Ls_mem (i : ℕ) (hi : i < 6) : Ls.getD i 1 ∈ Ls := by
  have : i < Ls.length := by
    rw [Ls, invAlph_length, List.length_map, sWd_len]
    omega
  rw [List.getD_eq_getElem _ _ this]
  exact List.getElem_mem _

@[expose] def okC (t : ℕ × ℕ × List ℕ × List ℕ) : Bool :=
  let y := comp (zK.getD t.1 kId) (dK.getD t.2.1 kId)
  let yi := comp (dinvK.getD t.2.1 kId) (zinvK.getD t.1 kId)
  let A := alph4K y yi
  let a := evc A t.2.2.1
  let b := evc A t.2.2.2
  let ab := comp a b
  let ab2 := comp ab ab
  let ab4 := comp ab2 ab2
  Nat.beq (comp a a) kId && Nat.beq (comp b (comp b b)) kId && !(Nat.beq b kId) &&
    Nat.beq (comp ab4 ab) kId

set_option maxRecDepth 100000 in
theorem cCheck_true : allL okC witCl = true := by decide +kernel

theorem cCover : ∀ k < 6, 1 ≤ k → ∀ j < 45, ∃ t ∈ witCl, t.1 = k ∧ t.2.1 = j := by
  decide +kernel

theorem witCl_lt : ∀ t ∈ witCl, (∀ l ∈ t.2.2.1, l < 8) ∧ ∀ l ∈ t.2.2.2, l < 8 := by decide +kernel

theorem claimC (k j : ℕ) (hk1 : 1 ≤ k) (hk : k < 6) (hj : j < 45) :
    ∃ a b : Mg, a ∈ Subgroup.closure ({x | x ∈ Ls} ∪ {zi k * di j}) ∧
      b ∈ Subgroup.closure ({x | x ∈ Ls} ∪ {zi k * di j}) ∧
      a ^ 2 = 1 ∧ b ^ 3 = 1 ∧ (a * b) ^ 5 = 1 ∧ b ≠ 1 := by
  obtain ⟨t, ht, htk, htj⟩ := cCover k hk hk1 j hj
  have h := allL_iff.1 cCheck_true t ht
  have hlt := witCl_lt t ht
  set y : Mg := zi k * di j with hy
  have hycd : cd y = comp (zK.getD k kId) (dK.getD j kId) := by
    rw [hy, cd_mul, cd_zi, cd_di]
  have hyicd : cd y⁻¹ = comp (dinvK.getD j kId) (zinvK.getD k kId) := by
    rw [hy, mul_inv_rev, cd_mul, cd_di_inv, cd_zi_inv]
  have hA : ∀ x ∈ alph4 y, x ∈ Subgroup.closure ({x | x ∈ Ls} ∪ {y}) := by
    intro x hx
    simp only [alph4, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure (Or.inl (Ls_mem 0 (by omega)))
    · exact Subgroup.subset_closure (Or.inl (Ls_mem 1 (by omega)))
    · exact Subgroup.subset_closure (Or.inl (Ls_mem 2 (by omega)))
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.subset_closure (Or.inl (Ls_mem 3 (by omega)))
    · exact Subgroup.subset_closure (Or.inl (Ls_mem 4 (by omega)))
    · exact Subgroup.subset_closure (Or.inl (Ls_mem 5 (by omega)))
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))
  have hcd : ∀ w, cd (ev (alph4 y) w) = evc (alph4K (comp (zK.getD k kId) (dK.getD j kId))
      (comp (dinvK.getD j kId) (zinvK.getD k kId))) w := by
    intro w
    rw [c_ev cd cd_mul cd_one, alph4_cd, hycd, hyicd]
  refine ⟨ev (alph4 y) t.2.2.1, ev (alph4 y) t.2.2.2, ev_mem hA _, ev_mem hA _, ?_⟩
  simp only [okC, htk, htj, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  set a := ev (alph4 y) t.2.2.1
  set b := ev (alph4 y) t.2.2.2
  have ea : cd a = evc (alph4K (comp (zK.getD k kId) (dK.getD j kId))
      (comp (dinvK.getD j kId) (zinvK.getD k kId))) t.2.2.1 := hcd _
  have eb : cd b = evc (alph4K (comp (zK.getD k kId) (dK.getD j kId))
      (comp (dinvK.getD j kId) (zinvK.getD k kId))) t.2.2.2 := hcd _
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply cd_injective
    rw [pow_two, cd_mul, cd_one, ea]
    exact Nat.eq_of_beq_eq_true h1
  · apply cd_injective
    rw [pow_three]
    simp only [cd_mul, cd_one, eb]
    exact Nat.eq_of_beq_eq_true h2
  · apply cd_injective
    rw [pow_five_eq]
    simp only [cd_mul, cd_one, ea, eb]
    exact Nat.eq_of_beq_eq_true h4
  · intro hb1
    have hh : evc (alph4K (comp (zK.getD k kId) (dK.getD j kId))
        (comp (dinvK.getD j kId) (zinvK.getD k kId))) t.2.2.2 = kId := by
      rw [← eb, hb1, cd_one]
    rw [hh] at h3
    exact absurd h3 (by simp [Nat.beq_refl])

end CFSG.Quasithin.ModG
