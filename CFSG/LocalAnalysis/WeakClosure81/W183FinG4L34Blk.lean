module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Par

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.Quasithin CFSG.Open
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

private def w183finL34BlkPres (g : Equiv.Perm (Fin 42)) : Prop :=
  ∀ p : Fin 42, p.val < 21 → (g p).val < 21

private theorem w183finL34BlkPres_rho (A : GL (Fin 3) F4) : w183finL34BlkPres (rho A) := by
  intro p hp
  rw [rho_apply]
  simp only [rhoFun, if_pos hp]
  exact vIdx_lt _

private theorem w183finL34BlkPres_inv {g : Equiv.Perm (Fin 42)} (hg : w183finL34BlkPres g) :
    w183finL34BlkPres g⁻¹ := by
  intro p hp
  have hmap : Set.MapsTo g {q : Fin 42 | q.val < 21} {q : Fin 42 | q.val < 21} :=
    fun q hq => hg q hq
  exact Equiv.Perm.perm_symm_mapsTo_of_mapsTo g hmap hp

private theorem w183finL34BlkPres_one : w183finL34BlkPres (1 : Equiv.Perm (Fin 42)) := by
  intro p hp
  simpa using hp

private theorem w183finL34BlkPres_mul {g h : Equiv.Perm (Fin 42)} (hg : w183finL34BlkPres g)
    (hh : w183finL34BlkPres h) : w183finL34BlkPres (g * h) := by
  intro p hp
  rw [Equiv.Perm.mul_apply]
  exact hg (h p) (hh p hp)

private theorem w183finL34Blk_closure_induction {k : Set (Equiv.Perm (Fin 42))}
    {p : Equiv.Perm (Fin 42) → Prop} (mem : ∀ x ∈ k, p x) (one : p 1)
    (mul : ∀ x y, p x → p y → p (x * y)) (inv : ∀ x, p x → p (x⁻¹))
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ Subgroup.closure k) : p x :=
  Subgroup.closure_induction (p := fun g _ => p g) mem one (fun x y _ _ hx hy => mul x y hx hy)
    (fun x _ hx => inv x hx) hx

private theorem w183finL34Blk_tab_fix {w : List ℕ} {x : Fin 42}
    (h : (wordTab w)[x.val]! = x.val) : wordPerm w x = x :=
  Fin.ext (by rw [← TabRep.apply (tabRep_wordTab w) x, h])

private theorem w183finL34Blk_gen_ne {j : ℕ} {x : Fin 42}
    (h : (genT j)[x.val]! ≠ x.val) : genS j x ≠ x := by
  intro hfix
  exact h (by rw [TabRep.apply (tabRep_genT j) x, hfix])

private theorem w183finL34Blk_word_ne {w : List ℕ} {x : Fin 42}
    (h : (wordTab w)[x.val]! ≠ x.val) : wordPerm w x ≠ x := by
  intro hfix
  exact h (by rw [TabRep.apply (tabRep_wordTab w) x, hfix])

private theorem w183finL34Blk_inv_fix {g : Equiv.Perm (Fin 42)} {x : Fin 42} (h : g x = x) :
    g⁻¹ x = x :=
  Equiv.Perm.inv_eq_iff_eq.mpr h.symm

theorem S_preserves_block0 {s : Equiv.Perm (Fin 42)} (hs : s ∈ S) :
    ∀ p : Fin 42, p.val < 21 → (s p).val < 21 := by
  change w183finL34BlkPres s
  rw [S] at hs
  refine w183finL34Blk_closure_induction ?_ ?_ ?_ ?_ hs
  · intro x hx
    rcases hx with rfl | rfl | rfl
    · simpa only [g₁] using w183finL34BlkPres_rho aGL
    · simpa only [g₂] using w183finL34BlkPres_rho bGL
    · simpa only [g₃] using w183finL34BlkPres_rho cGL
  · exact w183finL34BlkPres_one
  · intro x y hx hy
    exact w183finL34BlkPres_mul hx hy
  · intro x hx
    exact w183finL34BlkPres_inv hx

theorem P1_fixes_point2 : ∀ q ∈ P1, q ⟨2, by decide⟩ = ⟨2, by decide⟩ := by
  intro q hq
  rw [P1] at hq
  refine w183finL34Blk_closure_induction (p := fun g : Equiv.Perm (Fin 42) =>
    g ⟨2, by decide⟩ = ⟨2, by decide⟩) ?_ ?_ ?_ ?_ hq
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    simp only [wP₁, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact w183finL34Blk_tab_fix (by decide +kernel)
    · exact w183finL34Blk_tab_fix (by decide +kernel)
    · exact w183finL34Blk_tab_fix (by decide +kernel)
  · rfl
  · intro x y hx hy
    rw [Equiv.Perm.mul_apply, hy, hx]
  · intro x hx
    exact w183finL34Blk_inv_fix hx

private theorem w183finL34Blk_genS1_mem_P2 : genS 1 ∈ P2 := by
  rw [P2]
  exact Subgroup.subset_closure ⟨[1], by decide, rfl⟩

private theorem w183finL34Blk_word3_mem_P2 : wordPerm [0, 0, 1, 0, 1, 0] ∈ P2 := by
  rw [P2]
  exact Subgroup.subset_closure ⟨[0, 0, 1, 0, 1, 0], by decide, rfl⟩

private def w183finL34Blk_movesCheck : Bool :=
  (List.range 21).all fun k =>
    decide ((genT 1)[k]! ≠ k) || decide ((wordTab [0, 0, 1, 0, 1, 0])[k]! ≠ k)

private theorem w183finL34Blk_movesCheck_true : w183finL34Blk_movesCheck = true := by
  decide +kernel

theorem P2_moves_block0 : ∀ p : Fin 42, p.val < 21 → ∃ q ∈ P2, q p ≠ p := by
  intro p hp
  have hmem : p.val ∈ List.range 21 := List.mem_range.mpr hp
  have hall := (List.all_eq_true.mp w183finL34Blk_movesCheck_true) p.val hmem
  rw [Bool.or_eq_true] at hall
  rcases hall with h | h
  · exact ⟨genS 1, w183finL34Blk_genS1_mem_P2,
      w183finL34Blk_gen_ne (of_decide_eq_true h)⟩
  · exact ⟨wordPerm [0, 0, 1, 0, 1, 0], w183finL34Blk_word3_mem_P2,
      w183finL34Blk_word_ne (of_decide_eq_true h)⟩

private def w183finL34Blk_fixesPt (P : Subgroup (Equiv.Perm (Fin 42))) : Prop :=
  ∃ p : Fin 42, p.val < 21 ∧ ∀ q ∈ P, q p = p

private theorem w183finL34Blk_fixesPt_conj {P : Subgroup (Equiv.Perm (Fin 42))}
    {g : Equiv.Perm (Fin 42)} (hg : w183finL34BlkPres g) :
    w183finL34Blk_fixesPt (conjSubgroup P g) ↔ w183finL34Blk_fixesPt P := by
  constructor
  · rintro ⟨x, hx, hfix⟩
    refine ⟨g x, hg x hx, ?_⟩
    intro p hp
    have hmem : g⁻¹ * p * g ∈ conjSubgroup P g := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hp
    have h := hfix (g⁻¹ * p * g) hmem
    have := congrArg (fun y : Fin 42 => g y) h
    simpa [mul_assoc] using this
  · rintro ⟨x, hx, hfix⟩
    refine ⟨g⁻¹ x, w183finL34BlkPres_inv hg x hx, ?_⟩
    intro q hq
    have hmem : g * q * g⁻¹ ∈ P := (mem_conjSubgroup_iff.mp hq)
    have h := hfix (g * q * g⁻¹) hmem
    have := congrArg (fun y : Fin 42 => g⁻¹ y) h
    simpa [mul_assoc] using this

private theorem w183finL34Blk_P1_fixesPt : w183finL34Blk_fixesPt P1 :=
  ⟨⟨2, by decide⟩, by decide, fun q hq => P1_fixes_point2 q hq⟩

private theorem w183finL34Blk_conj_P2_not_fixesPt {k : Equiv.Perm (Fin 42)} (hk : k ∈ S) :
    ¬ w183finL34Blk_fixesPt (conjSubgroup P2 k) := by
  intro hfix
  have h2 : w183finL34Blk_fixesPt P2 :=
    (w183finL34Blk_fixesPt_conj (P := P2) (g := k) (S_preserves_block0 hk)).mp hfix
  obtain ⟨y, hy, hfy⟩ := h2
  obtain ⟨q, hqmem, hqne⟩ := P2_moves_block0 y hy
  exact hqne (hfy q hqmem)

private theorem w183finL34Blk_exists_conj_P1_of_fixesPt
    {P : Subgroup (Equiv.Perm (Fin 42))}
    (hP : IsMaxParabolicMod ⊥ S P) (hfix : w183finL34Blk_fixesPt P) :
    ∃ k ∈ S, P = conjSubgroup P1 k := by
  obtain ⟨k, hk, h | h⟩ := exists_conj_of_isMaxParabolicMod hP
  · exact ⟨k, hk, h⟩
  · exact absurd (h ▸ hfix) (w183finL34Blk_conj_P2_not_fixesPt hk)

private theorem w183finL34Blk_exists_conj_P2_of_not_fixesPt
    {P : Subgroup (Equiv.Perm (Fin 42))}
    (hP : IsMaxParabolicMod ⊥ S P) (hfix : ¬ w183finL34Blk_fixesPt P) :
    ∃ k ∈ S, P = conjSubgroup P2 k := by
  obtain ⟨k, hk, h | h⟩ := exists_conj_of_isMaxParabolicMod hP
  · refine absurd ?_ hfix
    rw [h]
    exact (w183finL34Blk_fixesPt_conj (P := P1) (g := k) (S_preserves_block0 hk)).mpr
      w183finL34Blk_P1_fixesPt
  · exact ⟨k, hk, h⟩

theorem not_actsOnDynkinMod_of_preserves
    {τ : Equiv.Perm (Fin 42)} (hτR : τ ∈ R)
    (hpres : ∀ p : Fin 42, p.val < 21 → (τ p).val < 21) : ¬ ActsOnDynkinMod ⊥ S τ := by
  rintro ⟨hτN, P, hPmax, hPne⟩
  have hQmax : IsMaxParabolicMod ⊥ S (conjSubgroup P τ⁻¹) :=
    isMaxParabolicMod_conj hτN hPmax
  have hpresτinv : w183finL34BlkPres τ⁻¹ := w183finL34BlkPres_inv hpres
  have hiff : w183finL34Blk_fixesPt (conjSubgroup P τ⁻¹) ↔ w183finL34Blk_fixesPt P :=
    w183finL34Blk_fixesPt_conj hpresτinv
  have hl : ∃ l ∈ S, conjSubgroup (conjSubgroup P τ⁻¹) l = P := by
    by_cases hfixP : w183finL34Blk_fixesPt P
    · obtain ⟨a, ha, hae⟩ := w183finL34Blk_exists_conj_P1_of_fixesPt hPmax hfixP
      obtain ⟨b, hb, hbe⟩ :=
        w183finL34Blk_exists_conj_P1_of_fixesPt hQmax (hiff.mpr hfixP)
      refine ⟨b⁻¹ * a, S.mul_mem (S.inv_mem hb) ha, ?_⟩
      rw [hbe, hae, conjSubgroup_conjSubgroup]
      congr 1
      group
    · obtain ⟨a, ha, hae⟩ := w183finL34Blk_exists_conj_P2_of_not_fixesPt hPmax hfixP
      obtain ⟨b, hb, hbe⟩ :=
        w183finL34Blk_exists_conj_P2_of_not_fixesPt hQmax (fun h => hfixP (hiff.mp h))
      refine ⟨b⁻¹ * a, S.mul_mem (S.inv_mem hb) ha, ?_⟩
      rw [hbe, hae, conjSubgroup_conjSubgroup]
      congr 1
      group
  obtain ⟨l, hlS, hl_eq⟩ := hl
  refine hPne l hlS ?_
  rw [← conjSubgroup_conjSubgroup]
  exact hl_eq

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end