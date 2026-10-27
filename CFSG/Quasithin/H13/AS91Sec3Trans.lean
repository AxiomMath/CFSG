module

public import CFSG.Quasithin.H13.AS91Sec3Lists
public import CFSG.Quasithin.H13.AS91Sec3Perms

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem getD_map_of_lt {α β : Type} (f : α → β) (l : List α) (d : α) (e : β) {j : ℕ}
    (hj : j < l.length) : (l.map f).getD j e = f (l.getD j d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj]
  rfl

theorem treeOK_get {α : Type} [Inhabited α] {l : Array α} {par gen : Array ℕ}
    {steps : List (α → α)} {idx : α → ℕ} (h : Native.treeOK l par gen steps idx = true) {p : ℕ}
    (hp : p < l.size) (hp0 : p ≠ 0) :
    par[p]! < p ∧ gen[p]! < steps.length ∧ idx ((steps.getD gen[p]! id) l[par[p]!]!) = p := by
  unfold Native.treeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Native.allLt_iff, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨-, hall⟩ := h
  rcases hall p hp with h0 | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h0 hp0
  · exact ⟨h1, h2, h3⟩

theorem exists_smul_of_step {X : Type*} [MulAction S24 X] (f : ℕ → X) (n : ℕ)
    (hstep : ∀ p, p < n → p ≠ 0 → ∃ (j : Fin 3) (i : ℕ), i < p ∧ genPerm j • f i = f p) :
    ∀ p < n, ∃ g ∈ M24g, g • f 0 = f p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨1, one_mem _, one_smul _ _⟩
    · obtain ⟨j, i, hip, hf⟩ := hstep p hp hp0
      obtain ⟨g, hg, hgi⟩ := ih i hip (lt_trans hip hp)
      exact ⟨genPerm j * g, mul_mem (genPerm_mem j) hg, by rw [mul_smul, hgi, hf]⟩

section Cert

theorem trioFin_step {p : ℕ} (hp : p < 3795) (hp0 : p ≠ 0) :
    ∃ (j : Fin 3) (i : ℕ), i < p ∧ genPerm j • trioFin i = trioFin p := by
  have h := trioCheck_true
  simp only [Native.trioCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hsize, -, -, htree, -⟩ := h
  have hsize' : (Native.trioList ()).size = 3795 := hsize
  obtain ⟨hpar, hgen, hidx⟩ := treeOK_get htree (p := p) (by rw [hsize']; exact hp) hp0
  generalize (Native.trioData ()).2.1[p]! = i at hpar hidx
  generalize (Native.trioData ()).2.2[p]! = j at hgen hidx
  have hj : j < 3 := by simpa [Native.genTabs] using hgen
  rw [getD_map_of_lt _ _ #[] id (by simpa [Native.genTabs] using hj)] at hidx
  have h3 : Native.trioIdx (Native.imgTrio (Native.genTabs.getD j #[]) (Native.trioList ())[i]!) <
      3795 := hidx ▸ hp
  refine ⟨⟨j, hj⟩, i, hpar, ?_⟩
  rw [smul_trioFin (genTabs_rep_nat hj) (by omega), ← trioOf_trioIdx h3, hidx]

theorem sextFin_step {q : ℕ} (hq : q < 1771) (hq0 : q ≠ 0) :
    ∃ (j : Fin 3) (i : ℕ), i < q ∧ genPerm j • sextFin i = sextFin q := by
  have h := sextCheck_true
  simp only [Native.sextCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hsize, -, -, htree, -⟩ := h
  have hsize' : (Native.sextList ()).size = 1771 := hsize
  obtain ⟨hpar, hgen, hidx⟩ := treeOK_get htree (p := q) (by rw [hsize']; exact hq) hq0
  generalize (Native.sextData ()).2.1[q]! = i at hpar hidx
  generalize (Native.sextData ()).2.2[q]! = j at hgen hidx
  have hj : j < 3 := by simpa [Native.genTabs] using hgen
  rw [getD_map_of_lt _ _ #[] id (by simpa [Native.genTabs] using hj)] at hidx
  have h3 : Native.sextIdx (Native.imgSext (Native.genTabs.getD j #[]) (Native.sextList ())[i]!) <
      1771 := hidx ▸ hq
  refine ⟨⟨j, hj⟩, i, hpar, ?_⟩
  rw [smul_sextFin (genTabs_rep_nat hj) (by omega), ← sextOfL_sextIdx h3, hidx]

theorem exists_smul_trioFin {p : ℕ} (hp : p < 3795) : ∃ g ∈ M24g, g • trioFin 0 = trioFin p :=
  exists_smul_of_step trioFin 3795 (fun _ hp hp0 => trioFin_step hp hp0) p hp

theorem exists_smul_sextFin {q : ℕ} (hq : q < 1771) : ∃ g ∈ M24g, g • sextFin 0 = sextFin q :=
  exists_smul_of_step sextFin 1771 (fun _ hq hq0 => sextFin_step hq hq0) q hq

theorem trio_transitive {l : Finset (Finset (Fin 24))} (hl : IsTrio l) :
    ∃ g ∈ M24g, g • l = trioFin 0 := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff l).1 hl
  obtain ⟨g, hg, hgp⟩ := exists_smul_trioFin hp
  exact ⟨g⁻¹, M24g.inv_mem hg, by rw [← hgp, inv_smul_smul]⟩

theorem sextet_transitive {U : Finset (Finset (Fin 24))} (hU : IsSextet U) :
    ∃ g ∈ M24g, g • U = sextFin 0 := by
  obtain ⟨q, hq, rfl⟩ := (isSextet_iff U).1 hU
  obtain ⟨g, hg, hgq⟩ := exists_smul_sextFin hq
  exact ⟨g⁻¹, M24g.inv_mem hg, by rw [← hgq, inv_smul_smul]⟩

end Cert

end CFSG.Quasithin.H13.AS91.M24G
