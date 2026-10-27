module

public import CFSG.Quasithin.H13.AS91Sec3Bridge
public import CFSG.Quasithin.H13.AS91Sec3Trans

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem reachOK_smul_fix {X Y : Type*} [MulAction S24 X] [MulAction S24 Y] (y : Y) (f : ℕ → X)
    (n : ℕ) (steps : List (ℕ → ℕ)) {m : ℕ} (hm : steps.length = m) (P : Fin m → S24)
    (hPm : ∀ j, P j ∈ M24g) (hfix : ∀ j, P j • y = y)
    (hstep : ∀ (j : Fin m) (i : ℕ), i < n → (steps.getD j id) i < n →
      f ((steps.getD j id) i) = P j • f i)
    {p : ℕ} {c : List ℕ} (h : Native.reachOK n steps p c = true) (hp : p < n) :
    ∀ q ∈ c, ∃ σ ∈ M24g, σ • y = y ∧ σ • f p = f q := by
  intro q hq
  obtain ⟨σ, hσ, he⟩ := reachOK_smul (X := Y × X) (fun i => (y, f i)) n steps hm P hPm
    (fun j i hi hji => by rw [Prod.smul_mk, hfix j, hstep j i hi hji]) h hp q hq
  rw [Prod.smul_mk, Prod.mk.injEq] at he
  exact ⟨σ, hσ, he⟩

theorem reachOK_trio_fix {Y : Type*} [MulAction S24 Y] (y : Y) (gs : List (Array ℕ))
    (P : Fin gs.length → Equiv.Perm (Fin 24)) (hP : ∀ j : Fin gs.length, RepT (gs.getD j #[]) (P j))
    (hPm : ∀ j, P j ∈ M24g) (hfix : ∀ j, P j • y = y) {p : ℕ} {c : List ℕ}
    (h : Native.reachOK 3795 (Native.trioSteps gs) p c = true) (hp : p < 3795) :
    ∀ q ∈ c, ∃ σ ∈ M24g, σ • y = y ∧ σ • trioFin p = trioFin q := by
  refine reachOK_smul_fix y trioFin 3795 (Native.trioSteps gs) (by simp [Native.trioSteps]) P hPm
    hfix ?_ h hp
  intro j i hi hji
  have e : (Native.trioSteps gs).getD j id i =
      Native.trioIdx (Native.imgTrio (gs.getD j #[]) (Native.trioList ())[i]!) := by
    simp only [Native.trioSteps]
    rw [getD_map_of_lt _ gs #[] id j.2]
  rw [e] at hji ⊢
  rw [smul_trioFin (hP j) hi, ← trioOf_trioIdx hji]

theorem reachOK_sext_fix {Y : Type*} [MulAction S24 Y] (y : Y) (gs : List (Array ℕ))
    (P : Fin gs.length → Equiv.Perm (Fin 24)) (hP : ∀ j : Fin gs.length, RepT (gs.getD j #[]) (P j))
    (hPm : ∀ j, P j ∈ M24g) (hfix : ∀ j, P j • y = y) {p : ℕ} {c : List ℕ}
    (h : Native.reachOK 1771 (Native.sextSteps gs) p c = true) (hp : p < 1771) :
    ∀ q ∈ c, ∃ σ ∈ M24g, σ • y = y ∧ σ • sextFin p = sextFin q := by
  refine reachOK_smul_fix y sextFin 1771 (Native.sextSteps gs) (by simp [Native.sextSteps]) P hPm
    hfix ?_ h hp
  intro j i hi hji
  have e : (Native.sextSteps gs).getD j id i =
      Native.sextIdx (Native.imgSext (gs.getD j #[]) (Native.sextList ())[i]!) := by
    simp only [Native.sextSteps]
    rw [getD_map_of_lt _ gs #[] id j.2]
  rw [e] at hji ⊢
  rw [smul_sextFin (hP j) hi, ← sextOfL_sextIdx hji]

section Cert


theorem trioList_zero : (Native.trioList ())[0]! = Native.baseTrio := by
  have h := trioCheck_true
  simp only [Native.trioCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

theorem sextList_zero : (Native.sextList ())[0]! = Native.baseSext := by
  have h := sextCheck_true
  simp only [Native.sextCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

theorem forall_trio_of_base {P : Finset (Finset (Fin 24)) → Prop}
    (hP : ∀ g ∈ M24g, ∀ l, P l → P (g • l)) (h0 : P (trioFin 0)) {l : Finset (Finset (Fin 24))}
    (hl : IsTrio l) : P l := by
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  have h := hP g⁻¹ (M24g.inv_mem hg) _ h0
  rwa [← hgl, inv_smul_smul] at h

theorem forall_sextet_of_base {P : Finset (Finset (Fin 24)) → Prop}
    (hP : ∀ g ∈ M24g, ∀ U, P U → P (g • U)) (h0 : P (sextFin 0)) {U : Finset (Finset (Fin 24))}
    (hU : IsSextet U) : P U := by
  obtain ⟨g, hg, hgU⟩ := sextet_transitive hU
  have h := hP g⁻¹ (M24g.inv_mem hg) _ h0
  rwa [← hgU, inv_smul_smul] at h

end Cert

end CFSG.Quasithin.H13.AS91.M24G
