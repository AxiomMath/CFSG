
module

public import CFSG.Sporadic.Schreier.RuReps

@[expose] public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem ptPosOK_spec {n : ℕ} {Fl pos : Array ℕ} (h : ptPosOK n Fl pos = true) :
    PtList n Fl ∧ ∀ i < Fl.size, pos[Fl[i]!]! = i := by
  have hi : ∀ i < Fl.size, Fl[i]! < n ∧ pos[Fl[i]!]! = i := fun i hi => by
    have := allLt_spec h hi
    simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  refine ⟨⟨fun i h' => (hi i h').1, fun i h₁ j h₂ e => ?_⟩, fun i h' => (hi i h').2⟩
  rw [← (hi i h₁).2, ← (hi j h₂).2, e]

theorem labListsOK_spec {n : ℕ} {Ls : List (Array ℕ)} {lab : Array ℕ} {pos : List (Array ℕ)}
    (h : labListsOK n Ls lab pos = true) :
    (∀ x : Fin n, lab[(x : ℕ)]! < Ls.length) ∧
    ∀ k < Ls.length, ∀ x : Fin n, x ∈ ptSet n (Ls.getD k #[]) ↔ lab[(x : ℕ)]! = k := by
  simp only [labListsOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hx : ∀ x : Fin n, lab[(x : ℕ)]! < Ls.length ∧
      (pos.getD lab[(x : ℕ)]! #[])[(x : ℕ)]! < (Ls.getD lab[(x : ℕ)]! #[]).size ∧
      (Ls.getD lab[(x : ℕ)]! #[])[(pos.getD lab[(x : ℕ)]! #[])[(x : ℕ)]!]! = x := fun x => by
    have := allLt_spec h2 x.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨fun x => (hx x).1, fun k hk x => ⟨?_, ?_⟩⟩
  · rintro ⟨i, hi, hix⟩
    have := allLt_spec (allLt_spec h1 hk) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    rw [← hix]
    exact this.2
  · intro hlab
    obtain ⟨-, h3, h4⟩ := hx x
    rw [hlab] at h3 h4
    exact ⟨_, h3, h4⟩

theorem genSubgroup_pair {n : ℕ} (g₀ g₁ : Equiv.Perm (Fin n)) :
    genSubgroup n 2 (fun k => [g₀, g₁].getD k 1) = Subgroup.closure {g₀, g₁} := by
  unfold genSubgroup
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem rep_ruCPair : ∀ k < #[ruC0A, ruC1A].size,
    Rep 4060 #[ruC0A, ruC1A][k]! ((fun k => [ruC0, ruC1].getD k 1) k) := by
  intro k hk
  exact rep_pair_getD rep_ruC0 rep_ruC1 k hk

theorem rep_ruNsPair' : ∀ k < #[ruNs0A, ruNs1A].size,
    Rep 4060 #[ruNs0A, ruNs1A][k]! ((fun k => [ruNs0, ruNs1].getD k 1) k) := by
  intro k hk
  exact rep_ruNsPair k hk

theorem ruCOrbits_getD {k : ℕ} (hk : k < 4) : ruCOrbits.getD k #[] = ruCOrbit k := by
  simp [ruCOrbits, List.getD_eq_getElem?_getD, hk]

theorem ruNOrbits_getD {k : ℕ} (hk : k < 3) : ruNOrbits.getD k #[] = ruNOrbit k := by
  simp [ruNOrbits, List.getD_eq_getElem?_getD, hk]

theorem ruF_size : ruF.size = 1920 := by
  simp only [ruF, ruPtList, Array.size_ofFn]
  decide

theorem ruY_size : ruY.size = 80 := by
  simp only [ruY, ruPtList, Array.size_ofFn]
  decide

theorem rep_finCongr {m m' : ℕ} (hm : m = m') {t : Array ℕ} {g : Equiv.Perm (Fin m)}
    (h : Rep m t g) : Rep m' t (Equiv.permCongrHom (finCongr hm) g) := by
  subst hm
  intro x
  rw [h x]
  rfl

end CFSG.Sporadic.RuSchreier
