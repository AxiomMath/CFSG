module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51Ten

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix

private theorem pat_mA : ∀ v : V, v ≠ 0 →
    (mA (orbOf v) = true ↔ ∃ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • e i) := by
  decide +kernel

private theorem pat_mB : ∀ v : V, v ≠ 0 →
    (mB (orbOf v) = true ↔
      (∃ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • e i) ∨ ∀ i, v i ≠ 0) := by
  decide +kernel

private theorem smul_e_ne_zero {c : ZMod 3} (hc : c ≠ 0) (i : Fin 4) : c • e i ≠ 0 :=
  fun h0 => by
    have := congrFun h0 i
    simp [e, hc] at this

theorem mem_Om_of_mA {Γ : Subgroup GL4} (h : Hyp Γ)
    (hA : (cfgOf Γ).1 = mA) (v : V) :
    v ∈ Om Γ ↔ ∃ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • e i := by
  rw [mem_Om_iff_pat h hA v]
  constructor
  · rintro ⟨hv, hm⟩
    exact (pat_mA v hv).1 hm
  · intro hex
    have hv : v ≠ 0 := by
      obtain ⟨i, c, hc, rfl⟩ := hex
      exact smul_e_ne_zero hc i
    exact ⟨hv, (pat_mA v hv).2 hex⟩

theorem mem_Om_of_mB {Γ : Subgroup GL4} (h : Hyp Γ)
    (hB : (cfgOf Γ).1 = mB) (v : V) :
    v ∈ Om Γ ↔ (∃ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • e i) ∨ ∀ i, v i ≠ 0 := by
  rw [mem_Om_iff_pat h hB v]
  constructor
  · rintro ⟨hv, hm⟩
    exact (pat_mB v hv).1 hm
  · intro hex
    have hv : v ≠ 0 := by
      rcases hex with ⟨i, c, hc, rfl⟩ | hall
      · exact smul_e_ne_zero hc i
      · intro h0
        exact hall 0 (by rw [h0]; rfl)
    exact ⟨hv, (pat_mB v hv).2 hex⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.P51

end
