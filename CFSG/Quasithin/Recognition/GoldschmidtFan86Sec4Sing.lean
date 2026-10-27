module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Max
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem IsMaxTArc.omega1_left (F : FanTree Γ G) (h40 : Fan40 F) {a b : ℤ}
    (h : IsMaxTArc T a b) : omega1 (T.subFixer (a - 1) b) ≤ T.fixer := by
  by_contra hc
  have := ((fan42_2b T F h40 a b).1 h).2 (a - 1) b (by omega) le_rfl
    ⟨by have := h.1.1; omega, hc⟩
  omega

theorem IsMaxTArc.omega1_right (F : FanTree Γ G) (h40 : Fan40 F) {a b : ℤ}
    (h : IsMaxTArc T a b) : omega1 (T.subFixer a (b + 1)) ≤ T.fixer := by
  by_contra hc
  have := ((fan42_2b T F h40 a b).1 h).2 a (b + 1) le_rfl (by omega)
    ⟨by have := h.1.1; omega, hc⟩
  omega

theorem fan44_1 (F : FanTree Γ G) (h40 : Fan40 F) (hne : T.fixer ≠ ⊥) (hrc : ReflClosed T)
    {a b : ℤ} (hmax : IsMaxTArc T a b) :
    omega1 (T.subFixer a (b - 1)) ≤ MulAction.stabilizer G (T.line.vert b) ∧
      omega1 (T.subFixer (a + 1) b) ≤ MulAction.stabilizer G (T.line.vert a) := by
  have hT := hmax.1
  have hev := fan_4_3_2 T F ⟨hne, hrc⟩ hT
  have hab := hT.1
  have hL := hmax.omega1_left T F h40
  have hR := hmax.omega1_right T F h40
  have notT1 : ¬ IsTArc T a (b - 1) := fun h => by
    have := fan_4_3_2 T F ⟨hne, hrc⟩ h
    omega
  have notT2 : ¬ IsTArc T (a + 1) b := fun h => by
    have := fan_4_3_2 T F ⟨hne, hrc⟩ h
    omega
  constructor
  · have h3 : omega1 (T.subFixer (a - 1) (b - 1 + 1)) ≤ T.fixer := by
      rwa [show b - 1 + 1 = b by omega]
    have hcases : omega1 (T.subFixer a (b - 1)) ≤ T.subFixer (a - 1) (b - 1) ∨
        omega1 (T.subFixer a (b - 1)) ≤ T.subFixer a (b - 1 + 1) := by
      by_contra hcon
      push Not at hcon
      exact notT1 ⟨by omega, hcon.1, hcon.2, h3⟩
    rcases hcases with h1 | h1
    · exfalso
      refine hT.2.1 fun y hy => ?_
      have hy1 : y ∈ omega1 (T.subFixer a (b - 1)) :=
        omega1_mono (T.subFixer_anti le_rfl (by omega)) hy
      have hy2 := h1 hy1
      have hyb : y ∈ T.subFixer a b := omega1_le _ hy
      refine (T.mem_subFixer).2 fun i hi1 hi2 => ?_
      by_cases hib : i ≤ b - 1
      · exact (T.mem_subFixer).1 hy2 i hi1 hib
      · exact (T.mem_subFixer).1 hyb i (by omega) hi2
    · intro y hy
      have := h1 hy
      rw [show b - 1 + 1 = b by omega] at this
      exact MulAction.mem_stabilizer_iff.2 ((T.mem_subFixer).1 this b hab.le le_rfl)
  · have h3 : omega1 (T.subFixer (a + 1 - 1) (b + 1)) ≤ T.fixer := by
      rwa [show a + 1 - 1 = a by omega]
    have hcases : omega1 (T.subFixer (a + 1) b) ≤ T.subFixer (a + 1 - 1) b ∨
        omega1 (T.subFixer (a + 1) b) ≤ T.subFixer (a + 1) (b + 1) := by
      by_contra hcon
      push Not at hcon
      exact notT2 ⟨by omega, hcon.1, hcon.2, h3⟩
    rcases hcases with h1 | h1
    · intro y hy
      have := h1 hy
      rw [show a + 1 - 1 = a by omega] at this
      exact MulAction.mem_stabilizer_iff.2 ((T.mem_subFixer).1 this a le_rfl hab.le)
    · exfalso
      refine hT.2.2.1 fun y hy => ?_
      have hy1 : y ∈ omega1 (T.subFixer (a + 1) b) :=
        omega1_mono (T.subFixer_anti (by omega) le_rfl) hy
      have hy2 := h1 hy1
      have hya : y ∈ T.subFixer a b := omega1_le _ hy
      refine (T.mem_subFixer).2 fun i hi1 hi2 => ?_
      by_cases hia : a + 1 ≤ i
      · exact (T.mem_subFixer).1 hy2 i hia hi2
      · exact (T.mem_subFixer).1 hya i hi1 (by omega)

theorem fan44_2 (F : FanTree Γ G) (h40 : Fan40 F) (hne : T.fixer ≠ ⊥) (hrc : ReflClosed T)
    {a b : ℤ} (hmax : IsMaxTArc T a b) :
    T.subFixer a (b - 1) ≤ MulAction.stabilizer G (T.line.vert b) ∨
      T.subFixer (a + 1) b ≤ MulAction.stabilizer G (T.line.vert a) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hT := hmax.1
  have hq := hT.isQuasi T
  have hev := fan_4_3_2 T F ⟨hne, hrc⟩ hT
  have hab := hT.1
  have hL := hmax.omega1_left T F h40
  have hR := hmax.omega1_right T F h40
  have q1 : IsQuasiTArc T a (b - 1) := by
    refine ⟨by omega, fun hle => hq.2.1 fun g hg => ?_, fun hle => hc1 fun g hg => ?_, ?_⟩
    · have h1 := hle (T.subFixer_anti (a := a) (b := b - 1) le_rfl (by omega) hg)
      refine (T.mem_subFixer).2 fun i hi1 hi2 => ?_
      by_cases hib : i ≤ b - 1
      · exact (T.mem_subFixer).1 h1 i hi1 hib
      · exact (T.mem_subFixer).1 hg i (by omega) hi2
    · have h1 := hle hg
      rw [show b - 1 + 1 = b by omega] at h1
      exact MulAction.mem_stabilizer_iff.2 ((T.mem_subFixer).1 h1 b hab.le le_rfl)
    · rwa [show b - 1 + 1 = b by omega]
  have q2 : IsQuasiTArc T (a + 1) b := by
    refine ⟨by omega, fun hle => hc2 fun g hg => ?_, fun hle => hq.2.2.1 fun g hg => ?_, ?_⟩
    · have h1 := hle hg
      rw [show a + 1 - 1 = a by omega] at h1
      exact MulAction.mem_stabilizer_iff.2 ((T.mem_subFixer).1 h1 a le_rfl hab.le)
    · have h1 := hle (T.subFixer_anti (a := a + 1) (b := b) (by omega) le_rfl hg)
      refine (T.mem_subFixer).2 fun i hi1 hi2 => ?_
      by_cases hia : a + 1 ≤ i
      · exact (T.mem_subFixer).1 h1 i hia hi2
      · exact (T.mem_subFixer).1 hg i hi1 (by omega)
    · rwa [show a + 1 - 1 = a by omega]
  rcases fan_4_3_1 T F hne q1 q2 with hk | hk
  · rw [T.exists_zpow_smul_iff F.isTree] at hk
    omega
  · rw [T.exists_zpow_smul_iff F.isTree] at hk
    omega

theorem Track.mem_stabRange_arc {a : ℤ} {k : ℕ} {g : G} :
    g ∈ stabRange G (T.line.arc a k).vert 0 k ↔ g ∈ T.subFixer (a) (a + k) := by
  rw [mem_stabRange, T.mem_subFixer]
  constructor
  · intro h i h1 h2
    have := h (i - a).toNat (Nat.zero_le _) (by omega)
    have e : a + ((i - a).toNat : ℤ) = i := by omega
    simp only [Line.arc] at this
    rwa [e] at this
  · intro h m _ hm
    simpa [Line.arc] using h (a + m) (by omega) (by omega)

theorem fan44_3 (F : FanTree Γ G) (h40 : Fan40 F) (hne : T.fixer ≠ ⊥) (hrc : ReflClosed T)
    {a b : ℤ} (hmax : IsMaxTArc T a b) : LineSingLe Γ G T.line (b - a - 1).toNat := by
  have hev := fan_4_3_2 T F ⟨hne, hrc⟩ hmax.1
  have hab := hmax.1.1
  have hk : (((b - a - 1).toNat : ℕ) : ℤ) = b - a - 1 := by omega
  rcases fan44_2 T F h40 hne hrc hmax with h | h
  · refine ⟨(b - a - 1).toNat, a, by omega, le_rfl, Or.inl ⟨T.line.vert b, ?_, ?_, ?_⟩⟩
    · have e : a + (((b - a - 1).toNat : ℕ) : ℤ) = b - 1 := by omega
      have := T.line.adj (b - 1)
      rw [show b - 1 + 1 = b by omega] at this
      show Γ.Adj (T.line.vert (a + (((b - a - 1).toNat : ℕ) : ℤ))) (T.line.vert b)
      rwa [e]
    · have := T.line.nb (b - 2)
      simp only [Line.arc]
      rw [show a + (((b - a - 1).toNat - 1 : ℕ) : ℤ) = b - 2 by omega]
      rw [show b - 2 + 2 = b by omega] at this
      exact this.symm
    · intro g hg
      have hg' := T.mem_stabRange_arc.1 hg
      rw [hk, show a + (b - a - 1) = b - 1 by omega] at hg'
      exact MulAction.mem_stabilizer_iff.1 (h hg')
  · refine ⟨(b - a - 1).toNat, a + 1, by omega, le_rfl, Or.inr ⟨T.line.vert a, ?_, ?_, ?_⟩⟩
    · simpa [Line.arc] using T.adj_pred (a + 1)
    · have := T.line.nb a
      simpa [Line.arc, show a + 1 + 1 = a + 2 by omega] using this
    · intro g hg
      have hg' := T.mem_stabRange_arc.1 hg
      rw [hk, show a + 1 + (b - a - 1) = b by omega] at hg'
      exact MulAction.mem_stabilizer_iff.1 (h hg')

end CFSG.Quasithin.Fan86
