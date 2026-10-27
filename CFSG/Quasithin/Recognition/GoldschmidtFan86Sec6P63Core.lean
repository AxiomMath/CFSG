module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62DCin

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P63

theorem exists_core_run (ℓ : Line Γ) {P : ℤ → Prop} {z : G} {tL tR i : ℤ}
    (hfix : ∀ k, k ∈ ℓ.fixIdx z ↔ tL ≤ k ∧ k ≤ tR)
    (hP : ∀ k, P k → k ∈ ℓ.fixIdx z ∧ k + 1 ∈ ℓ.fixIdx z) (hi : P i) :
    ∃ a b : ℤ, a ≤ i ∧ i < b ∧ ℓ.IsCoreWith P z a b := by
  classical
  have hiL : tL ≤ i := ((hfix i).1 (hP i hi).1).1
  have hiR : i + 1 ≤ tR := ((hfix (i + 1)).1 (hP i hi).2).2
  obtain ⟨a, ⟨ha1, ha2, ha3⟩, hamin⟩ := Int.exists_least_of_bdd
    (P := fun a => tL ≤ a ∧ a ≤ i ∧ ∀ k, a ≤ k → k ≤ i → P k)
    ⟨tL, fun a ha => ha.1⟩ ⟨i, hiL, le_rfl, fun k h1 h2 => by
      have : k = i := le_antisymm h2 h1
      rwa [this]⟩
  obtain ⟨b, ⟨hb1, hb2, hb3⟩, hbmax⟩ := Int.exists_greatest_of_bdd
    (P := fun b => i < b ∧ b ≤ tR ∧ ∀ k, i ≤ k → k < b → P k)
    ⟨tR, fun b hb => hb.2.1⟩ ⟨i + 1, by omega, hiR, fun k h1 h2 => by
      have : k = i := by omega
      rwa [this]⟩
  refine ⟨a, b, ha2, hb1, by omega, fun k h1 h2 => (hfix k).2 ⟨by omega, by omega⟩,
    fun k h1 h2 => ?_, ?_, ?_⟩
  · by_cases hk : k ≤ i
    · exact ha3 k h1 hk
    · exact hb3 k (by omega) h2
  · rintro ⟨h1, h2⟩
    have := hamin (a - 1) ⟨((hfix _).1 h1).1, by omega, fun k hk1 hk2 => by
      by_cases hk : k = a - 1
      · rw [hk]; exact h2
      · exact ha3 k (by omega) hk2⟩
    omega
  · rintro ⟨h1, h2⟩
    have := hbmax (b + 1) ⟨by omega, ((hfix _).1 (hP b h2).2).2, fun k hk1 hk2 => by
      by_cases hk : k = b
      · rw [hk]; exact h2
      · exact hb3 k hk1 (by omega)⟩
    omega

theorem cinv_core (F : FanTree Γ G) (h40 : Fan40 F) (h62 : Fan62 F) {T : Track Γ G}
    (hT : InXi T) {c : ℤ} {w : G} (hw : w ∈ Cinv G (T.line.vert c)) :
    w ∈ T.line.ZZ ∧ T.line.IsCore w (c - 1) (c + 1) ∧
      ∀ i : ℤ, w • T.line.vert i = T.line.vert i ↔ c - 4 ≤ i ∧ i ≤ c + 4 := by
  have hK : w ∈ nbrStab Γ G (T.line.vert c) := cinv_mem_nbrStab F hw
  obtain ⟨hw1, hw2, hwS, hwc⟩ := hw
  have hwc' : w • T.line.vert c = T.line.vert c := MulAction.mem_stabilizer_iff.1 hwS
  have hwR : w • T.line.vert (c + 1) = T.line.vert (c + 1) := mem_nbrStab.1 hK _ (T.line.adj c)
  have hwL : w • T.line.vert (c - 1) = T.line.vert (c - 1) := mem_nbrStab.1 hK _
    (T.line.adj_pred c)
  have hcenR : w ∈ Cen (T.line.edgeStab (G := G) c : Set G) :=
    ⟨⟨MulAction.mem_stabilizer_iff.2 hwc', MulAction.mem_stabilizer_iff.2 hwR⟩,
      fun h hh => hwc h hh.1⟩
  have hcenL : w ∈ Cen (T.line.edgeStab (G := G) (c - 1) : Set G) := by
    have e : T.line.vert (c - 1 + 1) = T.line.vert c := by rw [show c - 1 + 1 = c by omega]
    refine ⟨⟨MulAction.mem_stabilizer_iff.2 hwL, MulAction.mem_stabilizer_iff.2 ?_⟩,
      fun h hh => hwc h ?_⟩
    · rw [e]
      exact hwc'
    · have := hh.2
      rwa [e] at this
  have hZZ : w ∈ T.line.ZZ := ⟨hw2, c, hcenR⟩
  obtain ⟨⟨a₀, b₀, tL, tR, hfx⟩, hall⟩ := h62 h40 T hT w hZZ hw1
  have hP : ∀ k, w ∈ Cen (T.line.edgeStab (G := G) k : Set G) →
      k ∈ T.line.fixIdx w ∧ k + 1 ∈ T.line.fixIdx w := fun k hk =>
    ⟨MulAction.mem_stabilizer_iff.1 hk.1.1, MulAction.mem_stabilizer_iff.1 hk.1.2⟩
  obtain ⟨a, b, hac, hcb, hcore⟩ := exists_core_run T.line (P := fun i => w ∈ Cen
    (T.line.edgeStab (G := G) i : Set G)) hfx.fix hP hcenR
  have hcf : T.line.IsCoreFix w a b tL tR := ⟨hfx.fix, hcore⟩
  obtain ⟨hba, hrb, hal⟩ := hall a b tL tR hcf
  have hac' : a ≤ c - 1 := by
    by_contra hlt
    have hac2 : a = c := by omega
    apply hcore.2.2.2.1
    rw [show a - 1 = c - 1 by omega]
    exact ⟨hwL, hcenL⟩
  have ha : a = c - 1 := by omega
  have hb : b = c + 1 := by omega
  subst ha hb
  refine ⟨hZZ, hcore, fun i => ?_⟩
  have := hfx.fix i
  rw [show c - 4 = c - 1 - 3 by omega, show c + 4 = c + 1 + 3 by omega]
  have e1 : tL = c - 1 - 3 := by omega
  have e2 : tR = c + 1 + 3 := by omega
  rw [← e1, ← e2]
  exact this

end P63

end CFSG.Quasithin.Fan86
