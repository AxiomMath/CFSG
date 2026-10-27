module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Syl
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Over
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Self

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Orbit CFSG.Quasithin.H13.U3.GC137.S2

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem g2FactsAt_of (ρ : Gam →* MulAut W) (hρ : Function.Injective ρ)
    (hrk : rkIdx (fixV ((g2Derived (ZMod 2)).map ρ)) = 6)
    (hnoOff : ∀ B : Subgroup (MulAut W), B ≤ (g2Derived (ZMod 2)).map ρ → B ≠ ⊥ →
      IsElemAbelian2 B → Nat.card W ≤ Nat.card ↥B * Nat.card ↥(fixV B) → False)
    (hline : ∃ l₀ : Subgroup W, fixV ((g2Derived (ZMod 2)).map ρ) ≤ l₀ ∧
      Nat.card ↥l₀ = 4 * Nat.card ↥(fixV ((g2Derived (ZMod 2)).map ρ)) ∧
      ∀ g ∈ Pline, ∀ w ∈ l₀, ρ g w ∈ l₀)
    (hpoint : G2Point ρ.range ((g2Derived (ZMod 2)).map ρ) (Ppt.map ρ)) :
    G2FactsAt ρ.range ((g2Derived (ZMod 2)).map ρ) (sSubG.map ρ) := by
  have hcard : Nat.card ↥ρ.range = 12096 :=
    (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm.trans card_g2Two
  refine ⟨hcard, hrk, hnoOff, ?_, ?_⟩
  · rintro x ⟨⟨y, rfl⟩, hxN⟩
    have hy : y ∈ normalizer (sSubG : Set Gam) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        obtain ⟨s', hs', he⟩ := (Subgroup.mem_normalizer_iff.1 hxN (ρ s)).1 ⟨s, hs, rfl⟩
        have : y * s * y⁻¹ = s' := hρ (by rw [he]; simp)
        rw [this]
        exact hs'
      · intro hs
        have h1 : ρ y * ρ s * (ρ y)⁻¹ ∈ sSubG.map ρ := ⟨_, hs, by simp⟩
        have h2 := (Subgroup.mem_normalizer_iff.1 hxN (ρ s)).2 h1
        exact (Subgroup.mem_map_iff_mem hρ).1 h2
    exact ⟨y, normalizer_S_le hy, rfl⟩
  · intro P hSP hPX hPne hmax
    set Q : Subgroup Gam := P.comap ρ with hQ
    have hPQ : Q.map ρ = P := Subgroup.map_comap_eq_self hPX
    have hSQ : sSubG ≤ Q := fun s hs => hSP ⟨s, hs, rfl⟩
    have hQne : Q ≠ ⊤ := by
      intro h0
      apply hPne
      rw [← hPQ, h0, ← MonoidHom.range_eq_map]
    rcases overgroup hSQ hQne with hQP | hQL
    · right
      have hle : P ≤ Ppt.map ρ := by
        rw [← hPQ]
        exact Subgroup.map_mono hQP
      have hX : Ppt.map ρ ≤ ρ.range := Subgroup.map_le_range _ _
      rcases hmax _ hle hX with h0 | h0
      · rw [← h0]
        exact hpoint
      · exfalso
        have h1 := congrArg (fun H : Subgroup (MulAut W) => Nat.card ↥H) h0
        simp only [Subgroup.card_map_of_injective hρ, card_Ppt, hcard] at h1
        omega
    · left
      obtain ⟨l₀, h1, h2, h3⟩ := hline
      refine ⟨l₀, h1, h2, fun φ hφ w hw => ?_⟩
      rw [← hPQ] at hφ
      obtain ⟨g, hg, rfl⟩ := hφ
      exact h3 g (hQL hg) w hw

end CFSG.Quasithin.H13.U3.GC137
