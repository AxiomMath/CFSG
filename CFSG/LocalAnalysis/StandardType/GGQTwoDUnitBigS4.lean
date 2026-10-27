module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS2
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS3

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.RankThree.Classical

theorem qtwoDB44_core {m : ℕ} (hm : 6 ≤ m) {c : Fin m}
    (τ : Multiplicative (DVec m) →* StatedSp (m - 1) (ZMod 2))
    (hτker : ∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0)
    (hsc : ∀ z : StatedSp (m - 1) (ZMod 2),
      (∀ v : DVec m, z * τ (Multiplicative.ofAdd v) = τ (Multiplicative.ofAdd v) * z) →
        z ^ 3 = 1 → z ∈ τ.range)
    (hW : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : StatedSp (m - 1) (ZMod 2),
      ∀ v : DVec m, y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v))) :
    ∃ Q : QuadraticForm (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) → ZMod 2),
      (∀ x y, QuadraticMap.polar Q x y = spForm (m - 1) (ZMod 2) x y) ∧
      (qtwoDB44_IsPlus Q ↔ Even (m - 1)) ∧
      (∀ v : DVec m, ∀ x, Q (spEnd (τ (Multiplicative.ofAdd v)) x) = Q x) ∧
      (∀ u : DVec m, (∀ i, i ≠ c → u i ≠ 0) → ∀ y : StatedSp (m - 1) (ZMod 2),
        y * τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd u) * y →
        ∀ x, Q (spEnd y x) = Q x) := by
  classical
  have h3 : ∀ u : DVec m, (Multiplicative.ofAdd u : Multiplicative (DVec m)) ^ 3 = 1 := by
    intro u
    have h3v : (3 : ℕ) • u = 0 := by
      ext i
      show (3 : ℕ) • (u i) = (0 : ZMod 3)
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3 (u i), smul_eq_zero]
      exact Or.inl (by decide)
    change Multiplicative.ofAdd ((3 : ℕ) • u) = (1 : Multiplicative (DVec m))
    rw [h3v]
    rfl
  have hE : IsElemAbelian 3 τ.range := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, rfl⟩ := (Multiplicative.ofAdd : DVec m ≃ Multiplicative (DVec m)).surjective w
    rw [← map_pow, h3 u, map_one]
  have hsc' : ∀ Z : StatedSp (m - 1) (ZMod 2), (∀ Y ∈ τ.range, Z * Y = Y * Z) →
      Z ^ 3 = 1 → Z ∈ τ.range := fun Z hZ hZ3 =>
    hsc Z (fun v => hZ _ ⟨_, rfl⟩) hZ3
  obtain ⟨⟨L, hLf, hLa, hLfin, ζ, F, hL, hζ, hs⟩, -, -, -⟩ :=
    FrameRoute.exists_spFrame_of_selfCent_two (K := ZMod 2) (Nat.card_zmod 2) hE hsc'
  letI := hLf
  letI := hLa
  letI := hLfin
  obtain ⟨Q, hQ, hplus, hinv⟩ := qtwoDB44_frameQ (n := m - 1) (by omega) hL hζ F hs
  have hinvτ : ∀ v : DVec m, ∀ x, Q (spEnd (τ (Multiplicative.ofAdd v)) x) = Q x := by
    intro v x
    obtain ⟨f, hf⟩ := F.mem_tor (τ (Multiplicative.ofAdd v)) ⟨_, rfl⟩
    rw [← hf]
    exact hinv f x
  refine ⟨Q, hQ, hplus, hinvτ, ?_⟩
  intro u hu y hy
  exact qtwoDB44_centralizer_preserves hQ (qtwoDB44_generic_fixed hm hζ τ hτker hW F hs hu)
    (hinvτ u) hy

end CFSG.StandardType.QTwo

end
