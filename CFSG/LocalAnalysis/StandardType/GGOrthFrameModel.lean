module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth
import CFSG.LocalAnalysis.StandardType.GGOrthFrameModelAux

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth

theorem TBJOmData.mem_reflFixed_iff {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {i j : Fin r} {w : V ≃ₗ[K] V}
    (hw : ∀ f : Fin r → Multiplicative (ZMod p), w * Δ.τ f * w⁻¹ = Δ.τ (permAut (Equiv.swap i j) f))
    (t : V ≃ₗ[K] V) : t ∈ Δ.reflFixed i j ↔ t ∈ A ∧ w * t = t * w := by
  constructor
  · intro ht
    rw [TBJOmData.reflFixed] at ht
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp ht
    refine ⟨?_, ?_⟩
    · exact le_of_eq Δ.τ_range (MonoidHom.mem_range.mpr ⟨f, rfl⟩)
    · have hfa : f i = f j := (ggOFM_mem_reflFixedCoord_iff f).mp hf
      have hfix : SpCoord.permAut (Equiv.swap i j) f = f :=
        ggOFM_permAut_swap_eq_self_of_eq hfa
      have h1 : w * Δ.τ f * w⁻¹ = Δ.τ f := by rw [hw f, hfix]
      exact (mul_inv_eq_iff_eq_mul).mp h1
  · rintro ⟨ht, hcomm⟩
    rw [← Δ.τ_range] at ht
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp ht
    rw [TBJOmData.reflFixed]
    refine Subgroup.mem_map.mpr ⟨f, ?_, rfl⟩
    have h1 : w * Δ.τ f * w⁻¹ = Δ.τ f := (mul_inv_eq_iff_eq_mul).mpr hcomm
    have h2 : Δ.τ (SpCoord.permAut (Equiv.swap i j) f) = Δ.τ f := by rw [← hw f, h1]
    have hfix : SpCoord.permAut (Equiv.swap i j) f = f := Δ.τ_inj h2
    exact (ggOFM_mem_reflFixedCoord_iff f).mpr (ggOFM_eq_of_permAut_swap_eq_self hfix)

theorem TBJOmData.mem_reflFixedPos_iff {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {i j : Fin r} (hij : i ≠ j)
    {w : V ≃ₗ[K] V}
    (hw : ∀ f : Fin r → Multiplicative (ZMod p),
      w * Δ.τ f * w⁻¹ = Δ.τ (dinv i j (permAut (Equiv.swap i j) f))) (t : V ≃ₗ[K] V) :
    t ∈ Δ.reflFixedPos i j ↔ t ∈ A ∧ w * t = t * w := by
  constructor
  · intro ht
    rw [TBJOmData.reflFixedPos] at ht
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp ht
    refine ⟨?_, ?_⟩
    · exact le_of_eq Δ.τ_range (MonoidHom.mem_range.mpr ⟨f, rfl⟩)
    · have hfa : f i * f j = 1 := (ggOFM_mem_reflFixedCoordPos_iff f).mp hf
      have hfix : NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f) = f :=
        (ggOFM_dinv_permAut_eq_self_iff hij f).mpr hfa
      have h1 : w * Δ.τ f * w⁻¹ = Δ.τ f := by rw [hw f, hfix]
      exact (mul_inv_eq_iff_eq_mul).mp h1
  · rintro ⟨ht, hcomm⟩
    rw [← Δ.τ_range] at ht
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp ht
    rw [TBJOmData.reflFixedPos]
    refine Subgroup.mem_map.mpr ⟨f, ?_, rfl⟩
    have h1 : w * Δ.τ f * w⁻¹ = Δ.τ f := (mul_inv_eq_iff_eq_mul).mpr hcomm
    have h2 : Δ.τ (NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f)) = Δ.τ f := by
      rw [← hw f, h1]
    have hfix : NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f) = f := Δ.τ_inj h2
    exact (ggOFM_mem_reflFixedCoordPos_iff f).mpr
      ((ggOFM_dinv_permAut_eq_self_iff hij f).mp hfix)

theorem TBJOmData.swap_sq_comm {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {i j : Fin r} {w : V ≃ₗ[K] V}
    (hw : ∀ f : Fin r → Multiplicative (ZMod p), w * Δ.τ f * w⁻¹ = Δ.τ (permAut (Equiv.swap i j) f))
    (t : V ≃ₗ[K] V) (ht : t ∈ A) : w * w * t = t * (w * w) := by
  rw [← Δ.τ_range] at ht
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp ht
  have hperm : SpCoord.permAut (Equiv.swap i j) (SpCoord.permAut (Equiv.swap i j) f) = f := by
    funext x
    rw [SpCoord.permAut_apply, SpCoord.permAut_apply, Function.comp_apply, Function.comp_apply,
      Equiv.swap_inv, Equiv.swap_apply_self]
  have hmain : w * w * Δ.τ f * (w * w)⁻¹ = Δ.τ f := by
    calc
      w * w * Δ.τ f * (w * w)⁻¹ = w * (w * Δ.τ f * w⁻¹) * w⁻¹ := by group
      _ = w * Δ.τ (SpCoord.permAut (Equiv.swap i j) f) * w⁻¹ := by rw [hw f]
      _ = Δ.τ (SpCoord.permAut (Equiv.swap i j) (SpCoord.permAut (Equiv.swap i j) f)) :=
        hw (SpCoord.permAut (Equiv.swap i j) f)
      _ = Δ.τ f := by rw [hperm]
  exact (mul_inv_eq_iff_eq_mul).mp hmain

theorem TBJOmData.pos_sq_comm {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {i j : Fin r} (hij : i ≠ j)
    {w : V ≃ₗ[K] V}
    (hw : ∀ f : Fin r → Multiplicative (ZMod p),
      w * Δ.τ f * w⁻¹ = Δ.τ (dinv i j (permAut (Equiv.swap i j) f)))
    (t : V ≃ₗ[K] V) (ht : t ∈ A) : w * w * t = t * (w * w) := by
  rw [← Δ.τ_range] at ht
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp ht
  have hperm : NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j)
      (NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f))) = f :=
    ggOFM_dinv_permAut_dinv_permAut hij f
  have hmain : w * w * Δ.τ f * (w * w)⁻¹ = Δ.τ f := by
    calc
      w * w * Δ.τ f * (w * w)⁻¹ = w * (w * Δ.τ f * w⁻¹) * w⁻¹ := by group
      _ = w * Δ.τ (NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f)) * w⁻¹ := by
        rw [hw f]
      _ = Δ.τ (NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j)
            (NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f)))) :=
        hw (NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f))
      _ = Δ.τ f := by rw [hperm]
  exact (mul_inv_eq_iff_eq_mul).mp hmain

theorem TBJOmData.card_reflFixed {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    [Fact p.Prime] {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {i j : Fin r}
    (hij : i ≠ j) : Nat.card ↥(Δ.reflFixed i j) * p = Nat.card ↥A := by
  have hcoord := ggOFM_card_reflFixedCoord (p := p) (r := r) (i := i) (j := j) hij
  have hmap := ggOFM_card_reflFixed (Δ := Δ) i j
  have hA : Nat.card ↥A = p ^ r := by
    rw [← Δ.τ_range]
    rw [(Nat.card_congr (MonoidHom.ofInjective (f := Δ.τ) Δ.τ_inj).toEquiv).symm,
      ggTBJSpC_card_coord p r]
  calc
    Nat.card ↥(Δ.reflFixed i j) * p = Nat.card ↥(reflFixedCoord p r i j) * p := by rw [hmap]
    _ = p ^ r := hcoord
    _ = Nat.card ↥A := hA.symm

theorem TBJOmData.card_reflFixedPos {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    [Fact p.Prime] {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {i j : Fin r}
    (hij : i ≠ j) : Nat.card ↥(Δ.reflFixedPos i j) * p = Nat.card ↥A := by
  have hcoord := ggOFM_card_reflFixedCoordPos (p := p) (r := r) (i := i) (j := j) hij
  have hmap := ggOFM_card_reflFixedPos (Δ := Δ) i j
  have hA : Nat.card ↥A = p ^ r := by
    rw [← Δ.τ_range]
    rw [(Nat.card_congr (MonoidHom.ofInjective (f := Δ.τ) Δ.τ_inj).toEquiv).symm,
      ggTBJSpC_card_coord p r]
  calc
    Nat.card ↥(Δ.reflFixedPos i j) * p = Nat.card ↥(reflFixedCoordPos p r i j) * p := by
      rw [hmap]
    _ = p ^ r := hcoord
    _ = Nat.card ↥A := hA.symm

end OrthTorus

end CFSG.StandardType

end
