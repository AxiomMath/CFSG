module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel

theorem ggE8_inner_model
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.E8, 0, n⟩) (hinn : GGInnerDiagOn Bs X)
    (hlab : GGHasLabel ⟨.E8, 0, n⟩ (↥X ⧸ Subgroup.center ↥X)) {g : G} (hg : g ∈ Bs)
    (hgp : g ^ p = 1) (n' : ℕ) :
    ∃ (e : ↥X ≃* GGKb .E8 n' n) (c : GGKb .E8 n' n), c ^ p = 1 ∧
      g ∈ Subgroup.normalizer (X : Set G) ∧
      ∀ l l' : ↥X, (l' : G) = g * l * g⁻¹ → e l' = c * e l * c⁻¹ := by
  classical
  obtain ⟨K, _instK, _finK, _charK, hKcard, e₀, hZ, hBsN, hinner⟩ :=
    ggMaxRank_model hRig hΛ hinn hlab
  obtain ⟨x, hxX, hxconj⟩ := hinner g hg
  have hz_comm : ∀ y ∈ X, (x : G)⁻¹ * g * y = y * ((x : G)⁻¹ * g) := by
    intro y hy
    have h := hxconj y hy
    calc (x : G)⁻¹ * g * y
        = (x : G)⁻¹ * (g * y * g⁻¹) * g := by group
      _ = (x : G)⁻¹ * (x * y * x⁻¹) * g := by rw [h]
      _ = y * ((x : G)⁻¹ * g) := by group
  have hxzp : (x : G) ^ p * ((x : G)⁻¹ * g) ^ p = 1 := by
    have hcx : Commute (x : G) ((x : G)⁻¹ * g) := (hz_comm x hxX).symm
    have hxg : (x : G) * ((x : G)⁻¹ * g) = g := by group
    rw [← hcx.mul_pow p, hxg]
    exact hgp
  have hxpowG : (x : G) ^ p = (((x : G)⁻¹ * g) ^ p)⁻¹ := by
    calc (x : G) ^ p
        = (x : G) ^ p * ((x : G)⁻¹ * g) ^ p
            * (((x : G)⁻¹ * g) ^ p)⁻¹ := by group
      _ = 1 * (((x : G)⁻¹ * g) ^ p)⁻¹ := by rw [hxzp]
      _ = (((x : G)⁻¹ * g) ^ p)⁻¹ := by group
  have hxpow_center : (⟨x, hxX⟩ : ↥X) ^ p ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : G) * (x : G) ^ p = (x : G) ^ p * (y : G)
    rw [hxpowG]
    have hcy : Commute ((x : G)⁻¹ * g) (y : G) := hz_comm (y : G) y.2
    exact (Commute.inv_left (hcy.pow_left p)).symm
  have hxpow : (⟨x, hxX⟩ : ↥X) ^ p = 1 := by
    rw [hZ, Subgroup.mem_bot] at hxpow_center
    exact hxpow_center
  have hn1 : 1 ≤ n := hΛ.1
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let σ : K ≃+* GaloisField 2 n :=
    FiniteField.ringEquivOfCardEq (by
      have h1 : Nat.card K = Nat.card (GaloisField 2 n) := by
        rw [hKcard, GaloisField.card 2 n hn0]
      simpa only [Nat.card_eq_fintype_card] using h1)
  let e : ↥X ≃* GGKb .E8 n' n :=
    e₀.trans ((CFSG.HardMathSupport.Lang.AnisoE6.adjointGroupCongr (τ := .E8) σ).trans
      (ggKbEquivE8 n' n).symm)
  refine ⟨e, e ⟨x, hxX⟩, ?_, hBsN hg, ?_⟩
  · rw [← map_pow, hxpow, map_one]
  · intro l l' hl'
    have hle : l' = ⟨x, hxX⟩ * l * ⟨x, hxX⟩⁻¹ := by
      apply Subtype.ext
      rw [hl', hxconj l l.2]
      rfl
    rw [hle]
    simp only [map_mul, map_inv]

end CFSG.StandardType
