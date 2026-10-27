module

public import CFSG.Quasithin.Vol2.F134LieF4Group
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee

set_option linter.unusedSectionVars false

public section

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieF4
open scoped Pointwise

namespace CFSG.Quasithin.H13.NQCore.F4


theorem exists_embedding {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 f) {S : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime)
      (φ : X →* ModGL F4.tag K), 1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧
        Function.Injective φ ∧ φ.range = F4.reeGamma K a ∧
        S.map φ = F4.reeFixedPosUnipotent K a := by
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hn, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hU' : IsSylowOf 2 S ⊤ := isSylowTwoOf_iff_isSylowOf.1 hS
  have hU₀ : IsSylowOf 2 (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) :=
    isSylowOf_iff.2 ⟨reeFixedPosUnipotent_le_reeGamma,
      (isPGroup_posUnipotent 2 F4.tag).to_le inf_le_left,
      not_dvd_index_reeFixedPosUnipotent (t := F4)⟩
  set φ₀ : X →* ModGL F4.tag K := (F4.reeGamma K a).subtype.comp e.toMonoidHom with hφ₀
  have hφ₀i : Function.Injective φ₀ := Subtype.val_injective.comp e.injective
  have hφ₀r : (⊤ : Subgroup X).map φ₀ = F4.reeGamma K a := by
    rw [hφ₀, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hUφ₀ : IsSylowOf 2 (S.map φ₀) (F4.reeGamma K a) := by
    rw [← hφ₀r]
    exact isSylowOf_map_injective φ₀ hφ₀i hU'
  obtain ⟨g, hg, hgU⟩ := exists_mem_eq_map_conj_of_isSylowOf hUφ₀ hU₀
  set φ : X →* ModGL F4.tag K := (MulAut.conj g).toMonoidHom.comp φ₀ with hφ
  have hφi : Function.Injective φ := (MulAut.conj g).injective.comp hφ₀i
  have hφU : S.map φ = F4.reeFixedPosUnipotent K a := by
    rw [hφ, ← Subgroup.map_map, hgU]
  have hφr : φ.range = F4.reeGamma K a := by
    rw [MonoidHom.range_eq_map, hφ, ← Subgroup.map_map, hφ₀r]
    refine le_antisymm ?_ fun x hx => ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (F4.reeGamma K a).mul_mem ((F4.reeGamma K a).mul_mem hg hx)
        ((F4.reeGamma K a).inv_mem hg)
    · exact (F4.reeGamma K a).mul_mem ((F4.reeGamma K a).mul_mem
        ((F4.reeGamma K a).inv_mem hg) hx) hg
  exact ⟨a, K, hKF, hKFin, hcp, φ, ha, hn, hK, hφi, hφr, hφU⟩

theorem mem_normalizer_iff_mem_reeFixedBorel {X : Type} [Group X] {a : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K F4.prime] {φ : X →* ModGL F4.tag K} (hφ : Function.Injective φ)
    (hr : φ.range = F4.reeGamma K a) {S : Subgroup X}
    (hS : S.map φ = F4.reeFixedPosUnipotent K a) (x : X) :
    x ∈ Subgroup.normalizer (S : Set X) ↔ φ x ∈ F4.reeFixedBorel K a := by
  have hle : S.map φ ≤ φ.range := Subgroup.map_le_range φ S
  have h1 : (Subgroup.normalizer ((S.map φ : Subgroup (ModGL F4.tag K)) :
      Set (ModGL F4.tag K))).comap φ = Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range hle, Subgroup.comap_map_eq_self_of_injective hφ]
  rw [← h1, Subgroup.mem_comap, hS,
    ← reeGamma_inf_normalizer_reeFixedPosUnipotent (a := a) (K := K)]
  exact ⟨fun h => ⟨hr ▸ ⟨x, rfl⟩, h⟩, fun h => h.2⟩

theorem commutator_borel_mem_posUnipotent {τ : Tag} {R : Type} [Field R] {b c : ModGL τ R}
    (hb : b ∈ borelGroup τ R) (hc : c ∈ borelGroup τ R) :
    b * c * b⁻¹ * c⁻¹ ∈ posUnipotent τ R := by
  obtain ⟨hHab, -, hHN, -, hHU, -⟩ := triangular_borel_structure.{0, 0} τ R
  have hb' : b ∈ (torusGroup τ R : Set (ModGL τ R)) * (posUnipotent τ R : Set (ModGL τ R)) := by
    rw [← hHU]
    exact hb
  have hc' : c ∈ (torusGroup τ R : Set (ModGL τ R)) * (posUnipotent τ R : Set (ModGL τ R)) := by
    rw [← hHU]
    exact hc
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hb'
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := hc'
  have hconj : ∀ h ∈ torusGroup τ R, ∀ u ∈ posUnipotent τ R, h * u * h⁻¹ ∈ posUnipotent τ R :=
    fun h hh u hu => (Subgroup.mem_normalizer_iff.1 (hHN hh) u).1 hu
  have h12 : h₁ * h₂ * h₁⁻¹ = h₂ := by rw [hHab h₁ hh₁ h₂ hh₂, mul_inv_cancel_right]
  have e : h₁ * u₁ * (h₂ * u₂) * (h₁ * u₁)⁻¹ * (h₂ * u₂)⁻¹ =
      (h₁ * u₁ * h₁⁻¹) * ((h₁ * h₂) * (u₂ * u₁⁻¹) * (h₁ * h₂)⁻¹) *
        (h₁ * h₂ * h₁⁻¹ * u₂⁻¹ * h₂⁻¹) := by
    group
  rw [e, h12]
  exact mul_mem (mul_mem (hconj _ hh₁ _ hu₁)
    (hconj _ (mul_mem hh₁ hh₂) _ (mul_mem hu₂ (inv_mem hu₁)))) (hconj _ hh₂ _ (inv_mem hu₂))

theorem commutator_mem_of_mem_normalizer {X : Type} [Group X] {a : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K F4.prime] {φ : X →* ModGL F4.tag K} (hφ : Function.Injective φ)
    (hr : φ.range = F4.reeGamma K a) {S : Subgroup X}
    (hS : S.map φ = F4.reeFixedPosUnipotent K a) {x y : X}
    (hx : x ∈ Subgroup.normalizer (S : Set X)) (hy : y ∈ Subgroup.normalizer (S : Set X)) :
    x * y * x⁻¹ * y⁻¹ ∈ S := by
  have hx' := (mem_normalizer_iff_mem_reeFixedBorel hφ hr hS x).1 hx
  have hy' := (mem_normalizer_iff_mem_reeFixedBorel hφ hr hS y).1 hy
  have h1 : φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ ∈ posUnipotent F4.tag K ⊓ F4.reeGamma K a :=
    ⟨commutator_borel_mem_posUnipotent hx'.1 hy'.1,
      (F4.reeGamma K a).mul_mem ((F4.reeGamma K a).mul_mem ((F4.reeGamma K a).mul_mem hx'.2 hy'.2)
        ((F4.reeGamma K a).inv_mem hx'.2)) ((F4.reeGamma K a).inv_mem hy'.2)⟩
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h1
  have h2 : φ (x * y * x⁻¹ * y⁻¹) ∈ S.map φ := hS ▸ h1
  obtain ⟨s, hs, hsx⟩ := h2
  rwa [← hφ hsx]

theorem commutator_mem_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 n) {S : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {x y : X}
    (hx : x ∈ Subgroup.normalizer (S : Set X)) (hy : y ∈ Subgroup.normalizer (S : Set X)) :
    x * y * x⁻¹ * y⁻¹ ∈ S := by
  obtain ⟨_, K, _, _, _, φ, -, -, -, hφi, hφr, hφS⟩ := exists_embedding hX hS
  exact commutator_mem_of_mem_normalizer hφi hφr hφS hx hy

end CFSG.Quasithin.H13.NQCore.F4
