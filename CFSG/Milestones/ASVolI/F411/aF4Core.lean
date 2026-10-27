module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog
open scoped commutatorElement

section F4Core


theorem burnsideF411a_conj_xUnit_mul_eq (τ : Tag) {K : Type} [Field K] {i j : Fin τ.rank}
    (hij : i ≠ j) {v : ModGL τ K} (hv : v ∈ posUnipotent τ K) {c₁ c₂ d₁ d₂ : K}
    (h : v * (xUnit τ K i d₁ * xUnit τ K j d₂) * v⁻¹ = xUnit τ K i c₁ * xUnit τ K j c₂) :
    d₁ = c₁ := by
  have hx1 : ∀ (k : Fin τ.rank) (e : K), xUnit τ K k e ∈ heightSeries τ K 1 := fun k e => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α ∧ 1 ≤ height α})
      (α := Pi.single k 1) ⟨IsRoot.basis k, by simp, by simp⟩ e
  have hy1 : xUnit τ K i d₁ * xUnit τ K j d₂ ∈ heightSeries τ K 1 := mul_mem (hx1 i d₁) (hx1 j d₂)
  have hv1 : v ∈ heightSeries τ K 1 := by
    rw [heightSeries_one]
    exact hv
  have hcomm := commutator_heightSeries_le K 1 1 (Subgroup.commutator_mem_commutator hv1 hy1)
  have hU1 : (xUnit τ K i c₁)⁻¹ ∈ posUnipotent τ K :=
    inv_mem (heightSeries_le_posUnipotent 1 (hx1 i c₁))
  have hw := (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K (1 + 1) hU1) _).1 hcomm
  have hwe : (xUnit τ K i c₁)⁻¹ * ⁅v, xUnit τ K i d₁ * xUnit τ K j d₂⁆ * ((xUnit τ K i c₁)⁻¹)⁻¹ =
      xUnit τ K j (c₂ + -d₂) * xUnit τ K i (-d₁ + c₁) := by
    rw [commutatorElement_def, h, xUnit_add, xUnit_add, xUnit_neg, xUnit_neg]
    group
  rw [hwe] at hw
  set T : Set (Fin τ.rank → ℤ) :=
    {β | IsRoot τ β ∧ 0 < height β ∧ (β = Pi.single j 1 ∨ 2 ≤ height β)} with hT
  have hle : heightSeries τ K (1 + 1) ≤ rootSpan τ K T :=
    biSup_mono fun β hβ => ⟨hβ.1, hβ.2.1, Or.inr (by have := hβ.2.2; omega)⟩
  have hjT : ∀ e, xUnit τ K j e ∈ rootSpan τ K T := fun e => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan (S := T) (α := Pi.single j 1) ⟨IsRoot.basis j, by simp, Or.inl rfl⟩ e
  have hmem : pinnedX τ K (Pi.single i 1) (-d₁ + c₁) ∈ rootSpan τ K T := by
    rw [pinnedX_single]
    have e : xUnit τ K i (-d₁ + c₁) = (xUnit τ K j (c₂ + -d₂))⁻¹ *
        (xUnit τ K j (c₂ + -d₂) * xUnit τ K i (-d₁ + c₁)) := by group
    rw [e]
    exact mul_mem (inv_mem (hjT _)) (hle hw)
  have hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T := by
    intro β hβ γ hγ a b ha hb hr
    obtain ⟨hr', hp, hle'⟩ := nsmul_add_nsmul_mem_heightSet (h := 1) (k := 1)
      ⟨hβ.2.1, by have := hβ.2.1; omega⟩ ⟨hγ.2.1, by have := hγ.2.1; omega⟩ ha hb hr
    exact ⟨hr', hp, Or.inr (by omega)⟩
  by_contra hne
  have hne' : -d₁ + c₁ ≠ 0 := fun h0 => hne (by linear_combination -h0)
  have hiT := mem_of_pinnedX_mem_rootSpan (fun β hβ => ⟨hβ.1, hβ.2.1⟩) hTc
    ⟨IsRoot.basis i, by simp⟩ hne' hmem
  rcases hiT.2.2 with h1 | h2
  · apply hij
    have := congrFun h1 i
    simpa [Pi.single_apply, eq_comm] using this
  · simp at h2

theorem burnsideF411a_F4_inner_of_fix (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (α : MulAut (F4.reeGamma K a))
    (hα : ∀ x : F4.reeGamma K a, (x : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a → α x = x) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨-, hnf, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hnf α
  dsimp only at hxβ
  subst hxβ
  have hmap := map_reeFixedPosUnipotent_exactEntrywiseAut (t := F4) (K := K) (a := a) β
  have hfix' : ∀ y ∈ F4.reeFixedPosUnipotent K a, (x : ModGL F4.tag K) *
      Units.map (entrywiseHom β.toRingHom) y * (x : ModGL F4.tag K)⁻¹ = y := by
    intro y hy
    have hyΓ : y ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hy).2
    have h1 := congrArg Subtype.val (hα ⟨y, hyΓ⟩ hy)
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_reeGammaFieldAut, Subgroup.coe_inv] at h1
    exact h1
  have hxN : (x : ModGL F4.tag K) ∈
      Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hy' : y ∈ (F4.reeFixedPosUnipotent K a).map
          (exactEntrywiseAut F4.tag β).toMonoidHom := by
        rw [hmap]
        exact hy
      obtain ⟨y', hy'U, rfl⟩ := hy'
      have e : (exactEntrywiseAut F4.tag β).toMonoidHom y' =
          Units.map (entrywiseHom β.toRingHom) y' := rfl
      rw [e, hfix' y' hy'U]
      exact hy'U
    · intro hy
      have h1 := hfix' _ hy
      have h2 : Units.map (entrywiseHom β.toRingHom)
          ((x : ModGL F4.tag K) * y * (x : ModGL F4.tag K)⁻¹) = y := by
        calc Units.map (entrywiseHom β.toRingHom)
              ((x : ModGL F4.tag K) * y * (x : ModGL F4.tag K)⁻¹) =
            (x : ModGL F4.tag K)⁻¹ * ((x : ModGL F4.tag K) *
              Units.map (entrywiseHom β.toRingHom)
                ((x : ModGL F4.tag K) * y * (x : ModGL F4.tag K)⁻¹) *
              (x : ModGL F4.tag K)⁻¹) * (x : ModGL F4.tag K) := by group
          _ = (x : ModGL F4.tag K)⁻¹ * ((x : ModGL F4.tag K) * y * (x : ModGL F4.tag K)⁻¹) *
              (x : ModGL F4.tag K) := by rw [h1]
          _ = y := by group
      rw [← h2]
      have h3 := Subgroup.mem_map_of_mem (exactEntrywiseAut F4.tag β).toMonoidHom hy
      rwa [hmap] at h3
  have hxB : (x : ModGL F4.tag K) ∈ borelGroup F4.tag K := by
    have h1 : (x : ModGL F4.tag K) ∈ F4.reeGamma K a ⊓
        Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := ⟨x.2, hxN⟩
    rw [reeGamma_inf_normalizer_reeFixedPosUnipotent] at h1
    exact h1.1
  have hB : (x : ModGL F4.tag K) ∈ (borelGroup F4.tag K : Set (ModGL F4.tag K)) := hxB
  rw [(triangular_borel_structure.{0, 0} F4.tag K).2.2.2.2.2.1] at hB
  obtain ⟨v, hv, t, ht, hvt⟩ := hB
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hkey : ∀ c : K, (rootChar b (Pi.single largeReeI1 1) : K) * β c = c := by
    intro c
    have hc := hfix' _ (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent ⟨0, by decide⟩
      (largeReeA1X_mem_U1 hK c))
    have hσx : Units.map (entrywiseHom β.toRingHom) (largeReeA1X a c) =
        xUnit F4.tag K largeReeI1 (β c) * xUnit F4.tag K largeReeI4 (β (c ^ 2 ^ a)) := by
      rw [largeReeA1X, map_mul, units_map_entrywiseHom_xUnit, units_map_entrywiseHom_xUnit]
      rfl
    rw [hσx, largeReeA1X, ← hvt] at hc
    have hd : rootDiagUnit F4.tag b * (xUnit F4.tag K largeReeI1 (β c) *
        xUnit F4.tag K largeReeI4 (β (c ^ 2 ^ a))) * (rootDiagUnit F4.tag b)⁻¹ =
        xUnit F4.tag K largeReeI1 ((rootChar b (Pi.single largeReeI1 1) : K) * β c) *
          xUnit F4.tag K largeReeI4
            ((rootChar b (Pi.single largeReeI4 1) : K) * β (c ^ 2 ^ a)) := by
      rw [← pinnedX_single, ← pinnedX_single F4.tag K largeReeI4, ← pinnedX_single F4.tag K largeReeI1,
        ← pinnedX_single F4.tag K largeReeI4,
        ← rootDiagUnit_conj_pinnedX b (IsRoot.basis largeReeI1),
        ← rootDiagUnit_conj_pinnedX b (IsRoot.basis largeReeI4)]
      group
    have hc' : v * (xUnit F4.tag K largeReeI1 ((rootChar b (Pi.single largeReeI1 1) : K) * β c) *
        xUnit F4.tag K largeReeI4 ((rootChar b (Pi.single largeReeI4 1) : K) * β (c ^ 2 ^ a))) *
          v⁻¹ = xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) := by
      rw [← hd, ← hc]
      group
    exact burnsideF411a_conj_xUnit_mul_eq F4.tag (by decide) hv hc'
  have hchar : (rootChar b (Pi.single largeReeI1 1) : K) = 1 := by
    have h1 := hkey 1
    rwa [map_one, mul_one] at h1
  have hβ : β = 1 := RingEquiv.ext fun c => by
    have h1 := hkey c
    rw [hchar, one_mul] at h1
    rw [h1]
    rfl
  subst hβ
  refine ⟨x, ?_⟩
  have h1 : F4.reeGammaFieldAut K a 1 = 1 := (F4.reeGammaFieldAutHom K a).map_one
  rw [h1, mul_one]

theorem burnsideF411a_F4_inner_of_fix_sylow (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (α : MulAut (F4.reeGamma K a))
    (S : Sylow 2 (F4.reeGamma K a)) (hα : ∀ s ∈ (S : Subgroup (F4.reeGamma K a)), α s = s) :
    ∃ g, α = MulAut.conj g := by
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨P₀, hP₀⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (F4.reeGamma K a) P₀ S
  have hβ : ∀ u : F4.reeGamma K a, (u : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a →
      ((MulAut.conj x)⁻¹ * α * MulAut.conj x) u = u := by
    intro u hu
    have hu' : u ∈ (P₀ : Subgroup (F4.reeGamma K a)) := by
      rw [hP₀]
      exact Subgroup.mem_subgroupOf.2 hu
    have hxu : x * u * x⁻¹ ∈ (S : Subgroup (F4.reeGamma K a)) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      have h1 := Subgroup.smul_mem_pointwise_smul u (MulAut.conj x) (P₀ : Subgroup _) hu'
      rwa [MulAut.smul_def, MulAut.conj_apply] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hα _ hxu, MulAut.conj_inv_apply]
    group
  obtain ⟨g, hg⟩ := burnsideF411a_F4_inner_of_fix a ha K hK _ hβ
  refine ⟨x * g * x⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hg]
  group

end F4Core

end CFSG.ASVolI
