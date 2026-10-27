module

public import CFSG.Quasithin.EmptyFaithful.R3c20C

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def FixedVectorStatement : Prop :=
  ∀ H T L : Subgroup G, CharTwo H → CharTwo L → IsSylowTwoOf T H → IsSQTKTC H → L ∈ cComp H →
    H = L ⊔ T → ¬ T ≤ Subgroup.normalizer (L : Set G) →
    (∃ n : ℕ, 1 < n ∧ IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → ⁅L, thompsonJ T⁆ = L →
    ¬ L ≤ Subgroup.centralizer (VZ T H : Set G) →
    ∃ u ∈ VZ T H, (∃ l ∈ L, l * u ≠ u * l) ∧ (∀ j ∈ thompsonJ T, j * u = u * j) ∧
      ∀ x ∈ T, x ∉ Subgroup.normalizer (L : Set G) →
        ∀ l ∈ L, (x * l * x⁻¹) * u = u * (x * l * x⁻¹)

theorem mem_omegaOneCenter_thompsonJ {H T : Subgroup G} (hH : CharTwo H) (hT : IsSylowTwoOf T H)
    {u : G} (hu : u ∈ VZ T H) (hJu : ∀ j ∈ thompsonJ T, j * u = u * j) :
    u ∈ omegaOneCenterOf (thompsonJ T) := by
  have hV : IsTwoReducedIn H (VZ T H) := C1GN.isTwoReducedIn_VZ hH hT
  have hu2 : u ^ 2 = 1 := hV.2.2.1.2 u hu
  have hVT : VZ T H ≤ T := by
    have h1 : VZ T H ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.1 hV.2.1
        (B2F.isPGroup_of_isElemAbelian hV.2.2.1)
    exact h1.trans (pCoreOf_le_of_isSylowTwoOf hT)
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian T
  have hAJ : A ≤ thompsonJ T := GammaExtra.le_thompsonJ hA
  have huA : u ∈ A := by
    have hB := GammaExtra.isElemAbelian_sup_zpowers (le_refl A) hA.2.1
      (fun a ha => hJu a (hAJ ha)) hu2
    have hBT : A ⊔ Subgroup.zpowers u ≤ T := sup_le hA.1 (Subgroup.zpowers_le.mpr (hVT hu))
    have heq : A = A ⊔ Subgroup.zpowers u :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hBT hB)
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have huJ : u ∈ thompsonJ T := hAJ huA
  have huZ : u ∈ centerOf (thompsonJ T) :=
    ⟨huJ, Subgroup.mem_centralizer_iff.mpr fun j hj => hJu j hj⟩
  exact Subgroup.subset_closure ⟨huZ, hu2⟩

theorem baumNormalizesL2_of_fixedVector (h : FixedVectorStatement (G := G)) :
    R3c20.BaumNormalizesL2Statement (G := G) := by
  intro H T L hH hL hT hSQ hLH hHeq hTN hn hq hJ hLV
  obtain ⟨u, huV, ⟨l, hl, hlu⟩, hJu, hx⟩ := h H T L hH hL hT hSQ hLH hHeq hTN hn hq hJ hLV
  intro x hxB
  by_contra hxN
  have huΩ := mem_omegaOneCenter_thompsonJ hH hT huV hJu
  have hux : u * x = x * u := Subgroup.mem_centralizer_iff.mp hxB.2 u huΩ
  have hxinvN : x⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun hh =>
    hxN (by simpa using (Subgroup.inv_mem_iff _).mp hh)
  have hc := hx x⁻¹ (T.inv_mem hxB.1) hxinvN l hl
  rw [inv_inv] at hc
  have e1 : l = x * (x⁻¹ * l * x) * x⁻¹ := by group
  have e2 : u = x * u * x⁻¹ := by
    calc u = u * x * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [hux]
  apply hlu
  calc l * u = (x * (x⁻¹ * l * x) * x⁻¹) * (x * u * x⁻¹) := by rw [← e1, ← e2]
    _ = x * ((x⁻¹ * l * x) * u) * x⁻¹ := by group
    _ = x * (u * (x⁻¹ * l * x)) * x⁻¹ := by rw [hc]
    _ = (x * u * x⁻¹) * (x * (x⁻¹ * l * x) * x⁻¹) := by group
    _ = u * l := by rw [← e1, ← e2]

end R3c23

theorem R3c23.theoremC116L2_of_fixedVector
    (h : ∀ (G : Type) [Group G] [Finite G], R3c23.FixedVectorStatement (G := G)) :
    R3c20.TheoremC116L2 :=
  fun G _ _ => R3c23.baumNormalizesL2_of_fixedVector (h G)

end CFSG.Quasithin
