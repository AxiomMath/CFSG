module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_pCoreOf_of_normalizer152 {K Mc : Subgroup G} (hKMc : K ≤ Mc)
    (hn : Mc ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 Mc :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKMc)
    (hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem comm_mem_pCoreOf152 {Kc Mc Y R V : Subgroup G} (hKcMc : Kc ≤ Mc)
    (hMcn : Mc ≤ Subgroup.normalizer (Kc : Set G)) (hKcY : Kc ≤ Y)
    (hYK : Y ≤ Subgroup.normalizer (Kc : Set G)) (hRY : R ≤ Y)
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R) (hVR : V ≤ R) :
    ∀ k ∈ Kc, ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ pCoreOf 2 Mc := by
  intro k hk v hv
  have hvR : v ∈ R := hVR hv
  have hkR : k * v * k⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hYR (hKcY hk)) v).mp hvR
  have hcR : k * v * k⁻¹ * v⁻¹ ∈ R := R.mul_mem hkR (R.inv_mem hvR)
  have hvk : v * k⁻¹ * v⁻¹ ∈ Kc := by
    have := (Subgroup.mem_normalizer_iff.mp (hYK (hRY hvR)) k⁻¹).mp (Kc.inv_mem hk)
    exact this
  have hcK : k * v * k⁻¹ * v⁻¹ ∈ Kc := by
    have := Kc.mul_mem hk hvk
    simpa [mul_assoc] using this
  have hDn : Kc ≤ Subgroup.normalizer ((Kc ⊓ R : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgR := Subgroup.mem_normalizer_iff.mp (hYR (hKcY hg)) x
    have hgK := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x
    exact ⟨fun hx => ⟨hgK.mp hx.1, hgR.mp hx.2⟩, fun hx => ⟨hgK.mpr hx.1, hgR.mpr hx.2⟩⟩
  have hD2 : IsPGroup 2 (Kc ⊓ R : Subgroup G) := hR2.to_le inf_le_right
  have hDK : Kc ⊓ R ≤ pCoreOf 2 Kc :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hDn hD2
  exact pCoreOf_le_pCoreOf_of_normalizer152 hKcMc hMcn (hDK ⟨hcK, hcR⟩)

theorem oTwoUpper_le_centralizer_zS152 {T Mc M P : Subgroup G} (hs : Setting152 T Mc M)
    (h15209 : StageNotation15209) (h15211 : StageLemma15211) (h15213 : StageLemma15213)
    {B₀ : Subgroup (MulAut (V154 T Mc M))} (hB₀ : IsB0 T Mc M B₀) (hP : IsHStar T M P) :
    oTwoUpper P ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
  obtain ⟨B, hB⟩ := (h15209 G T Mc M hs P hP).sigmaPrime_nonempty
  obtain ⟨B₀', hB₀', huniq, hprop⟩ := (h15213 G T Mc M hs P hP).exists_B0
  have hB₀eq : B₀ = B₀' := huniq B₀ hB₀
  subst hB₀eq
  obtain ⟨-, -, hZ, -⟩ := hprop B hB
  have := (h15211 G T Mc M hs P hP B hB).centralizes
  rw [hZ] at this
  exact this

end CFSG.Quasithin
