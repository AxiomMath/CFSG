module

public import CFSG.Quasithin.Background.RonanE42Basic
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pCoreOf_le_of_sylow [Finite G] {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) :
    pCoreOf 2 H ≤ T := by
  obtain ⟨-, hTp, hTd⟩ := hT
  have hTH' : IsSylowIn 2 T H := by
    refine ⟨hTH, hTp, ?_⟩
    intro hd
    apply hTd
    rw [← Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top]
    exact Dvd.dvd.mul_right hd _
  have hN : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  exact hTH'.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hN
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem conjSubgroup_pCoreOf {H : Subgroup G} {g : G} (hg : g ∈ H) :
    conjSubgroup (pCoreOf 2 H) g = pCoreOf 2 H := by
  rw [conjSubgroup_eq_iff_mem_normalizer]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg

theorem exists_mem_le_of_sylow [Finite G] {T : Subgroup G} {Ω : Set (Subgroup G)}
    (hT : IsSylowIn 2 T ⊤) (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (h2 : ∀ A ∈ Ω, ∀ a ∈ A, a ^ 2 = 1) {A₀ : Subgroup G} (hA₀ : A₀ ∈ Ω) :
    ∃ A ∈ Ω, A ≤ T := by
  have hA₀p : IsPGroup 2 A₀ := by
    intro a
    exact ⟨1, Subtype.ext (by simpa using h2 A₀ hA₀ a.1 a.2)⟩
  obtain ⟨h, -, hle⟩ := CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn hT le_top hA₀p
  refine ⟨conjSubgroup A₀ h⁻¹, hΩ A₀ hA₀ h⁻¹, ?_⟩
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 := hle hx
  rw [mem_conjSubgroup_iff] at h1
  have e : h * (h⁻¹ * x * h⁻¹⁻¹) * h⁻¹ = x := by group
  rwa [e] at h1

section Interface

variable {V : Type} [CommGroup V] [Finite V]

theorem Om_comap_of_mem_aSet [Finite G] {ρ : G →* MulAut V} (hρ : Function.Injective ρ) {n : ℕ}
    {A' : Subgroup (MulAut V)} (hA' : A' ∈ aSet n ρ.range) : Om ρ n (A'.comap ρ) := by
  obtain ⟨hle, hne, ⟨hcomm, hsq⟩, hfix⟩ := hA'
  have hmap : (A'.comap ρ).map ρ = A' := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  unfold Om
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    have h' := congrArg (Subgroup.map ρ) h
    rw [hmap, Subgroup.map_bot] at h'
    exact h'
  · intro a ha
    apply hρ
    rw [map_pow, map_one]
    exact hsq (ρ a) (Subgroup.mem_comap.mp ha)
  · intro a ha b hb
    apply hρ
    rw [map_mul, map_mul]
    exact hcomm (ρ a) (Subgroup.mem_comap.mp ha) (ρ b) (Subgroup.mem_comap.mp hb)
  · intro B hBA hm
    have hBmap : B.map ρ ≤ A' := by
      rw [← hmap]
      exact Subgroup.map_mono hBA
    have hrel : (B.map ρ).relIndex A' = B.relIndex (A'.comap ρ) := by
      have h := Subgroup.relIndex_map_map_of_injective (f := ρ) B (A'.comap ρ) hρ
      rw [hmap] at h
      exact h
    have hm' : mQuot A' (B.map ρ) < n := by
      unfold mQuot at hm ⊢
      rw [hrel]
      exact hm
    have hfixB : fixV (B.map ρ) = fixV A' := hfix (B.map ρ) hBmap hm'
    show fixV (B.map ρ) = fixV ((A'.comap ρ).map ρ)
    rw [hmap]
    exact hfixB

theorem aParam_le_of_aSet_empty (X : Subgroup (MulAut V)) (k : ℕ)
    (h : ∀ A : Subgroup (MulAut V), A ∉ aSet (k + 1) X) : aParam X ≤ k := by
  unfold aParam
  split_ifs with heven
  · by_contra hlt
    push Not at hlt
    have hne : ({k : ℕ | 0 < k ∧ (aSet k X).Nonempty} : Set ℕ).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      rw [hem, csSup_empty] at hlt
      exact not_lt_bot hlt
    obtain ⟨a, ⟨-, A, hA⟩, hka⟩ := exists_lt_of_lt_csSup hne hlt
    exact h A (aSet_anti (Nat.succ_le_of_lt hka) X hA)
  · exact Nat.zero_le k

end Interface

end CFSG.Quasithin.RonanE42
