module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

variable {G X : Type*} [Group G] [Finite G] [Group X]

omit [Finite G] in
theorem eq_one_of_pow_three_of_pow_two {g : G} (h3 : g ^ 3 = 1) {k : ℕ} (h2 : g ^ (2 ^ k) = 1) :
    g = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨h3, h2⟩
  have hc : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  rwa [hc, pow_one] at h

theorem exists_lift (μ : G →* X) (hμ : Function.Surjective μ) (hker : ∀ g, μ g = 1 → g ^ 3 = 1)
    (hcen : ∀ g, μ g = 1 → ∀ x, x * g = g * x) (R : Subgroup X) (hR : IsPGroup 2 R) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S.map μ = R ∧ (∀ x ∈ S, μ x = 1 → x = 1) ∧
      ∀ h : G, μ h ∈ Subgroup.normalizer (R : Set X) → h ∈ Subgroup.normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Rh : Subgroup G := R.comap μ with hRh
  let μ' : ↥Rh →* ↥R := (μ.comp Rh.subtype).codRestrict R fun x => x.2
  have hμ' : Function.Surjective μ' := fun r => by
    obtain ⟨g, hg⟩ := hμ r
    exact ⟨⟨g, by rw [hRh, Subgroup.mem_comap, hg]; exact r.2⟩, Subtype.ext hg⟩
  let P : Sylow 2 ↥Rh := default
  have hPR : (P : Subgroup ↥Rh).map μ' = ⊤ := by
    have h2 := (Sylow.mapSurjective hμ' P).3 (hR.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h2
    exact h2.symm
  set S : Subgroup G := (P : Subgroup ↥Rh).map Rh.subtype with hS
  have hS2 : IsPGroup 2 S := P.2.map Rh.subtype
  have hSR : S.map μ = R := by
    have h1 : S.map μ = ((P : Subgroup ↥Rh).map μ').map R.subtype := by
      rw [hS, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hPR, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hSker : ∀ x ∈ S, μ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨k, hk⟩ := hS2 ⟨x, hx⟩
    exact eq_one_of_pow_three_of_pow_two (hker x hx1) (by simpa using congrArg Subtype.val hk)
  have hSRh : ∀ x ∈ S, x ∈ Rh := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hall : ∀ g ∈ Rh, ∀ k : ℕ, g ^ (2 ^ k) = 1 → g ∈ S := by
    intro g hg k hgk
    have hmem : μ g ∈ S.map μ := by rw [hSR]; exact hg
    obtain ⟨s, hs, hsg⟩ := hmem
    set z := s⁻¹ * g with hz
    have hzk : μ z = 1 := by rw [hz, map_mul, map_inv, hsg, inv_mul_cancel]
    have hz3 := hker z hzk
    have hgsz : g = s * z := by rw [hz]; group
    have hcomm : Commute s z := hcen z hzk s
    have h1 : g ^ (2 ^ k) = s ^ (2 ^ k) * z ^ (2 ^ k) := by
      rw [hgsz]
      exact hcomm.mul_pow _
    have h2 : z ^ (2 ^ k) = (s ^ (2 ^ k))⁻¹ := by
      rw [hgk] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    have h3 : z ^ (2 ^ k) ∈ S := by
      rw [h2]
      exact inv_mem (pow_mem hs _)
    have h4 : μ (z ^ (2 ^ k)) = 1 := by rw [map_pow, hzk, one_pow]
    have h5 : z ^ (2 ^ k) = 1 := hSker _ h3 h4
    have h6 : z = 1 := eq_one_of_pow_three_of_pow_two hz3 h5
    rw [hgsz, h6, mul_one]
    exact hs
  refine ⟨S, hS2, hSR, hSker, fun h hh => ?_⟩
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hxS : x ∈ S := hx
  obtain ⟨k, hk⟩ := hS2 ⟨x, hxS⟩
  have hxk : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hxR : μ x ∈ R := hSRh x hxS
  show h * x * h⁻¹ ∈ S
  refine hall (h * x * h⁻¹) ?_ k ?_
  · rw [hRh, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hh (μ x)).mp hxR
  · rw [conj_pow, hxk]
    group

theorem exists_isPGroup_map_eq {T : Type*} [Group T] (φ : G →* T) (hφ : Function.Surjective φ)
    {F : Subgroup T} (hF : IsPGroup 2 F) : ∃ B : Subgroup G, IsPGroup 2 B ∧ B.map φ = F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite T := Finite.of_surjective φ hφ
  obtain ⟨Q, hFQ⟩ := hF.exists_le_sylow
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hφ 2 Q
  refine ⟨(P : Subgroup G) ⊓ F.comap φ, P.2.to_inf_left, ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact hx
  · intro f hf
    have hfQ : f ∈ (Q : Subgroup T) := hFQ hf
    rw [← hP, Sylow.coe_mapSurjective] at hfQ
    obtain ⟨x, hxP, rfl⟩ := hfQ
    exact ⟨x, ⟨hxP, hf⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec15.KS1424
