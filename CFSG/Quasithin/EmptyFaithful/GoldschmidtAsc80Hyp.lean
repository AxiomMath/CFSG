module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6

namespace E2P

variable {X : Type} [Group X] [Finite X] {K T : Subgroup X}

theorem not_le_normalizer_of_simple (hK : K.Normal) [hs : IsSimpleGroup ↥K]
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hT : IsSylowTwoOf T ⊤) :
    ¬ (⊤ : Subgroup X) ≤ Subgroup.normalizer (T : Set X) := by
  intro htop
  have hTn : T.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr htop)
  have hSyl : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hK])
  have hSn : ((T ⊓ K).subgroupOf K).Normal := inferInstance
  obtain ⟨a, b, hab⟩ := hnab
  rcases hs.eq_bot_or_eq_top_of_normal ((T ⊓ K).subgroupOf K) with hb | ht
  ·
    have h1 : ((T ⊓ K).subgroupOf K).index = Nat.card K := by
      rw [hb, Subgroup.index_bot]
    have h2 := hSyl.2.2
    rw [h1] at h2
    have hodd : Odd (Nat.card K) := Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (Nat.card K) with he | ho
      · exact absurd (even_iff_two_dvd.mp he) h2
      · exact Nat.odd_iff.mp ho)
    have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard K hodd
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  ·
    have hKS : K ≤ T ⊓ K := fun x hx => by
      have : (⟨x, hx⟩ : ↥K) ∈ (T ⊓ K).subgroupOf K := by rw [ht]; trivial
      exact this
    have h2 : IsPGroup 2 K := by
      intro x
      obtain ⟨n, hn⟩ := hSyl.2.1 ⟨x, hKS x.2⟩
      exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent K := h2.isNilpotent
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance) a b)

theorem asHyp_of_uniqueMax {M : Subgroup X} (hK : K.Normal) (hs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hc : Subgroup.centralizer (K : Set X) = ⊥)
    (hT : IsSylowTwoOf T ⊤) (hsup : K ⊔ T = ⊤) (hM : IsUniqueMaxOver ⊤ T M) :
    ASHyp K T M :=
  { minPar := ⟨hT, not_le_normalizer_of_simple hK hnab hT, hM⟩
    normal := hK
    simple := hs
    nonab := hnab
    sup := hsup
    cent := hc }

omit [Finite X] in
theorem inducesOuter_of_not_le (hK : K.Normal) (hc : Subgroup.centralizer (K : Set X) = ⊥)
    (h : ¬ T ≤ K) : E2.InducesOuter T K := by
  obtain ⟨t, ht, htK⟩ := Set.not_subset.mp h
  refine ⟨t, ht, by rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial, fun k hk => ?_⟩
  by_contra hcon
  push Not at hcon
  apply htK
  have hmem : k⁻¹ * t ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hcon y hy
    calc y * (k⁻¹ * t) = k⁻¹ * (k * y * k⁻¹) * t := by group
      _ = k⁻¹ * (t * y * t⁻¹) * t := by rw [this]
      _ = k⁻¹ * t * y := by group
  rw [hc, Subgroup.mem_bot] at hmem
  have : t = k := by
    calc t = k * (k⁻¹ * t) := by group
      _ = k := by rw [hmem, mul_one]
  rw [this]
  exact hk

end E2P

end CFSG.Quasithin
