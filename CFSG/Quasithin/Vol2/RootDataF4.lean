module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4

public section

namespace CFSG.Quasithin.H13.RootData.F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

theorem mem_reeFixedPosUnipotent_of_centralizer
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : ModGL F4.tag K} (hgΓ : g ∈ F4.reeGamma K a)
    (hcU : ∀ y ∈ F4.reeFixedPosUnipotent K a, y * g = g * y) :
    g ∈ F4.reeFixedPosUnipotent K a := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨-, -, -, -, -, hNU, -⟩ := ree_Borel_self_normalizers F4 a K w₀ hw₀
  have hgN : g ∈ Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [show g * h * g⁻¹ = h by rw [← hcU h hh]; group]
      exact hh
    · intro hh
      have h1 := hcU _ hh
      have e : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [h1]
          _ = g * h * g⁻¹ := by group
      rw [e]
      exact hh
  have hgB : g ∈ F4.reeFixedBorel K a := by
    rw [← hNU]
    exact ⟨hgΓ, hgN⟩
  have hgP : g ∈ F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
    rw [← reeParabolic_singleton]
    exact reeFixedBorel_le_reeParabolic F4 K a _ hgB
  obtain ⟨hF0, -⟩ := CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeReeParabolicFacts a K ha hK
  have hgCV : g ∈ Subgroup.centralizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcU y (LargeReeInvolution.reeFixedOrbitComplementUnipotent_le _ hy)
  exact LargeReeInvolution.reeFixedOrbitComplementUnipotent_le _ (hF0.selfCentralizing ⟨hgP, hgCV⟩)

theorem eq_one_of_centralizer_of_odd
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : ModGL F4.tag K} (hgΓ : g ∈ F4.reeGamma K a)
    (hcU : ∀ y ∈ F4.reeFixedPosUnipotent K a, y * g = g * y) (hodd : Odd (orderOf g)) :
    g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hgU := mem_reeFixedPosUnipotent_of_centralizer ha hK hgΓ hcU
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := by
    have h1 : IsPGroup 2 ↥((PU : Subgroup ↥(F4.reeGamma K a)).map (F4.reeGamma K a).subtype) :=
      PU.isPGroup'.map _
    rwa [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 reeFixedPosUnipotent_le_reeGamma] at h1
  obtain ⟨k, hk⟩ := hUp ⟨g, hgU⟩
  have h1 : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hi] at hodd
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [h0, pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  · exact absurd hodd (Nat.not_odd_iff_even.mpr ((Nat.even_pow' hpos.ne').mpr even_two))

end CFSG.Quasithin.H13.RootData.F4
