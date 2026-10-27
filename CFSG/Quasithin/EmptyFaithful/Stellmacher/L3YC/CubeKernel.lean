module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.V4Aut
public import CFSG.Quasithin.EmptyFaithful.T1515C6P
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

variable {G : Type} [Group G]

omit [Group G] in
theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {y : G} {a : ℕ} (hy : y ^ 3 ^ a = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  intro x
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
  refine ⟨a, Subtype.ext ?_⟩
  show (x : G) ^ 3 ^ a = 1
  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

variable [Finite G]

theorem centralizes_of_cube_kernel {H V Q : Subgroup G}
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hV4 : Nat.card V = 4) (hsq : ∀ a ∈ V, a * a = 1)
    (hcyc : ∀ P : Subgroup G, P ≤ H → IsPGroup 3 ↥P → IsCyclic ↥P)
    (hcube : ∀ z ∈ H, ∀ m : ℕ, z ^ 3 ^ m = 1 → ∀ q ∈ Q, z ^ 3 * q * (z ^ 3)⁻¹ = q)
    {y : G} (hyH : y ∈ H) {a : ℕ} (hya : y ^ 3 ^ a = 1) (hymove : ∃ x ∈ V, y * x * y⁻¹ ≠ x)
    {g : G} (hgH : g ∈ H) {m : ℕ} (hgm : g ^ 3 ^ m = 1) (hgV : ∀ x ∈ V, g * x * g⁻¹ = x) :
    ∀ q ∈ Q, g * q * g⁻¹ = q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := card_mulAut_of_card_four hV4 hsq
  obtain ⟨P₀, hP₀S, hyP₀⟩ := exists_isSylowIn_ge 3
    (Subgroup.zpowers_le.mpr hyH : Subgroup.zpowers y ≤ H) (isPGroup_zpowers_of_pow hya)
  obtain ⟨P₁, hP₁S, hgP₁⟩ := exists_isSylowIn_ge 3
    (Subgroup.zpowers_le.mpr hgH : Subgroup.zpowers g ≤ H) (isPGroup_zpowers_of_pow hgm)
  obtain ⟨n, hnH, hn⟩ := isSylowIn_conj_of hP₀S hP₁S
  have hgP₀ : n⁻¹ * g * n ∈ P₀ := by
    have hg1 : g ∈ P₁ := hgP₁ (Subgroup.mem_zpowers g)
    rw [← hn, A1b.mem_conjSub_iff] at hg1
    exact hg1
  have hyP₀' : y ∈ P₀ := hyP₀ (Subgroup.mem_zpowers y)
  have hP₀H : P₀ ≤ H := hP₀S.le
  have hP₀3 : IsPGroup 3 ↥P₀ := hP₀S.isPGroup
  have hcycP : IsCyclic ↥P₀ := hcyc P₀ hP₀H hP₀3
  obtain ⟨w, hw⟩ := hcycP.exists_generator
  have hP₀V : P₀ ≤ Subgroup.normalizer (V : Set G) := hP₀H.trans hHV
  let ρ : ↥P₀ →* MulAut V := conjAut hP₀V
  have hρ : ∀ (k : ↥P₀) (x : V), ((ρ k x : V) : G) = (k : G) * x * (k : G)⁻¹ := fun k x => rfl
  obtain ⟨c, hc⟩ := hP₀3 w
  have hσ3 : ρ w ^ 3 = 1 := by
    refine pow_three_eq_one_of_odd hA (Odd.pow (by decide : Odd 3) : Odd (3 ^ c)) ?_
    rw [← map_pow, hc, map_one]
  have hσne : ρ w ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hxy⟩ := hymove
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hw ⟨y, hyP₀'⟩)
    have h2 : ρ ⟨y, hyP₀'⟩ = 1 := by rw [← hi, map_zpow, h1, one_zpow]
    apply hxy
    have := congrArg (fun φ : MulAut V => ((φ ⟨x, hx⟩ : V) : G)) h2
    simpa [hρ] using this
  have hσord : orderOf (ρ w) = 3 := by
    have h1 : orderOf (ρ w) ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσne
    · exact h
  set g' : G := n⁻¹ * g * n with hg'
  have hg'V : ∀ x ∈ V, g' * x * g'⁻¹ = x := by
    intro x hx
    have h1 : n * x * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hHV hnH) x).mp hx
    have h2 := hgV _ h1
    calc g' * x * g'⁻¹ = n⁻¹ * (g * (n * x * n⁻¹) * g⁻¹) * n := by rw [hg']; group
      _ = x := by rw [h2]; group
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hw ⟨g', hgP₀⟩)
  have hρi : ρ ⟨g', hgP₀⟩ = 1 := by
    ext x
    exact hg'V x x.2
  have h3i : (3 : ℤ) ∣ i := by
    have h1 : ρ w ^ i = 1 := by rw [← map_zpow, hi, hρi]
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hσord] at h2
    exact_mod_cast h2
  obtain ⟨j, hj⟩ := h3i
  have hz : ((w ^ j : ↥P₀) : G) ^ 3 = g' := by
    have : ((w ^ (3 * j) : ↥P₀) : G) = g' := by rw [← hj, hi]
    have e : (w ^ (3 * j) : ↥P₀) = (w ^ j) ^ 3 := by
      rw [mul_comm, zpow_mul, zpow_ofNat]
    rw [← this, e]
    simp
  obtain ⟨c', hc'⟩ := hP₀3 (w ^ j)
  have hzc : ((w ^ j : ↥P₀) : G) ^ 3 ^ c' = 1 := by
    have := congrArg Subtype.val hc'
    simpa using this
  have hzH : ((w ^ j : ↥P₀) : G) ∈ H := hP₀H (w ^ j).2
  have hg'Q := hcube _ hzH c' hzc
  rw [hz] at hg'Q
  intro q hq
  have hq' : n⁻¹ * q * n ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hnH)) q).mp hq
    simpa using this
  have h1 := hg'Q _ hq'
  calc g * q * g⁻¹ = n * (g' * (n⁻¹ * q * n) * g'⁻¹) * n⁻¹ := by rw [hg']; group
    _ = q := by rw [h1]; group

end Stellmacher.L3YC

end CFSG.Quasithin
