module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

section CyclicFour

variable {G : Type*} [Group G]

theorem mem_zpowers_four {d z : G} (hdd : d * d = z) (hz2 : z * z = 1) {y : G}
    (hy : y ∈ Subgroup.zpowers d) : y = 1 ∨ y = d ∨ y = z ∨ y = d * z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hd4 : d ^ (4 : ℤ) = 1 := by
    calc d ^ (4 : ℤ) = (d * d) * (d * d) := by
          rw [show (4 : ℤ) = 2 + 2 by norm_num, zpow_add, zpow_two]
      _ = 1 := by rw [hdd, hz2]
  have hk : d ^ k = d ^ (k % 4) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 4, zpow_add, zpow_mul, hd4, one_zpow, one_mul]
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
  rw [hk]
  generalize k % 4 = r at h0 h4 ⊢
  interval_cases r
  · left; simp
  · right; left; simp
  · right; right; left; rw [zpow_two]; exact hdd
  · right; right; right
    rw [show (3 : ℤ) = 1 + 2 by norm_num, zpow_add, zpow_two, hdd, zpow_one]

theorem tightlyEmbedded_zpowers_of_sq {d z : G} (hdd : d * d = z) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hN : ∀ g : G, g * z * g⁻¹ = z → g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    TightlyEmbedded (Subgroup.zpowers d) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf d = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · intro h
      apply hz1
      rw [← hdd, ← pow_two]
      simpa using h
    · calc d ^ 2 ^ (1 + 1) = d ^ (2 + 2) := by norm_num
        _ = (d * d) * (d * d) := by rw [pow_add, pow_two]
        _ = 1 := by rw [hdd, hz2]
  have hzd : z * d = d * z := by
    calc z * d = (d * d) * d := by rw [hdd]
      _ = d * (d * d) := by group
      _ = d * z := by rw [hdd]
  have hinv : ∀ y ∈ Subgroup.zpowers d, y * y = 1 → y = 1 ∨ y = z := by
    intro y hy hy2
    rcases mem_zpowers_four hdd hz2 hy with h | h | h | h
    · exact Or.inl h
    · exfalso
      apply hz1
      rw [← hdd, ← h]
      exact hy2
    · exact Or.inr h
    · exfalso
      apply hz1
      rw [h] at hy2
      calc z = (d * d) * (z * z) := by rw [hdd, hz2, mul_one]
        _ = (d * z) * (d * z) := by
          calc (d * d) * (z * z) = d * (d * z) * z := by group
            _ = d * (z * d) * z := by rw [hzd]
            _ = (d * z) * (d * z) := by group
        _ = 1 := hy2
  refine ⟨?_, fun g hg => ?_⟩
  · rw [Nat.card_zpowers, hord]
    decide
  · have hbot : (Subgroup.zpowers d ⊓ rightConjugate (Subgroup.zpowers d) g : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxD, hxg'⟩ := hx
      have hxg := (mem_rightConjugate_iff _ g x).mp hxg'
      rw [Subgroup.mem_bot]
      by_contra hx1
      apply hg
      apply hN
      have hgz : g * z * g⁻¹ ∈ Subgroup.zpowers d → g * z * g⁻¹ = z := by
        intro hmem
        have hsq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
          calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
            _ = 1 := by rw [hz2]; group
        rcases hinv _ hmem hsq with h | h
        · exact absurd (by
            calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
              _ = 1 := by rw [h]; group) hz1
        · exact h
      rcases mem_zpowers_four hdd hz2 hxD with h | h | h | h
      · exact absurd h hx1
      ·
        subst h
        apply hgz
        have : g * z * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) := by
          calc g * z * g⁻¹ = g * (x * x) * g⁻¹ := by rw [hdd]
            _ = (g * x * g⁻¹) * (g * x * g⁻¹) := by group
        rw [this]
        exact (Subgroup.zpowers x).mul_mem hxg hxg
      ·
        subst h
        exact hgz hxg
      ·
        subst h
        apply hgz
        have h2 : (d * z) * (d * z) = z := by
          calc (d * z) * (d * z) = d * (z * d) * z := by group
            _ = d * (d * z) * z := by rw [hzd]
            _ = (d * d) * (z * z) := by group
            _ = z := by rw [hdd, hz2, mul_one]
        have : g * z * g⁻¹ = (g * (d * z) * g⁻¹) * (g * (d * z) * g⁻¹) := by
          calc g * z * g⁻¹ = g * ((d * z) * (d * z)) * g⁻¹ := by rw [h2]
            _ = (g * (d * z) * g⁻¹) * (g * (d * z) * g⁻¹) := by group
        rw [this]
        exact (Subgroup.zpowers d).mul_mem hxg hxg
    rw [hbot]
    simp

end CyclicFour

section Wgen

variable {G : Type*} [Group G]

theorem Wgen_comm {Γ : Set (Subgroup G)} (hΓ : CommFam Γ)
    (hR : ∀ R ∈ Γ, ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) :
    ∀ x ∈ Wgen Γ, ∀ y ∈ Wgen Γ, x * y = y * x := by
  have key : ∀ x ∈ Wgen Γ, ∀ y : G, (∃ R ∈ Γ, y ∈ R) → x * y = y * x := by
    intro x hx y hy
    obtain ⟨R', hR', hyR'⟩ := hy
    unfold Wgen at hx
    induction hx using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨R, hRΓ, huR⟩ := hu
      by_cases hRR : R = R'
      · subst hRR
        exact hR R hRΓ u huR y hyR'
      · exact hΓ R hRΓ R' hR' hRR u huR y hyR'
    | one => simp
    | mul a b _ _ ha hb =>
      calc a * b * y = a * (b * y) := by group
        _ = a * (y * b) := by rw [hb]
        _ = (a * y) * b := by group
        _ = (y * a) * b := by rw [ha]
        _ = y * (a * b) := by group
    | inv a _ ha =>
      have : a * y = y * a := ha
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [this]
        _ = y * a⁻¹ := by group
  intro x hx y hy
  unfold Wgen at hy
  induction hy using Subgroup.closure_induction with
  | mem u hu => exact key x hx u hu
  | one => simp
  | mul a b _ _ ha hb =>
    calc x * (a * b) = (x * a) * b := by group
      _ = (a * x) * b := by rw [ha]
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [hb]
      _ = (a * b) * x := by group
  | inv a _ ha =>
    have : x * a = a * x := ha
    calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [this]
      _ = a⁻¹ * x := by group

end Wgen

section WeakClosure

variable {G : Type*} [Group G] [Finite G]

theorem isWeaklyClosedIn_Wgen_delta (D T : Subgroup G) :
    IsWeaklyClosedIn (Wgen (Delta ⊤ D T)) T := by
  intro g hg
  set X := Wgen (Delta (⊤ : Subgroup G) D T) with hX
  have key : ∀ x ∈ X, g⁻¹ * x * g ∈ X := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨R, hRΔ, huR⟩ := hu
      obtain ⟨⟨h, -, hRh⟩, hRT⟩ := hRΔ
      have hRX : R ≤ X := le_Wgen ⟨⟨h, trivial, hRh⟩, hRT⟩
      have hRgT : CFSG.conjugate R g ≤ T := by
        intro y hy
        rw [mem_conjugate_iff] at hy
        exact hg (mem_conjSubgroup_iff.mpr (hRX hy))
      have hRg : CFSG.conjugate R g ∈ Delta (⊤ : Subgroup G) D T :=
        ⟨⟨h * g, trivial, by rw [hRh, conjugate_conjugate]⟩, hRgT⟩
      have hu' : g⁻¹ * u * g ∈ CFSG.conjugate R g := by
        rw [mem_conjugate_iff]
        have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
        rw [e]; exact huR
      exact le_Wgen hRg hu'
    | one => simp
    | mul a b _ _ ha hb =>
      have : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  have hle : conjSubgroup X g ≤ X := by
    intro w hw
    have := key _ (mem_conjSubgroup_iff.mp hw)
    have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    rwa [e] at this
  have hcard : Nat.card X ≤ Nat.card (conjSubgroup X g) := by
    unfold conjSubgroup
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard)

end WeakClosure

end S143

end CFSG.Quasithin
