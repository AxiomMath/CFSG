module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SSN

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Ronan138S
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_mul_pow_of_frame {A L E F K : Subgroup G} {c x y t e : G}
    (hfr : Sec13.Ronan138S.Frame138 A L E F c x y t) (heE : e ∈ E) (heF : e ∈ F)
    (heL : e ∉ L) (heK : e ∉ K) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hautIn : Nonempty (Sec4.autIn K E ≃* Multiplicative (ZMod 3))) :
    ∃ k ∈ K, ∃ a b : ℕ, c = k ^ a * e ^ b := by
  obtain ⟨φ⟩ := hautIn
  set d := ⁅x, y⁆ with hd
  have hframe := hfr.frame
  have heZ : e ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨heE, heF⟩
  have he3 : e ^ 3 = 1 := hfr.hE3 e heE
  have he1 : e ≠ 1 := fun h => heL (h ▸ L.one_mem)
  set σ : Sec4.autIn K E := φ.symm (Multiplicative.ofAdd 1) with hσ
  have hσ1 : (σ : MulAut E) ≠ 1 := by
    intro h
    have h1 : σ = 1 := Subtype.ext h
    have h2 : φ σ = 1 := by rw [h1, map_one]
    rw [hσ, MulEquiv.apply_symm_apply] at h2
    exact absurd h2 (by decide)
  obtain ⟨k₀, hk₀N, hk₀K, hk₀σ⟩ := Sec4.mem_autIn_iff.mp σ.2
  have hmove : ∃ x₁ : E, (σ : MulAut E) x₁ ≠ x₁ := by
    by_contra hall
    push Not at hall
    exact hσ1 (MulEquiv.ext hall)
  obtain ⟨x₁, hx₁⟩ := hmove
  rw [← hk₀σ] at hx₁
  have hconj : (((E.normalizerMonoidHom ⟨k₀, hk₀N⟩) x₁ : E) : G) = k₀ * x₁ * k₀⁻¹ := rfl
  set d' : G := k₀ * x₁ * k₀⁻¹ * (x₁ : G)⁻¹ with hd'
  have hd'E : d' ∈ E := by
    rw [hd', ← hconj]
    exact E.mul_mem (E.normalizerMonoidHom ⟨k₀, hk₀N⟩ x₁).2 (E.inv_mem x₁.2)
  have hd'K : d' ∈ K := by
    have h1 : (x₁ : G) * k₀⁻¹ * (x₁ : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hEK x₁.2) _).mp (K.inv_mem hk₀K)
    have h2 : d' = k₀ * ((x₁ : G) * k₀⁻¹ * (x₁ : G)⁻¹) := by rw [hd']; group
    rw [h2]
    exact K.mul_mem hk₀K h1
  have hd'1 : d' ≠ 1 := by
    intro h
    apply hx₁
    apply Subtype.ext
    rw [hconj]
    calc k₀ * (x₁ : G) * k₀⁻¹ = d' * x₁ := by rw [hd']; group
      _ = x₁ := by rw [h, one_mul]
  obtain ⟨i, hi⟩ := isNF_of_mem_left hframe hfr.hxE hfr.hE27 hfr.h9 hd'E
  have hcomm : ⁅d', y⁆ = d ^ i := by
    have := IsNF.commutator hframe hi IsNF.gen_y
    rw [this]
    congr 1
    ring
  have hcK : ⁅d', y⁆ ∈ K := by
    have h1 : y * d'⁻¹ * y⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hyK _).mp (K.inv_mem hd'K)
    have h2 : ⁅d', y⁆ = d' * (y * d'⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact K.mul_mem hd'K h1
  have key : ∃ k ∈ K, k ∈ E ⊓ F ∧ k ^ 3 = 1 ∧ k ≠ 1 ∧ k ∉ Subgroup.zpowers e := by
    by_cases hi3 : 3 ∣ i
    ·
      obtain ⟨z, hz, hzeq⟩ := hi
      obtain ⟨m, rfl⟩ := hi3
      have hd'z : d' = z := by
        rw [hzeq, pow_mul, hframe.x3, one_pow, pow_zero, one_mul, one_mul]
      refine ⟨d', hd'K, hd'z ▸ hz, hfr.hE3 d' hd'E, hd'1, fun hmem => heK ?_⟩
      have heq := zpowers_eq_of_mem (hfr.hE3 d' hd'E) hd'1 he3 he1 hmem
      have : e ∈ Subgroup.zpowers d' := heq ▸ Subgroup.mem_zpowers e
      exact Subgroup.zpowers_le.mpr hd'K this
    ·
      have hdK : d ∈ K := by
        have hdi : d ^ i ∈ K := hcomm ▸ hcK
        have hmod : d ^ i = d ^ (i % 3) := by
          conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, hfr.hd3, one_pow, one_mul]
        rw [hmod] at hdi
        have h12 : i % 3 = 1 ∨ i % 3 = 2 := by omega
        rcases h12 with h1 | h2
        · rw [h1, pow_one] at hdi
          exact hdi
        · rw [h2] at hdi
          have : d = (d ^ 2) ^ 2 := by
            rw [← pow_mul]
            calc d = d ^ 3 * d := by rw [hfr.hd3, one_mul]
              _ = d ^ (2 * 2) := by rw [← pow_succ]
          rw [this]
          exact K.pow_mem hdi 2
      refine ⟨d, hdK, hfr.hdZ, hfr.hd3, hfr.hd1, fun hmem => heL ?_⟩
      have heq := zpowers_eq_of_mem hfr.hd3 hfr.hd1 he3 he1 hmem
      have : e ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers e
      exact Subgroup.zpowers_le.mpr hfr.hdL this
  obtain ⟨k, hkK, hkZ, hk3, hk1, hke⟩ := key
  have hinf : Subgroup.zpowers k ⊓ Subgroup.zpowers e = ⊥ :=
    Sec13.zpowers_inf_eq_bot hk3 hke
  have hke' : k * e = e * k :=
    hfr.hEab k (Subgroup.mem_inf.mp hkZ).1 e heE
  obtain ⟨α, β, hαβ⟩ := exists_pow_mul_pow_of_card hkZ heZ hke' hk3 hk1 he3 he1 hinf hfr.h9
    hfr.hcZ
  exact ⟨k, hkK, α, β, hαβ⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
