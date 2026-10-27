module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.SEITZ2.SUnMain

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {σ : K ≃+* K} {σ₀ : k ≃+* k}

theorem exists_center {N : ℕ} (hN : 4 ≤ N) (hσi : ∀ c, σ (σ c) = c)
    (hσ₀ : IsUnitaryInvolution σ₀) (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K))
    (A : GL (Fin N) K)
    (hA : conjTr σ (A : Matrix (Fin N) (Fin N) K) * (A : Matrix (Fin N) (Fin N) K) = 1)
    (hne : (phiN hσk).range.map (conjU A hA) ≠ (phiN hσk).range) :
    ∃ y : Fin N → K, y ≠ 0 ∧ herm σ y y = 0 ∧
      (∃ t ∈ (phiN hσk).range ⊔ (phiN hσk).range.map (conjU A hA), IsTv σ t y 1) ∧
      ¬ ∃ lam : K, lam ≠ 0 ∧ σ lam * lam ∈ k ∧ ∃ w : Fin N → K, (∀ i, w i ∈ k) ∧
        y = lam • w := by
  classical
  set R := (phiN hσk).range with hR
  set R' := R.map (conjU A hA) with hR'
  set M := R ⊔ R' with hM
  have hR'M : R' ≤ M := le_sup_right
  have hex : ∃ (t₁ : SUid σ₀ N) (a₁ : Fin N → k) (c₁ : k), IsTv σ₀ t₁ a₁ c₁ ∧
      herm σ₀ a₁ a₁ = 0 ∧ c₁ + σ₀ c₁ = 0 ∧ conjU A hA (phiN hσk t₁) ∉ R := by
    by_contra hcon
    push Not at hcon
    have hle : R' ≤ R := by
      let S : Subgroup (SUid σ₀ N) := R.comap ((conjU A hA).comp (phiN hσk))
      have hT : T σ₀ N ≤ S := by
        rw [T]
        refine (Subgroup.closure_le S).2 ?_
        rintro t ⟨a, c, ha', hc', ht⟩
        exact hcon t a c ht ha' hc'
      have htop : T σ₀ N = ⊤ := T_eq_top hσ₀ (by omega) (fun h => absurd h (by omega))
      have hS : S = ⊤ := eq_top_iff.2 (htop ▸ hT)
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      have hg : g ∈ S := hS ▸ Subgroup.mem_top g
      exact hg
    have hcard : Nat.card R' = Nat.card R :=
      Subgroup.card_map_of_injective (conjU_injective A hA)
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  obtain ⟨t₁, a₁, c₁, ht₁, ha₁, hc₁, hnot⟩ := hex
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha₁0 : a₁ ≠ 0 := by
    intro h
    apply hnot
    have h1 : t₁ = 1 := by
      apply ext_smul σ₀
      intro v
      rw [ht₁ v, h]
      simp
    rw [h1, map_one, map_one]
    exact R.one_mem
  set a : Fin N → K := incl a₁ with ha_def
  set y : Fin N → K := (A : Matrix (Fin N) (Fin N) K) *ᵥ a with hy_def
  have haiso : herm σ a a = 0 := by
    rw [ha_def, herm_incl hσk, ha₁]
    rfl
  have hyiso : herm σ y y = 0 := by rw [hy_def, herm_unitary_mulVec hA]; exact haiso
  have hAinv : ∀ v : Fin N → K, (((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
      ((A : Matrix (Fin N) (Fin N) K) *ᵥ v)) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hy0 : y ≠ 0 := by
    intro h
    have h1 : a = 0 := by
      have := hAinv a
      rw [← hy_def, h, Matrix.mulVec_zero] at this
      exact this.symm
    apply ha₁0
    apply incl_injective (K := K)
    rw [← ha_def, h1]
    funext i
    simp [incl]
  have hc₁σ : σ (c₁ : K) = c₁ := by
    have := congrArg (fun z : k => (z : K)) hc₁
    simp only [Subfield.coe_add, Subfield.coe_zero] at this
    rw [← hσk] at this
    linear_combination this - (c₁ : K) * h2
  refine ⟨y, hy0, hyiso, ?_, ?_⟩
  · have hc' : (⟨1, k.one_mem⟩ : k) + σ₀ ⟨1, k.one_mem⟩ = 0 := by
      apply Subtype.ext
      change (1 : K) + ((σ₀ ⟨1, k.one_mem⟩ : k) : K) = 0
      rw [← hσk ⟨1, k.one_mem⟩]
      simp only [map_one]
      exact CharTwo.add_self_eq_zero 1
    obtain ⟨t₂, ht₂⟩ := exists_isTv hσ₀.invol ha₁ hc'
    exact ⟨conjU A hA (phiN hσk t₂), hR'M ⟨phiN hσk t₂, ⟨t₂, rfl⟩, rfl⟩,
      (isTv_phiN hσk ht₂).conjU⟩
  · rintro ⟨lam, hlam0, hlamN, w, hw, hyw⟩
    have ht : IsTv σ (conjU A hA (phiN hσk t₁)) y (c₁ : K) := (isTv_phiN hσk ht₁).conjU
    rw [hyw, isTv_smul_vec] at ht
    have hNlam : σ lam * lam ≠ 0 := mul_ne_zero ((map_ne_zero σ).2 hlam0) hlam0
    have hwiso : herm σ w w = 0 := by
      have h3 : herm σ y y = (σ lam * lam) * herm σ w w := by
        rw [hyw, herm_smul_left, herm_smul_right]
        ring
      rw [hyiso] at h3
      exact (mul_eq_zero.1 h3.symm).resolve_left hNlam
    obtain ⟨t', ht'R, ht'⟩ := exists_phiN_isTv hσ₀.invol hσk hw hwiso
      (c := (c₁ : K) * (σ lam * lam)) (k.mul_mem c₁.2 hlamN)
      (by rw [map_mul, hc₁σ, map_mul, hσi]; ring)
    exact hnot (ht.unique ht' ▸ ht'R)

end CFSG.RankThree.PartOne.SEITZ5
