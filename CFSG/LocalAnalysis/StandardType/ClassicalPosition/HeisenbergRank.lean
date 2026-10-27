module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDescent
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergInduction

public section

namespace CFSG.StandardType.ClassicalPosition

private lemma heisRk_natCast_ne_zero {K : Type} [Field K] {p : ℕ} (hp : (p : K) ≠ 0) :
    (p : AlgebraicClosure K) ≠ 0 := by
  intro h
  apply hp
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [← map_natCast (algebraMap K (AlgebraicClosure K)) p] at h
  simpa using h

theorem dvd_and_card_le_of_not_commute_lifts {K : Type} [Field K] {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) (E : Subgroup (GL (Fin N) K))
    (hpow : ∀ a ∈ E, a ^ p ∈ Subgroup.center (GL (Fin N) K))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center (GL (Fin N) K))
    (hnc : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a) :
    p ∣ N ∧ Nat.card (E ⧸ (Subgroup.center (GL (Fin N) K)).subgroupOf E) ≤ p ^ (N / p + 1) := by
  have hpF : (p : AlgebraicClosure K) ≠ 0 := heisRk_natCast_ne_zero hp
  obtain ⟨φ, hφ_inj, hker⟩ := HeisRank.exists_rep_over (F := AlgebraicClosure K) E
  have hpow' : ∀ g : E, φ g ^ p ∈ HeisRank.scalarAut (AlgebraicClosure K)
      (Fin N → AlgebraicClosure K) := by
    intro g
    have hg : φ (g ^ p) ∈ HeisRank.scalarAut (AlgebraicClosure K)
        (Fin N → AlgebraicClosure K) := by
      rw [← Subgroup.mem_comap, hker, Subgroup.mem_subgroupOf]
      simpa using hpow (g : GL (Fin N) K) g.2
    rwa [map_pow] at hg
  have hcomm' : ∀ g h : E, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈
      HeisRank.scalarAut (AlgebraicClosure K) (Fin N → AlgebraicClosure K) := by
    intro g h
    have hg : φ (g * h * g⁻¹ * h⁻¹) ∈ HeisRank.scalarAut (AlgebraicClosure K)
        (Fin N → AlgebraicClosure K) := by
      rw [← Subgroup.mem_comap, hker, Subgroup.mem_subgroupOf]
      simpa using hcomm (g : GL (Fin N) K) g.2 (h : GL (Fin N) K) h.2
    have heq : φ (g * h * g⁻¹ * h⁻¹) = φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ := by
      simp only [map_mul, map_inv]
    rwa [heq] at hg
  have hnc' : ∃ g h : E, φ g * φ h ≠ φ h * φ g := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    intro h
    apply hab
    have h2 : ((⟨a, ha⟩ : E) * ⟨b, hb⟩ : E) = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply hφ_inj
      rwa [map_mul, map_mul]
    have h3 := congrArg (fun x : E => (x : GL (Fin N) K)) h2
    simpa using h3
  obtain ⟨hdvd, -, hle⟩ := HeisRank.dvd_and_index_le_of_not_commute
    (F := AlgebraicClosure K) (V := Fin N → AlgebraicClosure K) (G := E) (p := p)
    hp2 hpF φ hpow' hcomm' hnc'
  rw [hker] at hle
  refine ⟨?_, ?_⟩
  · simpa [Module.finrank_fin_fun] using hdvd
  · rw [← Subgroup.index_eq_card]
    simpa [Module.finrank_fin_fun] using hle

theorem card_le_of_commute_lifts {K : Type} [Field K] {N p : ℕ}
    (hp : (p : K) ≠ 0) (E : Subgroup (GL (Fin N) K))
    (hpow : ∀ a ∈ E, a ^ p ∈ Subgroup.center (GL (Fin N) K))
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Nat.card (E ⧸ (Subgroup.center (GL (Fin N) K)).subgroupOf E) ≤ p ^ (N - 1) := by
  have hpF : (p : AlgebraicClosure K) ≠ 0 := heisRk_natCast_ne_zero hp
  obtain ⟨φ, hφ_inj, hker⟩ := HeisRank.exists_rep_over (F := AlgebraicClosure K) E
  have hpow' : ∀ g : E, φ g ^ p ∈ HeisRank.scalarAut (AlgebraicClosure K)
      (Fin N → AlgebraicClosure K) := by
    intro g
    have hg : φ (g ^ p) ∈ HeisRank.scalarAut (AlgebraicClosure K)
        (Fin N → AlgebraicClosure K) := by
      rw [← Subgroup.mem_comap, hker, Subgroup.mem_subgroupOf]
      simpa using hpow (g : GL (Fin N) K) g.2
    rwa [map_pow] at hg
  have hc' : ∀ g h : E, φ g * φ h = φ h * φ g := by
    intro g h
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using hc (g : GL (Fin N) K) g.2 (h : GL (Fin N) K) h.2
  obtain ⟨-, hle⟩ := HeisRank.index_le_of_commute
    (F := AlgebraicClosure K) (V := Fin N → AlgebraicClosure K) (G := E) (p := p)
    hpF φ hpow' hc'
  rw [hker] at hle
  rw [← Subgroup.index_eq_card]
  simpa [Module.finrank_fin_fun] using hle

end CFSG.StandardType.ClassicalPosition
