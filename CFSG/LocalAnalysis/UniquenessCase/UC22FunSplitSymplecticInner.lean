module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCModel
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts

theorem normalizer_inner_of_isLongRootSp2 {K : Type} [Field K] {n : ℕ}
    (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)} {i : StatedSp n K}
    (hL : IsLongRootSp2 L i) {g : StatedSp n K}
    (hg : g ∈ normalizer (L : Set (StatedSp n K))) :
    ∃ r ∈ L, ∀ x ∈ L, g * x * g⁻¹ = r * x * r⁻¹ := by
  have hcl := hL.isClassicalSL2 h2
  have huniq : CFSG.ClassicalInvolution.Generic.IsUniqueInvolution L i :=
    { mem := hcl.mem
      ne_one := by
        intro h1
        have hord := hcl.orderOf_eq_two
        rw [h1, orderOf_one] at hord
        omega
      sq := by
        have h := pow_orderOf_eq_one i
        rw [hcl.orderOf_eq_two] at h
        simpa [pow_two] using h
      unique := by
        intro y hy hy2
        by_cases h1 : y = 1
        · exact Or.inl h1
        · exact Or.inr (hL.eq_of_orderOf_eq_two h2 hy
            (orderOf_eq_prime (by rwa [pow_two]) h1)) }
  have hgc : g ∈ Subgroup.centralizer ({i} : Set (StatedSp n K)) :=
    CFSG.ClassicalInvolution.G2D4Models.normalizer_le_centralizer huniq hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hL.exists_mul_of_mem_centralizer h2 hgc
  refine ⟨a, ha, fun x hx => ?_⟩
  have hbx : b * x * b⁻¹ = x := by
    have hcomm : Commute x b := hL.commute_of_mem_complGroup h2 hx hb
    rw [Commute.eq hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
  calc
    (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = a * x * a⁻¹ := by rw [hbx]

theorem normalizer_inner_fundamental_psp
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n e : ℕ} (hadm : StatedLieAdmissible .PSp n p e)
    (R : Subgroup (modelUniv .PSp n p e Fact.out).K)
    (hR : R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D)
    (g : (modelUniv .PSp n p e Fact.out).K)
    (hg : g ∈ normalizer (R : Set (modelUniv .PSp n p e Fact.out).K)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨P, hP, hRP⟩ :=
    (mem_fundamentalSubgroups_PSp_iff (m := n) (f := e) hadm R).mp hR
  subst R
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 (planeGroup P)).mpr ⟨P, hP, rfl⟩
  exact normalizer_inner_of_isLongRootSp2 h2 hi hg

end CFSG.LocalAnalysis.UniquenessCase.UC22
