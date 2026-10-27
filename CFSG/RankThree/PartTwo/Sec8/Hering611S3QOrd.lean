module

import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction
public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.RankThree.PartTwo.KFacts

private theorem conj_injective_psl2 (K : Type) [Field K] [Finite K] :
    Function.Injective (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) := by
  intro x y hxy
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  apply CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K
  rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL,
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL]
  exact hxy

theorem card_two_subgroup_inn_dvd_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 6)
    (Q : Subgroup (MulAut (PSL2 K))) (hQ2 : IsPGroup 2 Q)
    (hQI : Q ≤ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range) : Nat.card Q ∣ 8 := by
  have hcinj := conj_injective_psl2 K
  have hodd : IsOddPrimePower (Nat.card K) := ⟨3, 6, Nat.prime_three, ⟨1, rfl⟩, by norm_num, hK⟩
  have hPSL : Nat.card (PSL2 K) = 8 * 24213735 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula K hodd, hK] <;> norm_num
  have hmap : (Q.comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K))).map
      (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) = Q := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hQI]
  have hcard : Nat.card (Q.comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K))) = Nat.card Q := by
    have h := Subgroup.card_map_of_injective
      (K := Q.comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K))) hcinj
    rw [hmap] at h
    exact h.symm
  have hpg : IsPGroup 2 (Q.comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K))) := by
    intro g
    have hg : (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) (g : PSL2 K) ∈ Q := g.2
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hg⟩
    have h1 : (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) (g : PSL2 K) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    refine ⟨k, Subtype.ext (hcinj ?_)⟩
    simpa [map_pow] using h1
  haveI : Finite (Q.comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K))) := inferInstance
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
  have hdvd := Subgroup.card_subgroup_dvd_card (Q.comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K)))
  rw [hn, hPSL] at hdvd
  have hcop : Nat.Coprime (2 ^ n) 24213735 := Nat.Coprime.pow_left n (by norm_num)
  rw [← hcard, hn]
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem index_inn_pglRange {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 6) :
    ((MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range.subgroupOf (pglAction K).range).index = 2 := by
  have hinj : Function.Injective (pglAction K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K
  have hodd : IsOddPrimePower (Nat.card K) := ⟨3, 6, Nat.prime_three, ⟨1, rfl⟩, by norm_num, hK⟩
  have hmap : ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).map
      (MonoidHom.ofInjective hinj).toMonoidHom =
      (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range.subgroupOf (pglAction K).range := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨g, ⟨y, rfl⟩, rfl⟩
      show pglAction K (Matrix.ProjectiveSpecialLinearGroup.toPGL y) ∈ _
      rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL]
      exact ⟨y, rfl⟩
    · intro hx
      obtain ⟨y, hy⟩ := hx
      obtain ⟨g, hg⟩ := x.2
      have hyg : Matrix.ProjectiveSpecialLinearGroup.toPGL y = g := by
        apply hinj
        rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL, hy, hg]
      exact ⟨g, ⟨y, hyg⟩, Subtype.ext hg⟩
  rw [← hmap]
  exact (Subgroup.index_map_equiv _ (MonoidHom.ofInjective hinj)).trans
    (CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two K hodd)

theorem card_mod_three_of_fpf {M : Type*} [Group M] {R : Subgroup M} [Finite R] {β : M}
    (hβ3 : β ^ 3 = 1) (hβR : ∀ r ∈ R, β * r * β⁻¹ ∈ R)
    (hfix : ∀ r ∈ R, β * r * β⁻¹ = r → r = 1) : Nat.card R % 3 = 1 := by
  classical
  haveI := Fintype.ofFinite R
  let f : Function.End R := fun r => ⟨β * (r : M) * β⁻¹, hβR (r : M) r.2⟩
  have hpow : ∀ (n : ℕ) (r : R), ((f^[n] r : R) : M) = β ^ n * (r : M) * (β ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro r
      show ((r : R) : M) = β ^ 0 * (r : M) * (β ^ 0)⁻¹
      simp
    | succ n ih =>
      intro r
      rw [Function.iterate_succ_apply']
      show β * ((f^[n] r : R) : M) * β⁻¹ = _
      rw [ih r]
      group
  have hf : f ^ 3 ^ 1 = 1 := by
    funext r
    apply Subtype.ext
    show ((f^[3 ^ 1] r : R) : M) = (r : M)
    rw [hpow, pow_one, hβ3]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have hfp : Nat.card (Function.fixedPoints f) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · show f 1 = 1
      apply Subtype.ext
      show β * ((1 : R) : M) * β⁻¹ = ((1 : R) : M)
      simp
    · rintro ⟨y, hy⟩
      have hy2 : f y = y := hy
      have hy' : β * (y : M) * β⁻¹ = (y : M) := congrArg Subtype.val hy2
      apply Subtype.ext
      apply Subtype.ext
      exact hfix (y : M) y.2 hy'
  rw [hfp] at hmod
  unfold Nat.ModEq at hmod
  omega

end CFSG.RankThree.PartTwo.Sec8.Hering611
