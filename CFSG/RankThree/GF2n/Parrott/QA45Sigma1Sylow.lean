module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem sigma2_mul_alpha2_mul_sigma2_inv : sigma2 * alpha2 * sigma2⁻¹ = beta2 := by
  decide +kernel

theorem sigma2_mul_beta2_mul_sigma2_inv : sigma2 * beta2 * sigma2⁻¹ = beta2 * alpha2 := by
  decide +kernel

theorem beta2_ne_alpha2 : beta2 ≠ alpha2 := by
  decide +kernel


theorem exists_mem_centralizer_sigma1_conj_closure_alpha2_beta2
    {A' : Subgroup QA45.originalSubgroup}
    (hle : A' ≤ Subgroup.centralizer
      ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup))
    (hcard : Nat.card A' = 8) :
    ∃ c ∈ Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup),
      ∀ x, x ∈ A' ↔ c⁻¹ * x * c ∈ Subgroup.closure
        ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup QA45.originalSubgroup :=
    Subgroup.closure ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} :
      Set QA45.originalSubgroup) with hA
  have hAK : A ≤ Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} :
      Set QA45.originalSubgroup) := by
    rw [hA]
    exact qa45_sigma_centralizer_sylow.1.1
  have hAcard : Nat.card A = 8 := by
    rw [hA]
    exact qa45_sigma_centralizer_sylow.1.2.1
  have hKcard : Nat.card (Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} :
      Set QA45.originalSubgroup)) = 648 := card_centralizer_sigma1_QA45
  have h648 : Nat.factorization 648 2 = 3 := by
    have hfac : 648 = 2 ^ 3 * 81 := by norm_num
    rw [hfac, Nat.factorization_mul (a := (2 : ℕ) ^ 3) (b := 81)
      (by norm_num) (by norm_num)]
    change ((2 : ℕ) ^ 3).factorization 2 + (81 : ℕ).factorization 2 = 3
    rw [Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (81 : ℕ)), add_zero]
  have hAsylow : CFSG.ABGLocalTools.IsSylowOf 2 A
      (Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup)) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hAK ?_
    rw [hAcard, hKcard, h648]
    norm_num
  have hA'sylow : CFSG.ABGLocalTools.IsSylowOf 2 A'
      (Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup)) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [hcard, hKcard, h648]
    norm_num
  obtain ⟨c, hcK, hc⟩ := hAsylow.exists_mem_conj hA'sylow
  exact ⟨c, hcK, fun x => hc x⟩

theorem nonempty_mulEquiv_quaternionGroup_of_le_centralizer_sigma1
    {A' : Subgroup QA45.originalSubgroup}
    (hle : A' ≤ Subgroup.centralizer
      ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup))
    (hcard : Nat.card A' = 8) :
    Nonempty (↥A' ≃* QuaternionGroup 2) := by
  classical
  obtain ⟨c, -, hc⟩ :=
    exists_mem_centralizer_sigma1_conj_closure_alpha2_beta2 hle hcard
  set A : Subgroup QA45.originalSubgroup :=
    Subgroup.closure ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} :
      Set QA45.originalSubgroup) with hA
  have hcA : ∀ x, x ∈ A' ↔ c⁻¹ * x * c ∈ A := by
    intro x
    rw [hA]
    exact hc x
  let e : ↥A' ≃* ↥A :=
    { toFun := fun x => ⟨c⁻¹ * (x : QA45.originalSubgroup) * c, (hcA x).mp x.2⟩
      invFun := fun y => ⟨c * (y : QA45.originalSubgroup) * c⁻¹, (hcA _).mpr (by
        have hcy : c⁻¹ * (c * (y : QA45.originalSubgroup) * c⁻¹) * c =
            (y : QA45.originalSubgroup) := by group
        rw [hcy]
        exact y.2)⟩
      left_inv := fun x => Subtype.ext (by
        show c * (c⁻¹ * (x : QA45.originalSubgroup) * c) * c⁻¹ =
          (x : QA45.originalSubgroup)
        group)
      right_inv := fun y => Subtype.ext (by
        show c⁻¹ * (c * (y : QA45.originalSubgroup) * c⁻¹) * c =
          (y : QA45.originalSubgroup)
        group)
      map_mul' := fun x y => Subtype.ext (by
        show c⁻¹ * ((x : QA45.originalSubgroup) * (y : QA45.originalSubgroup)) * c =
          (c⁻¹ * (x : QA45.originalSubgroup) * c) *
            (c⁻¹ * (y : QA45.originalSubgroup) * c)
        group) }
  have hAq : Nonempty (↥A ≃* QuaternionGroup 2) := by
    rw [hA]
    exact qa45_sigma_centralizer_sylow.1.2.2
  obtain ⟨f⟩ := hAq
  exact ⟨e.trans f⟩

theorem exists_pow_three_eq_one_normalizes_of_le_centralizer_sigma1
    {A' : Subgroup QA45.originalSubgroup}
    (hle : A' ≤ Subgroup.centralizer
      ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup))
    (hcard : Nat.card A' = 8) :
    ∃ r ∈ Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup),
      r ^ 3 = 1 ∧ (∀ x ∈ A', r * x * r⁻¹ ∈ A') ∧ ∃ x ∈ A', r * x * r⁻¹ ≠ x := by
  classical
  let a : QA45.originalSubgroup := ⟨alpha2, alpha2_mem_A⟩
  let b : QA45.originalSubgroup := ⟨beta2, beta2_mem_A⟩
  let s2 : QA45.originalSubgroup := ⟨sigma2, sigma2_mem_A⟩
  set A : Subgroup QA45.originalSubgroup :=
    Subgroup.closure ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} :
      Set QA45.originalSubgroup) with hA
  obtain ⟨c, hcK, hc⟩ :=
    exists_mem_centralizer_sigma1_conj_closure_alpha2_beta2 hle hcard
  let r : QA45.originalSubgroup := c * s2 * c⁻¹
  have hs2cube : s2 ^ 3 = 1 := by
    refine Subtype.ext ?_
    simpa [s2] using sigma2_cube
  have hr3 : r ^ 3 = 1 := by
    have hconj : r = (MulAut.conj c) s2 := by
      show c * s2 * c⁻¹ = (MulAut.conj c) s2
      exact (MulAut.conj_apply c s2).symm
    rw [hconj, ← map_pow, hs2cube, map_one]
  have hs2K : s2 ∈ Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} :
      Set QA45.originalSubgroup) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext sigma1_commute_sigma2.symm
  have hrK : r ∈ Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} :
      Set QA45.originalSubgroup) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hcK hs2K) (Subgroup.inv_mem _ hcK)
  have hs2a : s2 * a * s2⁻¹ = b := by
    refine Subtype.ext ?_
    simpa [s2, a, b] using sigma2_mul_alpha2_mul_sigma2_inv
  have hs2b : s2 * b * s2⁻¹ = b * a := by
    refine Subtype.ext ?_
    simpa [s2, a, b] using sigma2_mul_beta2_mul_sigma2_inv
  have hcomap : A ≤ Subgroup.comap (MulAut.conj s2).toMonoidHom A := by
    conv_lhs => rw [hA]
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · change (MulAut.conj s2) a ∈ A
      rw [MulAut.conj_apply, hs2a]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · change (MulAut.conj s2) b ∈ A
      rw [MulAut.conj_apply, hs2b]
      exact A.mul_mem
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        (Subgroup.subset_closure (Set.mem_insert _ _))
  have hnorm : ∀ y ∈ A, s2 * y * s2⁻¹ ∈ A := by
    intro y hy
    simpa [MulAut.conj_apply] using hcomap hy
  have hA'norm : ∀ x ∈ A', r * x * r⁻¹ ∈ A' := by
    intro x hx
    refine (hc (r * x * r⁻¹)).mpr ?_
    have hconv : c⁻¹ * (r * x * r⁻¹) * c = s2 * (c⁻¹ * x * c) * s2⁻¹ := by
      dsimp only [r]
      group
    rw [hconv]
    exact hnorm _ ((hc x).mp hx)
  have hxA' : c * a * c⁻¹ ∈ A' := by
    refine (hc (c * a * c⁻¹)).mpr ?_
    have hca : c⁻¹ * (c * a * c⁻¹) * c = a := by group
    rw [hca]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hrx : r * (c * a * c⁻¹) * r⁻¹ = c * b * c⁻¹ := by
    dsimp only [r]
    calc (c * s2 * c⁻¹) * (c * a * c⁻¹) * (c * s2 * c⁻¹)⁻¹
        = c * (s2 * a * s2⁻¹) * c⁻¹ := by group
      _ = c * b * c⁻¹ := by rw [hs2a]
  have hba_ne : b ≠ a := by
    intro h
    exact beta2_ne_alpha2 (by
      have hval := congrArg (fun z : QA45.originalSubgroup => (z : Equiv.Perm (Fin 45))) h
      simpa [a, b] using hval)
  have hne : c * b * c⁻¹ ≠ c * a * c⁻¹ := by
    intro h
    exact hba_ne ((MulAut.conj c).injective (by
      simpa [MulAut.conj_apply] using h))
  exact ⟨r, hrK, hr3, hA'norm, ⟨c * a * c⁻¹, hxA', by rw [hrx]; exact hne⟩⟩

end CFSG.RankThree.GF2n.Parrott
