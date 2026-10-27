module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.GH74.Generic.S45.LAlt6

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open Subgroup CFSG.ComponentClassification

theorem ks1543A6 : KS1543A6 := by
  intro Q _ _ hQ htc K hK1 hKp P hP hKP
  classical
  haveI : Group.IsPerfect Q := hQ.1
  haveI : Group.IsPerfect K := hKp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨φ⟩⟩ := htc
  set Z := Subgroup.center Q with hZ
  set π : Q →* Q ⧸ Z := QuotientGroup.mk' Z with hπ
  set c : Q →* MulAut Q := MulAut.conj with hc
  have hcZ : ∀ q : Q, c q = 1 → q ∈ Z := by
    intro q hq
    rw [hZ, Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun σ : MulAut Q => σ g) hq
    simp only [hc, MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * q = q * g * q⁻¹ * q := by rw [h1]
      _ = q * g := by group
  have hπZ : ∀ q : Q, q ∈ Z → π q = 1 := fun q hq => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hq
  set T : Subgroup (Q ⧸ Z) := K.map π with hT
  have hTp : Group.IsPerfect T := Group.IsPerfect.map π
  have hT1 : T ≠ ⊥ := by
    intro h
    apply hK1
    have hKZ : K ≤ Z := by
      rw [hT, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
      exact h
    calc K = ⁅K, K⁆ := Subgroup.commutator_eq_self.symm
      _ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact Subgroup.mem_center_iff.mp (hKZ hx) y
  set S : Subgroup (Q ⧸ Z) := ((P ⊓ c.range).comap c).map π with hS
  have hS2 : IsPGroup 2 S := by
    rintro ⟨_, q, hq, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hq
    obtain ⟨n, hn⟩ := hP ⟨c q, (Subgroup.mem_inf.mp hq).1⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : c (q ^ 2 ^ n) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    exact hπZ _ (hcZ _ h1)
  have hTS : T ≤ normalizer (S : Set (Q ⧸ Z)) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨q, hq, rfl⟩
    refine ⟨k * q * k⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hq ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨k * q * k⁻¹, rfl⟩⟩
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hKP k hk) (c q)).mp (Subgroup.mem_inf.mp hq).1
  have hSbot : S = ⊥ := by
    haveI := hS2.isNilpotent
    exact Proof15Res8Diag.eq_bot_of_isSolvable_six φ hTp hT1 inferInstance hTS
  have hPinn : ∀ q : Q, c q ∈ P → q ∈ Z := by
    intro q hq
    have hqS : π q ∈ S :=
      ⟨q, Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨hq, ⟨q, rfl⟩⟩), rfl⟩
    rw [hSbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hqS
    exact hqS
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hfixT : ∀ t ∈ T, PerfectAutomorphisms.onCenterQuotient σ t = t := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : c (σ k * k⁻¹) ∈ P := by
      have h : c (σ k * k⁻¹) = σ * (c k * σ⁻¹ * (c k)⁻¹) := by
        ext x
        simp [hc, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, mul_assoc]
      rw [h]
      exact P.mul_mem hσ ((mem_normalizer_iff.mp (hKP k hk) σ⁻¹).mp (P.inv_mem hσ))
    have h2 := hπZ _ (hPinn _ h1)
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    rw [hπ, PerfectAutomorphisms.onCenterQuotient_apply_mk]
    exact h2
  have hσ1 : PerfectAutomorphisms.onCenterQuotient σ = 1 := by
    rcases Proof15Res8Diag.eq_top_or_card_eq_sixty_six φ hTp hT1 with hTt | ⟨-, h60⟩
    · ext x
      rw [MulAut.one_apply]
      exact hfixT x (hTt ▸ Subgroup.mem_top x)
    · haveI : IsSimpleGroup (Q ⧸ Z) := hQ.2.1
      exact GH74.Generic.S45.LAlt.aut_eq_one_of_fixes_index_six (Proof15Res8Diag.card_six φ) _ T
        h60 hfixT
  exact PerfectAutomorphisms.onCenterQuotient_eq_one_imp σ hσ1

end CFSG.RankThree.PartTwo.Sec15.Wales154
