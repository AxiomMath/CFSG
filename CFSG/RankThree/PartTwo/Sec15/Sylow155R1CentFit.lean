module

public import CFSG.Open.LocalVocabulary
import CFSG.Foundations.MaxCardThompson
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.Quasithin.Background.SzQFitting

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem res1Cent_exists_prime_not_le_centralizer {G : Type} [Group G] [Finite G]
    {Γ L U : Subgroup G} (hΓ : Group.IsSolvable Γ) (h2 : CFSG.Open.pCoreOf 2 Γ = ⊥)
    (h3 : ¬ 3 ∣ Nat.card Γ) (hUΓ : U ≤ Subgroup.normalizer (Γ : Set G)) (hLUΓ : ⁅L, U⁆ ≤ Γ)
    (hLU : ⁅L, U⁆ ≠ ⊥) (hLU2 : IsPGroup 2 (⁅L, U⁆ : Subgroup G)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ¬ L ≤ Subgroup.centralizer (CFSG.Open.pCoreOf p Γ : Set G) := by
  by_contra hcon
  have hcon' : ∀ p : ℕ, p.Prime → 5 ≤ p →
      L ≤ Subgroup.centralizer (CFSG.Open.pCoreOf p Γ : Set G) :=
    fun p hp hp5 => by_contra fun hn => hcon ⟨p, hp, hp5, hn⟩
  have hq : ∀ q : ℕ, q.Prime → q ∣ Nat.card Γ →
      L ≤ Subgroup.centralizer (CFSG.Open.pCoreOf q Γ : Set G) := by
    intro q hqp hqd
    by_cases hq2 : q = 2
    · subst hq2
      rw [h2]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
    · refine hcon' q hqp ?_
      have hq3 : q ≠ 3 := fun h => h3 (h ▸ hqd)
      have hq2le := hqp.two_le
      by_contra hlt
      have hq4 : q = 4 := by omega
      exact absurd (hq4 ▸ hqp) (by norm_num)
  have hLF : L ≤ Subgroup.centralizer
      (((CFSG.fittingSubgroup ↥Γ).map Γ.subtype : Subgroup G) : Set G) := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    exact CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (fun q : (Nat.card ↥Γ).primeFactors.attach => (CFSG.pCore q.1.1 ↥Γ).map Γ.subtype)
      fun q => hq q.1.1 (Nat.prime_of_mem_primeFactors q.1.2)
        (Nat.dvd_of_mem_primeFactors q.1.2)
  have hUF : U ≤ Subgroup.normalizer
      (((CFSG.fittingSubgroup ↥Γ).map Γ.subtype : Subgroup G) : Set G) :=
    hUΓ.trans (CFSG.normalizer_le_normalizer_image_of_characteristic Γ (CFSG.fittingSubgroup ↥Γ))
  have hUF' : ⁅U, (CFSG.fittingSubgroup ↥Γ).map Γ.subtype⁆ ≤
      (CFSG.fittingSubgroup ↥Γ).map Γ.subtype :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hUF
  have hFL : ⁅(CFSG.fittingSubgroup ↥Γ).map Γ.subtype, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLF
  have hrot : ⁅⁅L, U⁆, (CFSG.fittingSubgroup ↥Γ).map Γ.subtype⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · exact le_bot_iff.mp ((Subgroup.commutator_mono_left hUF').trans hFL.le)
    · rw [hFL]
      exact Subgroup.commutator_bot_left U
  have hcent : ⁅L, U⁆ ≤ Subgroup.centralizer
      (((CFSG.fittingSubgroup ↥Γ).map Γ.subtype : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrot
  have hLUF : ∀ x ∈ (⁅L, U⁆ : Subgroup G), ∃ y ∈ CFSG.fittingSubgroup ↥Γ, (y : G) = x := by
    intro x hx
    have hxΓ : x ∈ Γ := hLUΓ hx
    refine ⟨⟨x, hxΓ⟩, ?_, rfl⟩
    refine CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hΓ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp (hcent hx)) (f : G) (Subgroup.mem_map_of_mem Γ.subtype hf))
  have hcore2 : CFSG.pCore 2 ↥Γ = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h2
  have hTp : IsPGroup 2 (Subgroup.subgroupOf ⁅L, U⁆ Γ) :=
    hLU2.of_equiv (Subgroup.subgroupOfEquivOfLe hLUΓ).symm
  have hTF : Subgroup.subgroupOf ⁅L, U⁆ Γ ≤ CFSG.fittingSubgroup ↥Γ := by
    intro y hy
    obtain ⟨y', hy', hyy⟩ := hLUF (y : G) (Subgroup.mem_subgroupOf.mp hy)
    have hyy' : y' = y := Subtype.ext hyy
    rwa [← hyy']
  have hTbot : Subgroup.subgroupOf ⁅L, U⁆ Γ = ⊥ :=
    CFSG.Quasithin.SzQ.eq_bot_of_isPGroup_two_of_le_fitting hcore2 hTp hTF
  apply hLU
  calc (⁅L, U⁆ : Subgroup G)
      = (Subgroup.subgroupOf ⁅L, U⁆ Γ).map Γ.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hLUΓ).symm
    _ = ⊥ := by rw [hTbot, Subgroup.map_bot]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
