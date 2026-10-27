module

public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem a5_perfect_eq_top155 (H : Subgroup (alternatingGroup (Fin 5))) (hH : ⁅H, H⁆ = H)
    (hne : H ≠ ⊥) : H = ⊤ := by
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  by_contra htop
  have hdvd : Nat.card H ∣ 60 := by
    rw [← h60]
    exact Subgroup.card_subgroup_dvd_card H
  have hperf : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  have hnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have hne60 : Nat.card H ≠ 60 := by
    intro h
    exact htop (Subgroup.eq_top_of_card_eq H (by rw [h, h60]))
  have h30 : Nat.card H = 30 := by
    by_contra h30
    have hle : (Nat.card H).primeFactors.card ≤ 2 := by
      have hmem : Nat.card H ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have key : ∀ d ∈ Nat.divisors 60, d ≠ 30 → d ≠ 60 → d.primeFactors.card ≤ 2 := by
        decide +kernel
      exact key _ hmem h30 hne60
    exact Group.IsPerfect.not_isSolvable H
      (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two hle)
  have hidx : H.index = 2 := by
    have := Subgroup.card_mul_index H
    rw [h30, h60] at this
    omega
  have hn : H.Normal := Subgroup.normal_of_index_eq_two hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact hne h
  · exact htop h

variable {G : Type} [Group G] [Finite G]

theorem le_pCore155 {p : ℕ} {H : Type*} [Group H] {N : Subgroup H} (hN : N.Normal)
    (hp : IsPGroup p N) : N ≤ CFSG.pCore p H :=
  le_sSup ⟨hN, hp⟩

theorem nonempty_mulEquiv_a5_of_le155 {X J : Subgroup G} (hXJ : X ≤ J)
    (hXp : Group.IsPerfect ↥X) (hX1 : X ≠ ⊥)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  set f : ↥X →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp (Subgroup.inclusion hXJ))
    with hf
  have hfker : ∀ x : ↥X, x ∈ f.ker ↔ Subgroup.inclusion hXJ x ∈ CFSG.pCore 2 ↥J := by
    intro x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hker2 : IsPGroup 2 f.ker := by
    have hinj : Function.Injective (fun x : f.ker =>
        (⟨Subgroup.inclusion hXJ x, (hfker x).mp x.2⟩ : CFSG.pCore 2 ↥J)) := by
      intro x y hxy
      apply Subtype.ext
      exact Subgroup.inclusion_injective hXJ (congrArg Subtype.val hxy)
    intro x
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥J))
      ⟨Subgroup.inclusion hXJ x, (hfker x).mp x.2⟩
    refine ⟨k, hinj ?_⟩
    simp only
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hsurj : Function.Surjective f := by
    have hrange : f.range = ⊤ := by
      apply a5_perfect_eq_top155
      · have := hXp
        rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
          Group.IsPerfect.commutator_eq_top (G := ↥X)]
      · intro hbot
        have hk : f.ker = ⊤ := by
          rw [eq_top_iff]
          intro x _
          have hx : f x ∈ f.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
          rw [hbot, Subgroup.mem_bot] at hx
          exact hx
        have hX2 : IsPGroup 2 ↥X := by
          have e' : f.ker ≃* ↥X := (MulEquiv.subgroupCongr hk).trans Subgroup.topEquiv
          exact hker2.of_equiv e'
        have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
        have : Group.IsNilpotent ↥X := hX2.isNilpotent
        exact Group.IsPerfect.not_isSolvable ↥X inferInstance
    exact MonoidHom.range_eq_top.mp hrange
  have hkerle : f.ker ≤ CFSG.pCore 2 ↥X := le_pCore155 (MonoidHom.normal_ker f) hker2
  have hle : CFSG.pCore 2 ↥X ≤ f.ker := by
    have hn : ((CFSG.pCore 2 ↥X).map f).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥X)).map f hsurj
    have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥X).map f) :=
      (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥X)).map f
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥X).map f) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      rw [ht] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
      rw [Subgroup.card_top, h60] at hk
      have h3 : (3 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num : (3 : ℕ) ∣ 60)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hle hkerle)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

@[expose] noncomputable def Step155UpPi (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ Y, IsY155 A Y →
    (¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥(oPrimeResidualOf 3 Y) ⧸
      CFSG.pCore 2 ↥(oPrimeResidualOf 3 Y)) 2 n) →
    IsEmpty (↥(oPrimeResidualOf 3 Y) ⧸ CFSG.pCore 2 ↥(oPrimeResidualOf 3 Y) ≃*
      alternatingGroup (Fin 5)) →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ oPrimeResidualOf 3 Y) ⊔ CFSG.Open.pCoreOf 2 L') →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
    ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → oPrimeResidualOf 3 Y < J →
    (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n) →
    ∀ K ∈ scriptY0Star A (lB A), J ≤ K →
      (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        L' = (L' ⊓ J) ⊔ CFSG.Open.pCoreOf 2 L') ∨ K = J ⊔ CFSG.Open.pCoreOf 2 K

theorem step155Up_of_pi {A : Subgroup G} {c : G} {L : Subgroup G} (hpi : Step155UpPi A c L) :
    Step155Up A c L := by
  intro h Y hY hXpi hXa5 hXcl M hM J hJM hJ0 hXJ K hK hJK
  have hX4 : oPrimeResidualOf 3 Y ∈ scriptY4 A (lB A) := hY.2.1
  by_cases hJpi : ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n
  · rcases hpi h Y hY hXpi hXa5 hXcl M hM J hJM hJ0 hXJ hJpi K hK hJK with hcl | hKJ
    · exact Or.inl (Or.inr hcl)
    · exact Or.inr hKJ
  · refine Or.inl (Or.inl ⟨hJpi, ⟨fun e => ?_⟩⟩)
    obtain ⟨e'⟩ := nonempty_mulEquiv_a5_of_le155 hXJ.le (isPerfect_of_mem_scriptY4 hX4)
      (ne_bot_of_mem_scriptY4 hX4) e
    exact hXa5.false e'

end CFSG.RankThree.PartTwo.Sec15
