module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionSetup
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionHall
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly.RankThreeEven
  CFSG.RankThree.GroupTheory

variable {G : Type*} [Group G]

theorem nontrivial_action_on_pCore [Finite G] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {W R₁ : Subgroup G} (hW : ∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = q)
    [Group.IsSolvable W] (hO2 : inSubgroup (pCore 2) W = ⊥) (hR₁W : R₁ ≤ W)
    (hR₁2 : IsPGroup 2 R₁) (hR₁ : R₁ ≠ ⊥) : ⁅R₁, inSubgroup (pCore q) W⁆ ≠ ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have hO2' : pCore 2 W = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (pCore 2 W) W.subtype_injective).mp hO2
  have hF : fittingSubgroup W = pCore q W := by
    apply le_antisymm
    · rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
      refine iSup_le fun p => ?_
      have hp := Nat.prime_of_mem_primeFactors p.2
      rcases hW p hp (Nat.dvd_of_mem_primeFactors p.2) with h | h
      · rw [h, hO2']
        exact bot_le
      · rw [h]
    · exact CFSG.LocalCores.fitting_characteristic.2.2 _ inferInstance (pCore_isNilpotent)
  have hcent : centralizer (pCore q W : Set W) ≤ pCore q W := by
    rw [← hF]
    exact CFSG.RankThree.PGroups.solvable_fitting_self_centralizing W
  intro hcomm
  have hle : R₁ ≤ centralizer ((inSubgroup (pCore q) W : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h1 : R₁.subgroupOf W ≤ pCore q W := by
    intro x hx
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ inSubgroup (pCore q) W := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle hx) y hy')
  have hR2 : IsPGroup 2 (R₁.subgroupOf W) :=
    hR₁2.of_equiv (Subgroup.subgroupOfEquivOfLe hR₁W).symm
  have hRq : IsPGroup q (R₁.subgroupOf W) := (pCore_isPGroup (p := q) (G := W)).to_le h1
  have hbot : R₁.subgroupOf W = ⊥ := by
    have := inf_eq_bot_of_isPGroup Nat.prime_two hq (Ne.symm hq2) hR2 hRq
    simpa using this
  apply hR₁
  refine eq_bot_iff.mpr fun x hx => ?_
  have : (⟨x, hR₁W hx⟩ : W) ∈ R₁.subgroupOf W := hx
  rw [hbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem subgroupOf_eq_bot_iff {H K : Subgroup G} (h : H ≤ K) : H.subgroupOf K = ⊥ ↔ H = ⊥ := by
  constructor
  · intro hbot
    refine eq_bot_iff.mpr fun x hx => ?_
    have : (⟨x, h hx⟩ : K) ∈ H.subgroupOf K := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · rintro rfl
    ext x
    simp

theorem qd32_of_core_action (hI2 : TwoLocalRankTwoOddCoreAction) {G : Type} [Group G] [Finite G]
    {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) (hloc : localRank q G ≤ 2)
    {H₁ R₁ O : Subgroup G} {c : G} (hc5 : orderOf c = 5) (hcH : c ∈ H₁) (hR₁H : R₁ ≤ H₁)
    (hR₁2 : IsPGroup 2 R₁) (hR₁ : R₁ ≠ ⊥) (hcR : c ∈ normalizer (R₁ : Set G))
    (hRc : ⁅R₁, zpowers c⁆ = R₁) (hOq : IsPGroup q O) (hOH : O ≤ H₁)
    (hHO : H₁ ≤ normalizer (O : Set G)) (hRO : ⁅R₁, O⁆ ≠ ⊥) :
    Nonempty (R₁ ≃* QD32) := by
  have hzH : zpowers c ≤ H₁ := Subgroup.zpowers_le.mpr hcH
  have hzR : zpowers c ≤ normalizer (R₁ : Set G) := Subgroup.zpowers_le.mpr hcR
  have h5 : Nat.Prime 5 := by norm_num
  obtain ⟨-, hQD, -⟩ := hI2 H₁ 5 q ((zpowers c).subgroupOf H₁) (R₁.subgroupOf H₁) h5 hq
    (by norm_num) (by omega) (by omega)
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzH).toEquiv).trans
      ((Nat.card_zpowers c).trans hc5))
    (fun a ha => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hax := (Subgroup.mem_normalizer_iff.mp (hzR (Subgroup.mem_subgroupOf.mp ha)) x)
      simpa [Subgroup.mem_subgroupOf] using hax)
    (hR₁2.of_equiv (Subgroup.subgroupOfEquivOfLe hR₁H).symm)
    (fun h => hR₁ ((subgroupOf_eq_bot_iff hR₁H).mp h))
    (by
      apply Subgroup.map_injective H₁.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hR₁H,
        Subgroup.map_subgroupOf_eq_of_le hzH, hRc])
    (by
      intro hcomm
      apply hRO
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hnormal : (O.subgroupOf H₁).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr hHO
      have hpg : IsPGroup q (O.subgroupOf H₁) :=
        hOq.of_equiv (Subgroup.subgroupOfEquivOfLe hOH).symm
      have hY : (⟨y, hOH hy⟩ : H₁) ∈ pCore q H₁ :=
        (le_sSup ⟨hnormal, hpg⟩ : O.subgroupOf H₁ ≤ pCore q H₁) hy
      have hX : (⟨x, hR₁H hx⟩ : H₁) ∈ R₁.subgroupOf H₁ := hx
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hX) _ hY))
    ((CFSG.RankThree.PartTwo.localRank_subgroup_le hq H₁).trans hloc)
  obtain ⟨e⟩ := hQD
  exact ⟨(Subgroup.subgroupOfEquivOfLe hR₁H).symm.trans e⟩

theorem centralizes_of_qd32 (hQDA : QuaternionDihedralAutomorphismPrimeSupport) {G : Type}
    [Group G] [Finite G] {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) {R₁ E : Subgroup G}
    (hE : IsPGroup q E) (hER : E ≤ normalizer (R₁ : Set G)) (hR : Nonempty (R₁ ≃* QD32)) :
    ⁅R₁, E⁆ = ⊥ := by
  obtain ⟨-, h⟩ := hQDA R₁ hR
  have hf := h q E hq hq5 hE ((Subgroup.normalizerMonoidHom R₁).comp (Subgroup.inclusion hER))
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 := congrArg (fun φ : E →* MulAut R₁ => ((φ ⟨e, he⟩ ⟨r, hr⟩ : R₁) : G)) hf
  simp at h1
  calc e * r = (e * r * e⁻¹) * e := by group
    _ = r * e := by rw [h1]

theorem final_contradiction (hI2 : TwoLocalRankTwoOddCoreAction)
    (hQDA : QuaternionDihedralAutomorphismPrimeSupport) {G : Type} [Group G] [Finite G]
    {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) (hloc : localRank q G ≤ 2)
    {M U E X : Subgroup G} {c : G} (hc5 : orderOf c = 5) (hcM : c ∈ M)
    (hUθ : U ≤ inSubgroup (aschbacherSolvableCore 5) M)
    (hEθ : E ≤ inSubgroup (aschbacherSolvableCore 5) M)
    (hU2 : IsPGroup 2 U) (hEq : IsPGroup q E) (hcU : c ∈ normalizer (U : Set G))
    (hcE : c ∈ centralizer (E : Set G)) (hEU : E ≤ normalizer (U : Set G))
    {r : ℕ} (hr : 3 ≤ r) (hXθ : X ≤ inSubgroup (aschbacherSolvableCore 5) M)
    (hXc : IsMulCommutative X) (hXe : ∀ x ∈ X, x ^ q = 1) (hXr : Nat.card X = q ^ r)
    (hnt : ⁅⁅U, zpowers c⁆, E⁆ ≠ ⊥) : False := by
  have h5 : Nat.Prime 5 := by norm_num
  have hq2 : q ≠ 2 := by omega
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨hNsolv0, -, hN5, -⟩ := solvable_prime_complement_core_characterization (H := M) h5
  have : Group.IsSolvable (aschbacherSolvableCore 5 M) := hNsolv0
  have hNsolv : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 5) M) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore 5 M) M.subtype
        M.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective _ _ M.subtype_injective).surjective
  have hN5' : ¬ 5 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 5) M) := by
    rw [inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
    exact hN5
  have hcop : Nat.Coprime (Nat.card (zpowers c))
      (Nat.card (inSubgroup (aschbacherSolvableCore 5) M)) := by
    rw [Nat.card_zpowers, hc5]
    exact (Nat.Prime.coprime_iff_not_dvd h5).mpr hN5'
  have hcN : c ∈ normalizer ((inSubgroup (aschbacherSolvableCore 5) M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype M (aschbacherSolvableCore 5 M) hcM
  have hcEn : c ∈ normalizer (E : Set G) := centralizer_le_normalizer _ hcE
  have hVπ : ∀ p : ℕ, p.Prime → p ∣ Nat.card (U ⊔ E : Subgroup G) → p = 2 ∨ p = q := by
    intro p hp hdvd
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hU2
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hEq
    have h1 := hdvd.trans (card_sup_dvd_mul hEU)
    rw [ha, hb] at h1
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨W, hVW, hWN, hcW, hWπ, g, hgN, hgX⟩ := exists_invariant_hall hq hNsolv hcop hcN
    (sup_le hUθ hEθ) hVπ (mem_normalizer_sup hcU hcEn)
    hXθ (IsPGroup.of_card hXr)
  have hUW : U ≤ W := le_sup_left.trans hVW
  have hO2 : inSubgroup (pCore 2) W = ⊥ := by
    by_contra hne
    have hX'W : X.map (MulAut.conj g).toMonoidHom ≤ W := by
      rintro _ ⟨x, hx, rfl⟩
      exact hgX x hx
    have := le_localRank_of_normalizes hq.one_lt hne (isPGroup_inSubgroup_pCore 2 W)
      (Subgroup.map_isMulCommutative _ _)
      (by
        rintro _ ⟨x, hx, rfl⟩
        change (g * x * g⁻¹) ^ q = 1
        rw [conj_pow, hXe x hx]
        group)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hXr])
      (hX'W.trans (le_normalizer_inSubgroup_pCore 2 W))
    omega
  have : Group.IsSolvable (W.subgroupOf (inSubgroup (aschbacherSolvableCore 5) M)) := inferInstance
  have hWsolv : Group.IsSolvable W :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hWN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hWN).surjective
  have hzU : zpowers c ≤ normalizer (U : Set G) := Subgroup.zpowers_le.mpr hcU
  have hR₁U : ⁅U, zpowers c⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hzU
  have hR₁W : ⁅U, zpowers c⁆ ≤ W := hR₁U.trans hUW
  have hR₁2 : IsPGroup 2 (⁅U, zpowers c⁆ : Subgroup G) := hU2.to_le hR₁U
  have hR₁ : (⁅U, zpowers c⁆ : Subgroup G) ≠ ⊥ := fun h =>
    hnt (by rw [h, Subgroup.commutator_bot_left])
  have hU5 : ¬ 5 ∣ Nat.card U := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hU2
    rw [ha]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq h5 Nat.prime_two).mp (h5.dvd_of_dvd_pow h)
    omega
  have hz5 : IsPGroup 5 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc5, pow_one])
  have hRc : ⁅⁅U, zpowers c⁆, zpowers c⁆ = (⁅U, zpowers c⁆ : Subgroup G) :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 5 h5 (zpowers c) U hz5
      hU5 hzU
  have hcR : c ∈ normalizer ((⁅U, zpowers c⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hcU (mem_normalizer_zpowers_self c)
  have := hWsolv
  have hnontriv := nontrivial_action_on_pCore hq hq2 hWπ hO2 hR₁W hR₁2 hR₁
  have hcWn : c ∈ normalizer (W : Set G) := hcW
  have hqd := qd32_of_core_action hI2 hq hq5 hloc hc5
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c) : c ∈ W ⊔ zpowers c)
    (hR₁W.trans le_sup_left) hR₁2 hR₁ hcR hRc (isPGroup_inSubgroup_pCore q W)
    ((Subgroup.map_subtype_le _).trans le_sup_left)
    (sup_le (le_normalizer_inSubgroup_pCore q W)
      (Subgroup.zpowers_le.mpr (mem_normalizer_inSubgroup_pCore q hcWn)))
    hnontriv
  have hEz : E ≤ normalizer ((zpowers c : Subgroup G) : Set G) := fun e he =>
    mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_iff.mp hcE e he)
  have hER : E ≤ normalizer ((⁅U, zpowers c⁆ : Subgroup G) : Set G) := fun e he =>
    mem_normalizer_commutator (hEU he) (hEz he)
  exact hnt (centralizes_of_qd32 hQDA hq hq5 hEq hER hqd)

end CFSG.RankThree.PartOne.Sec9Excl
