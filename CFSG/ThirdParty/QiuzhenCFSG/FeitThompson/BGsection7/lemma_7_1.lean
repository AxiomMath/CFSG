module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG
/-! # Lemma 7.1 from BG Section 7 -/

open scoped Pointwise

section

variable {G : Type*} [Group G] [Finite G]

private lemma CFSG.lemma_7_1_local [IsMinCE G]
    {A H Q₁ Q₂ : Subgroup G} (hA : Hypothesis7_1 A)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hQ₁ : Q₁ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))
    (hQ₂ : Q₂ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))
    (hAH : A ≤ H) (hHproper : H ≠ ⊤)
    (hHQ₁ : H ⊓ Q₁ ≠ ⊥) (hHQ₂ : H ⊓ Q₂ ≠ ⊥) :
    ∃ k : section7K A, ∃ Q₃ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes),
      Q₁.conjBy (k : G) ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) ∧
      (k : G) ∈ H ∧
      H ⊓ Q₁.conjBy (k : G) ≠ ⊥ ∧
      H ⊓ Q₃ ≠ ⊥ ∧
      H ⊓ Q₁.conjBy (k : G) ≤ Q₃ ∧
      H ⊓ Q₂ ≤ Q₃ := by
  classical
  let M : Subgroup G := piCoreIn (subgroupPrimeSet A)ᶜ H
  have hHQ₁_core : H ⊓ Q₁ ≤ M := by
    simpa [M] using inf_le_piCoreIn_of_hypothesis hA hq hQ₁ hAH hHproper
  have hHQ₂_core : H ⊓ Q₂ ≤ M := by
    simpa [M] using inf_le_piCoreIn_of_hypothesis hA hq hQ₂ hAH hHproper
  have hM_le_H : M ≤ H := by
    simpa [M] using piCoreIn_le (G := G) (subgroupPrimeSet A)ᶜ H
  have hA_le_normH : A ≤ Subgroup.normalizer (H : Set G) :=
    hAH.trans Subgroup.le_normalizer
  have : Subgroup.Normalizes A H := ⟨hA_le_normH⟩
  have hMsub_eq : M.subgroupOf H = piCore (subgroupPrimeSet A)ᶜ ↥H := by
    simpa [M] using piCore_map_subtype_subgroupOf (G := G) (subgroupPrimeSet A)ᶜ H
  have hMsub_char : (M.subgroupOf H).Characteristic := by
    rw [hMsub_eq]
    exact piCore_characteristic (G := ↥H) (subgroupPrimeSet A)ᶜ
  let : IsInvariant (↥A) (↥H) (M.subgroupOf H) :=
    isInvariant_of_characteristic (A := ↥A) (G := ↥H) (M.subgroupOf H)
  have hA_le_normM : A ≤ Subgroup.normalizer (M : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem M A ?_
    intro a x hx
    let xH : H := ⟨x, hM_le_H hx⟩
    have hxH : xH ∈ M.subgroupOf H := by
      exact Subgroup.mem_subgroupOf.mpr hx
    have hxInv : a • xH ∈ M.subgroupOf H :=
      (IsInvariant.invariant (A := ↥A) (G := ↥H) (H := M.subgroupOf H) a xH).1 hxH
    have hxInv' : ((a • xH : H) : G) ∈ M :=
      Subgroup.mem_subgroupOf.mp hxInv
    change (a : G) * x * (a : G)⁻¹ ∈ M
    simpa [xH, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hA_le_normH] using hxInv'
  have : Subgroup.Normalizes A M := ⟨hA_le_normM⟩
  have hQ₁fam : Q₁ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hQ₁
  have hQ₂fam : Q₂ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hQ₂
  have hA_le_normHQ₁ : A ≤ Subgroup.normalizer ((H ⊓ Q₁ : Subgroup G) : Set G) := by
    have hA_le_inf :
        A ≤ Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (Q₁ : Set G) := by
      intro a ha
      exact ⟨hA_le_normH ha, hQ₁fam.2.2 ha⟩
    exact hA_le_inf.trans Subgroup.inf_normalizer_le_normalizer_inf
  have hA_le_normHQ₂ : A ≤ Subgroup.normalizer ((H ⊓ Q₂ : Subgroup G) : Set G) := by
    have hA_le_inf :
        A ≤ Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (Q₂ : Set G) := by
      intro a ha
      exact ⟨hA_le_normH ha, hQ₂fam.2.2 ha⟩
    exact hA_le_inf.trans Subgroup.inf_normalizer_le_normalizer_inf
  let K₁ : Subgroup M := (H ⊓ Q₁).subgroupOf M
  let K₂ : Subgroup M := (H ⊓ Q₂).subgroupOf M
  have hK₁_pi : IsPiSubgroup (G := M) ({q} : Set Nat.Primes) K₁ := by
    have hHQ₁_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) (H ⊓ Q₁) :=
      IsPiSubgroup.of_le inf_le_right hQ₁fam.2.1
    exact hHQ₁_pi.subgroupOf hHQ₁_core
  have hK₂_pi : IsPiSubgroup (G := M) ({q} : Set Nat.Primes) K₂ := by
    have hHQ₂_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) (H ⊓ Q₂) :=
      IsPiSubgroup.of_le inf_le_right hQ₂fam.2.1
    exact hHQ₂_pi.subgroupOf hHQ₂_core
  have hK₁_inv : IsInvariant (↥A) (↥M) K₁ := by
    simpa [K₁] using
      (isInvariant_subgroupOf_of_le_normalizer
        (A := A) (H := M) (K := H ⊓ Q₁) hA_le_normM hA_le_normHQ₁ hHQ₁_core)
  have hK₂_inv : IsInvariant (↥A) (↥M) K₂ := by
    simpa [K₂] using
      (isInvariant_subgroupOf_of_le_normalizer
        (A := A) (H := M) (K := H ⊓ Q₂) hA_le_normM hA_le_normHQ₂ hHQ₂_core)
  let : Group.IsSolvable H := solvable_of_proper_subgroup hHproper
  have hsolvMsub : Group.IsSolvable (M.subgroupOf H) := inferInstance
  let eM : M.subgroupOf H ≃* M := Subgroup.subgroupOfEquivOfLe hM_le_H
  have hsolvM : Group.IsSolvable M :=
    Group.isSolvable_of_surjective (f := eM.toMonoidHom) eM.surjective
  have hcopM : Nat.Coprime (Nat.card A) (Nat.card M) := by
    simpa [M] using coprime_card_of_piCoreIn_compl (G := G) A H
  obtain ⟨R₁sub, hR₁Hall, hR₁inv, hK₁_le_R₁⟩ :=
    proposition_1_5_b (G := ↥M) (A := ↥A) hsolvM hcopM ({q} : Set Nat.Primes) K₁ hK₁_pi hK₁_inv
  obtain ⟨R₂sub, hR₂Hall, hR₂inv, hK₂_le_R₂⟩ :=
    proposition_1_5_b (G := ↥M) (A := ↥A) hsolvM hcopM ({q} : Set Nat.Primes) K₂ hK₂_pi hK₂_inv
  obtain ⟨m, hmfix, hR₂_eq⟩ :=
    proposition_1_5_c (G := ↥M) (A := ↥A) hsolvM hcopM ({q} : Set Nat.Primes)
      R₁sub R₂sub hR₁Hall hR₂Hall hR₁inv hR₂inv
  have hfix_eq :
      fixedPointSubgroup (↥A) (↥M) = (subgroupCentralizerIn M A).subgroupOf M := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn M A hA_le_normM
  have hmcent_sub : m ∈ (subgroupCentralizerIn M A).subgroupOf M := by
    rwa [hfix_eq] at hmfix
  have hmcent : (m : G) ∈ subgroupCentralizerIn M A := by
    simpa [Subgroup.mem_subgroupOf] using hmcent_sub
  have hM_pi : IsPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ M := by
    simpa [M] using piCoreIn_isPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ H
  have hcentM_pi :
      IsPiSubgroup (G := G) (subgroupPrimeSet A)ᶜ (subgroupCentralizerIn M A) :=
    IsPiSubgroup.of_le inf_le_left hM_pi
  have hcentM_le_cent : subgroupCentralizerIn M A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    exact hx.2
  have hmK : (m : G) ∈ section7K A :=
    le_section7K_of_le_centralizer_isPiSubgroup hA hcentM_le_cent hcentM_pi hmcent
  let k : section7K A := ⟨m, hmK⟩
  let R₁ : Subgroup G := R₁sub.map M.subtype
  let R₂ : Subgroup G := R₂sub.map M.subtype
  have hR₁_le_M : R₁ ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  have hR₂_le_M : R₂ ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  have hR₁_eq_sub : R₁.subgroupOf M = R₁sub := by
    change (R₁sub.map M.subtype).comap M.subtype = R₁sub
    exact Subgroup.comap_map_eq_self_of_injective (H := R₁sub) (f := M.subtype) M.subtype_injective
  have hR₂_eq_ambient : R₂ = R₁.conjBy (k : G) := by
    calc
      R₂ = R₂sub.map M.subtype := rfl
      _ = (R₁sub.map (MulAut.conj m).toMonoidHom).map M.subtype := by
            exact congrArg (fun S : Subgroup M => S.map M.subtype) hR₂_eq
      _ = ((R₁.subgroupOf M).map (MulAut.conj (m : M)).toMonoidHom).map M.subtype := by
            rw [hR₁_eq_sub]
      _ = R₁.map (MulAut.conj ((m : M) : G)).toMonoidHom := by
            simpa using map_subgroupOf_map_conj_eq (K0 := M) (K := R₁) hR₁_le_M m
      _ = R₁.conjBy (k : G) := rfl
  have hR₁_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) R₁ := by
    simpa [R₁] using (hR₁Hall.isPiSubgroup).map M.subtype
  have hR₂_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) R₂ := by
    simpa [R₂] using (hR₂Hall.isPiSubgroup).map M.subtype
  let : IsInvariant (↥A) (↥M) R₁sub := hR₁inv
  let : IsInvariant (↥A) (↥M) R₂sub := hR₂inv
  have hA_le_normR₁ : A ≤ Subgroup.normalizer (R₁ : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem R₁ A ?_
    intro a x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyInv : a • y ∈ R₁sub :=
      (IsInvariant.invariant (A := ↥A) (G := ↥M) (H := R₁sub) a y).1 hy
    exact Subgroup.mem_map.mpr ⟨a • y, hyInv, by
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
  have hA_le_normR₂ : A ≤ Subgroup.normalizer (R₂ : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem R₂ A ?_
    intro a x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyInv : a • y ∈ R₂sub :=
      (IsInvariant.invariant (A := ↥A) (G := ↥M) (H := R₂sub) a y).1 hy
    exact Subgroup.mem_map.mpr ⟨a • y, hyInv, by
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
  have hR₂_fam : R₂ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    exact ⟨le_top, hR₂_pi, hA_le_normR₂⟩
  obtain ⟨Q₃, hQ₃, hR₂_le_Q₃⟩ := exists_mem_section7HStarFamily_of_mem_family hR₂_fam
  have hk_cent : (k : G) ∈ Subgroup.centralizer (A : Set G) :=
    section7K_le_centralizer A k.property
  have hQ₁k : Q₁.conjBy (k : G) ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    mem_section7HStarFamily_top_conjBy_of_mem_centralizer hk_cent hQ₁
  have hHQ₁_le_R₁ : H ⊓ Q₁ ≤ R₁ := by
    intro x hx
    have hxK₁ : (⟨x, hHQ₁_core hx⟩ : M) ∈ K₁ := by
      exact Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hHQ₁_core hx⟩, hK₁_le_R₁ hxK₁, rfl⟩
  have hHQ₂_le_R₂ : H ⊓ Q₂ ≤ R₂ := by
    intro x hx
    have hxK₂ : (⟨x, hHQ₂_core hx⟩ : M) ∈ K₂ := by
      exact Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hHQ₂_core hx⟩, hK₂_le_R₂ hxK₂, rfl⟩
  have hmH : (m : G) ∈ H := hM_le_H m.property
  have hm_normH : (m : G) ∈ Subgroup.normalizer (H : Set G) := H.le_normalizer hmH
  have hHQ₁k_le_Q₃ : H ⊓ Q₁.conjBy (k : G) ≤ Q₃ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx.2 with ⟨y, hyQ₁, rfl⟩
    have hyH : y ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hm_normH y).2 hx.1
    have hyR₁ : y ∈ R₁ := hHQ₁_le_R₁ ⟨hyH, hyQ₁⟩
    have hxR₂ : (m : G) * y * (m : G)⁻¹ ∈ R₂ := by
      rw [hR₂_eq_ambient]
      exact Subgroup.mem_map.mpr ⟨y, hyR₁, rfl⟩
    exact hR₂_le_Q₃ hxR₂
  have hHQ₂_le_Q₃ : H ⊓ Q₂ ≤ Q₃ :=
    hHQ₂_le_R₂.trans hR₂_le_Q₃
  have hHQ₁k_nonbot : H ⊓ Q₁.conjBy (k : G) ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hHQ₁ with ⟨x, hxne⟩
    have hxH : (x : G) ∈ H := x.property.1
    have hxQ₁ : (x : G) ∈ Q₁ := x.property.2
    have hxH' : (m : G) * (x : G) * (m : G)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hm_normH _).1 hxH
    have hxQ₁' :
        (m : G) * (x : G) * (m : G)⁻¹ ∈ Q₁.conjBy (k : G) :=
      Subgroup.mem_map.mpr ⟨(x : G), hxQ₁, rfl⟩
    have hxne' : (m : G) * (x : G) * (m : G)⁻¹ ≠ 1 := by
      intro hx1
      apply hxne
      apply Subtype.ext
      apply (MulAut.conj (m : G)).injective
      simpa [MulAut.conj_apply] using hx1
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨_, ⟨hxH', hxQ₁'⟩⟩, by
      intro h
      exact hxne' (congrArg Subtype.val h)⟩
  have hHQ₃_nonbot : H ⊓ Q₃ ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hHQ₂ with ⟨x, hxne⟩
    have hxQ₃ : (x : G) ∈ Q₃ := hHQ₂_le_Q₃ x.property
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨_, ⟨x.property.1, hxQ₃⟩⟩, by
      intro h
      have hx1 : (x : G) = 1 := congrArg Subtype.val h
      apply hxne
      apply Subtype.ext
      simpa using hx1⟩
  exact ⟨k, Q₃, hQ₃, hQ₁k, hmH, hHQ₁k_nonbot, hHQ₃_nonbot, hHQ₁k_le_Q₃, hHQ₂_le_Q₃⟩

end

public theorem CFSG.lemma_7_1
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A H Q₁ Q₂ : Subgroup G} (hA : Hypothesis7_1 A)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hQ₁ : Q₁ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))
    (hQ₂ : Q₂ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))
    (hAH : A ≤ H) (hHproper : H ≠ ⊤)
    (hHQ₁ : H ⊓ Q₁ ≠ ⊥) (hHQ₂ : H ⊓ Q₂ ≠ ⊥) :
    ∃ k : section7K A, Q₂ = Q₁.conjBy (k : G) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {H Q₁ Q₂ : Subgroup G},
      Q₁ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) →
      Q₂ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) →
      A ≤ H → H ≠ ⊤ →
      H ⊓ Q₁ ≠ ⊥ → H ⊓ Q₂ ≠ ⊥ →
      Nat.card G - Nat.card ↥(Q₁ ⊓ Q₂) = n →
      ∃ k : section7K A, Q₂ = Q₁.conjBy (k : G)
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on (p := P) n ?_
    intro n ih H Q₁ Q₂ hQ₁ hQ₂ hAH hHproper hHQ₁ hHQ₂ hmeasure
    by_cases hQbot : Q₁ ⊓ Q₂ = ⊥
    · obtain ⟨k, Q₃, hQ₃, hQ₁k, hkH, hHQ₁k_nonbot, hHQ₃_nonbot, hHQ₁k_le_Q₃, hHQ₂_le_Q₃⟩ :=
        lemma_7_1_local hA hq hQ₁ hQ₂ hAH hHproper hHQ₁ hHQ₂
      let Q₁k : Subgroup G := Q₁.conjBy (k : G)
      have hQ₁k_mem : Q₁k ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
        simpa [Q₁k] using hQ₁k
      have hHQ₁k_nonbot' : H ⊓ Q₁k ≠ ⊥ := by
        simpa [Q₁k] using hHQ₁k_nonbot
      have hHQ₁k_le_Q₃' : H ⊓ Q₁k ≤ Q₃ := by
        simpa [Q₁k] using hHQ₁k_le_Q₃
      have hQ₁kQ₃_nonbot : Q₁k ⊓ Q₃ ≠ ⊥ := by
        rcases Subgroup.ne_bot_iff_exists_ne_one.mp hHQ₁k_nonbot' with ⟨x, hxne⟩
        have hxQ₃ : (x : G) ∈ Q₃ := hHQ₁k_le_Q₃' x.property
        exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨_, ⟨x.property.2, hxQ₃⟩⟩, by
          intro h
          have hx1 : (x : G) = 1 := congrArg Subtype.val h
          apply hxne
          apply Subtype.ext
          simpa using hx1⟩
      have hQ₂Q₃_nonbot : Q₂ ⊓ Q₃ ≠ ⊥ := by
        rcases Subgroup.ne_bot_iff_exists_ne_one.mp hHQ₂ with ⟨x, hxne⟩
        have hxQ₃ : (x : G) ∈ Q₃ := hHQ₂_le_Q₃ x.property
        exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨_, ⟨x.property.2, hxQ₃⟩⟩, by
          intro h
          have hx1 : (x : G) = 1 := congrArg Subtype.val h
          apply hxne
          apply Subtype.ext
          simpa using hx1⟩
      have hcard₁ : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₁k ⊓ Q₃) := by
        rw [hQbot]
        simpa using (Subgroup.one_lt_card_iff_ne_bot (Q₁k ⊓ Q₃)).2 hQ₁kQ₃_nonbot
      have hcard₂ : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₂ ⊓ Q₃) := by
        rw [hQbot]
        simpa using (Subgroup.one_lt_card_iff_ne_bot (Q₂ ⊓ Q₃)).2 hQ₂Q₃_nonbot
      have hQ₁kQ₃_le_G : Nat.card ↥(Q₁k ⊓ Q₃) ≤ Nat.card G :=
        Subgroup.card_le_card_group (H := Q₁k ⊓ Q₃)
      have hQ₂Q₃_le_G : Nat.card ↥(Q₂ ⊓ Q₃) ≤ Nat.card G :=
        Subgroup.card_le_card_group (H := Q₂ ⊓ Q₃)
      have hmeasure₁ : Nat.card G - Nat.card ↥(Q₁k ⊓ Q₃) < n := by
        rw [← hmeasure]
        omega
      have hmeasure₂ : Nat.card G - Nat.card ↥(Q₂ ⊓ Q₃) < n := by
        rw [← hmeasure]
        omega
      obtain ⟨f, hf⟩ :=
        ih (Nat.card G - Nat.card ↥(Q₁k ⊓ Q₃)) hmeasure₁
          hQ₁k_mem hQ₃ hAH hHproper hHQ₁k_nonbot' hHQ₃_nonbot rfl
      obtain ⟨g, hg⟩ :=
        ih (Nat.card G - Nat.card ↥(Q₂ ⊓ Q₃)) hmeasure₂
          hQ₃ hQ₂ hAH hHproper hHQ₃_nonbot hHQ₂ (by simp [inf_comm])
      refine ⟨g * f * k, ?_⟩
      calc
        Q₂ = Q₃.conjBy (g : G) := hg
        _ = (Q₁k.conjBy (f : G)).conjBy (g : G) := by rw [hf]
        _ = Q₁k.conjBy ((g : G) * (f : G)) := by rw [Subgroup.conjBy_conjBy]
        _ = (Q₁.conjBy (k : G)).conjBy ((g : G) * (f : G)) := by simp [Q₁k]
        _ = Q₁.conjBy (((g : G) * (f : G)) * (k : G)) := by rw [Subgroup.conjBy_conjBy]
        _ = Q₁.conjBy ((g * f * k : section7K A) : G) := by simp [mul_assoc]
    · let Q : Subgroup G := Q₁ ⊓ Q₂
      have hmeasureQ : Nat.card G - Nat.card ↥Q = n := by
        simpa [Q] using hmeasure
      by_cases hQtop : Q = ⊤
      · have hQ₁_top : Q₁ = ⊤ := top_unique <| by
          simpa [Q, hQtop] using (inf_le_left : Q₁ ⊓ Q₂ ≤ Q₁)
        have hQ₂_top : Q₂ = ⊤ := top_unique <| by
          simpa [Q, hQtop] using (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂)
        refine ⟨1, ?_⟩
        simp [hQ₁_top, hQ₂_top, Subgroup.conjBy_one]
      · let N : Subgroup G := Subgroup.normalizer (Q : Set G)
        have hQ₁fam : Q₁ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
          section7HStarFamily.mem_family hQ₁
        have hQ₂fam : Q₂ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
          section7HStarFamily.mem_family hQ₂
        have hA_le_N : A ≤ N := by
          have hA_le_inf :
              A ≤ Subgroup.normalizer (Q₁ : Set G) ⊓ Subgroup.normalizer (Q₂ : Set G) := by
            intro a ha
            exact ⟨hQ₁fam.2.2 ha, hQ₂fam.2.2 ha⟩
          exact hA_le_inf.trans <| by
            simpa [N, Q] using (Subgroup.inf_normalizer_le_normalizer_inf :
              Subgroup.normalizer (Q₁ : Set G) ⊓ Subgroup.normalizer (Q₂ : Set G) ≤
                Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G))
        have hNproper : N ≠ ⊤ := by
          intro hNtop
          have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
          let : IsSimpleGroup G := IsMinCE.simple
          rcases hQnormal.eq_bot_or_eq_top with hQeq_bot | hQeq_top
          · exact hQbot hQeq_bot
          · exact hQtop hQeq_top
        have hQ_le_NQ₁ : Q ≤ N ⊓ Q₁ := by
          intro x hx
          exact ⟨Subgroup.le_normalizer hx, hx.1⟩
        have hQ_le_NQ₂ : Q ≤ N ⊓ Q₂ := by
          intro x hx
          exact ⟨Subgroup.le_normalizer hx, hx.2⟩
        have hNQ₁_nonbot : N ⊓ Q₁ ≠ ⊥ :=
          ne_bot_of_le_ne_bot hQbot hQ_le_NQ₁
        have hNQ₂_nonbot : N ⊓ Q₂ ≠ ⊥ :=
          ne_bot_of_le_ne_bot hQbot hQ_le_NQ₂
        obtain ⟨k, Q₃, hQ₃, hQ₁k, hkN, hNQ₁k_nonbot, hNQ₃_nonbot, hNQ₁k_le_Q₃, hNQ₂_le_Q₃⟩ :=
          lemma_7_1_local hA hq hQ₁ hQ₂ hA_le_N hNproper hNQ₁_nonbot hNQ₂_nonbot
        let Q₁k : Subgroup G := Q₁.conjBy (k : G)
        have hQ₁k_mem : Q₁k ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
          simpa [Q₁k] using hQ₁k
        have hNQ₁k_nonbot' : N ⊓ Q₁k ≠ ⊥ := by
          simpa [Q₁k] using hNQ₁k_nonbot
        have hNQ₁k_le_Q₃' : N ⊓ Q₁k ≤ Q₃ := by
          simpa [Q₁k] using hNQ₁k_le_Q₃
        have hQ_le_Q₁k : Q ≤ Q₁k := by
          intro x hx
          have hxQ : (k : G)⁻¹ * x * (k : G) ∈ Q :=
            (Subgroup.mem_normalizer_iff''.mp hkN x).mp hx
          exact Subgroup.mem_map.mpr ⟨(k : G)⁻¹ * x * (k : G), hxQ.1, by
            change (k : G) * ((k : G)⁻¹ * x * (k : G)) * (k : G)⁻¹ = x
            group⟩
        have hQ_le_NQ₁k : Q ≤ N ⊓ Q₁k := by
          intro x hx
          exact ⟨Subgroup.le_normalizer hx, hQ_le_Q₁k hx⟩
        have hQ_le_Q₃ : Q ≤ Q₃ :=
          hQ_le_NQ₁k.trans hNQ₁k_le_Q₃'
        have hQ_le_J₁ : Q ≤ Q₁k ⊓ Q₃ := by
          intro x hx
          exact ⟨hQ_le_Q₁k hx, hQ_le_Q₃ hx⟩
        have hQ_le_J₂ : Q ≤ Q₂ ⊓ Q₃ := by
          intro x hx
          exact ⟨hx.2, hQ_le_Q₃ hx⟩
        by_cases hcard₁ : Nat.card ↥Q < Nat.card ↥(Q₁k ⊓ Q₃)
        · by_cases hcard₂ : Nat.card ↥Q < Nat.card ↥(Q₂ ⊓ Q₃)
          · have hQ₁kQ₃_le_G : Nat.card ↥(Q₁k ⊓ Q₃) ≤ Nat.card G :=
              Subgroup.card_le_card_group (H := Q₁k ⊓ Q₃)
            have hQ₂Q₃_le_G : Nat.card ↥(Q₂ ⊓ Q₃) ≤ Nat.card G :=
              Subgroup.card_le_card_group (H := Q₂ ⊓ Q₃)
            have hmeasure₁ : Nat.card G - Nat.card ↥(Q₁k ⊓ Q₃) < n := by
              rw [← hmeasureQ]
              omega
            have hmeasure₂ : Nat.card G - Nat.card ↥(Q₂ ⊓ Q₃) < n := by
              rw [← hmeasureQ]
              omega
            obtain ⟨f, hf⟩ :=
              ih (Nat.card G - Nat.card ↥(Q₁k ⊓ Q₃)) hmeasure₁
                hQ₁k_mem hQ₃ hA_le_N hNproper hNQ₁k_nonbot' hNQ₃_nonbot rfl
            obtain ⟨g, hg⟩ :=
              ih (Nat.card G - Nat.card ↥(Q₂ ⊓ Q₃)) hmeasure₂
                hQ₃ hQ₂ hA_le_N hNproper hNQ₃_nonbot hNQ₂_nonbot (by simp [inf_comm])
            refine ⟨g * f * k, ?_⟩
            calc
              Q₂ = Q₃.conjBy (g : G) := hg
              _ = (Q₁k.conjBy (f : G)).conjBy (g : G) := by rw [hf]
              _ = Q₁k.conjBy ((g : G) * (f : G)) := by rw [Subgroup.conjBy_conjBy]
              _ = (Q₁.conjBy (k : G)).conjBy ((g : G) * (f : G)) := by simp [Q₁k]
              _ = Q₁.conjBy (((g : G) * (f : G)) * (k : G)) := by rw [Subgroup.conjBy_conjBy]
              _ = Q₁.conjBy ((g * f * k : section7K A) : G) := by simp [mul_assoc]
          · have hNQ₂_le_J₂ : N ⊓ Q₂ ≤ Q₂ ⊓ Q₃ := by
              intro x hx
              exact ⟨hx.2, hNQ₂_le_Q₃ hx⟩
            have hQ_eq_J₂ : Q = Q₂ ⊓ Q₃ :=
              Subgroup.eq_of_le_of_card_ge hQ_le_J₂ (le_of_not_gt hcard₂)
            have hNQ₂_eq_Q : N ⊓ Q₂ = Q := by
              apply le_antisymm
              · calc
                  N ⊓ Q₂ ≤ Q₂ ⊓ Q₃ := hNQ₂_le_J₂
                  _ = Q := hQ_eq_J₂.symm
              · exact hQ_le_NQ₂
            have hQ_eq_Q₂ : Q = Q₂ := by
              by_contra hQeqQ₂
              have hQ₂_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q₂ :=
                hQ₂fam.2.1
              have hnc : NormalizerCondition ↥Q₂ :=
                normalizerCondition_of_isPiSubgroup_singleton hQ₂_pi
              have hQsub_ne_top : Q.subgroupOf Q₂ ≠ ⊤ := by
                intro htop
                have hQ₂_le_Q : Q₂ ≤ Q := Subgroup.subgroupOf_eq_top.mp htop
                exact hQeqQ₂ (le_antisymm (by simp [Q]) hQ₂_le_Q)
              have hQsub_lt_top : Q.subgroupOf Q₂ < ⊤ :=
                lt_top_iff_ne_top.mpr hQsub_ne_top
              have hlt_norm :
                  Q.subgroupOf Q₂ <
                    Subgroup.normalizer ((Q.subgroupOf Q₂ : Subgroup Q₂) : Set Q₂) :=
                hnc _ hQsub_lt_top
              have hnorm_eq :
                  Subgroup.normalizer ((Q.subgroupOf Q₂ : Subgroup Q₂) : Set Q₂) =
                    Q.subgroupOf Q₂ := by
                calc
                  Subgroup.normalizer ((Q.subgroupOf Q₂ : Subgroup Q₂) : Set Q₂)
                      = (N ⊓ Q₂).subgroupOf Q₂ := by
                          symm
                          calc
                            (N ⊓ Q₂).subgroupOf Q₂ = N.subgroupOf Q₂ := by simp
                            _ = Subgroup.normalizer ((Q.subgroupOf Q₂ : Subgroup Q₂) : Set Q₂) := by
                                change (Subgroup.normalizer (Q : Set G)).subgroupOf Q₂ =
                                  Subgroup.normalizer ((Q.subgroupOf Q₂ : Subgroup Q₂) : Set Q₂)
                                exact Subgroup.subgroupOf_normalizer_eq (H := Q) (N := Q₂)
                                  (by simp [Q])
                  _ = Q.subgroupOf Q₂ := by simp [hNQ₂_eq_Q]
              exact hlt_norm.ne hnorm_eq.symm
            have hQ₂_le_Q₁k : Q₂ ≤ Q₁k := by
              simpa [Q, hQ_eq_Q₂] using hQ_le_Q₁k
            exact ⟨k, (hQ₂.2 _ hQ₂_le_Q₁k hQ₁k_mem.1).symm⟩
        · have hNQ₁k_le_J₁ : N ⊓ Q₁k ≤ Q₁k ⊓ Q₃ := by
            intro x hx
            exact ⟨hx.2, hNQ₁k_le_Q₃' hx⟩
          have hQ_eq_J₁ : Q = Q₁k ⊓ Q₃ :=
            Subgroup.eq_of_le_of_card_ge hQ_le_J₁ (le_of_not_gt hcard₁)
          have hNQ₁k_eq_Q : N ⊓ Q₁k = Q := by
            apply le_antisymm
            · calc
                N ⊓ Q₁k ≤ Q₁k ⊓ Q₃ := hNQ₁k_le_J₁
                _ = Q := hQ_eq_J₁.symm
            · exact hQ_le_NQ₁k
          have hQ_eq_Q₁k : Q = Q₁k := by
            by_contra hQeqQ₁k
            have hQ₁k_pi : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q₁k :=
              (section7HStarFamily.mem_family hQ₁k_mem).2.1
            have hnc : NormalizerCondition ↥Q₁k :=
              normalizerCondition_of_isPiSubgroup_singleton hQ₁k_pi
            have hQsub_ne_top : Q.subgroupOf Q₁k ≠ ⊤ := by
              intro htop
              have hQ₁k_le_Q : Q₁k ≤ Q := Subgroup.subgroupOf_eq_top.mp htop
              exact hQeqQ₁k (le_antisymm hQ_le_Q₁k hQ₁k_le_Q)
            have hQsub_lt_top : Q.subgroupOf Q₁k < ⊤ :=
              lt_top_iff_ne_top.mpr hQsub_ne_top
            have hlt_norm :
                Q.subgroupOf Q₁k <
                  Subgroup.normalizer ((Q.subgroupOf Q₁k : Subgroup Q₁k) : Set Q₁k) :=
              hnc _ hQsub_lt_top
            have hnorm_eq :
                Subgroup.normalizer ((Q.subgroupOf Q₁k : Subgroup Q₁k) : Set Q₁k) =
                  Q.subgroupOf Q₁k := by
              calc
                Subgroup.normalizer ((Q.subgroupOf Q₁k : Subgroup Q₁k) : Set Q₁k)
                    = (N ⊓ Q₁k).subgroupOf Q₁k := by
                        symm
                        calc
                          (N ⊓ Q₁k).subgroupOf Q₁k = N.subgroupOf Q₁k := by simp
                          _ = Subgroup.normalizer ((Q.subgroupOf Q₁k : Subgroup Q₁k) : Set Q₁k) := by
                              change (Subgroup.normalizer (Q : Set G)).subgroupOf Q₁k =
                                Subgroup.normalizer ((Q.subgroupOf Q₁k : Subgroup Q₁k) : Set Q₁k)
                              exact Subgroup.subgroupOf_normalizer_eq (H := Q) (N := Q₁k) hQ_le_Q₁k
                _ = Q.subgroupOf Q₁k := by simp [hNQ₁k_eq_Q]
            exact hlt_norm.ne hnorm_eq.symm
          have hQ₁k_le_Q₂ : Q₁k ≤ Q₂ := by
            simpa [Q, hQ_eq_Q₁k] using (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂)
          exact ⟨k, hQ₁k_mem.2 _ hQ₁k_le_Q₂ hQ₂.1⟩
  exact hP (Nat.card G - Nat.card ↥(Q₁ ⊓ Q₂)) hQ₁ hQ₂ hAH hHproper hHQ₁ hHQ₂ rfl
