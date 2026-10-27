module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.Holt.Induced
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (toImg9)

variable {G : Type} [Group G] [Finite G]

private theorem r920iml_subgroupOf_I9_le_pCore {H X : Subgroup G} {m : ℕ} (hXH : X ≤ H)
    (hL2 : IsL2 (Bar2 X) m) :
    (F09.I9 H).subgroupOf X ≤ CFSG.pCore 2 ↥X := by
  haveI : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHI : H ≤ normalizer (F09.I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  set J : Subgroup ↥X := (F09.I9 H).subgroupOf X with hJ
  set Q : Subgroup ↥X := CFSG.pCore 2 ↥X with hQ
  have hJn : J.Normal := by
    rw [hJ]
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHI (hXH g.2)) (x : G)).mp hx
    simpa using h1
  haveI : (J.map (QuotientGroup.mk' Q)).Normal :=
    hJn.map _ (QuotientGroup.mk'_surjective Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map (QuotientGroup.mk' Q)) with h | h
  · intro x hx
    have h1 : QuotientGroup.mk' Q x ∈ J.map (QuotientGroup.mk' Q) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    have h1 : Nat.card (Bar2 X) ∣ Nat.card J := by
      rw [← Subgroup.card_top (G := Bar2 X), ← h]
      exact Subgroup.card_map_dvd _ _
    have h2 : Nat.card J ∣ Nat.card (F09.I9 H) := by
      rw [hJ, ← Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcop : Nat.Coprime 3 (Nat.card (F09.I9 H)) :=
      CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore (r := 3) H
    have h3 : 3 ∣ Nat.card (Bar2 X) :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.three_dvd_card_of_isL2 hL2
    exact absurd (Nat.Coprime.coprime_dvd_right (h3.trans (h1.trans h2)) hcop) (by decide)

theorem isPGroup_ker_toImg9_of_isL2 {H X : Subgroup G} {m : ℕ} (hXH : X ≤ H)
    (hL2 : IsL2 (Bar2 X) m) : IsPGroup 2 (toImg9 hXH).ker := by
  refine (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).to_le ?_
  intro x hx
  exact r920iml_subgroupOf_I9_le_pCore hXH hL2
    (Subgroup.mem_subgroupOf.2
      ((CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.mem_ker_toImg9 hXH).1 hx))

theorem exists_le_card_eq_img9_eq {H X : Subgroup G} (hXH : X ≤ H)
    (hker : IsPGroup 2 (toImg9 hXH).ker) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Qb : Subgroup (F09.Hbar9 H)} (hQ : IsPGroup p Qb) (hQX : Qb ≤ F09.img9 H X) :
    ∃ A : Subgroup G, A ≤ X ∧ Nat.card A = Nat.card Qb ∧ F09.img9 H A = Qb := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := toImg9 hXH
  set Qc : Subgroup ↥(F09.img9 H X) := Qb.subgroupOf (F09.img9 H X)
  have eQ : ↥Qc ≃* ↥Qb := Subgroup.subgroupOfEquivOfLe hQX
  obtain ⟨P, -, -, hP, hPQ⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le (H := ⊤) (E := ⊥) ψ
    (hQ.of_equiv eQ.symm)
    (by rw [Subgroup.map_top_of_surjective ψ
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.toImg9_surjective hXH)]; exact le_top)
    IsPGroup.of_bot bot_le (by rw [Subgroup.map_bot]; exact bot_le)
  have hcop : p.Coprime (Nat.card ψ.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨e⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_pGroup_equiv_image p hp ψ hcop P hP
  refine ⟨P.map X.subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_congr e.toEquiv, hPQ,
      Nat.card_congr eQ.toEquiv]
  · ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
      have h1 : ψ x ∈ Qc := hPQ ▸ Subgroup.mem_map_of_mem ψ hx
      have hxy' : Subgroup.inclusion hXH x = y := Subtype.ext hxy
      have h2 : ((ψ x : ↥(F09.img9 H X)) : F09.Hbar9 H) =
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y := by
        rw [← hxy']
        rfl
      rw [← h2]
      exact Subgroup.mem_subgroupOf.1 h1
    · intro hz
      have hz' : (⟨z, hQX hz⟩ : ↥(F09.img9 H X)) ∈ P.map ψ := by
        rw [hPQ]
        exact Subgroup.mem_subgroupOf.2 hz
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hz'
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hXH x,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, hx, rfl⟩), congrArg Subtype.val hxz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
