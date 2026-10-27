module

public import CFSG.RankThree.GroupTheory.SteinbergBMAlphaProductStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RepeatedActionGeneration

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_sup_commutator {Y N C K : Subgroup G} (hY : Y = N ⊔ C)
    (hCN : C ≤ normalizer (N : Set G)) (hKN : K ≤ normalizer (N : Set G)) :
    ⁅Y, K⁆ ≤ N ⊔ ⁅C, K⁆ := by
  rw [commutator_le]
  intro y hy x hx
  have hy' : y ∈ (N : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left N C hCN, ← hY]
    exact hy
  obtain ⟨n, hn, c, hc, rfl⟩ := hy'
  have e : ⁅n * c, x⁆ = n * ⁅c, x⁆ * (x * n⁻¹ * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (mem_sup_left hn) (mem_sup_right (commutator_mem_commutator hc hx)))
    (mem_sup_left ((mem_normalizer_iff.mp (hKN hx) n⁻¹).mp (inv_mem hn)))

theorem le_twoCoreAlpha_of_commutator_le [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A B D Y : Subgroup G} (hBA : B ≤ A) (hDA : D ≤ A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hDpow : ∀ x ∈ D, x ^ p = 1)
    (hD : Nat.card D = p ^ 2) (hY2 : IsPGroup 2 Y) (hYB : ⁅Y, B⁆ = Y)
    (hBY : B ≤ normalizer (Y : Set G)) (hDY : D ≤ normalizer (Y : Set G))
    (hmix : ∀ d ∈ D, d ≠ 1 → ⁅Y ⊓ centralizer ({d} : Set G), A⁆ ≤
      inSubgroup (pCore 2) (centralizer ({d} : Set G))) :
    Y ≤ twoCoreAlpha D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : ∀ S : Subgroup G, IsPGroup 2 S → ¬ p ∣ Nat.card S := by
    intro S hS h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hsolv : ∀ S : Subgroup G, IsPGroup 2 S → Group.IsSolvable S := fun S hS => by
    have := hS.isNilpotent
    infer_instance
  have hDp : IsPGroup p D := IsPGroup.of_card hD
  have hDcomm : ∀ x y : D, x * y = y * x := fun x y =>
    Subtype.ext (hAcomm x (hDA x.2) y (hDA y.2))
  have hDpow' : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext ((D.coe_pow x p).trans (hDpow x x.2))
  have hJD : ∀ d ∈ D, d ≠ 1 → ⁅inSubgroup (pCore 2) (centralizer ({d} : Set G)), D⁆ ≤
      twoCoreAlpha D := fun d hd hd1 =>
    (commutator_le_twoCoreJ hd hd1).trans (twoCoreJ_le_twoCoreAlpha D)
  have hfac := RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    p hp D Y hDp (hcop Y hY2) hDY
  have hBN : B ≤ normalizer ((⁅Y, D⁆ : Subgroup G) : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_commutator (hBY hx) (centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun y hy => hAcomm y (hDA hy) x (hBA hx)))
  have hYle : Y ≤ ⁅Y, D⁆ ⊔ ⁅Y ⊓ centralizer (D : Set G), B⁆ := by
    conv_lhs => rw [← hYB]
    exact commutator_le_sup_commutator hfac (inf_le_left.trans (normalizer_commutator_ge_left Y D))
      hBN
  refine hYle.trans (sup_le ?_ ?_)
  ·
    rw [RankThreeEvenClassification.Helpers.repeated_action_commutator_generation p hp D Y hDcomm
      hDpow' hD (hsolv Y hY2) (hcop Y hY2) hDY]
    refine iSup₂_le fun d hd1 => ?_
    have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hDYd : D ≤ normalizer ((Y ⊓ centralizer ({(d : G)} : Set G) : Subgroup G) : Set G) :=
      fun x hx => SteinbergBY.mem_normalizer_inf (hDY hx)
        (le_normalizer (mem_centralizer_singleton_iff.mpr (hAcomm x (hDA hx) d (hDA d.2))))
    rw [← RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp D _ hDp
      (hcop _ (hY2.to_le inf_le_left)) hDYd]
    exact (commutator_mono ((commutator_mono le_rfl hDA).trans (hmix d d.2 hd1')) le_rfl).trans
      (hJD d d.2 hd1')
  ·
    refine le_trans (fun y hy => mem_twoCoreX_iff.mpr fun d hd hd1 => hmix d hd hd1 ?_)
      (twoCoreX_le_twoCoreAlpha D)
    exact commutator_mono (inf_le_inf_left Y (centralizer_le (Set.singleton_subset_iff.mpr hd)))
      hBA hy

theorem twoCoreAlpha_le_of_hyperplanes [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hα : ∀ E : Subgroup G, E ≤ A → Nat.card E = p ^ 2 → ∀ c ∈ A, c ≠ 1 →
      (twoCoreAlpha (E.subgroupOf (centralizer ({c} : Set G)))).map
          (centralizer ({c} : Set G)).subtype ≤
        inSubgroup (pCore 2) (centralizer ({c} : Set G)))
    {B D : Subgroup G} (hBA : B ≤ A) (hB : Nat.card B = p ^ 2) (hDA : D ≤ A)
    (hD : Nat.card D = p ^ 2) :
    twoCoreAlpha B ≤ twoCoreAlpha D := by
  have := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : ∀ S : Subgroup G, IsPGroup 2 S → ¬ p ∣ Nat.card S := by
    intro S hS h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hsolv : ∀ S : Subgroup G, IsPGroup 2 S → Group.IsSolvable S := fun S hS => by
    have := hS.isNilpotent
    infer_instance
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hAR : ∀ a ∈ A, A ≤ normalizer
      (inSubgroup (pCore 2) (centralizer ({a} : Set G)) : Set G) := fun a ha x hx =>
    SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
      (mem_centralizer_singleton_iff.mpr (hAcomm x hx a ha))
  have hcentB : ∀ x ∈ A, x ∈ normalizer (B : Set G) := fun x hx =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => hAcomm b (hBA hb) x hx)
  have hDpow : ∀ x ∈ D, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x (hDA hx)
  have hDp : IsPGroup p D := IsPGroup.of_card hD
  have hBp : IsPGroup p B := IsPGroup.of_card hB
  have hDcomm : ∀ x y : D, x * y = y * x := fun x y =>
    Subtype.ext (hAcomm x (hDA x.2) y (hDA y.2))
  have hDpow' : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext ((D.coe_pow x p).trans (hDpow x x.2))
  have hmix := SteinbergBY.alpha_local_mixed_commutator_bound hp hA hAcard hα
  have hJD : ∀ d ∈ D, d ≠ 1 → ⁅inSubgroup (pCore 2) (centralizer ({d} : Set G)), D⁆ ≤
      twoCoreAlpha D := fun d hd hd1 =>
    (commutator_le_twoCoreJ hd hd1).trans (twoCoreJ_le_twoCoreAlpha D)
  have hB0 : B ≠ ⊥ := fun h => by
    rw [h, card_bot] at hB
    have := hp.two_le
    nlinarith
  obtain ⟨hXO, -, -, -, hCX, -, -⟩ := alpha_product_structure hB0
  have hX2 : IsPGroup 2 (twoCoreX B) := (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hXO
  have hDX : D ≤ normalizer (twoCoreX B : Set G) := fun x hx =>
    hCX (mem_centralizer_iff.mpr fun b hb => hAcomm b (hBA hb) x (hDA hx))
  have hXd : ∀ d ∈ D, d ≠ 1 → twoCoreX B ⊓ centralizer ({d} : Set G) ≤
      inSubgroup (pCore 2) (centralizer ({d} : Set G)) := by
    intro d hd hd1 y hy
    refine hα B hBA hB d (hDA hd) hd1 (mem_map_of_mem (centralizer ({d} : Set G)).subtype
      (x := ⟨y, hy.2⟩) (twoCoreX_le_twoCoreAlpha _ ?_))
    rw [mem_twoCoreX_iff]
    intro b' hb' hb'1
    have hb'1' : (b' : G) ≠ 1 := fun h => hb'1 (Subtype.ext h)
    rw [← mem_map_iff_mem (centralizer ({d} : Set G)).subtype_injective,
      SteinbergBY.map_subtype_inSubgroup_pCore_centralizer]
    have hyR := mem_twoCoreX_iff.mp hy.1 (b' : G) hb' hb'1'
    exact SteinbergBY.inf_inSubgroup_pCore_le inf_le_right
      ⟨⟨hy.2, SteinbergBY.inSubgroup_pCore_le 2 _ hyR⟩, hyR⟩
  have hX : twoCoreX B ≤ twoCoreAlpha D := by
    rw [RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization p hp D
      (twoCoreX B) hDp (hcop _ hX2) hDX]
    refine sup_le ?_ ?_
    · rw [RankThreeEvenClassification.Helpers.repeated_action_commutator_generation p hp D
        (twoCoreX B) hDcomm hDpow' hD (hsolv _ hX2) (hcop _ hX2) hDX]
      refine iSup₂_le fun d hd1 => ?_
      have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
      exact (commutator_mono (hXd d d.2 hd1') le_rfl).trans (hJD d d.2 hd1')
    · refine le_trans (fun y hy => mem_twoCoreX_iff.mpr fun d hd hd1 => hXd d hd hd1 ?_)
        (twoCoreX_le_twoCoreAlpha D)
      exact ⟨hy.1, centralizer_le (Set.singleton_subset_iff.mpr hd) hy.2⟩
  have hJ : twoCoreJ B ≤ twoCoreAlpha D := by
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    have hBR : B ≤ normalizer (inSubgroup (pCore 2) (centralizer ({b} : Set G)) : Set G) :=
      hBA.trans (hAR b (hBA hb))
    have hYR := le_normalizer_iff_commutator_le_left.mp hBR
    refine le_twoCoreAlpha_of_commutator_le hp hp2 hBA hDA hAcomm hDpow hD
      ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hYR)
      (RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp B _ hBp
        (hcop _ (SteinbergBY.isPGroup_inSubgroup_pCore 2 _)) hBR)
      (normalizer_commutator_ge_right _ B)
      (fun x hx => SteinbergBY.mem_normalizer_commutator (hAR b (hBA hb) (hDA hx))
        (hcentB x (hDA hx))) fun d hd hd1 => ?_
    exact (commutator_mono (inf_le_inf_right _ hYR) le_rfl).trans
      (hmix b (hBA hb) hb1 d (hDA hd) hd1)
  exact sup_le hJ hX

theorem alpha_hyperplane_independence [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hα : ∀ E : Subgroup G, E ≤ A → Nat.card E = p ^ 2 → ∀ c ∈ A, c ≠ 1 →
      (twoCoreAlpha (E.subgroupOf (centralizer ({c} : Set G)))).map
          (centralizer ({c} : Set G)).subtype ≤
        inSubgroup (pCore 2) (centralizer ({c} : Set G)))
    {B D : Subgroup G} (hBA : B ≤ A) (hB : Nat.card B = p ^ 2) (hDA : D ≤ A)
    (hD : Nat.card D = p ^ 2) :
    twoCoreAlpha B = twoCoreAlpha D :=
  le_antisymm (twoCoreAlpha_le_of_hyperplanes hp hp2 hA hAcard hα hBA hB hDA hD)
    (twoCoreAlpha_le_of_hyperplanes hp hp2 hA hAcard hα hDA hD hBA hB)

end CFSG.RankThree.GroupTheory.SteinbergBM
