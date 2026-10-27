module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Induction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.L2OddFixed
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Max
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GorensteinWalter
open Subgroup

@[expose] def GoodL2o (J : Type) [Group J] : Prop :=
  Finite J ∧ 3 ∣ Nat.card J ∧ ¬ 9 ∣ Nat.card J ∧ ¬ 7 ∣ Nat.card J ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (ℓ f : ℕ), ℓ.Prime ∧ ℓ ≠ 2 ∧ 1 ≤ f ∧
      Nat.card K = ℓ ^ f ∧ Nonempty (J ≃* coordinateG K)

theorem l2o_stepConcl {J : Type} [Group J] [Finite J]
    (hJ : GoodL2o J) (W : Subgroup (MulAut J)) (hW7 : Nat.card W = 7) (Z : Sylow 3 J)
    (hZ : ∀ w ∈ W, ∀ z ∈ (Z : Subgroup J), w z = z) : StepConcl GoodL2o W (Z : Subgroup J) := by
  obtain ⟨hJfin, h3, h9, h7, K, hKfield, hKfin, ℓ, f, hℓ, hℓ2, hf, hKcard, ⟨e⟩⟩ := hJ
  haveI hFact7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI hWcyc : IsCyclic ↥W := isCyclic_of_prime_card hW7
  obtain ⟨α, hαgen⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := ↥W)).mp hWcyc
  let a : MulAut J := (α : ↥W)
  have hα7 : orderOf α = 7 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hαgen, hW7]
  have ha7 : orderOf a = 7 := by
    change orderOf ((α : ↥W) : MulAut J) = 7
    rw [Subgroup.orderOf_coe, hα7]
  have hW_eq : W = Subgroup.zpowers a := by
    have h1 : (Subgroup.zpowers α).map W.subtype = W := by
      rw [hαgen, Subgroup.map_top, Subgroup.range_subtype]
    rw [← h1, MonoidHom.map_zpowers]
    rfl
  haveI hFact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard : Nat.card (Z : Subgroup J) = 3 := by
    rw [Sylow.card_eq_multiplicity]
    have hn : Nat.card J ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card J).factorization 3 := by
      have h := (Nat.prime_three.pow_dvd_iff_le_factorization (k := 1) hn).mp
        (by simpa using h3)
      simpa using h
    have h2 : ¬ 2 ≤ (Nat.card J).factorization 3 := by
      intro hle
      exact h9 (by
        have h := (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2) hn).mpr hle
        simpa using h)
    have hf1 : (Nat.card J).factorization 3 = 1 := by omega
    rw [hf1, pow_one]
  haveI hZcyc : IsCyclic (Z : Subgroup J) := isCyclic_of_prime_card hZcard
  obtain ⟨xZ, hxZgen⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := (Z : Subgroup J))).mp hZcyc
  let x : J := (xZ : J)
  have hxordZ : orderOf xZ = 3 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hxZgen, hZcard]
  have hxord : orderOf x = 3 := by
    change orderOf ((xZ : J)) = 3
    rw [Subgroup.orderOf_coe, hxordZ]
  have hxcard : Nat.card (Subgroup.zpowers x : Subgroup J) = 3 := by
    rw [Nat.card_zpowers, hxord]
  have hZeq : (Z : Subgroup J) = Subgroup.zpowers x := by
    have h1 : (Subgroup.zpowers xZ).map (Z : Subgroup J).subtype = (Z : Subgroup J) := by
      rw [hxZgen, Subgroup.map_top, Subgroup.range_subtype]
    rw [← h1, MonoidHom.map_zpowers]
    rfl
  let F : Subgroup J := fixedBy (Subgroup.zpowers a)
  unfold StepConcl
  rw [hW_eq, hZeq]
  change GoodL2o ↥⁅F, F⁆ ∧ Subgroup.zpowers x ≤ ⁅F, F⁆ ∧
    Subgroup.normalizer (Subgroup.zpowers x : Set J) ⊔ ⁅F, F⁆ = ⊤
  obtain ⟨h7f, k, hkcard, ⟨φ⟩⟩ :=
    exists_equiv_fixedBy_zpowers_coordinateG (T := J) hℓ Nat.prime_seven (by norm_num) hf
      hKcard e h7 ha7
  let ψF : ↥F ≃* PSL2 ↥k := φ.trans (pslEquivCoordinateG ↥k).symm
  let ψ' : J ≃* PSL2 K := e.trans (pslEquivCoordinateG K).symm
  have hZF : Subgroup.zpowers x ≤ F := by
    intro z hz
    rw [mem_fixedBy]
    intro w hw
    have hwW : w ∈ W := by rwa [hW_eq]
    exact hZ w hwW z (by rwa [hZeq])
  have hKdvd : Nat.card K ∣ Nat.card J := by
    rw [Nat.card_congr e.toEquiv]
    rw [← CFSG.LinearGroups.card_coordinateU (K := K)]
    exact Subgroup.card_dvd_of_le (CFSG.LinearGroups.coordinateU_le_coordinateG (K := K))
  have hℓ3 : ℓ ≠ 3 := by
    intro hℓ3eq
    have h9K : 9 ∣ Nat.card K := by
      rw [hKcard, hℓ3eq]
      have h2f : 2 ≤ f := by
        rcases h7f with ⟨c, rfl⟩
        omega
      refine ⟨3 ^ (f - 2), ?_⟩
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    exact h9 (h9K.trans hKdvd)
  have hℓ2le : 2 ≤ ℓ := hℓ.two_le
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hℓ5 : 5 ≤ ℓ := by
    rcases hℓodd with ⟨m, hm⟩
    omega
  have hf0 : 1 ≤ f / 7 := by
    rcases h7f with ⟨c, rfl⟩
    rw [Nat.mul_div_cancel_left c (by norm_num : 0 < 7)]
    omega
  have hk5 : 5 ≤ Nat.card ↥k := by
    rw [hkcard]
    calc (5 : ℕ) = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ (f / 7) := pow_le_pow_right₀ (by norm_num) hf0
      _ ≤ ℓ ^ (f / 7) := pow_le_pow_left₀ (by norm_num) hℓ5 _
  have h9lt : 9 < ℓ ^ f := by
    have h2f : 2 ≤ f := by
      rcases h7f with ⟨c, rfl⟩
      omega
    calc (9 : ℕ) < 5 ^ 2 := by norm_num
      _ ≤ 5 ^ f := pow_le_pow_right₀ (by norm_num) h2f
      _ ≤ ℓ ^ f := pow_le_pow_left₀ (by norm_num) hℓ5 f
  haveI : Fintype ↥k := Fintype.ofFinite ↥k
  have hk4 : ∃ s : Finset ↥k, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ↥k)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  haveI hperfPSL : Group.IsPerfect (PSL2 ↥k) :=
    CFSG.LinearGroups.linear_projective_perfect (K := ↥k) (n := 2) le_rfl (Or.inr hk4)
  haveI hsimpleF : IsSimpleGroup ↥F :=
    (ψF.isSimpleGroup_congr).mpr
      ((CFSG.LinearGroups.linear_projective_simple (K := ↥k) (n := 2) le_rfl
        (Or.inr hk4)).2.1)
  haveI hperfF : Group.IsPerfect ↥F :=
    Group.IsPerfect.ofSurjective (f := ψF.symm.toMonoidHom) ψF.symm.surjective
  have hcommF : ⁅F, F⁆ = F := Subgroup.commutator_eq_self
  have hq0dvd : Nat.card ↥k ∣ Nat.card ↥F := by
    rw [Nat.card_congr φ.toEquiv]
    rw [← CFSG.LinearGroups.card_coordinateU (K := ↥k)]
    exact Subgroup.card_dvd_of_le (CFSG.LinearGroups.coordinateU_le_coordinateG (K := ↥k))
  have hcardF_ge : 5 ≤ Nat.card ↥F :=
    le_trans hk5 (Nat.le_of_dvd Nat.card_pos hq0dvd)
  have hcardFacts := card_facts_of_le hZF hxcard h9 h7
  have hGoodF : GoodL2o ↥F :=
    ⟨inferInstance, hcardFacts.1, hcardFacts.2.1, hcardFacts.2.2,
      ↥k, inferInstance, inferInstance, ℓ, f / 7, hℓ, hℓ2, hf0, hkcard, ⟨φ⟩⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : DecidableEq K := Classical.decEq K
  have hN' : IsCoatom (Subgroup.normalizer (Subgroup.zpowers (ψ' x) : Set (PSL2 K))) := by
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    exact CFSG.RankThree.PartTwo.Sec20.isCoatom_normalizer_zpowers_of_orderOf_eq_three
      (F := K) hKcard hℓ2 hℓ3 h9lt (by rw [MulEquiv.orderOf_eq ψ' x, hxord])
  have hN : IsCoatom (Subgroup.normalizer (Subgroup.zpowers x : Set J)) :=
    (OrderIso.isCoatom_iff (ψ'.mapSubgroup) _).mp (by
      rw [MulEquiv.coe_mapSubgroup, Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
      exact hN')
  refine ⟨?_, ?_, ?_⟩
  · rw [hcommF]
    exact hGoodF
  · rw [hcommF]
    exact hZF
  · rcases (hN.le_iff).mp (le_sup_left :
        Subgroup.normalizer (Subgroup.zpowers x : Set J) ≤
          Subgroup.normalizer (Subgroup.zpowers x : Set J) ⊔ F) with htop | hNeq
    · rw [hcommF]
      exact htop
    · exfalso
      have hFN : F ≤ Subgroup.normalizer (Subgroup.zpowers x : Set J) := by
        rw [← hNeq]
        exact le_sup_right
      have hNormal : ((Subgroup.zpowers x).subgroupOf F).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hZF).mpr hFN
      have hcard_sub : Nat.card ↥((Subgroup.zpowers x).subgroupOf F) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZF).toEquiv, Nat.card_zpowers, hxord]
      rcases Subgroup.Normal.eq_bot_or_eq_top ((Subgroup.zpowers x).subgroupOf F) with hbot | htop'
      · rw [hbot, Subgroup.card_bot] at hcard_sub
        omega
      · rw [htop', Subgroup.card_top] at hcard_sub
        omega

theorem sevenFree_of_goodL2o {J : Type} [Group J]
    (hJ : GoodL2o J) : SevenFree J :=
  sevenFree_of_prime_step GoodL2o (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun _ _ _ hJ W _ hW7 Z hZ => l2o_stepConcl hJ W hW7 Z hZ) J hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
