module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofLinAlg
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r4a_fixed_of_involutive {α : Type*} [Finite α] {f : α → α} (hf : Function.Involutive f)
    (hodd : Odd (Nat.card α)) : ∃ x, f x = x := by
  haveI : Fintype α := Fintype.ofFinite α
  have hsq : Function.Involutive.toPerm f hf * Function.Involutive.toPerm f hf = 1 :=
    Equiv.ext fun x => hf x
  have hσ : (Function.Involutive.toPerm f hf) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact hsq
  have hnd : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hnd hσ
  exact ⟨a, ha⟩

theorem r4a_card_fiber {M : Type*} [Group M] (R : Subgroup M) [R.Normal] (g₀ : M) :
    Nat.card {x : M // (x : M ⧸ R) = (g₀ : M ⧸ R)} = Nat.card R := by
  have hmem : ∀ r : R, ((g₀ * (r : M) : M) : M ⧸ R) = (g₀ : M ⧸ R) := fun r => by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (r : M)).2 r.2, mul_one]
  have hmem' : ∀ x : M, (x : M ⧸ R) = (g₀ : M ⧸ R) → g₀⁻¹ * x ∈ R := fun x hx =>
    QuotientGroup.eq.1 hx.symm
  refine (Nat.card_congr ?_).symm
  exact
    { toFun := fun r => ⟨g₀ * (r : M), hmem r⟩
      invFun := fun x => ⟨g₀⁻¹ * x.1, hmem' x.1 x.2⟩
      left_inv := fun r => Subtype.ext (inv_mul_cancel_left g₀ (r : M))
      right_inv := fun x => Subtype.ext (mul_inv_cancel_left g₀ x.1) }

theorem r4a_lift {M : Type*} [Group M] [Finite M] (R : Subgroup M) [R.Normal]
    (hR : Odd (Nat.card R)) {u : M} (hu2 : u * u = 1) (g₀ : M)
    (hc : (u : M ⧸ R) * (g₀ : M ⧸ R) = (g₀ : M ⧸ R) * (u : M ⧸ R)) :
    ∃ g : M, (g : M ⧸ R) = (g₀ : M ⧸ R) ∧ u * g = g * u := by
  have huu : (u : M ⧸ R) * (u : M ⧸ R) = 1 := by
    rw [← QuotientGroup.mk_mul, hu2, QuotientGroup.mk_one]
  have hpres : ∀ x : M, (x : M ⧸ R) = (g₀ : M ⧸ R) →
      ((u * x * u : M) : M ⧸ R) = (g₀ : M ⧸ R) := by
    intro x hx
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hx, hc, mul_assoc, huu, mul_one]
  have hinv : ∀ x : M, u * (u * x * u) * u = x := by
    intro x
    calc u * (u * x * u) * u = (u * u) * x * (u * u) := by simp only [mul_assoc]
      _ = x := by rw [hu2, one_mul, mul_one]
  let σ : {x : M // (x : M ⧸ R) = (g₀ : M ⧸ R)} → {x : M // (x : M ⧸ R) = (g₀ : M ⧸ R)} :=
    fun t => ⟨u * t.1 * u, hpres t.1 t.2⟩
  have hσ : Function.Involutive σ := fun t => Subtype.ext (hinv t.1)
  have hodd : Odd (Nat.card {x : M // (x : M ⧸ R) = (g₀ : M ⧸ R)}) := by
    rw [r4a_card_fiber R g₀]
    exact hR
  obtain ⟨t, ht⟩ := r4a_fixed_of_involutive hσ hodd
  have h1 : u * t.1 * u = t.1 := congrArg Subtype.val ht
  have h2 : u * t.1 = t.1 * u := by
    have h3 : u * t.1 * u * u = t.1 * u := by rw [h1]
    calc u * t.1 = u * t.1 * (u * u) := by rw [hu2, mul_one]
      _ = u * t.1 * u * u := by simp only [mul_assoc]
      _ = t.1 * u := h3
  exact ⟨t.1, t.2, h2⟩

theorem r4_abs_u {M : Type*} [Group M] [Finite M] (R : Subgroup M) [R.Normal] (hR : Odd (Nat.card R))
    {u : M} (hu2 : u * u = 1) (A₀ : Subgroup M) (hA₀ : IsPGroup 2 A₀)
    (hA₀N : ∀ k : M, k * u = u * k → k ∈ Subgroup.normalizer (A₀ : Set M))
    (J : Subgroup (M ⧸ R)) (hJp : Group.IsPerfect J) (hJ1 : J ≠ ⊥)
    (hJU : J ≤ ⁅J, A₀.map (QuotientGroup.mk' R)⁆)
    (hc : ∀ j ∈ J, (u : M ⧸ R) * j = j * (u : M ⧸ R)) : False := by
  have hJP : J ≤ A₀.map (QuotientGroup.mk' R) := by
    refine hJU.trans (Subgroup.commutator_le.2 ?_)
    intro j hj a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective j
    obtain ⟨g, hg, hgu⟩ := r4a_lift R hR hu2 g₀ (hc _ hj)
    have hgN : g * a' * g⁻¹ ∈ A₀ :=
      (Subgroup.mem_normalizer_iff.1 (hA₀N g hgu.symm) a').mp ha'
    have h1 : (g₀ : M ⧸ R) * QuotientGroup.mk' R a' * (g₀ : M ⧸ R)⁻¹ ∈
        A₀.map (QuotientGroup.mk' R) := by
      refine Subgroup.mem_map.2 ⟨g * a' * g⁻¹, hgN, ?_⟩
      simp [hg]
    rw [commutatorElement_def]
    exact (A₀.map (QuotientGroup.mk' R)).mul_mem h1
      ((A₀.map (QuotientGroup.mk' R)).inv_mem ha)
  have hP2 : IsPGroup 2 (A₀.map (QuotientGroup.mk' R)) := hA₀.map (QuotientGroup.mk' R)
  have hJ2 : IsPGroup 2 J := IsPGroup.to_le hP2 hJP
  have hnil : Group.IsNilpotent J := IsPGroup.isNilpotent hJ2
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).2 hJ1
  exact Group.IsPerfect.not_isNilpotent J hnil

end CFSG.RankThree.PartTwo.Sec13.F135Last
