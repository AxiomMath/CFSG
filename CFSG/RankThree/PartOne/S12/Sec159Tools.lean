module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG Subgroup

namespace Sec159

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElementaryAbelian_of_le {p : ℕ} {A K : Subgroup G} (hA : IsElementaryAbelian p ↥A)
    (hKA : K ≤ A) : IsElementaryAbelian p ↥K := CFSG.IsElementaryAbelian.of_le hA hKA

theorem le_iSup_hyperplane_centralizers {p : ℕ} [Fact p.Prime] {A V : Subgroup G}
    [IsElementaryAbelian p A] [Nontrivial A] (hAV : A ≤ normalizer (V : Set G))
    (hVp : ¬ p ∣ Nat.card V) :
    V ≤ ⨆ (B : Subgroup A) (_ : B.index = p),
      V ⊓ centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
  classical
  let : MulDistribMulAction A V := Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
  have hgen := SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := V) hVp
  set target : Subgroup G := ⨆ (B : Subgroup A) (_ : B.index = p),
      V ⊓ centralizer ((B.map A.subtype : Subgroup G) : Set G) with htarget
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B V) ≤
      target.comap V.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    rw [Subgroup.mem_comap]
    have hcomm : ∀ b : B, ((b : A) : G) * (x : G) * ((b : A) : G)⁻¹ = x := fun b =>
      congrArg Subtype.val (hx b)
    refine Subgroup.mem_iSup_of_mem B (Subgroup.mem_iSup_of_mem hB ?_)
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hyB, rfl⟩
    have h1 := hcomm ⟨y, hyB⟩
    change ((y : A) : G) * (x : G) = (x : G) * ((y : A) : G)
    calc ((y : A) : G) * (x : G) = (((y : A) : G) * x * ((y : A) : G)⁻¹) * ((y : A) : G) := by
          group
      _ = (x : G) * ((y : A) : G) := by rw [h1]
  intro x hx
  have hx' : (⟨x, hx⟩ : V) ∈ (⊤ : Subgroup V) := mem_top _
  rw [← hgen] at hx'
  exact hle hx'

theorem le_of_pPrime_normalized {p : ℕ} (hp : p.Prime) {A Z N : Subgroup G}
    (hAel : IsElementaryAbelian p ↥A) (hAcard : Nat.card ↥A = p ^ 3)
    (hN : ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic ↥B → normalizer (B : Set G) ≤ N)
    (hAZ : A ≤ normalizer (Z : Set G)) (hZp : ¬ p ∣ Nat.card ↥Z) : Z ≤ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p A := hAel
  have : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [hAcard]
    have := hp.two_le
    calc 1 < p := hp.one_lt
      _ ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
  refine (le_iSup_hyperplane_centralizers hAZ hZp).trans ?_
  refine iSup₂_le fun B hB => ?_
  refine inf_le_right.trans ?_
  refine (Subgroup.centralizer_le_normalizer _).trans (hN _ ?_ ?_)
  · exact Subgroup.map_subtype_le B
  ·
    have hBcard : Nat.card ↥(B.map A.subtype) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective A.subtype_injective]
      have h1 := B.card_mul_index
      rw [hB, hAcard] at h1
      have : Nat.card ↥B * p = p ^ 2 * p := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    have hBel : IsElementaryAbelian p ↥(B.map A.subtype) :=
      isElementaryAbelian_of_le hAel (Subgroup.map_subtype_le B)
    exact hBel.not_isCyclic_of_card_eq_prime_sq hBcard

omit [Finite G] in
theorem exists_fixed_in_coset {p : ℕ} [Fact p.Prime] {U V : Subgroup G} (hU : IsPGroup p ↥U)
    (hVp : ¬ p ∣ Nat.card ↥V) (hUV : U ≤ normalizer (V : Set G)) {x : G}
    (hxV : x ∈ normalizer (V : Set G)) (hx : ∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ V) :
    ∃ v ∈ V, ∀ u ∈ U, u * (x * v) * u⁻¹ = x * v := by
  classical
  let T : Type := {y : G // x⁻¹ * y ∈ V}
  have hclosed : ∀ (u : ↥U) (y : T), x⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) ∈ V := by
    intro u y
    have hw := hx u u.2
    have hv : (u : G) * (x⁻¹ * (y : G)) * (u : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hUV u.2) _).1 y.2
    have hxw : x⁻¹ * ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (V : Set G)).inv_mem hxV) _).1 hw
      simpa [mul_assoc] using this
    have : x⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) =
        (x⁻¹ * ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x) * ((u : G) * (x⁻¹ * (y : G)) * (u : G)⁻¹) := by
      group
    rw [this]
    exact V.mul_mem hxw hv
  let inst : MulAction ↥U T :=
    { smul := fun u y => ⟨(u : G) * (y : G) * (u : G)⁻¹, hclosed u y⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : ↥U) : G) * (y : G) * ((1 : ↥U) : G)⁻¹ = (y : G)
        simp)
      mul_smul := fun u₁ u₂ y => Subtype.ext (by
        show ((u₁ * u₂ : ↥U) : G) * (y : G) * ((u₁ * u₂ : ↥U) : G)⁻¹ =
          (u₁ : G) * ((u₂ : G) * (y : G) * (u₂ : G)⁻¹) * (u₁ : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card T = Nat.card ↥V := by
    refine Nat.card_congr ⟨fun y => ⟨x⁻¹ * (y : G), y.2⟩, fun v => ⟨x * (v : G), by simp⟩,
      fun y => by apply Subtype.ext; simp, fun v => by apply Subtype.ext; simp⟩
  obtain ⟨y, hy⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card T (by rw [hcard]; exact hVp)
  refine ⟨x⁻¹ * (y : G), y.2, fun u hu => ?_⟩
  have h1 : (u : G) * (y : G) * (u : G)⁻¹ = (y : G) := by
    have := congrArg Subtype.val (hy ⟨u, hu⟩)
    exact this
  have : x * (x⁻¹ * (y : G)) = (y : G) := by group
  rw [this]
  exact h1

end Sec159

end CFSG.RankThree.PartOne
