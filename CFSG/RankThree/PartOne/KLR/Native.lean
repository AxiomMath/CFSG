module

public import CFSG.RankThree.PartOne.KE.PlaneOdd
public import CFSG.RankThree.PartOne.KE.Endpoint
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.RankThree.PartOne.KE.Statements

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.RankThree.GroupTheory CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.LieType.Ree CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

theorem odd_card_of_odd_inner_of_odd_outer {C : Type*} [Group C] [Finite C]
    (hout : ¬ 2 ∣ Nat.card (Outer C)) {S : Subgroup (MulAut C)}
    (hinn : Odd (Nat.card ↥(S ⊓ (MulAut.conj : C →* MulAut C).range))) : Odd (Nat.card S) := by
  classical
  set π : MulAut C →* Outer C := QuotientGroup.mk' (inner C) with hπ
  let φ : S →* Outer C := π.comp S.subtype
  have hrodd : Odd (Nat.card φ.range) := by
    have hdvd : Nat.card φ.range ∣ Nat.card (Outer C) := Subgroup.card_subgroup_dvd_card _
    exact Odd.of_dvd_nat (Nat.not_even_iff_odd.1 fun h => hout (even_iff_two_dvd.1 h)) hdvd
  have hkodd : Odd (Nat.card φ.ker) := by
    refine Odd.of_dvd_nat hinn (Subgroup.card_dvd_of_injective
      ((S.subtype.comp φ.ker.subtype).codRestrict (S ⊓ (MulAut.conj : C →* MulAut C).range)
        fun x => ?_) fun a b hab => ?_)
    · refine ⟨x.1.2, ?_⟩
      have h := x.2
      rw [MonoidHom.mem_ker] at h
      exact (QuotientGroup.eq_one_iff (N := inner C) (x.1 : MulAut C)).1 h
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(S ⊓ (MulAut.conj : C →* MulAut C).range) => (z : MulAut C)) hab
  have hcard : Nat.card φ.ker * φ.ker.index = Nat.card S := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker φ] at hcard
  rw [← hcard]
  exact hkodd.mul hrodd

theorem planeLocalCoreOdd_of_theta_odd {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (htheta : ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ t ∈ B, orderOf t = p →
        Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({t} : Set (MulAut C)))))) :
    PlaneLocalCoreOdd p C := by
  classical
  intro B hB A hAB hA hAcard t htA ht1
  have : IsElementaryAbelian p A := hA
  have : Fact p.Prime := ⟨hp⟩
  have htp : orderOf t = p := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) t htA) ht1
  set S := inSubgroup (aschbacherSolvableCore p)
    (B ⊓ Subgroup.centralizer ({t} : Set (MulAut C))) with hS
  have hSodd : ¬ 2 ∣ Nat.card S := (htheta B hB t (hAB htA) htp).not_two_dvd_nat
  have hAC : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut C)) := by
    intro x hx
    exact Subgroup.mem_inf.2 ⟨hAB hx, Subgroup.mem_centralizer_singleton_iff.2
      (SteinbergBY.mul_comm_of_isMulCommutative hx htA)⟩
  have hAS : A ≤ Subgroup.normalizer (S : Set (MulAut C)) := fun x hx =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore
      p _ (Subgroup.le_normalizer (hAC hx))
  have hSA : ⁅S, A⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hAS
  have hIS : autThetaT p B A ≤ S := fun x hx => by
    simp only [autThetaT, Subgroup.mem_iInf] at hx
    exact hx t htA ht1
  have hle : autPlaneProduct p B A t ≤ S := sup_le hSA hIS
  intro h2
  exact hSodd (h2.trans (Subgroup.card_dvd_of_le hle))

theorem theta_odd_of_native {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) (hout : ¬ 2 ∣ Nat.card (Outer C))
    (hsolv : ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → Odd (Nat.card V))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {t : MulAut C}
    (htB : t ∈ B) (htp : orderOf t = p) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut C))))) := by
  by_cases htn : t ∈ (MulAut.conj : C →* MulAut C).range
  · obtain ⟨x, rfl⟩ := htn
    have hxp : orderOf x = p :=
      ((orderOf_injective _ (conj_injective_of_center_eq_bot hC) x).symm).trans htp
    exact odd_card_of_odd_inner_of_odd_outer hout
      (odd_card_inf_range_of_solvable (B := B) hp hC hB (hsolv x hxp))
  · rw [hcore B hB t htB htn htp, Subgroup.card_bot]
    exact odd_one

theorem planeLocalCoreOdd_of_native {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) (hout : ¬ 2 ∣ Nat.card (Outer C))
    (hsolv : ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → Odd (Nat.card V))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range) : PlaneLocalCoreOdd p C :=
  planeLocalCoreOdd_of_theta_odd hp fun _ hB _ htB htp =>
    theta_odd_of_native hp hC hout hsolv hcore hB htB htp

section Native

@[expose] def LargeReeSolvOdd : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p →
      ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))),
          V.Normal → Group.IsSolvable V → Odd (Nat.card V)

@[expose] def LargeReeNoninnerCore : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p →
      LocalCoreTrivialOn p fun α : MulAut (ReeTag.F4.reeGamma K a) =>
        α ∉ (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)).range

theorem largeRee_all_actors_of_native_aux
    (hsolv : LargeReeSolvOdd) (hcore : LargeReeNoninnerCore) :
    LargeReeAllActorsActualComponentLocalCoreProductOddAction := by
  intro G _ _ p hp hp3 E hE hEc t ht ht1 L hL ℓ f hmod hEL hSL
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hFin, -, -, hℓ2, ⟨a, ha, hfa⟩, hmodel⟩ := ReeTag.large_Ree_model_Schreier _ ℓ f hmod
  subst hℓ2
  obtain ⟨-, a', hfa', hrel⟩ := hmod
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := hrel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K ReeTag.F4.prime := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  have haa : a' = a := by omega
  subst haa
  obtain ⟨e'⟩ := hmodel a' K hfa' hKcard ⟨e⟩
  have hK : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hKcard, hfa']
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a' K hK
  obtain ⟨-, -, -, -, hOut, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form
      a' ha K hK
  have hout : ¬ 2 ∣ Nat.card (Outer (ReeTag.F4.reeGamma K a')) := by
    rw [hOut]
    omega
  have hodd : PlaneLocalCoreOdd p (ReeTag.F4.reeGamma K a') :=
    planeLocalCoreOdd_of_native hp hZ hout (hsolv a' ha K hK p hp hp3)
      (hcore a' ha K hK p hp hp3)
  exact actual_component_endpoint_of_native hp hp2 hE hEc ht ht1 hL hEL hSL e'.symm hodd
    (hcore a' ha K hK p hp hp3)

end Native

end CFSG.RankThree.PartOne.KLR
