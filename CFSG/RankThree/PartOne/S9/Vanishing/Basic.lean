module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Dihedral.OriginalSylowControl
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne.Vanish

open CFSG CFSG.RankThree.LocalRank

variable {G : Type*} [Group G]

theorem isElementaryAbelian_of_le {p : ℕ} {A B : Subgroup G} (hA : IsElementaryAbelian p A)
    (hBA : B ≤ A) : IsElementaryAbelian p B := CFSG.IsElementaryAbelian.of_le hA hBA

theorem mul_comm_of_isElementaryAbelian {p : ℕ} {A : Subgroup G} (hA : IsElementaryAbelian p A)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem le_assemblyPRank [Finite G] {p : ℕ} (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Assembly.pRank p H := by
  refine le_csSup ⟨Nat.card G, ?_⟩
    ⟨E, hEH, ⟨hE.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩, hk⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

theorem isSylowOf_iff_abg [Finite G] {p : ℕ} [Fact p.Prime] {T K : Subgroup G} :
    IsSylowOf p T K ↔ ABGLocalTools.IsSylowOf p T K :=
  ABGLocalTools.isSylowOf_iff.symm

theorem isSylowOf_of_isSylowIn {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T K : Subgroup G} (h : DihedralBlueprint.IsSylowIn p T K) : IsSylowOf p T K := by
  obtain ⟨Q, hQ⟩ := (DihedralBlueprint.isSylowIn_iff_exists_sylow p T K).mp h
  exact isSylowOf_iff_abg.mpr ⟨Q, hQ⟩

theorem not_dvd_card_inSubgroup_aschbacherSolvableCore [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) H) := by
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  exact RankThreeEvenClassification.Helpers.thetaCoreOf_prime_complement p hp H

theorem le_normalizer_inSubgroup_aschbacherSolvableCore (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore p) H : Set G) :=
  Subgroup.le_normalizer.trans
    (RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore
      p H)

theorem le_of_forall_hyperplane_inf_centralizer_le [Finite G] {p : ℕ} (hp : p.Prime)
    {A R X : Subgroup G} (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR : ¬ p ∣ Nat.card R)
    (hX : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 →
      R ⊓ Subgroup.centralizer (D : Set G) ≤ X) : R ≤ X := by
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  let : MulDistribMulAction A R := MulDistribMulAction.compHom R (Subgroup.inclusion hAR)
  have hsmul : ∀ (a : A) (x : R), ((a • x : R) : G) = a * x * (a : G)⁻¹ := fun _ _ => rfl
  have : Nontrivial A := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hAcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  have key := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := R) hR
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B R) ≤
      X.comap R.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    have hBcard : Nat.card B = p ^ 2 := by
      have h := B.card_mul_index
      rw [hB, hAcard] at h
      exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h]; ring)
    have hxc : (x : G) ∈ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h1 : b • x = x := hx ⟨b, hb⟩
      have h2 := congrArg Subtype.val h1
      rw [hsmul] at h2
      change (b : G) * x = x * b
      calc (b : G) * x = (b : G) * x * (b : G)⁻¹ * b := by group
        _ = x * b := by rw [h2]
    exact hX (B.map A.subtype) (Subgroup.map_subtype_le B)
      (by rw [Subgroup.card_map_of_injective A.subtype_injective, hBcard]) ⟨x.2, hxc⟩
  intro r hr
  have hr' : (⟨r, hr⟩ : R) ∈ (⊤ : Subgroup R) := trivial
  rw [← key] at hr'
  exact hle hr'

end CFSG.RankThree.PartOne.Vanish
