module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelSolvable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open scoped Pointwise

@[expose] def BorelPositionTwo (X : Type) [Group X] [Finite X] : Prop :=
  ∀ (S : Sylow 2 X) (A : Subgroup X), IsMulCommutative A → Odd (Nat.card A) →
    Nat.card ↥((S : Subgroup X) ⊔ A) = Nat.card (S : Subgroup X) * Nat.card A →
    A ≤ Subgroup.normalizer ((S : Subgroup X) : Set X)

theorem borelPositionTwo_of_isL2 {X : Type} [Group X] [Finite X] {a : ℕ} (h : IsL2 X a) :
    BorelPositionTwo X :=
  fun S A hA hodd hcard => kBor_holds X a (Or.inl h) S A hA hodd hcard

theorem BorelPositionTwo.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : BorelPositionTwo Y) : BorelPositionTwo X := by
  intro S A hA hodd hcard
  let S' : Sylow 2 Y := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A' : Subgroup Y := A.map e.toMonoidHom
  have hS' : (S' : Subgroup Y) = (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective S
  haveI : IsMulCommutative A := hA
  have hA' : IsMulCommutative A' := Subgroup.map_isMulCommutative (H := A) e.toMonoidHom
  have hodd' : Odd (Nat.card A') := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hodd
  have hcard' : Nat.card ↥((S' : Subgroup Y) ⊔ A') =
      Nat.card (S' : Subgroup Y) * Nat.card A' := by
    rw [hS']
    change Nat.card ↥((S : Subgroup X).map e.toMonoidHom ⊔ A.map e.toMonoidHom) =
      Nat.card ↥((S : Subgroup X).map e.toMonoidHom) * Nat.card ↥(A.map e.toMonoidHom)
    rw [← Subgroup.map_sup, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  have hnorm := h S' A' hA' hodd' hcard'
  intro a ha
  have hmem : e a ∈ Subgroup.normalizer ((S' : Subgroup Y) : Set Y) :=
    hnorm (Subgroup.mem_map_of_mem (f := e.toMonoidHom) ha)
  rw [hS', ← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv] at hmem
  simpa using hmem

private theorem card_sup_eq_mul_of_coe_mul_eq {G : Type} [Group G] [Finite G] {S A : Subgroup G}
    (hinf : S ⊓ A = ⊥) (h : (S : Set G) * (A : Set G) = ((S ⊔ A : Subgroup G) : Set G)) :
    Nat.card ↥(S ⊔ A) = Nat.card S * Nat.card A := by
  refine le_antisymm ?_ (CFSG.Timmesfeld.ARS.card_mul_card_le_card_sup hinf)
  have hcardprod : Nat.card ↥(S ⊔ A) = Nat.card ↥((S : Set G) * (A : Set G)) :=
    Nat.card_congr (Set.equivOfEq h.symm)
  have hle := Nat.card_le_card_of_surjective
    (fun p : ↥S × ↥A => (⟨(p.1 : G) * (p.2 : G),
      (⟨p.1, p.1.2, p.2, p.2.2, rfl⟩ : (p.1 : G) * p.2 ∈ (S : Set G) * (A : Set G))⟩ :
        ↥((S : Set G) * (A : Set G))))
    (by
      rintro ⟨x, hx⟩
      obtain ⟨s, hs, a, ha, rfl⟩ := hx
      exact ⟨(⟨s, hs⟩, ⟨a, ha⟩), rfl⟩)
  rw [Nat.card_prod] at hle
  exact hcardprod.trans_le hle

theorem BorelPositionTwo.prod {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (hX : BorelPositionTwo X) (hY : BorelPositionTwo Y) : BorelPositionTwo (X × Y) := by
  intro S A hA hodd hcard
  let S₁ : Sylow 2 X := S.mapSurjective (f := MonoidHom.fst X Y) Prod.fst_surjective
  let S₂ : Sylow 2 Y := S.mapSurjective (f := MonoidHom.snd X Y) Prod.snd_surjective
  have hS₁ : (S₁ : Subgroup X) = (S : Subgroup (X × Y)).map (MonoidHom.fst X Y) :=
    Sylow.coe_mapSurjective _ _
  have hS₂ : (S₂ : Subgroup Y) = (S : Subgroup (X × Y)).map (MonoidHom.snd X Y) :=
    Sylow.coe_mapSurjective _ _
  let A₁ : Subgroup X := A.map (MonoidHom.fst X Y)
  let A₂ : Subgroup Y := A.map (MonoidHom.snd X Y)
  haveI : IsMulCommutative A := hA
  have hA₁ : IsMulCommutative A₁ :=
    Subgroup.map_isMulCommutative (H := A) (MonoidHom.fst X Y)
  have hA₂ : IsMulCommutative A₂ :=
    Subgroup.map_isMulCommutative (H := A) (MonoidHom.snd X Y)
  have hodd₁ : Odd (Nat.card A₁) :=
    Odd.of_dvd_nat hodd (Subgroup.card_map_dvd A (MonoidHom.fst X Y))
  have hodd₂ : Odd (Nat.card A₂) :=
    Odd.of_dvd_nat hodd (Subgroup.card_map_dvd A (MonoidHom.snd X Y))
  have hinf : (S : Subgroup (X × Y)) ⊓ A = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd S.isPGroup' hodd
  have hprod : (((S : Subgroup (X × Y)) : Set (X × Y)) * (A : Set (X × Y))) =
      ((((S : Subgroup (X × Y)) ⊔ A : Subgroup (X × Y))) : Set (X × Y)) :=
    CFSG.Quasithin.H.L3Wr.coe_mul_eq_sup_of_card hinf (le_of_eq hcard)
  have hmap₁ : (S₁ : Subgroup X) ⊔ A₁ =
      ((S : Subgroup (X × Y)) ⊔ A).map (MonoidHom.fst X Y) := by
    rw [hS₁, Subgroup.map_sup]
  have hmap₂ : (S₂ : Subgroup Y) ⊔ A₂ =
      ((S : Subgroup (X × Y)) ⊔ A).map (MonoidHom.snd X Y) := by
    rw [hS₂, Subgroup.map_sup]
  have himg₁ : (((S₁ : Subgroup X) : Set X) * (A₁ : Set X)) =
      (((S₁ : Subgroup X) ⊔ A₁ : Subgroup X) : Set X) := by
    have h := congrArg (Set.image (MonoidHom.fst X Y)) hprod
    rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map,
      ← hmap₁, ← hS₁] at h
    exact h
  have himg₂ : (((S₂ : Subgroup Y) : Set Y) * (A₂ : Set Y)) =
      (((S₂ : Subgroup Y) ⊔ A₂ : Subgroup Y) : Set Y) := by
    have h := congrArg (Set.image (MonoidHom.snd X Y)) hprod
    rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map,
      ← hmap₂, ← hS₂] at h
    exact h
  have hcard₁ : Nat.card ↥((S₁ : Subgroup X) ⊔ A₁) = Nat.card S₁ * Nat.card A₁ :=
    card_sup_eq_mul_of_coe_mul_eq
      (CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd S₁.isPGroup' hodd₁) himg₁
  have hcard₂ : Nat.card ↥((S₂ : Subgroup Y) ⊔ A₂) = Nat.card S₂ * Nat.card A₂ :=
    card_sup_eq_mul_of_coe_mul_eq
      (CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd S₂.isPGroup' hodd₂) himg₂
  have hSprod : (S : Subgroup (X × Y)) = (S₁ : Subgroup X).prod (S₂ : Subgroup Y) := by
    refine (S.is_maximal' (Q := (S₁ : Subgroup X).prod (S₂ : Subgroup Y)) ?_ ?_).symm
    · have hpg : IsPGroup 2 (↥S₁ × ↥S₂) := IsPGroup.prod S₁.isPGroup' S₂.isPGroup'
      exact hpg.of_equiv (Subgroup.prodEquiv (S₁ : Subgroup X) (S₂ : Subgroup Y)).symm
    · intro x hx
      rw [Subgroup.mem_prod]
      exact ⟨Subgroup.mem_map_of_mem (f := MonoidHom.fst X Y) hx,
        Subgroup.mem_map_of_mem (f := MonoidHom.snd X Y) hx⟩
  have hnorm₁ := hX S₁ A₁ hA₁ hodd₁ hcard₁
  have hnorm₂ := hY S₂ A₂ hA₂ hodd₂ hcard₂
  intro a ha
  have ha₁ : a.1 ∈ A₁ := Subgroup.mem_map_of_mem (f := MonoidHom.fst X Y) ha
  have ha₂ : a.2 ∈ A₂ := Subgroup.mem_map_of_mem (f := MonoidHom.snd X Y) ha
  rw [hSprod, Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ (S₁ : Subgroup X).prod (S₂ : Subgroup Y) := hx
    rw [Subgroup.mem_prod] at hx'
    change a * x * a⁻¹ ∈ (S₁ : Subgroup X).prod (S₂ : Subgroup Y)
    rw [Subgroup.mem_prod]
    exact ⟨(Subgroup.mem_set_normalizer_iff.mp (hnorm₁ ha₁) x.1).mp hx'.1,
      (Subgroup.mem_set_normalizer_iff.mp (hnorm₂ ha₂) x.2).mp hx'.2⟩
  · intro hx
    have hx' : a * x * a⁻¹ ∈ (S₁ : Subgroup X).prod (S₂ : Subgroup Y) := hx
    rw [Subgroup.mem_prod] at hx'
    change x ∈ (S₁ : Subgroup X).prod (S₂ : Subgroup Y)
    rw [Subgroup.mem_prod]
    exact ⟨(Subgroup.mem_set_normalizer_iff.mp (hnorm₁ ha₁) x.1).mpr hx'.1,
      (Subgroup.mem_set_normalizer_iff.mp (hnorm₂ ha₂) x.2).mpr hx'.2⟩

theorem borelPositionTwo_of_isL2Square {X : Type} [Group X] [Finite X] {a : ℕ}
    (h : IsL2Square X a) : BorelPositionTwo X := by
  obtain ⟨A, B, hGA, hGB, ⟨e⟩, hA, hB⟩ := h
  letI := hGA
  letI := hGB
  haveI : Finite A := Finite.of_injective (fun x : A => e.symm (x, 1)) (by
    intro x y hxy
    have h' := congrArg e hxy
    simp only [MulEquiv.apply_symm_apply] at h'
    simpa using congrArg Prod.fst h')
  haveI : Finite B := Finite.of_injective (fun y : B => e.symm (1, y)) (by
    intro x y hxy
    have h' := congrArg e hxy
    simp only [MulEquiv.apply_symm_apply] at h'
    simpa using congrArg Prod.snd h')
  exact BorelPositionTwo.of_mulEquiv e
    (BorelPositionTwo.prod (borelPositionTwo_of_isL2 hA) (borelPositionTwo_of_isL2 hB))

theorem borelPositionTwo_of_isOmegaMinus_four {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (h : IsOmegaMinus X 4 n) : BorelPositionTwo X :=
  borelPositionTwo_of_isL2 (S18.isL2_of_isOmegaMinus_four hn h)

theorem borelPositionTwo_of_isOmegaPlus_four {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (h : IsOmegaPlus X 4 n) : BorelPositionTwo X :=
  borelPositionTwo_of_isL2Square (isL2Square_of_isOmegaPlus hn h)

theorem subsingleton_of_isOmegaPlus_four_one {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} (h : IsOmegaPlus ↥H 4 1) (hperf : ⁅H, H⁆ = H) : Subsingleton ↥H := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨ε⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : Fintype ↥(orthGroup (StatedQuadPlus 2 K)) := Fintype.ofFinite _
  have hcard : Nat.card ↥(orthGroup (StatedQuadPlus 2 K)) = 2 ^ 3 * 3 ^ 2 := by
    rw [card_orthGroup_quadPlus_two, hK2]
    norm_num
  have hsolOrth : Group.IsSolvable ↥(orthGroup (StatedQuadPlus 2 K)) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])
  haveI := hsolOrth
  have hsolOmega : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (statedOmega_le_orthGroup (StatedQuadPlus 2 K)))
      (Subgroup.inclusion_injective _)
  haveI := hsolOmega
  have hsolProj : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus 2 K))) :=
    Group.isSolvable_of_surjective
      (QuotientGroup.mk'_surjective ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadPlus 2 K))))
  haveI := hsolProj
  have hsolH : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := ε.toMonoidHom) ε.injective
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  haveI : Nontrivial ↥H := hns
  haveI : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  exact (Group.IsPerfect.not_isSolvable (G := ↥H)) hsolH

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

end
