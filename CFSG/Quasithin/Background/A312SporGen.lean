module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem not_isSolvable_sup {S B : Subgroup Γ} (hB : B ∈ lFamily S) :
    ¬ Group.IsSolvable ↥(B ⊔ S) := fun _ =>
  not_isSolvable_of_mem_cComp hB
    (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_of_mem_cComp hB : B ≤ B ⊔ S))
      (Subgroup.inclusion_injective _))

theorem isSolvable_of_card_pq {Y : Subgroup Γ} {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (h : Nat.card Y = p ^ a * q ^ b) : Group.IsSolvable ↥Y := by
  let _ : Fintype ↥Y := Fintype.ofFinite ↥Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

omit [Finite Γ] in
theorem isSolvable_of_normal {Y N : Subgroup Γ} (hNY : N ≤ Y)
    (hN : Y ≤ Subgroup.normalizer (N : Set Γ)) (hNs : Group.IsSolvable ↥N)
    (hq : ∀ [(N.subgroupOf Y).Normal], Group.IsSolvable (↥Y ⧸ N.subgroupOf Y)) :
    Group.IsSolvable ↥Y := by
  have hnorm : (N.subgroupOf Y).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hN y.2) x).mp hx
  have hNs' : Group.IsSolvable ↥(N.subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNY).injective
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf Y).subtype
    (QuotientGroup.mk' (N.subgroupOf Y)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem a312For_of_members (hq : CFSG.IsQuasisimple Γ) {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) {L : Array ℕ} {Y : ℕ → Subgroup Γ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hmem : ∀ j < L.size, ∀ B ∈ lFamily S, B ⊔ S = Y j → A312Case B ⊤) : A312For Γ := by
  refine A312For.of_sylow S hS fun B hB hBtop => ?_
  obtain ⟨j, hj, hjZ⟩ := hall (B ⊔ S) le_sup_right
  by_cases hjL : j < L.size
  · rw [memberOrTop, ite_eq_left hjL] at hjZ
    exact hmem j hjL B hB hjZ
  · exfalso
    rw [memberOrTop, ite_eq_right hjL] at hjZ
    have hB' : B ∈ cComp (B ⊔ S) := hB
    rw [hjZ] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')

theorem perfectCore_eq_of_index_two {Y A : Subgroup Γ} (hAY : A ≤ Y)
    (hcard : Nat.card Y = 2 * Nat.card A) (hA : ⁅A, A⁆ = A) : perfectCore Y = A := by
  have hcomm : ⁅Y, Y⁆ ≤ A := PermLat.commutator_le_of_card_eq_two_mul hAY hcard
  exact le_antisymm ((Seven.perfectCore_le_commutator Y).trans hcomm)
    (le_perfectCore_of_perfect hAY hA)

theorem isAlt5_of_perfectCore {S B : Subgroup Γ} (hB : B ∈ lFamily S)
    [IsSimpleGroup ↥(perfectCore (B ⊔ S))] (h60 : Nat.card ↥(perfectCore (B ⊔ S)) = 60) :
    IsAlt 5 ↥B := by
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
  have := Seven.alt5_simple
  exact Seven.lFamily_equiv_of_perfectCore_equiv hB Seven.alt5_nonabelian e

end CFSG.Quasithin.A312S
