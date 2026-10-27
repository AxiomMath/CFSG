module

public import CFSG.Timmesfeld.Bridge.OddTranspSecondKind

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem secondKind_commutator_zpowers_le (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v) :
    ⁅conjClosure (Subgroup.closure {u, w}) (u * v), Subgroup.zpowers w⁆ ≤
      conjClosure (Subgroup.closure {u, w}) (u * v) := by
  have S : SecondKindStructure u w v :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hD hN htri h4 hno
  set Q := conjClosure (Subgroup.closure {u, w}) (u * v) with hQ
  have hwK : w ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hbK : b ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.zpowers_le.mpr hwK hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ Q := S.normal b hbK a⁻¹ (Subgroup.inv_mem _ ha)
  have h2 : a * (b * a⁻¹ * b⁻¹) ∈ Q := Subgroup.mul_mem _ ha h1
  simpa only [commutatorElement_def, mul_assoc] using h2

theorem secondKind_commutator_zpowers_u_le (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v) :
    ⁅conjClosure (Subgroup.closure {u, w}) (u * v), Subgroup.zpowers u⁆ ≤
      conjClosure (Subgroup.closure {u, w}) (u * v) := by
  have S : SecondKindStructure u w v :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hD hN htri h4 hno
  set Q := conjClosure (Subgroup.closure {u, w}) (u * v) with hQ
  have huK : u ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hbK : b ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.zpowers_le.mpr huK hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ Q := S.normal b hbK a⁻¹ (Subgroup.inv_mem _ ha)
  have h2 : a * (b * a⁻¹ * b⁻¹) ∈ Q := Subgroup.mul_mem _ ha h1
  simpa only [commutatorElement_def, mul_assoc] using h2

theorem secondKind_closure_eq (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v) :
    Subgroup.closure ({u, w} : Set G) ⊔ conjClosure (Subgroup.closure {u, w}) (u * v) =
      Subgroup.closure ({u, w, v} : Set G) := by
  have S : SecondKindStructure u w v :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hD hN htri h4 hno
  set Q := conjClosure (Subgroup.closure {u, w}) (u * v) with hQ
  obtain ⟨x, hxQ, hxu⟩ := S.conj
  have hxQ' : x ∈ Q :=
    secondKind_commutator_zpowers_le hD hN htri h4 hno hxQ
  apply le_antisymm
  · rw [Subgroup.sup_eq_closure]
    refine (Subgroup.closure_le (K := Subgroup.closure ({u, w, v} : Set G))).mpr ?_
    intro y hy
    rcases hy with hyX | hyQ
    · exact Subgroup.closure_mono (by intro z hz; rcases hz with rfl | rfl <;> simp) hyX
    · exact S.le hyQ
  · refine (Subgroup.closure_le (K := Subgroup.closure ({u, w} : Set G) ⊔ Q)).mpr ?_
    intro y hy
    rcases hy with hyu | hyw | hyv
    · rw [hyu]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hyw]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hyv, ← hxu]
      have hx' : x ∈ Subgroup.closure ({u, w} : Set G) ⊔ Q := Subgroup.mem_sup_right hxQ'
      have hu' : u ∈ Subgroup.closure ({u, w} : Set G) ⊔ Q :=
        Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx' hu') (Subgroup.inv_mem _ hx')

theorem secondKind_commutator_le_centralizer (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v) :
    ⁅conjClosure (Subgroup.closure {u, w}) (u * v), Subgroup.zpowers u⁆ ≤
      Subgroup.centralizer ({u} : Set G) := by
  have S : SecondKindStructure u w v :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hD hN htri h4 hno
  set Q := conjClosure (Subgroup.closure {u, w}) (u * v) with hQ
  have hQ2 : IsPGroup 2 Q := fun q =>
    ⟨1, Subtype.ext (by simpa [pow_two] using S.sq q q.2)⟩
  have huK : u ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hnorm : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := fun q hq => S.normal u huK q hq
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmem : ⁅a, b⁆ ∈ ⁅Q, Subgroup.zpowers u⁆ :=
    Subgroup.commutator_mem_commutator ha hb
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (CFSG.Timmesfeld.Bridge.OddTransp.commute_of_mem_commutator_zpowers hD hN hQ2 htri.1
      hnorm hmem).symm

end CFSG.OddTranspositions
