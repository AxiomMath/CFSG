module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAInv

public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_R {P : Subgroup G} {a : G} (ha : a ∈ P) {r : G}
    (hr : r ∈ pCoreOf 2 (perfectCore P)) : a * r * a⁻¹ ∈ pCoreOf 2 (perfectCore P) := by
  have h1 : a ∈ Subgroup.normalizer (perfectCore P : Set G) :=
    normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer ha)
  have h2 := normalizer_localGroup_le_normalizer_pCoreOf 2 (perfectCore P) h1
  exact (Subgroup.mem_normalizer_iff.mp h2 r).mp hr

theorem conj_mem_perfectCore {P : Subgroup G} {m : G} (hm : m ∈ Subgroup.normalizer (P : Set G))
    {x : G} (hx : x ∈ perfectCore P) : m * x * m⁻¹ ∈ perfectCore P :=
  (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_perfectCore P hm) x).mp hx

theorem conj_mem_R_of_normalizer {P : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (P : Set G)) {r : G} (hr : r ∈ pCoreOf 2 (perfectCore P)) :
    m * r * m⁻¹ ∈ pCoreOf 2 (perfectCore P) := by
  have h1 := normalizer_le_normalizer_perfectCore P hm
  have h2 := normalizer_localGroup_le_normalizer_pCoreOf 2 (perfectCore P) h1
  exact (Subgroup.mem_normalizer_iff.mp h2 r).mp hr

theorem le_normalizer_R (P : Subgroup G) :
    P ≤ Subgroup.normalizer (pCoreOf 2 (perfectCore P) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => conj_mem_R ha hr, fun hr => ?_⟩
  have := conj_mem_R (P.inv_mem ha) hr
  simpa [mul_assoc] using this

def leviCent (P : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ P ∧ ∀ x ∈ perfectCore P, ⁅g, x⁆ ∈ pCoreOf 2 (perfectCore P)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨P.mul_mem ha hb, fun x hx => ?_⟩
    have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (conj_mem_R ha (hb' x hx)) (ha' x hx)
  one_mem' := ⟨P.one_mem, fun x _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨P.inv_mem ha, fun x hx => ?_⟩
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have := conj_mem_R (P.inv_mem ha) ((pCoreOf 2 (perfectCore P)).inv_mem (ha' x hx))
    simpa using this

theorem mem_leviCent {P : Subgroup G} {g : G} :
    g ∈ leviCent P ↔ g ∈ P ∧ ∀ x ∈ perfectCore P, ⁅g, x⁆ ∈ pCoreOf 2 (perfectCore P) :=
  Iff.rfl

theorem leviCent_le (P : Subgroup G) : leviCent P ≤ P := fun _ hg => hg.1

theorem le_normalizer_leviCent (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (leviCent P : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (P : Set G), ∀ g ∈ leviCent P, m * g * m⁻¹ ∈ leviCent P := by
    intro m hm g hg
    refine ⟨(Subgroup.mem_normalizer_iff.mp hm g).mp hg.1, fun x hx => ?_⟩
    have hx' : m⁻¹ * x * m ∈ perfectCore P := by
      have := conj_mem_perfectCore ((Subgroup.normalizer (P : Set G)).inv_mem hm) hx
      simpa using this
    have e : ⁅m * g * m⁻¹, x⁆ = m * ⁅g, m⁻¹ * x * m⁆ * m⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_R_of_normalizer hm (hg.2 _ hx')
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key m hm g hg, fun hg => ?_⟩
  have := key m⁻¹ ((Subgroup.normalizer (P : Set G)).inv_mem hm) _ hg
  simpa [mul_assoc] using this

theorem leviCent_normal (P : Subgroup G) : ((leviCent P).subgroupOf P).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (leviCent_le P)).mpr
    (Subgroup.le_normalizer.trans (le_normalizer_leviCent P))

section Finite

variable [Finite G]

theorem leviCent_charTwo {P : Subgroup G} (hP : CharTwo P) : CharTwo (leviCent P) :=
  CharTwo.of_normal hP (leviCent_le P) (leviCent_normal P)

theorem leviCent_carrier {P : Subgroup G} (hP : CharTwo P)
    (hall : ∀ x ∈ leviCent P, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ pCoreOf 2 P) :
    IsCarrier (leviCent P) (pCoreOf 2 (leviCent P)) := by
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hinf : pCoreOf 2 P ⊓ leviCent P ≤ pCoreOf 2 (leviCent P) := by
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right (fun y hy => ?_)
      (hQ2.to_le inf_le_left)
    exact mem_normalizer_inf (localGroup_le_normalizer_pCoreOf 2 P (leviCent_le P hy))
      (Subgroup.le_normalizer hy)
  have hch : CharTwo (leviCent P) := leviCent_charTwo hP
  refine ⟨pCoreOf_le 2 _, pCoreOf_isPGroup 2 _, localGroup_le_normalizer_pCoreOf 2 _, ?_, ?_⟩
  · intro x hx k hk
    exact hinf ⟨hall x hx k hk, hx⟩
  · intro x hx hc
    exact hch ⟨hx, Subgroup.mem_centralizer_iff.mpr fun h hh => (hc h hh).symm⟩

end Finite

end CFSG.Quasithin.GoldMLB
