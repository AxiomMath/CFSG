module

public import CFSG.Sporadic.Co2Smith.Sp6Pres
public import CFSG.Sporadic.Co2Smith.Sp6EnumCheck
public import CFSG.Certificates.CosetTableColumns
public import CFSG.Sporadic.Co2Smith.Structure

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.CosetTable

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

abbrev sp6RelSet : Set (FreeGroup (Fin 8)) := {r | r ∈ Native.sp6Rels.map FreeGroup.mk}

theorem lift_sp6Gen_relSet :
    ∀ r ∈ sp6RelSet, FreeGroup.lift sp6Gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact lift_sp6Gen_rel hw

abbrev PGsp6 : Type := PG 8 Native.sp6Rels

@[expose] noncomputable def sp6Hom :
    PGsp6 →* S0 := PresentedGroup.toGroup lift_sp6Gen_relSet

theorem sp6Hom_of
    (i : Fin 8) : sp6Hom (PresentedGroup.of i) = sp6Gen i :=
  PresentedGroup.toGroup.of _

theorem sp6Hom_mk
    (f : FreeGroup (Fin 8)) :
    sp6Hom (PresentedGroup.mk _ f) = FreeGroup.lift sp6Gen f := rfl

theorem sp6Hom_surjective :
    Function.Surjective sp6Hom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_sp6Gen, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, sp6Hom_of i⟩

theorem subsetOf_nil (m : ℕ) : subsetOf m [] = [] := by
  simp [subsetOf]

theorem card_le_of_subsetCheckC_nil {m : ℕ} (ws : List (List (Fin m × Bool))) {cap n : ℕ}
    (h : subsetCheckC ws [] cap n = true) : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS := subsetOf_nil m
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]
    exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]
    exact card_PG_zero _
  obtain ⟨hf, hle⟩ := card_le_of_subsetCheckC ws [] h
  rw [hc, mul_one] at hle
  exact ⟨hf, hle⟩

theorem finite_card_PGsp6 :
    Finite PGsp6 ∧ Nat.card PGsp6 ≤ 1451520 :=
  sp6_card

theorem sp6Hom_bijective :
    Function.Bijective sp6Hom := by
  have := finite_card_PGsp6.1
  exact sp6Hom_surjective.bijective_of_nat_card_le (by
    rw [card_S0]
    exact finite_card_PGsp6.2)

theorem lift_sp6Gen_eq_one_iff
    (f : FreeGroup (Fin 8)) :
    FreeGroup.lift sp6Gen f = 1 ↔ f ∈ Subgroup.normalClosure sp6RelSet := by
  rw [← PresentedGroup.mk_eq_one_iff, ← sp6Hom_mk]
  constructor
  · intro h
    exact sp6Hom_bijective.1 (h.trans (map_one sp6Hom).symm)
  · intro h
    rw [h, map_one]

end CFSG.Sporadic.Co2Smith
