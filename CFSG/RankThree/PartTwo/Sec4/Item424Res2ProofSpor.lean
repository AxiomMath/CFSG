module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofPairing
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensusAlt
public import CFSG.RankThree.Asc83Table.M22
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.RankThree.Asc83Table.HS

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.RankThree.Asc83Table

@[expose] def K424Inner46FiveRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* NativeSporadic.Carrier .M12) ∨ Nonempty (X ≃* NativeSporadic.Carrier .J2) ∨
      Nonempty (X ≃* NativeSporadic.Carrier .J3) ∨
      Nonempty (X ≃* NativeSporadic.Carrier .McL)) →
    Census424 X

namespace Item424Res2

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

variable {X : Type} [Group X] [Finite X]

theorem qI_pow : qI ^ 4 = 1 ∧ qI ^ 2 ≠ 1 := by
  constructor <;> decide +kernel

theorem m23_sdR_sq_pow : (M23.sdR ^ 2) ^ 4 = 1 ∧ (M23.sdR ^ 2) ^ 2 ≠ 1 := by
  constructor <;> decide +kernel

theorem hs_sdR_sq_pow : (HS.sdR ^ 2) ^ 4 = 1 ∧ (HS.sdR ^ 2) ^ 2 ≠ 1 := by
  constructor <;> decide +kernel

omit [Finite X] in
theorem exists_pow_four_of_automizer {D : Subgroup X} {M : Type*} [Group M]
    (f : Automizer D ≃* M) {m : M} (h4 : m ^ 4 = 1) (h2 : m ^ 2 ≠ 1) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 :=
  exists_pow_four_of_mulEquiv ((Sporadic.automizerEquivAutIn D).symm.trans f) h4 h2

omit [Finite X] in
theorem exists_pow_four_m22 (e : X ≃* NativeSporadic.Carrier .M22)
    {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨-, -, h₃⟩ := e9_transport M22.E M22.factorization_card (e : X ≃* NativeSporadic.M22)
  obtain ⟨f⟩ := h₃ D hD9
  exact exists_pow_four_of_automizer (f.trans M22.E.automizerEquiv) (m := ⟨qI, M22.qI_mem⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact qI_pow.1))
    (fun h => qI_pow.2 (by simpa using congrArg Subtype.val h))

omit [Finite X] in
theorem exists_pow_four_m23
    (e : X ≃* NativeSporadic.Carrier .M23) {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨-, -, h₃⟩ := e9_transport M23.E M23.factorization_card (e : X ≃* NativeSporadic.M23)
  obtain ⟨f⟩ := h₃ D hD9
  exact exists_pow_four_of_automizer (f.trans M23.E.automizerEquiv)
    (m := ⟨M23.sdR ^ 2, pow_mem M23.sdR_mem 2⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact m23_sdR_sq_pow.1))
    (fun h => m23_sdR_sq_pow.2 (by simpa using congrArg Subtype.val h))

omit [Finite X] in
theorem exists_pow_four_hs
    (e : X ≃* NativeSporadic.Carrier .HS) {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨-, -, h₃⟩ := e9_transport HS.E HS.factorization_card (e : X ≃* NativeSporadic.HS)
  obtain ⟨f⟩ := h₃ D hD9
  exact exists_pow_four_of_automizer (f.trans HS.E.automizerEquiv)
    (m := ⟨HS.sdR ^ 2, pow_mem HS.sdR_mem 2⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact hs_sdR_sq_pow.1))
    (fun h => hs_sdR_sq_pow.2 (by simpa using congrArg Subtype.val h))

omit [Finite X] in
theorem exists_pow_four_j4
    (e : X ≃* NativeSporadic.Carrier .J4) {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨-, -, h₃⟩ := ex27_transport (J4.facts.x_cube (spec2fr 112) J4.j4_check)
    (J4.facts.y_cube (spec2fr 112) J4.j4_check) (J4.facts.z_x (spec2fr 112) J4.j4_check)
    (J4.facts.z_y (spec2fr 112) J4.j4_check) (J4.facts.z_ne (spec2fr 112) J4.j4_check)
    J4.factorization_card (e : X ≃* NativeSporadic.J4)
  obtain ⟨i, ⟨f⟩⟩ := h₃ D hD9
  obtain ⟨q⟩ := J4.automizer_B i
  exact exists_pow_four_of_automizer (f.trans q) qI_pow.1 qI_pow.2

omit [Finite X] in
theorem exists_pow_four_ru
    (e : X ≃* NativeSporadic.Carrier .Ru) {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨-, -, h₃⟩ := ex27_transport (Ru.facts.x_cube (spec2fr 28) Ru.ru_check)
    (Ru.facts.y_cube (spec2fr 28) Ru.ru_check) (Ru.facts.z_x (spec2fr 28) Ru.ru_check)
    (Ru.facts.z_y (spec2fr 28) Ru.ru_check) (Ru.facts.z_ne (spec2fr 28) Ru.ru_check)
    Ru.factorization_card (e : X ≃* NativeSporadic.Ru)
  obtain ⟨i, ⟨f⟩⟩ := h₃ D hD9
  obtain ⟨q⟩ := Ru.automizer_B i
  exact exists_pow_four_of_automizer (f.trans q) qI_pow.1 qI_pow.2

omit [Finite X] in
theorem isSolvable_centralizer_of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) (c : X)
    (h : Group.IsSolvable (Subgroup.centralizer ({e c} : Set Y))) :
    Group.IsSolvable (Subgroup.centralizer ({c} : Set X)) := by
  have hmemC : ∀ x : Subgroup.centralizer ({c} : Set X),
      e x ∈ Subgroup.centralizer ({e c} : Set Y) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (x : X) * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [← map_mul, ← map_mul, hx]
  let φ : Subgroup.centralizer ({c} : Set X) →* Subgroup.centralizer ({e c} : Set Y) :=
    (e.toMonoidHom.comp (Subgroup.centralizer ({c} : Set X)).subtype).codRestrict _ hmemC
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (e.injective (congrArg Subtype.val hab))
  exact Group.isSolvable_of_isSolvable_injective hφ

theorem census424_of_m11
    (e : X ≃* NativeSporadic.Carrier .M11) : Census424 X := by
  intro D c d K h
  exfalso
  let e' : X ≃* NativeSporadic.M11 := e
  have hc3 : e' c ^ 3 = 1 := by
    rw [← map_pow, h.maximal.prop.2 c h.c_mem, map_one]
  have hc1 : e' c ≠ 1 := fun h1 =>
    h.c_ne_one (e'.injective (h1.trans (map_one e').symm))
  have hcard := Item434SporM11.card_centralizer_eq hc3 hc1
  have hsol : Group.IsSolvable (Subgroup.centralizer ({e' c} : Set NativeSporadic.M11)) :=
    isSolvable_of_card_eq_two_mul_pow_three (k := 2) (by rw [hcard]; norm_num)
  exact not_isSolvable_centralizer h (isSolvable_centralizer_of_mulEquiv e' c hsol)

theorem census424_of_j1 (e : X ≃* NativeSporadic.Carrier .J1) :
    Census424 X := by
  refine census424_of_not_nine_dvd ?_
  have h : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  rw [h]
  norm_num

theorem census424_of_m24_he
    (hX : Nonempty (X ≃* NativeSporadic.M24) ∨ Nonempty (X ≃* NativeSporadic.He)) :
    Census424 X := by
  intro D c d K h
  refine ⟨?_, Or.inr (Res424Two.nonempty_autIn_dihedral_spor hX h)⟩
  rcases hX with hM | hH
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hH))))

end Item424Res2

open Item424Res2

theorem k424Inner46Five_of
    (hR : K424Inner46FiveRest) : K424Inner46Five := by
  rintro X _ _ hX hq hZ -
  rcases hX with ⟨s, hs, ⟨e⟩⟩ | ⟨s, -, hX⟩
  · simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact census424_of_m11 e
    · exact hR X (Or.inl ⟨e⟩)
    · intro D c d K h
      exact (false_of_pow_four h (exists_pow_four_m22 e h.card_eq)).elim
    · intro D c d K h
      exact (false_of_pow_four h (exists_pow_four_m23 e h.card_eq)).elim
    · exact census424_of_m24_he (Or.inl ⟨e⟩)
    · exact census424_of_j1 e
    · exact hR X (Or.inr (Or.inl ⟨e⟩))
    · exact hR X (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    · intro D c d K h
      exact (false_of_pow_four h (exists_pow_four_j4 e h.card_eq)).elim
    · exact hR X (Or.inr (Or.inr (Or.inr ⟨e⟩)))
    · intro D c d K h
      exact (false_of_pow_four h (exists_pow_four_hs e h.card_eq)).elim
    · exact census424_of_m24_he (Or.inr ⟨e⟩)
    · intro D c d K h
      exact (false_of_pow_four h (exists_pow_four_ru e h.card_eq)).elim
  · exact (Res423Alt.false_of_isExtOf_three hq hZ hX).elim

end CFSG.RankThree.PartTwo.Sec4
