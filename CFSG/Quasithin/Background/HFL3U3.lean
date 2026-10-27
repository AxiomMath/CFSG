module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

variable {F : Type*} [Field F]

theorem uni3_entries {x : SpecialLinearGroup (Fin 3) F} (hx : x ∈ unitriangular 3 F) :
    (x : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (x : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧
      (x : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 ∧ (x : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (x : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hx
  exact ⟨hdiag 0, hdiag 1, hdiag 2, hlow 1 0 (by decide), hlow 2 0 (by decide),
    hlow 2 1 (by decide)⟩

theorem uni3_mul_02 {x y : SpecialLinearGroup (Fin 3) F} (hx : x ∈ unitriangular 3 F)
    (hy : y ∈ unitriangular 3 F) :
    ((x * y : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 =
      (y : Matrix (Fin 3) (Fin 3) F) 0 2 +
        (x : Matrix (Fin 3) (Fin 3) F) 0 1 * (y : Matrix (Fin 3) (Fin 3) F) 1 2 +
        (x : Matrix (Fin 3) (Fin 3) F) 0 2 := by
  obtain ⟨x00, -, x22, -, -, -⟩ := uni3_entries hx
  obtain ⟨-, -, y22, -, -, -⟩ := uni3_entries hy
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, x00, y22]
  ring

theorem uni3_cases [CharP F 2] {E : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hEU : E ≤ unitriangular 3 F) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) :
    (∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) ∨
      ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨⟨x, hxE, hx12⟩, ⟨y, hyE, hy01⟩⟩ := hno
  have hsq : ∀ z ∈ E, (z : Matrix (Fin 3) (Fin 3) F) 0 1 *
      (z : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    intro z hz
    have h1 := congrArg (fun w : SpecialLinearGroup (Fin 3) F =>
      (w : Matrix (Fin 3) (Fin 3) F) 0 2) (hs z hz)
    rw [uni3_mul_02 (hEU hz) (hEU hz), SpecialLinearGroup.coe_one, Matrix.one_apply_ne
      (by decide)] at h1
    have h2 : (z : Matrix (Fin 3) (Fin 3) F) 0 2 + (z : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 :=
      CharTwo.add_self_eq_zero _
    linear_combination h1 - h2
  have hx01 : (x : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
    have := hsq x hxE
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hx12
  have hy12 : (y : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    have := hsq y hyE
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy01
    · exact h
  have hcomm := congrArg (fun w : SpecialLinearGroup (Fin 3) F =>
    (w : Matrix (Fin 3) (Fin 3) F) 0 2) (hc x hxE y hyE)
  rw [uni3_mul_02 (hEU hxE) (hEU hyE), uni3_mul_02 (hEU hyE) (hEU hxE), hx01, hy12] at hcomm
  have : (y : Matrix (Fin 3) (Fin 3) F) 0 1 * (x : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    linear_combination -hcomm
  rcases mul_eq_zero.1 this with h | h
  · exact hy01 h
  · exact hx12 h

theorem uni3_ext {x y : SpecialLinearGroup (Fin 3) F} (hx : x ∈ unitriangular 3 F)
    (hy : y ∈ unitriangular 3 F)
    (h01 : (x : Matrix (Fin 3) (Fin 3) F) 0 1 = (y : Matrix (Fin 3) (Fin 3) F) 0 1)
    (h02 : (x : Matrix (Fin 3) (Fin 3) F) 0 2 = (y : Matrix (Fin 3) (Fin 3) F) 0 2)
    (h12 : (x : Matrix (Fin 3) (Fin 3) F) 1 2 = (y : Matrix (Fin 3) (Fin 3) F) 1 2) :
    x = y := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx
  obtain ⟨y00, y11, y22, y10, y20, y21⟩ := uni3_entries hy
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem card_le_sq_of_uni3 [CharP F 2] [Finite F] {E : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hEU : E ≤ unitriangular 3 F) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Nat.card F ^ 2 := by
  rcases uni3_cases hEU hc hs with h | h
  · let f : E → F × F := fun x => ((x : Matrix (Fin 3) (Fin 3) F) 0 1,
      (x : Matrix (Fin 3) (Fin 3) F) 0 2)
    have hf : Function.Injective f := fun x y hxy => Subtype.ext (uni3_ext (hEU x.2) (hEU y.2)
      (congrArg Prod.fst hxy) (congrArg Prod.snd hxy) ((h x x.2).trans (h y y.2).symm))
    calc Nat.card E ≤ Nat.card (F × F) := Nat.card_le_card_of_injective f hf
      _ = Nat.card F ^ 2 := by rw [Nat.card_prod, sq]
  · let f : E → F × F := fun x => ((x : Matrix (Fin 3) (Fin 3) F) 0 2,
      (x : Matrix (Fin 3) (Fin 3) F) 1 2)
    have hf : Function.Injective f := fun x y hxy => Subtype.ext (uni3_ext (hEU x.2) (hEU y.2)
      ((h x x.2).trans (h y y.2).symm) (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    calc Nat.card E ≤ Nat.card (F × F) := Nat.card_le_card_of_injective f hf
      _ = Nat.card F ^ 2 := by rw [Nat.card_prod, sq]

theorem exists_conj_le_uni3 [CharP F 2] [Finite F] {P : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hP : IsPGroup 2 P) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ x ∈ P, g * x * g⁻¹ ∈ unitriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) Q U
  refine ⟨g, fun x hx => ?_⟩
  have h1 : MulAut.conj g • x ∈ MulAut.conj g • (Q : Subgroup (SpecialLinearGroup (Fin 3) F)) :=
    Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) Q (hPQ hx)
  rw [← Sylow.coe_subgroup_smul, hg, hU] at h1
  exact h1

theorem card_le_sq_of_elemAb [CharP F 2] [Finite F]
    {E : Subgroup (SpecialLinearGroup (Fin 3) F)} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Nat.card F ^ 2 := by
  have hP : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hs x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_uni3 hP
  set E' := E.map (MulAut.conj g).toMonoidHom
  have hE'U : E' ≤ unitriangular 3 F := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hc' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have hs' : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hs x hx, map_one]
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [← hcard]
  exact card_le_sq_of_uni3 hE'U hc' hs'

end CFSG.Quasithin.H.L3Nine
