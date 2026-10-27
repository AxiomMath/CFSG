module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup

@[expose] def CompModel (F₁ F₂ : Type) [Group F₁] [Group F₂] (T : Type) [Group T] : Prop :=
  ∀ E : Subgroup T, CFSG.IsComponent E → Nonempty (↥E ≃* F₁) ∨ Nonempty (↥E ≃* F₂)

variable {F₁ F₂ : Type} [Group F₁] [Group F₂]

theorem CompModel.of_mulEquiv {T T' : Type} [Group T] [Group T'] (ψ : T ≃* T')
    (h : CompModel F₁ F₂ T') : CompModel F₁ F₂ T := by
  intro E hE
  have hE' := CFSG.LocalCores.isComponent_map_mulEquiv ψ hE
  have e : ↥E ≃* ↥(E.map ψ.toMonoidHom) := E.equivMapOfInjective ψ.toMonoidHom ψ.injective
  exact (h _ hE').imp (fun ⟨f⟩ => ⟨e.trans f⟩) (fun ⟨f⟩ => ⟨e.trans f⟩)

theorem compModel_of_sub {X : Type} [Group X] {T : Subgroup X}
    (h : ∀ E : Subgroup X, E ≤ T → CFSG.IsComponent (E.subgroupOf T) →
      Nonempty (↥E ≃* F₁) ∨ Nonempty (↥E ≃* F₂)) : CompModel F₁ F₂ ↥T := by
  intro E' hE'
  have hle : E'.map T.subtype ≤ T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsub : (E'.map T.subtype).subgroupOf T = E' :=
    Subgroup.comap_map_eq_self_of_injective T.subtype_injective E'
  have e : ↥E' ≃* ↥(E'.map T.subtype) := E'.equivMapOfInjective T.subtype T.subtype_injective
  exact (h (E'.map T.subtype) hle (by rw [hsub]; exact hE')).imp (fun ⟨f⟩ => ⟨e.trans f⟩)
    (fun ⟨f⟩ => ⟨e.trans f⟩)

@[expose] def cenEquiv {X X' : Type} [Group X] [Group X'] (φ : X ≃* X') (y : X) :
    ↥(Subgroup.centralizer ({y} : Set X)) ≃* ↥(Subgroup.centralizer ({φ y} : Set X')) where
  toFun x := ⟨φ x.1, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]⟩
  invFun x := ⟨φ.symm x.1, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x z := Subtype.ext (by simp)

theorem CompModel.centralizer_of_mulEquiv {X X' : Type} [Group X] [Group X'] (φ : X ≃* X')
    {y : X} (h : CompModel F₁ F₂ ↥(Subgroup.centralizer ({φ y} : Set X'))) :
    CompModel F₁ F₂ ↥(Subgroup.centralizer ({y} : Set X)) :=
  h.of_mulEquiv (cenEquiv φ y)

theorem centralizer_pow_eq {X : Type} [Group X] {y : X} (h7 : y ^ 7 = 1) {k : ℕ}
    (hk : Nat.Coprime k 7) :
    Subgroup.centralizer ({y ^ k} : Set X) = Subgroup.centralizer ({y} : Set X) := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk (by norm_num)
  have hy : (y ^ k) ^ m = y := by
    rw [← pow_mul, ← Nat.mod_add_div (k * m) 7, hm, pow_add, pow_mul, h7, one_pow, mul_one,
      pow_one]
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : Commute z (y ^ k) := h
    have := hc.pow_right m
    rw [hy] at this
    exact this
  · intro h
    exact (Commute.pow_right (show Commute z y from h) k).eq

theorem CompModel.centralizer_of_pow {X : Type} [Group X] {y : X} (h7 : y ^ 7 = 1) {k : ℕ}
    (hk : Nat.Coprime k 7)
    (h : CompModel F₁ F₂ ↥(Subgroup.centralizer ({y ^ k} : Set X))) :
    CompModel F₁ F₂ ↥(Subgroup.centralizer ({y} : Set X)) := by
  rw [centralizer_pow_eq h7 hk] at h
  exact h

end CFSG.RankThree.PartOne.MB3
