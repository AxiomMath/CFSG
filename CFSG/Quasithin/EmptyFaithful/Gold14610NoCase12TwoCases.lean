module

public import CFSG.Quasithin.EmptyFaithful.Gold14610NoCase12Two
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace Gold14610

namespace NC12

variable {D : Type} [Group D] [Finite D]

theorem card_subgroup_prod {G H : Type*} [Group G] [Group H] (A : Subgroup G) (B : Subgroup H) :
    Nat.card ↥(A.prod B) = Nat.card ↥A * Nat.card ↥B := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Subgroup.prodEquiv A B).toEquiv

theorem alt3_comm {x y : Equiv.Perm (Fin 3)} (hx : x ∈ alternatingGroup (Fin 3))
    (hy : y ∈ alternatingGroup (Fin 3)) : x * y = y * x := by
  have key : ∀ x y : Equiv.Perm (Fin 3), Equiv.Perm.sign x = 1 → Equiv.Perm.sign y = 1 →
      x * y = y * x := by decide
  exact key x y (Equiv.Perm.mem_alternatingGroup.mp hx) (Equiv.Perm.mem_alternatingGroup.mp hy)

theorem exists_normal_of_perm_prod {D₁ D₂ : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂)
    (e : D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :
    ∃ P : Subgroup D, P.Normal ∧ twoResidual D₂ ≤ P ∧ ¬ twoResidual D₁ ≤ P := by
  classical
  let A : Subgroup (Equiv.Perm (Fin 3)) := alternatingGroup (Fin 3)
  let N : Subgroup D := (A.prod A).comap e.toMonoidHom
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance _
  have hAc : Nat.card ↥A = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hNc : Nat.card ↥N = 9 := by
    have : Nat.card ↥N = Nat.card ↥(A.prod A) := by
      show Nat.card ↥(Subgroup.comap (e : D →* _) (A.prod A)) = _
      rw [Subgroup.comap_equiv_eq_map_symm]
      exact Subgroup.card_map_of_injective e.symm.injective
    rw [this, card_subgroup_prod, hAc]
  have hN3 : IsPGroup 3 ↥N := IsPGroup.of_card (n := 2) (by rw [hNc]; norm_num)
  have hmem : ∀ x : D, x ∈ N ↔ (e x).1 ∈ A ∧ (e x).2 ∈ A := fun x => Iff.rfl
  have hN2 : ∀ x : D, ∃ k : ℕ, x ^ 2 ^ k ∈ N := fun x => ⟨1, by
    rw [hmem, pow_one, map_pow]
    constructor
    · rw [Prod.pow_fst, Equiv.Perm.mem_alternatingGroup, map_pow]
      exact Int.units_sq _
    · rw [Prod.pow_snd, Equiv.Perm.mem_alternatingGroup, map_pow]
      exact Int.units_sq _⟩
  have hcomm : (⁅N, N⁆ : Subgroup D) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx y hy
    apply e.injective
    have hx' := (hmem x).mp hx
    have hy' := (hmem y).mp hy
    rw [map_mul, map_mul]
    exact Prod.ext (alt3_comm hy'.1 hx'.1) (alt3_comm hy'.2 hx'.2)
  exact exists_normal_of_normal_three hT hN3 hN2 (by rw [hcomm, Subgroup.card_bot, hNc]; norm_num)

theorem exists_normal_of_extension {D₁ D₂ : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂)
    (h : F6.IsExtensionWith D (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      (fun N => IsPOnePlusTwo 3 ↥N)) :
    ∃ P : Subgroup D, P.Normal ∧ twoResidual D₂ ≤ P ∧ ¬ twoResidual D₁ ≤ P := by
  classical
  obtain ⟨φ, -, hex, hcard, -⟩ := h
  have hZ : ∀ x y : ↥φ.ker, ⁅x, y⁆ ∈ Subgroup.center ↥φ.ker := by
    intro x y
    have := CFSG.IsExtraspecial.quotient_elementary_abelian 3 ↥φ.ker
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact IsMulCommutative.is_comm.comm _ _
  have hcomm : Nat.card ↥(⁅φ.ker, φ.ker⁆ : Subgroup D) ≤ 3 := by
    have hle : (⁅φ.ker, φ.ker⁆ : Subgroup D) ≤ (Subgroup.center ↥φ.ker).map φ.ker.subtype := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact ⟨⁅⟨x, hx⟩, ⟨y, hy⟩⁆, hZ _ _, rfl⟩
    calc Nat.card ↥(⁅φ.ker, φ.ker⁆ : Subgroup D)
        ≤ Nat.card ↥((Subgroup.center ↥φ.ker).map φ.ker.subtype) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥(Subgroup.center ↥φ.ker) :=
          Subgroup.card_map_of_injective φ.ker.subtype_injective
      _ = 3 := hex.center_order_p
  refine exists_normal_of_normal_three hT (N := φ.ker) (IsPGroup.of_card hcard) ?_ ?_
  · intro x
    refine ⟨1, ?_⟩
    rw [MonoidHom.mem_ker, pow_one, map_pow]
    generalize φ x = y
    revert y
    decide
  · rw [hcard]
    omega

theorem exists_normal_of_isF618CaseTwo {D₁ D₂ : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂)
    (h : F6.IsF618CaseTwo D) :
    ∃ P : Subgroup D, P.Normal ∧ twoResidual D₂ ≤ P ∧ ¬ twoResidual D₁ ≤ P := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact exists_normal_of_perm_prod hT e
  · exact exists_normal_of_extension hT h

end NC12

end Gold14610

end CFSG.Quasithin
