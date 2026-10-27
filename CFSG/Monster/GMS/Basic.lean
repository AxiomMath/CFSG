module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Monster.GMS

open Subgroup

variable {G : Type*} [Group G]

theorem card_pCore_centralizer_le_two [Finite G] {a : G} (ha : orderOf a = 2) {H : Type*}
    [Group H] [IsSimpleGroup H] (hnonab : ∃ x y : H, x * y ≠ y * x)
    (φ : Subgroup.centralizer ({a} : Set G) →* H) (hφ : Function.Surjective φ)
    (hker : φ.ker.map (Subgroup.centralizer ({a} : Set G)).subtype = Subgroup.zpowers a) :
    Nat.card (pCore 2 (Subgroup.centralizer ({a} : Set G))) ≤ 2 := by
  have hn : ((pCore 2 (Subgroup.centralizer ({a} : Set G))).map φ).Normal :=
    (pCore_normal (p := 2) (G := Subgroup.centralizer ({a} : Set G))).map φ hφ
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal H _ _ _ hn with hbot | htop
  · have hle : pCore 2 (Subgroup.centralizer ({a} : Set G)) ≤ φ.ker :=
      (Subgroup.map_eq_bot_iff _).mp hbot
    calc Nat.card (pCore 2 (Subgroup.centralizer ({a} : Set G))) ≤ Nat.card φ.ker :=
          Subgroup.card_le_of_le hle
      _ = Nat.card (φ.ker.map (Subgroup.centralizer ({a} : Set G)).subtype) :=
          (Subgroup.card_map_of_injective
            (Subgroup.centralizer ({a} : Set G)).subtype_injective).symm
      _ = 2 := by rw [hker, Nat.card_zpowers, ha]
  · exfalso
    have : Finite H := Finite.of_surjective φ hφ
    have hpH : IsPGroup 2 H := by
      have h1 : IsPGroup 2 ((pCore 2 (Subgroup.centralizer ({a} : Set G))).map φ) :=
        (pCore_isPGroup (p := 2) (G := Subgroup.centralizer ({a} : Set G))).map φ
      rw [htop] at h1
      exact h1.of_equiv Subgroup.topEquiv
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent H := hpH.isNilpotent
    obtain ⟨x, y, hxy⟩ := hnonab
    have h : IsMulCommutative H := IsCyclic.isMulCommutative
    exact hxy (h.is_comm.comm x y)

theorem exists_not_commute_of_perfect {C H : Type*} [Group C] [Group H] [Nontrivial H]
    (hperf : commutator C = ⊤) (φ : C →* H) (hφ : Function.Surjective φ) :
    ∃ x y : H, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  obtain ⟨c, rfl⟩ := hφ h
  have hc : c ∈ commutator C := hperf ▸ Subgroup.mem_top c
  have hle : commutator C ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hcon (φ x) (φ y)]
    group
  exact hh (hle hc)

theorem card_pCore_centralizer_eq_of_isConj (p : ℕ) {a b : G} (h : IsConj a b) :
    Nat.card (pCore p (Subgroup.centralizer ({a} : Set G))) =
      Nat.card (pCore p (Subgroup.centralizer ({b} : Set G))) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hmap : (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({b} : Set G) := by
    rw [← hc]
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc c * y * c⁻¹ * (c * a * c⁻¹) = c * (y * a) * c⁻¹ := by group
        _ = c * (a * y) * c⁻¹ := by rw [hy]
        _ = c * a * c⁻¹ * (c * y * c⁻¹) := by group
    · intro hx
      refine ⟨c⁻¹ * x * c, ?_, by group⟩
      calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * a * c⁻¹) * x) * c := by rw [hx]
        _ = a * (c⁻¹ * x * c) := by group
  let e : Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({b} : Set G) :=
    ((MulAut.conj c).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  rw [← pCore_map_iso p e]
  exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm

theorem not_isConj_of_card_pCore {a z : G}
    (ha : Nat.card (pCore 2 (Subgroup.centralizer ({a} : Set G))) ≤ 2)
    (hz : 2 < Nat.card (pCore 2 (Subgroup.centralizer ({z} : Set G)))) : ¬ IsConj a z := by
  intro h
  rw [card_pCore_centralizer_eq_of_isConj 2 h] at ha
  omega

end CFSG.Monster.GMS
