module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.GaschutzNorm

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem sup_fixed_eq_of_coprime_index [Finite G] {X T W U : Subgroup G} {e : ℕ}
    (hcop : Nat.Coprime e (T.relIndex X)) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWe : ∀ w ∈ W, w ^ e = 1) (hUW : U ≤ W) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hXU : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ U)
    (hWT : W ≤ U ⊔ W ⊓ Subgroup.centralizer (T : Set G)) :
    U ⊔ W ⊓ Subgroup.centralizer (X : Set G) = W := by
  classical
  refine le_antisymm (sup_le hUW inf_le_left) ?_
  set S := U ⊔ W ⊓ Subgroup.centralizer (X : Set G) with hS
  have : IsMulCommutative ↥W := ⟨⟨fun a b => Subtype.ext (hWc a a.2 b b.2)⟩⟩
  let _ : Fintype (↥X ⧸ T.subgroupOf X) := Fintype.ofFinite _
  have hconj : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun x hx w hw =>
    (Subgroup.mem_normalizer_iff.mp (hXW hx) w).mp hw
  have key : ∀ z ∈ W, z ∈ Subgroup.centralizer (T : Set G) → z ∈ S := by
    intro z hzW hzT
    let f : ↥X ⧸ T.subgroupOf X → ↥W := fun q =>
      Quotient.liftOn' q (fun g : ↥X => (⟨(g : G) * z * (g : G)⁻¹, hconj g g.2 z hzW⟩ : ↥W))
        (fun a b hab => by
          rw [QuotientGroup.leftRel_apply] at hab
          have hab' : ((a⁻¹ * b : ↥X) : G) ∈ T := hab
          have hc := Subgroup.mem_centralizer_iff.mp hzT _ hab'
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
          calc (a : G) * z * (a : G)⁻¹ =
                (a : G) * (((a : G)⁻¹ * b) * z * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by
                rw [hc]
                group
            _ = (b : G) * z * (b : G)⁻¹ := by group)
    have hfmk : ∀ g : ↥X, f (g : ↥X ⧸ T.subgroupOf X) =
        ⟨(g : G) * z * (g : G)⁻¹, hconj g g.2 z hzW⟩ := fun g => rfl
    set N : ↥W := ∏ q, f q with hN
    have hNX : (N : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      let cx : ↥W →* ↥W :=
        { toFun := fun w => ⟨x * w * x⁻¹, hconj x hx w w.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
      have h1 : cx N = N := by
        rw [hN, map_prod]
        have h2 : ∀ q, cx (f q) = f ((⟨x, hx⟩ : ↥X) • q) := by
          intro q
          induction q using QuotientGroup.induction_on with
          | H g =>
            apply Subtype.ext
            show x * ((g : G) * z * (g : G)⁻¹) * x⁻¹ = (((⟨x, hx⟩ : ↥X) * g : ↥X) : G) * z *
              (((⟨x, hx⟩ : ↥X) * g : ↥X) : G)⁻¹
            simp only [Subgroup.coe_mul, mul_inv_rev]
            group
        simp only [h2]
        exact Fintype.prod_equiv (MulAction.toPerm (⟨x, hx⟩ : ↥X)) _ _ (fun q => rfl)
      have h3 := congrArg Subtype.val h1
      change x * (N : G) * x⁻¹ = N at h3
      calc x * (N : G) = x * (N : G) * x⁻¹ * x := by group
        _ = N * x := by rw [h3]
    have hcomm : ∀ q, ((f q / ⟨z, hzW⟩ : ↥W) : G) ∈ U := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hfmk, Subgroup.coe_div, div_eq_mul_inv]
        exact hXU g g.2 z hzW
    have hcard : Fintype.card (↥X ⧸ T.subgroupOf X) = T.relIndex X := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    have hNz : N = (∏ q, (f q / ⟨z, hzW⟩)) * ⟨z, hzW⟩ ^ T.relIndex X := by
      rw [hN, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      simp only [div_mul_cancel]
    have hP : ((∏ q, (f q / ⟨z, hzW⟩) : ↥W) : G) ∈ U := by
      have : (∏ q, (f q / ⟨z, hzW⟩) : ↥W) ∈ U.subgroupOf W :=
        Subgroup.prod_mem (U.subgroupOf W) (fun q _ => Subgroup.mem_subgroupOf.mpr (hcomm q))
      exact Subgroup.mem_subgroupOf.mp this
    have hzn : (((⟨z, hzW⟩ : ↥W) ^ T.relIndex X : ↥W) : G) ∈ S := by
      have h1 : (((⟨z, hzW⟩ : ↥W) ^ T.relIndex X : ↥W) : G) =
          ((∏ q, (f q / ⟨z, hzW⟩) : ↥W) : G)⁻¹ * (N : G) := by
        rw [hNz]
        simp only [Subgroup.coe_mul]
        group
      rw [h1]
      exact S.mul_mem (S.inv_mem (le_sup_left (a := U) hP))
        (le_sup_right (a := U) ⟨N.2, hNX⟩)
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (T.relIndex X : ℤ) * a + (e : ℤ) * b = 1 := by
      refine ⟨Nat.gcdB e (T.relIndex X), Nat.gcdA e (T.relIndex X), ?_⟩
      have h := Nat.gcd_eq_gcd_ab e (T.relIndex X)
      rw [hcop] at h
      push_cast at h
      linarith
    have hze : z ^ e = 1 := hWe z hzW
    have hz : z = (z ^ T.relIndex X) ^ a := by
      calc z = z ^ ((T.relIndex X : ℤ) * a + (e : ℤ) * b) := by rw [hab, zpow_one]
        _ = (z ^ T.relIndex X) ^ a * (z ^ e) ^ b := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
        _ = (z ^ T.relIndex X) ^ a := by rw [hze, one_zpow, mul_one]
    rw [hz]
    have : z ^ T.relIndex X ∈ S := by simpa using hzn
    exact S.zpow_mem this a
  intro w hw
  have h1 : (⟨w, hw⟩ : ↥W) ∈ (U ⊔ W ⊓ Subgroup.centralizer (T : Set G)).subgroupOf W :=
    Subgroup.mem_subgroupOf.mpr (hWT hw)
  rw [Subgroup.subgroupOf_sup hUW inf_le_left] at h1
  obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup.mp h1
  rw [Subgroup.mem_subgroupOf] at hu hz
  have hw' : w = (u : G) * z := by
    have := congrArg Subtype.val huz
    simpa using this.symm
  rw [hw']
  exact S.mul_mem (le_sup_left (a := U) hu) (key z z.2 hz.2)

end CFSG.Quasithin.GaschutzNorm
