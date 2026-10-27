module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.IsPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A normal complement in a semidirect subgroup

This is the elementary algebraic core used in the linear equation-(11)
classification step.  If `N ⊴ H`, `H = N C`, `C` is cyclic, and no nontrivial
element of `N` normalizes the selected prime-order subgroup `X ≤ C`, then
`N` is the normal complement of `N_H(X)`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

public theorem normal_complement_of_semidirect_cyclic_normalizer
    {H : Type u} [Group H] [Finite H]
    (N C X : Subgroup H)
    (hNnormal : N.Normal)
    (hCcyc : IsCyclic C)
    (hdisj : Disjoint N C)
    (hjoin : N ⊔ C = ⊤)
    (hXleC : X ≤ C)
    (hNnorm : ∀ n : H, n ∈ N → n ∈ Subgroup.normalizer (X : Set H) → n = 1) :
    N.Normal ∧
      (Subgroup.normalizer (X : Set H) = C) ∧
      N ⊓ Subgroup.normalizer (X : Set H) = ⊥ ∧
      N ⊔ Subgroup.normalizer (X : Set H) = ⊤ := by
  classical
  let : N.Normal := hNnormal
  have hCleN : C ≤ Subgroup.normalizer (X : Set H) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hcomm : (c : H) * x = x * (c : H) := by
        let : IsMulCommutative (↥C) := hCcyc.isMulCommutative
        exact congrArg Subtype.val
          (show (⟨c, hc⟩ : C) * ⟨x, hXleC hx⟩ =
              ⟨x, hXleC hx⟩ * ⟨c, hc⟩ by
            exact (isMulCommutative_iff.mp inferInstance) _ _)
      rw [hcomm]
      simpa using hx
    · intro hx
      let y : H := c * x * c⁻¹
      have hyC : y ∈ C := hXleC hx
      have hcomm : (c : H) * y = y * (c : H) := by
        let : IsMulCommutative (↥C) := hCcyc.isMulCommutative
        exact congrArg Subtype.val
          (show (⟨c, hc⟩ : C) * ⟨y, hyC⟩ =
              ⟨y, hyC⟩ * ⟨c, hc⟩ by
            exact (isMulCommutative_iff.mp inferInstance) _ _)
      have hrecover : (c : H)⁻¹ * y * (c : H) = y := by
        calc
          (c : H)⁻¹ * y * (c : H) = (c : H)⁻¹ * (y * (c : H)) := by rw [mul_assoc]
          _ = (c : H)⁻¹ * ((c : H) * y) := by
            exact congrArg (fun z : H => (c : H)⁻¹ * z) hcomm.symm
          _ = y := by group
      have hxy : x = y := by
        dsimp [y]
        calc
          x = (c : H)⁻¹ * ((c : H) * x * (c : H)⁻¹) * (c : H) := by group
          _ = (c : H)⁻¹ * y * (c : H) := by rfl
          _ = y := hrecover
      exact hxy ▸ hx
  have hNleNorm : N ⊓ Subgroup.normalizer (X : Set H) = ⊥ := by
    apply le_bot_iff.mp
    intro n hn
    exact hNnorm n hn.1 hn.2
  have hNormleC : Subgroup.normalizer (X : Set H) ≤ C := by
    intro z hz
    have hzprod : z ∈ ((N : Set H) * (C : Set H) : Set H) := by
      rw [← Subgroup.normal_mul N C, hjoin]
      trivial
    rcases hzprod with ⟨n, hn, c, hc, hzc⟩
    have hnnorm : n ∈ Subgroup.normalizer (X : Set H) := by
      have hnexpr : (n : H) = z * (c : H)⁻¹ := by
        rw [← hzc]
        group
      rw [hnexpr]
      exact (Subgroup.normalizer (X : Set H)).mul_mem hz
        ((Subgroup.normalizer (X : Set H)).inv_mem (hCleN hc))
    have hn1 : (n : H) = 1 := hNnorm n hn hnnorm
    rw [← hzc, hn1]
    simp only [one_mul]
    exact hc
  refine ⟨hNnormal, ?_, hNleNorm, ?_⟩
  · exact le_antisymm hNormleC hCleN
  · rw [← hjoin]
    rw [le_antisymm hNormleC hCleN]

/-! A perfect group has no nontrivial homomorphism into a cyclic group. -/

public theorem MonoidHom.eq_one_of_perfect_of_cyclic
    {H C : Type u} [Group H] [Group C]
    (hH : Group.IsPerfect H) (hC : IsCyclic C) (f : H →* C) :
    ∀ x : H, f x = 1 := by
  let : Group.IsPerfect H := hH
  let : IsCyclic C := hC
  intro x
  have hcomm : x ∈ commutator H := by
    rw [hH.commutator_eq_top]
    trivial
  let R : Subgroup C := (⊤ : Subgroup H).map f
  have hRcyc : IsCyclic R :=
    Subgroup.isCyclic_of_le (show R ≤ ⊤ by exact le_top)
  have hRcomm : ⁅R, R⁆ = ⊥ := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer).2
    exact (Subgroup.le_centralizer_iff_isMulCommutative).2 hRcyc.isMulCommutative
  have hmap : (commutator H).map f = ⁅R, R⁆ := by
    have hm := Subgroup.map_commutator (⊤ : Subgroup H) (⊤ : Subgroup H) f
    calc
      (commutator H).map f = (⊤ : Subgroup H).map f := by
        rw [hH.commutator_eq_top]
      _ = ⁅(⊤ : Subgroup H).map f, (⊤ : Subgroup H).map f⁆ := by
        calc
          (⊤ : Subgroup H).map f = (commutator H).map f := by
            rw [hH.commutator_eq_top]
          _ = ⁅(⊤ : Subgroup H).map f, (⊤ : Subgroup H).map f⁆ := hm
      _ = ⁅R, R⁆ := by rfl
  have hxmap : f x ∈ ⁅R, R⁆ := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨x, hcomm, rfl⟩
  rw [hRcomm] at hxmap
  exact Subgroup.mem_bot.mp hxmap

public theorem card_dvd_field_card_of_pgroup_subgroup_psl2
    {F : Type u} [Field F] [Finite F]
    {r f : ℕ} [Fact r.Prime]
    (hFcard : Nat.card F = r ^ f)
    (N : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))
    (hN : IsPGroup r N) :
    Nat.card N ∣ Nat.card F := by
  obtain ⟨S, hNS⟩ := hN.exists_le_sylow
  have hNdivS : Nat.card N ∣ Nat.card (S : Subgroup
      (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) :=
    Subgroup.card_dvd_of_le hNS
  have hScard : Nat.card (S : Subgroup
      (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨e⟩ := Glauberman.Dickson.huppert_II_8_2_a_sylow_equiv_additive
      hFcard S
    exact (Nat.card_congr e.toEquiv).symm
  rw [hScard] at hNdivS
  exact hNdivS

end CFSG.GorensteinWalter
