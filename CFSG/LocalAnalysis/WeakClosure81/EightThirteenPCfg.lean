module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

structure Cfg813 {Q : Type} [Group Q] [Finite Q] (T A B R L₀ : Subgroup Q) : Prop where
  no_normal_two : ∀ P : Subgroup Q, P.Normal → IsPGroup 2 P → P = ⊥
  sylow : IsSylowIn 2 T ⊤
  A_le : A ≤ T
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card A = 4
  K1 : K1In ⊤ A
  TIS : ∀ q : Q, A ⊓ conjSubgroup B q = ⊥ ∨ A ≤ conjSubgroup B q
  maxT : calNIn (⊤ : Subgroup Q) T = {B}
  R_normal : R.Normal
  R_solvable : IsSolvable R
  R_le_B : R ≤ B
  L₀_comp : IsComponentModN R ⊤ L₀
  L₀_simple : HasQuotShape L₀ (R : Set Q) (fun X _ => IsSimpleGroup X)
  L₀_sup : L₀ ⊔ T = ⊤
  L₀_shape :
    (HasQuotShape L₀ (R : Set Q) (fun X _ => IsL2 X 2) ∨
        HasQuotShape L₀ (R : Set Q) (fun X _ => IsU3 X 2)) ∨
      ((HasQuotShape L₀ (R : Set Q) (fun X _ => IsL3 X 2) ∨
          HasQuotShape L₀ (R : Set Q) (fun X _ => IsSp4 X 2)) ∧
        ∃ t ∈ T ⊓ normalizer (L₀ : Set Q), ActsOnDynkinMod R L₀ t)

section Astar

variable {Q : Type} [Group Q]

def Astar (T J A : Subgroup Q) : Subgroup Q where
  carrier := {ℓ | ℓ ∈ T ⊓ J ∧ ∃ c ∈ T ⊓ centralizer (J : Set Q), ℓ * c ∈ A}
  mul_mem' := by
    rintro x y ⟨hx, c₁, hc₁, hxc⟩ ⟨hy, c₂, hc₂, hyc⟩
    refine ⟨(T ⊓ J).mul_mem hx hy, c₁ * c₂, (T ⊓ centralizer (J : Set Q)).mul_mem hc₁ hc₂, ?_⟩
    have hcomm : y * c₁ = c₁ * y :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₁).2 y (Subgroup.mem_inf.mp hy).2
    have : x * y * (c₁ * c₂) = (x * c₁) * (y * c₂) := by
      calc x * y * (c₁ * c₂) = x * (y * c₁) * c₂ := by group
        _ = x * (c₁ * y) * c₂ := by rw [hcomm]
        _ = (x * c₁) * (y * c₂) := by group
    rw [this]
    exact A.mul_mem hxc hyc
  one_mem' := ⟨(T ⊓ J).one_mem, 1, (T ⊓ centralizer (J : Set Q)).one_mem, by
    simpa using A.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, c, hc, hxc⟩
    refine ⟨(T ⊓ J).inv_mem hx, c⁻¹, (T ⊓ centralizer (J : Set Q)).inv_mem hc, ?_⟩
    have hcomm : x * c = c * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 x (Subgroup.mem_inf.mp hx).2
    have : x⁻¹ * c⁻¹ = (x * c)⁻¹ := by
      calc x⁻¹ * c⁻¹ = (c * x)⁻¹ := by group
        _ = (x * c)⁻¹ := by rw [hcomm]
    rw [this]
    exact A.inv_mem hxc

theorem mem_Astar {T J A : Subgroup Q} {ℓ : Q} :
    ℓ ∈ Astar T J A ↔
      ℓ ∈ T ⊓ J ∧ ∃ c ∈ T ⊓ centralizer (J : Set Q), ℓ * c ∈ A :=
  Iff.rfl

end Astar

end CFSG.LocalAnalysis.WeakClosure81

end
