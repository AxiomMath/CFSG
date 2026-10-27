module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOddKernel

open MulAction Subgroup

theorem exists_involution
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (x : X)
    (hK : Nat.card (toPermHom Q (orbit Q x)).ker = 2)
    (g : normalizer (Q : Set G))
    (hstable : ∀ y : X, g.val • y ∈ orbit Q x ↔ y ∈ orbit Q x) :
    ∃ z : Q, z ≠ 1 ∧ z ^ 2 = 1 ∧
      (∀ y ∈ orbit Q x, z • y = y) ∧ g.val*z.val = z.val*g.val := by
  let f := toPermHom Q (orbit Q x)
  let K := f.ker
  obtain ⟨z,hzne,hunique⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hK
  have hzne' : z.val ≠ 1 := fun he => hzne (Subtype.ext he)
  have hfix (y : X) (hy : y ∈ orbit Q x) : z.val • y = y := by
    exact congrArg Subtype.val (DFunLike.congr_fun z.property (⟨y,hy⟩ : orbit Q x))
  let e : MulAut Q := Q.normalizerMonoidHom g
  have heK : e z.val ∈ K := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    change (g.val*z.val.val*g.val⁻¹) • y.val = y.val
    have hy : g.val⁻¹ • y.val ∈ orbit Q x :=
      (hstable (g.val⁻¹ • y.val)).mp (by simpa only [smul_inv_smul] using y.property)
    have hf : z.val.val • (g.val⁻¹ • y.val) = g.val⁻¹ • y.val := hfix _ hy
    rw [mul_smul,mul_smul,hf,smul_inv_smul]
  have hen : (⟨e z.val,heK⟩ : K) ≠ 1 := by
    intro he
    apply hzne'
    exact e.injective ((congrArg Subtype.val he).trans (map_one e).symm)
  have heq : e z.val = z.val := congrArg Subtype.val (hunique _ hen)
  have hcomm : g.val*z.val.val = z.val.val*g.val := by
    have he := congrArg Subtype.val heq
    change g.val*z.val.val*g.val⁻¹ = z.val.val at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  refine ⟨z.val,hzne',?_,hfix,hcomm⟩
  have hz2 : z ^ 2 = 1 := by rw [←hK]; exact pow_card_eq_one' (x := z)
  exact congrArg Subtype.val hz2

end FiveTransitive.Degree52TwoOddKernel

end CFSG
