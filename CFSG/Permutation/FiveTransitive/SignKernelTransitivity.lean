module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.SignKernelTransitivity

open MulAction

theorem index_ker_eq_two
    {G:Type*} [Group G] (f:G→*ℤˣ) (a:G) (ha:f a = -1) : f.ker.index=2 := by
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨a,?_,?_⟩
  · rw [MonoidHom.mem_ker,ha]
    norm_num
  · intro b
    rcases Int.units_eq_one_or (f b) with hb|hb
    · exact Or.inr (MonoidHom.mem_ker.mpr hb)
    · left
      rw [MonoidHom.mem_ker,map_mul,hb,ha]
      norm_num

private theorem odd_ker_of_sylow_two
    {G:Type*} [Group G] [Finite G] (f:G→*ℤˣ)
    (P:Sylow 2 G) (hP:Nat.card P=2) (a:G) (ha:f a = -1) : Odd (Nat.card f.ker) := by
  have hi := index_ker_eq_two f a ha
  have hcard := (P:Subgroup G).card_mul_index
  have hker := f.ker.index_mul_card
  rw [hP] at hcard
  rw [hi] at hker
  have he:Nat.card f.ker=(P:Subgroup G).index := by omega
  rw [he,Nat.odd_iff]
  have hn := P.not_dvd_index
  omega

theorem pretransitive_ker
    {G Y:Type*} [Group G] [MulAction G Y] [IsPretransitive G Y]
    (f:G→*ℤˣ) (hfix:∀y:Y,∃a:G,a • y=y ∧ f a = -1) : IsPretransitive f.ker Y := by
  constructor
  intro x y
  obtain ⟨g,hg⟩ := exists_smul_eq G x y
  rcases Int.units_eq_one_or (f g) with hfg|hfg
  · exact ⟨⟨g,MonoidHom.mem_ker.mpr hfg⟩,hg⟩
  · obtain ⟨a,hax,hfa⟩ := hfix x
    have hga:g*a∈f.ker := by rw [MonoidHom.mem_ker,map_mul,hfg,hfa]; norm_num
    refine ⟨⟨g*a,hga⟩,?_⟩
    change (g*a) • x=y
    rw [mul_smul,hax,hg]

theorem odd_stabilizer_ker
    {G Y:Type*} [Group G] [Finite G] [MulAction G Y]
    (f:G→*ℤˣ) (y:Y) (P:Sylow 2 (stabilizer G y)) (hP:Nat.card P=2)
    (a:stabilizer G y) (ha:f a.val = -1) : Odd (Nat.card (stabilizer f.ker y)) := by
  let ψ:(stabilizer G y)→*ℤˣ := f.comp (stabilizer G y).subtype
  have hodd:Odd (Nat.card ψ.ker) := odd_ker_of_sylow_two ψ P hP a ha
  let E:ψ.ker ≃* stabilizer f.ker y := {
    toFun := fun q => ⟨⟨q.val.val,q.property⟩,q.val.property⟩
    invFun := fun q => ⟨⟨q.val.val,q.property⟩,q.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  rwa [Nat.card_congr E.toEquiv] at hodd

end FiveTransitive.SignKernelTransitivity

end CFSG
