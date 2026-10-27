module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki

variable {f n : ℕ}

@[expose] noncomputable def l2WreathBase (f n : ℕ) : Subgroup (L2Wreath f n) :=
  (SemidirectProduct.inl : (Fin n → PSL2Model f) →* L2Wreath f n).range

theorem psl2Model_nontrivial {f : ℕ} (hf : 2 ≤ f) : Nontrivial (PSL2Model f) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsBenderGroup (PSL2Model f) := IsBenderGroup.isPSL2 f hf (MulEquiv.refl _)
  haveI : IsSimpleGroup (PSL2Model f) := IsBenderGroup.isSimpleGroup hB
  infer_instance

def coordZero (f n : ℕ) [NeZero n] : Subgroup (Fin n → PSL2Model f) :=
  { carrier := {x | ∀ j, j ≠ 0 → x j = 1}
    one_mem' := by intro j hj; rfl
    mul_mem' := by
      intro x y hx hy j hj
      rw [Pi.mul_apply, hx j hj, hy j hj, mul_one]
    inv_mem' := by
      intro x hx j hj
      rw [Pi.inv_apply, hx j hj, inv_one] }

theorem coordZero_normal (f n : ℕ) [NeZero n] : (coordZero f n).Normal := by
  refine ⟨fun x hx g => ?_⟩
  intro j hj
  rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, hx j hj, mul_one, mul_inv_cancel]

theorem coordZero_ne_bot {f n : ℕ} [NeZero n] (hf : 2 ≤ f) : coordZero f n ≠ ⊥ := by
  intro h
  obtain ⟨l, hl⟩ := exists_ne (1 : PSL2Model f)
  let x : Fin n → PSL2Model f := Pi.mulSingle (M := fun _ => PSL2Model f) 0 l
  have hx : x ∈ coordZero f n := by
    intro j hj
    exact Pi.mulSingle_eq_of_ne (M := fun _ => PSL2Model f) hj l
  rw [h] at hx
  have hx1 : x = 1 := by simpa using hx
  have hx0 : x 0 = l := Pi.mulSingle_eq_same (M := fun _ => PSL2Model f) 0 l
  rw [hx1] at hx0
  exact hl hx0.symm

theorem coordZero_ne_top {f n : ℕ} [NeZero n] (hf : 2 ≤ f) (hn : 2 ≤ n) :
    coordZero f n ≠ ⊤ := by
  intro h
  obtain ⟨l, hl⟩ := exists_ne (1 : PSL2Model f)
  have h0 : (0 : Fin n) ≠ 1 := by
    intro h01
    have h := congrArg Fin.val h01
    simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)] at h
    omega
  let x : Fin n → PSL2Model f := Pi.mulSingle (M := fun _ => PSL2Model f) 1 l
  have hx1 : x 1 = l := Pi.mulSingle_eq_same (M := fun _ => PSL2Model f) 1 l
  have hx : x ∉ coordZero f n := by
    intro hmem
    have h1 : x 1 = 1 := hmem 1 (by omega)
    rw [hx1] at h1
    exact hl h1
  rw [h] at hx
  exact hx (Subgroup.mem_top x)

theorem l2WreathBase_not_isSimpleGroup (hf : 2 ≤ f) (hn : 2 ≤ n) :
    ¬ IsSimpleGroup (l2WreathBase f n) := by
  haveI : NeZero n := ⟨by omega⟩
  have hinl : Function.Injective (SemidirectProduct.inl : (Fin n → PSL2Model f) →* L2Wreath f n) :=
    SemidirectProduct.inl_injective
  have hmap : (⊤ : Subgroup (Fin n → PSL2Model f)).map
      (SemidirectProduct.inl : (Fin n → PSL2Model f) →* L2Wreath f n) = l2WreathBase f n := by
    rw [Subgroup.map_top]
    rfl
  have hequiv : (Fin n → PSL2Model f) ≃* l2WreathBase f n := by
    have h := Subgroup.equivMapOfInjective (⊤ : Subgroup (Fin n → PSL2Model f))
      (SemidirectProduct.inl : (Fin n → PSL2Model f) →* L2Wreath f n) hinl
    rw [hmap] at h
    exact Subgroup.topEquiv.symm.trans h
  rw [← MulEquiv.isSimpleGroup_congr hequiv]
  intro hsimple
  have hP : (coordZero f n).Normal := coordZero_normal f n
  have hne := coordZero_ne_bot (f := f) (n := n) hf
  have htop := coordZero_ne_top (f := f) (n := n) hf hn
  rcases hsimple.eq_bot_or_eq_top_of_normal (coordZero f n) with h | h
  · exact hne h
  · exact htop h

end CFSG.OddTranspositions
