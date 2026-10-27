
module

public import CFSG.Sporadic.Th.KernelCentralizerBase1

public import CFSG.Sporadic.Th.KernelCoset
public import CFSG.GroupTheory.FixedPointCount
public import CFSG.Sporadic.Th.Max3.AllConj
public import CFSG.Sporadic.Th.Max3.Quotient
public import CFSG.Sporadic.ThSchreier.AutAssembly
public import Certificates.Kernel.ThCent.Leaves
public import Certificates.Certificate10088Base
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.Th.Max3 TauCeti Pointwise MulAction

variable (h : KernelFacts)
include h

theorem isConj_gen_zero :
    ∀ u : P, orderOf u = 2 → IsConj (gen 0) u := by
  obtain ⟨e, -, h2⟩ := exists_equiv h
  have hJ := all_involutions_conjugate_of_card (card_J_eq h)
  have ha : orderOf (e (gen 0)) = 2 := by
    refine orderOf_eq_prime h2 fun h1 => gen_zero_ne_one h ?_
    exact e.injective (h1.trans (map_one e).symm)
  intro u hu
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hc : IsConj (e (gen 0)) (e u) := (hJ _ ha).symm.trans (hJ _ hu')
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
  simp [hc]

theorem card_centralizer_le :
    Nat.card (Subgroup.centralizer ({gen 0} : Set P)) ≤ 92897280 := by
  have := h.finite
  obtain ⟨v, -, -, -, -, -, -, hinv, -⟩ := h.dce (card_P_eq h)
  obtain ⟨-, hKc⟩ := (isPreprimitive_Om h).2
  have hf := CFSG.GroupAction.card_fix_mul_card_stabilizer (G := P) (X := Om) (pt 1) (gen 0)
  rw [MulAction.stabilizer_quotient, hKc] at hf
  have hconj : 69615 ≤ Nat.card {k : P // k ∈ K ∧ IsConj (gen 0) k} := by
    refine hinv.trans (Nat.card_le_card_of_injective
      (fun k => ⟨k.1, k.2.1, isConj_gen_zero h _ k.2.2⟩) ?_)
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext hxy
  have hfix := card_fix_le h
  have h1 : Nat.card (Subgroup.centralizer ({gen 0} : Set P)) * 69615 ≤ 10200 * 634023936 := by
    calc Nat.card (Subgroup.centralizer ({gen 0} : Set P)) * 69615
        ≤ Nat.card (Subgroup.centralizer ({gen 0} : Set P)) *
          Nat.card {k : P // k ∈ K ∧ IsConj (gen 0) k} := Nat.mul_le_mul_left _ hconj
      _ = Nat.card {p : Om // gen 0 • p = p} * 634023936 := hf.symm
      _ ≤ 10200 * 634023936 := Nat.mul_le_mul_right _ hfix
  exact Nat.le_of_mul_le_mul_right (h1.trans (by norm_num)) (by norm_num : 0 < 69615)

theorem centralizer_a_eq_M :
    Subgroup.centralizer ({a} : Set J) = M := by
  obtain ⟨e, -, h2⟩ := exists_equiv h
  have hle : M ≤ Subgroup.centralizer ({a} : Set J) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff, ← z_eq_a]
    exact ((commute_z_of_mem_M hm).symm).eq
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_M]
  have ha : orderOf (e (gen 0)) = 2 := by
    refine orderOf_eq_prime h2 fun h1 => gen_zero_ne_one h ?_
    exact e.injective (h1.trans (map_one e).symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 (all_involutions_conjugate_of_card (card_J_eq h) _ ha)
  have e1 : Nat.card (Subgroup.centralizer ({a} : Set J)) =
      Nat.card (Subgroup.centralizer ({e (gen 0)} : Set J)) := by
    have hinj : Function.Injective (MulAut.conj c).toMonoidHom := by
      intro x y hxy
      have hxy' : c * x * c⁻¹ = c * y * c⁻¹ := hxy
      simpa using hxy'
    rw [← hc, ← CFSG.Sporadic.ThSchreier.centralizer_map_conj c a]
    exact (Subgroup.card_map_of_injective hinj).symm
  have e2 : Nat.card (Subgroup.centralizer ({e (gen 0)} : Set J)) =
      Nat.card (Subgroup.centralizer ({gen 0} : Set P)) := by
    have hmem : ∀ x : J, x ∈ Subgroup.centralizer ({e (gen 0)} : Set J) ↔
        e.symm x ∈ Subgroup.centralizer ({gen 0} : Set P) := by
      intro x
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hx
      · intro hx
        have := congrArg e hx
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv hmem)
  rw [e1, e2]
  exact card_centralizer_le h

end CFSG.Sporadic.Th.Kernel
