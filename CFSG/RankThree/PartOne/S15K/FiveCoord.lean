module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.U5K.Pkg.Fixed
public import CFSG.RankThree.PartOne.U5K.Pkg.Rel

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.U5K.Pkg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} {c : E}

@[expose] noncomputable def fiveT (M : Model p E c) (a b : Fin 5) : MulAut E :=
  ((M.ψ.symm (Equiv.swap a b) : ↥(reflectionGroup p E)) : MulAut E)

theorem fiveT_mem (M : Model p E c) {a b : Fin 5} (hab : a ≠ b) :
    fiveT M a b ∈ reflectionSet p E := by
  obtain ⟨t, ht, hψ⟩ := M.surj_swap (σ := Equiv.swap a b) ⟨a, b, hab, rfl⟩
  have h : M.ψ.symm (Equiv.swap a b) = ⟨t, Subgroup.subset_closure ht⟩ := by
    rw [← hψ]
    exact M.ψ.symm_apply_apply _
  have : fiveT M a b = t := by
    unfold fiveT
    rw [h]
  rw [this]
  exact ht

theorem exists_fiveT_of_mem (M : Model p E c) {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    ∃ a b : Fin 5, a ≠ b ∧ fiveT M a b = t := by
  obtain ⟨a, b, hab, hψ⟩ := M.swap_of_mem ht
  refine ⟨a, b, hab, ?_⟩
  have h : M.ψ.symm (Equiv.swap a b) = ⟨t, Subgroup.subset_closure ht⟩ := by
    rw [← hψ]
    exact M.ψ.symm_apply_apply _
  unfold fiveT
  rw [h]

theorem fiveT_apply_v (M : Model p E c) (a b i : Fin 5) :
    fiveT M a b (M.v i) = M.v (Equiv.swap a b i) := by
  have := M.equivariant (M.ψ.symm (Equiv.swap a b)) i
  rw [MulEquiv.apply_symm_apply] at this
  exact this

theorem five_v_ne (M : Model p E c) {i j : Fin 5} (hij : i ≠ j) : M.v i ≠ M.v j := by
  have : Fact p.Prime := ⟨M.prime⟩
  have := M.elem
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E M.card
  intro h
  refine M.u_ne f hij ?_
  have h1 : Multiplicative.ofAdd (M.u f i) = Multiplicative.ofAdd (M.u f j) := by
    apply f.injective
    rw [M.f_ofAdd_u f i, M.f_ofAdd_u f j, h]
  have h2 : M.u f i = M.u f j := Multiplicative.ofAdd.injective h1
  rw [h2]
  exact sub_self _

theorem fiveT_mul_orderOf (M : Model p E c) {a b l : Fin 5} (hab : a ≠ b) (hbl : b ≠ l)
    (hal : a ≠ l) : orderOf (fiveT M a b * fiveT M b l) = 3 := by
  have h1 : fiveT M a b * fiveT M b l =
      ((M.ψ.symm (Equiv.swap a b * Equiv.swap b l) : ↥(reflectionGroup p E)) : MulAut E) := by
    unfold fiveT
    rw [map_mul, Subgroup.coe_mul]
  have h3 : (Equiv.swap a b * Equiv.swap b l).IsThreeCycle := by
    rw [Equiv.swap_comm a b]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab.symm hbl hal
  rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact h3.orderOf

theorem fiveT_fix_prod (M : Model p E c) (a b : Fin 5) :
    fiveT M a b (M.v a * M.v b) = M.v a * M.v b := by
  have hcomm : ∀ x y : E, x * y = y * x := fun x y => M.elem.is_comm.comm x y
  rw [map_mul, fiveT_apply_v, fiveT_apply_v, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact hcomm _ _

theorem fiveFixed_ne (M : Model p E c) {a b l : Fin 5} (hab : a ≠ b) (hbl : b ≠ l) (hal : a ≠ l) :
    autFixed E (fiveT M a b) ≠ autFixed E (fiveT M b l) := by
  intro h
  have hmem : M.v a * M.v b ∈ autFixed E (fiveT M a b) := fiveT_fix_prod M a b
  rw [h] at hmem
  have h2 : fiveT M b l (M.v a * M.v b) = M.v a * M.v b := hmem
  rw [map_mul, fiveT_apply_v, fiveT_apply_v, Equiv.swap_apply_of_ne_of_ne hab hal,
    Equiv.swap_apply_left] at h2
  exact five_v_ne M hbl.symm (mul_left_cancel h2)

theorem card_fiveFixed_inf (M : Model p E c) {a b l : Fin 5} (hab : a ≠ b) (hbl : b ≠ l)
    (hal : a ≠ l) :
    Nat.card ↥(autFixed E (fiveT M a b) ⊓ autFixed E (fiveT M b l)) = p ^ 2 := by
  have hp := M.prime
  have hd : RefFacts.ElemData p E :=
    RefFacts.ElemData.of_isElementaryAbelian hp (by have := M.five_le; omega) M.elem
  have ht := (fiveT_mem M hab).1
  have hs := (fiveT_mem M hbl).1
  have h1 : (autFixed E (fiveT M a b)).relIndex ⊤ = p := by
    have := RefFacts.relIndex_inf_fixed hd ht (B := ⊤) le_top
    rwa [top_inf_eq] at this
  have h2 : (autFixed E (fiveT M b l)).relIndex ⊤ = p := by
    have := RefFacts.relIndex_inf_fixed hd hs (B := ⊤) le_top
    rwa [top_inf_eq] at this
  have h3 := RefFacts.relIndex_inf_inf_of_ne hd (B := ⊤) le_top le_top h1 h2
    (fiveFixed_ne M hab hbl hal)
  rw [Subgroup.relIndex_top_right] at h3
  have h4 := Subgroup.card_mul_index (autFixed E (fiveT M a b) ⊓ autFixed E (fiveT M b l))
  rw [h3, M.card] at h4
  have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
  have h5 : Nat.card ↥(autFixed E (fiveT M a b) ⊓ autFixed E (fiveT M b l)) * p ^ 2 =
      p ^ 2 * p ^ 2 := by
    rw [h4]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

theorem card_fiveFixedInG_inf (M : Model p E c) {a b l : Fin 5} (hab : a ≠ b) (hbl : b ≠ l)
    (hal : a ≠ l) :
    Nat.card ↥(autFixedInG E (fiveT M a b) ⊓ autFixedInG E (fiveT M b l)) = p ^ 2 := by
  have h : autFixedInG E (fiveT M a b) ⊓ autFixedInG E (fiveT M b l) =
      (autFixed E (fiveT M a b) ⊓ autFixed E (fiveT M b l)).map E.subtype := by
    unfold autFixedInG
    exact (Subgroup.map_inf _ _ E.subtype E.subtype_injective).symm
  rw [h, Subgroup.card_map_of_injective E.subtype_injective]
  exact card_fiveFixed_inf M hab hbl hal

end CFSG.RankThree.PartOne.S15K
