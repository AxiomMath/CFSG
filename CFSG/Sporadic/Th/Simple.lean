
module

public import CFSG.Sporadic.Th.SimpleBase1

public import CFSG.Sporadic.Th.Local

public section

namespace CFSG.Sporadic.Th

open Native Pointwise

section TreeId

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {g₁ g₂ : G} {pl : Table}

end TreeId

section Global

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem mem_H_of_globalTest
    {s i : ℕ} (hi : i < nX)
    (h : globalTest gplT (letters alphaT betaT) (letters alphaT betaInvT) chainT s i = true) :
    (treeElt gplT (lettersG a b) (idx nX (lettersG a b s) i))⁻¹ * lettersG a b s *
      treeElt gplT (lettersG a b) i ∈ H := by
  obtain ⟨k0, k1, hk⟩ := globalTest_spec (nX_ge hC) (rep_ab_letters hC) (rep_ab_letters_inv hC)
    (rep_chain_inv0 hC) (rep_chain_inv1 hC) hi h
  have hr := eq_of_residue hC (r := treeElt chainT.pl0 (lettersG xJ yJ) k0 *
    treeElt chainT.pl1 (lettersG z0J z1J) k1) (by rw [mul_inv_rev]; exact hk)
  rw [hr]
  exact H.mul_mem (treeElt_mem H _ (xy_mem_H) k0) (L_le_H (treeElt_mem L _ z_mem_L k1))

theorem fix_zero_mem_H :
    ∀ g : J, idx nX g 0 = 0 → g ∈ H := by
  intro g hg
  have hT := treeData_J hC
  have hgl := globalChecks_parts hC
  have hmem := hT.stab_le_two_three_id (a_sq hC) (b_cube hC) H (P₁ := ap alphaT) (P₂ := ap betaT)
    (fun k hk => rep_a hC k hk) (fun k hk => rep_b hC k hk) ?_ ?_ g
    (by rw [closure_ab]; exact Subgroup.mem_top g) hg
  · exact hmem
  · intro k hk hreq
    have := mem_H_of_globalTest hC hk ((hgl.1 k hk).1 hreq)
    have ha : lettersG a b 1 = a := by simp [lettersG]
    rw [ha, ← rep_a hC k hk] at this
    exact this
  · intro k hk hreq
    have := mem_H_of_globalTest hC hk ((hgl.1 k hk).2 hreq)
    have hb : lettersG a b 2 = b := by simp [lettersG]
    rw [hb, ← rep_b hC k hk] at this
    exact this

theorem stabilizer_root :
    MulAction.stabilizer J (root hC) = H := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    apply fix_zero_mem_H hC
    have := idx_val g (root hC)
    rw [h] at this
    exact this
  · intro h
    exact smul_eq_of_idx g _ _ (H_fix_zero hC g h)

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J (root hC)) = 634023936 := by
  rw [stabilizer_root hC]
  exact card_H hC

theorem faithful :
    FaithfulSMul J (Fin nX) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := by
    apply eq_one_of_fix hC
    intro j hj
    have hjn : j < nX := lt_of_lt_of_le hj (nX_ge hC)
    rw [idx_mul]
    have h1 := idx_val g ⟨j, hjn⟩
    rw [hgh, ← idx_val] at h1
    rw [show j = (⟨j, hjn⟩ : Fin nX).val from rfl, h1, idx_inv_idx]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem orderOf_a :
    orderOf a = 2 := orderOf_eq_prime (a_sq hC) (a_ne_one hC)

theorem orderOf_b :
    orderOf b = 3 := orderOf_eq_prime (b_cube hC) (b_ne_one hC)

theorem orderOf_ab :
    orderOf (a * b) = 19 := by
  have h19 : (a * b) ^ 19 = 1 := by
    apply eq_one_of_idx_id hC
    intro i hi
    rw [← abPow19_eq (rep_a hC) (rep_b hC) 19 hi]
    exact (globalChecks_parts hC).2 i hi
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact orderOf_eq_prime h19 (ab_ne_one hC)

theorem isSimpleGroup_J :
    IsSimpleGroup J := by
  have := faithful hC
  have := isPreprimitive hC
  have : Finite J := inferInstance
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin nX) ?_ a b closure_ab (root hC) ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin, hC.count]; norm_num
  · rw [orderOf_a hC, orderOf_b hC]; norm_num
  · rw [orderOf_ab hC, card_stabilizer_root hC]; norm_num

theorem isSimpleGroup_Th :
    IsSimpleGroup Blueprint.NativeSporadic.Th :=
  @MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_J hC) thEquivJ

end Global

end CFSG.Sporadic.Th
