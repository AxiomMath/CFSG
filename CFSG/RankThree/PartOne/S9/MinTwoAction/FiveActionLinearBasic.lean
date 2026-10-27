module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionDefs
public import CFSG.RankThree.GroupTheory.SteinbergCEExtraspecialMinusModule
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.RankThree.PartOne.S9.QD32.Basic
public import CFSG.RankThree.GroupTheory.SteinbergCESmallBinaryOrbitCounts

public section

namespace CFSG.RankThree.PartOne.FiveAction.Lin

open CFSG CFSG.RankThree.GroupTheory SemidirectProduct
open scoped IsMulCommutative

section Irreducible

variable {K : Type*} [Field K] {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module K W]

theorem isIrreducible_of_forall [Nontrivial W] {ρ : Representation K Γ W}
    (h : ∀ U : Submodule K W, (∀ g : Γ, ∀ w ∈ U, ρ g w ∈ U) → U = ⊥ ∨ U = ⊤) :
    ρ.IsIrreducible := by
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  refine
    { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩
      eq_bot_or_eq_top := fun a => ?_ }
  · have h1 : v ∈ (⊤ : Subrepresentation ρ) := trivial
    rw [← h'] at h1
    exact hv ((Submodule.mem_bot K).1 h1)
  · rcases h a.toSubmodule a.apply_mem_toSubmodule with h' | h'
    · exact Or.inl (Subrepresentation.ext h')
    · exact Or.inr (Subrepresentation.ext h')

theorem rep_eq_neg_one_of_central_involution {ρ : Representation K Γ W} (hρ : ρ.IsIrreducible)
    {c : Γ} (hc : ∀ x : Γ, c * x = x * c) (hc2 : c * c = 1) (hne : ρ c ≠ 1) : ρ c = -1 := by
  have hinv : ∀ g : Γ, ∀ w ∈ Module.End.eigenspace (ρ c) 1,
      ρ g w ∈ Module.End.eigenspace (ρ c) 1 := by
    intro g w hw
    rw [Module.End.mem_eigenspace_iff, one_smul] at hw ⊢
    calc ρ c (ρ g w) = ρ (c * g) w := by rw [map_mul]; rfl
      _ = ρ (g * c) w := by rw [hc g]
      _ = ρ g (ρ c w) := by rw [map_mul]; rfl
      _ = ρ g w := by rw [hw]
  rcases eq_bot_or_eq_top_of_isIrreducible hρ _ hinv with h | h
  · refine LinearMap.ext fun w => ?_
    have hmem : ρ c w + w ∈ Module.End.eigenspace (ρ c) 1 := by
      rw [Module.End.mem_eigenspace_iff, one_smul, map_add]
      have hcc : ρ c (ρ c w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, hc2, map_one]
        rfl
      rw [hcc, add_comm]
    rw [h, Submodule.mem_bot] at hmem
    rw [LinearMap.neg_apply, Module.End.one_apply]
    exact eq_neg_of_add_eq_zero_left hmem
  · exfalso
    apply hne
    refine LinearMap.ext fun w => ?_
    have hw : w ∈ Module.End.eigenspace (ρ c) 1 := by rw [h]; exact Submodule.mem_top
    rwa [Module.End.mem_eigenspace_iff, one_smul] at hw

end Irreducible

theorem two_ne_zero_zmod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1)

section Group

variable {S A : Type*} [Group S] [Group A] {φ : A →* MulAut S}

theorem inr_central {b : A} (hbφ : ∀ s : S, φ b s = s) (hbc : ∀ a : A, a * b = b * a)
    (x : S ⋊[φ] A) : x * inr b = inr b * x := by
  have h1 : (inl x.left : S ⋊[φ] A) * inr b = inr b * inl x.left := by
    have h := inl_aut (φ := φ) b x.left
    rw [hbφ, map_inv] at h
    calc (inl x.left : S ⋊[φ] A) * inr b = (inr b * inl x.left * (inr b)⁻¹) * inr b := by
          rw [← h]
      _ = inr b * inl x.left := by group
  have h2 : (inr x.right : S ⋊[φ] A) * inr b = inr b * inr x.right := by
    rw [← map_mul, ← map_mul, hbc]
  calc x * inr b = (inl x.left * inr x.right) * inr b := by rw [inl_left_mul_inr_right]
    _ = inl x.left * (inr x.right * inr b) := by rw [mul_assoc]
    _ = inl x.left * (inr b * inr x.right) := by rw [h2]
    _ = (inl x.left * inr b) * inr x.right := by rw [mul_assoc]
    _ = (inr b * inl x.left) * inr x.right := by rw [h1]
    _ = inr b * (inl x.left * inr x.right) := by rw [mul_assoc]
    _ = inr b * x := by rw [inl_left_mul_inr_right]

theorem aut_fixes_center_generator {z : S} (hz2 : orderOf z = 2)
    (hz : Subgroup.center S = Subgroup.zpowers z) (α : MulAut S) : α z = z := by
  have hc : α z ∈ Subgroup.center S := QD32Facts.aut_mem_center α (hz ▸ Subgroup.mem_zpowers z)
  rw [hz, SteinbergBY.mem_zpowers_of_orderOf_eq_two hz2] at hc
  rcases hc with h | h
  · exfalso
    have h1 : z = 1 := α.injective (h.trans (map_one α).symm)
    rw [h1, orderOf_one] at hz2
    omega
  · exact h

theorem inl_central {z : S} (hz2 : orderOf z = 2) (hz : Subgroup.center S = Subgroup.zpowers z)
    (x : S ⋊[φ] A) : (inl z : S ⋊[φ] A) * x = x * inl z := by
  have h1 : (inl z : S ⋊[φ] A) * inl x.left = inl x.left * inl z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.1 (hz ▸ Subgroup.mem_zpowers z) x.left).symm
  have h2 : (inl z : S ⋊[φ] A) * inr x.right = inr x.right * inl z := by
    have h := inl_aut (φ := φ) x.right z
    rw [aut_fixes_center_generator hz2 hz] at h
    conv_lhs => rw [h]
    rw [mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  calc inl z * x = inl z * (inl x.left * inr x.right) := by rw [inl_left_mul_inr_right]
    _ = (inl z * inl x.left) * inr x.right := by rw [mul_assoc]
    _ = (inl x.left * inl z) * inr x.right := by rw [h1]
    _ = inl x.left * (inl z * inr x.right) := by rw [mul_assoc]
    _ = inl x.left * (inr x.right * inl z) := by rw [h2]
    _ = (inl x.left * inr x.right) * inl z := by rw [mul_assoc]
    _ = x * inl z := by rw [inl_left_mul_inr_right]

end Group

section Shapes

variable {S A : Type} [Group S] [Finite S] [Group A] {φ : A →* MulAut S}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_fixed_three (hel : IsElementaryAbelian 2 S) (hS : Nat.card S = 16)
    (hφ : Nat.card φ.range = 5)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hK : (2 : K) ≠ 0) (ρ : Representation K (S ⋊[φ] A) W) (hρ : ρ.IsIrreducible)
    (hinj : Function.Injective (ρ.comp inl)) :
    ∃ s : S, s ≠ 1 ∧ 3 ≤ Module.finrank K (Module.End.eigenspace (ρ (inl s)) 1) := by
  have := hel
  let _ : CommGroup S := IsMulCommutative.instCommGroup
  let _ : Module (ZMod 2) (Additive S) := IsElementaryAbelian.isVectorSpace 2
  obtain ⟨-, -, e, he, -, -, -, h5, -⟩ := small_binary_prime_orbit_fixed_space_counts
    (p := 5) (d := 4) (Or.inr ⟨rfl, rfl⟩) (by rw [hS]; norm_num) hφ hirr hK ρ hρ hinj
  obtain ⟨s, hs1, hs2⟩ := Set.nonempty_of_ncard_ne_zero (by rw [(h5 rfl).1]; norm_num)
  exact ⟨s, hs1, by omega⟩

theorem exists_fixed_two_qd32 (e : S ≃* QD32) (hK : (2 : K) ≠ 0)
    (ρ : Representation K (S ⋊[φ] A) W) (hρ : ρ.IsIrreducible)
    (hinj : Function.Injective (ρ.comp inl)) :
    ∃ s : S, s ≠ 1 ∧ 2 ≤ Module.finrank K (Module.End.eigenspace (ρ (inl s)) 1) := by
  obtain ⟨hcardQ, hextQ, -⟩ := SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
  have hext : IsExtraspecialPGroup 2 S :=
    Torsion37.isExtraspecialPGroup_of_mulEquiv e.symm hextQ
  have hcard : Nat.card S = 2 ^ (1 + 2 * 2) := by
    rw [Nat.card_congr e.toEquiv, hcardQ]
    norm_num
  obtain ⟨z, hz2, hz, -, hgen, -⟩ := QD32Facts.exists_data_of_equiv_QD32 e
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  obtain ⟨s, hs2, hsc⟩ : ∃ s : S, s ^ 2 = 1 ∧ s ∉ Subgroup.center S := by
    by_contra hno
    push Not at hno
    have hle : Subgroup.closure {s : S | s ^ 2 = 1} ≤ Subgroup.center S :=
      (Subgroup.closure_le _).mpr fun s hs => hno s hs
    rw [hgen, top_le_iff] at hle
    have h1 := hext.2.2.2
    rw [hle, Subgroup.card_top, hcard] at h1
    omega
  have hs1 : s ≠ 1 := fun h => hsc (h ▸ Subgroup.one_mem _)
  have hs2' : orderOf s = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hs2 hs1
  have hz' : (ρ.comp inl) z = -1 := by
    have hne : ρ (inl z) ≠ 1 := fun h => hz1 (hinj (by
      rw [map_one]
      exact h))
    have hcen := inl_central (φ := φ) (A := A) hz2 hz
    have hmul : (inl z : S ⋊[φ] A) * inl z = 1 := by
      rw [← map_mul, ← pow_two, ← hz2, pow_orderOf_eq_one, map_one]
    exact rep_eq_neg_one_of_central_involution hρ hcen hmul hne
  have : Nontrivial W := nontrivial_of_isIrreducible hρ
  obtain ⟨-, hbound⟩ := extraspecial_two_minus_module_bound hext hcard hz hK (ρ.comp inl) hz'
  obtain ⟨-, h2⟩ := hbound s hsc hs2'
  exact ⟨s, hs1, by simpa using h2⟩

theorem exists_fixed_two (hφ : Nat.card φ.range = 5) (hsh : Shape S A φ) (hK : (2 : K) ≠ 0)
    (ρ : Representation K (S ⋊[φ] A) W) (hρ : ρ.IsIrreducible)
    (hinj : Function.Injective (ρ.comp inl)) :
    ∃ s : S, s ≠ 1 ∧ 2 ≤ Module.finrank K (Module.End.eigenspace (ρ (inl s)) 1) := by
  rcases hsh with ⟨hel, hS, hirr⟩ | ⟨⟨e⟩⟩
  · obtain ⟨s, hs, h3⟩ := exists_fixed_three hel hS hφ hirr hK ρ hρ hinj
    exact ⟨s, hs, by omega⟩
  · exact exists_fixed_two_qd32 e hK ρ hρ hinj

end Shapes

end CFSG.RankThree.PartOne.FiveAction.Lin
