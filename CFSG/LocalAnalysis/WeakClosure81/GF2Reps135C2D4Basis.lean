module

public import CFSG.Quasithin.Background.SmithB42D4Main

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Chevalley

private lemma w183_zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have hle : c.val ≤ 1 := by
    have := ZMod.val_lt c
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
  · left
    rw [← ZMod.natCast_zmod_val c, h]
    norm_num
  · right
    rw [← ZMod.natCast_zmod_val c, h]
    norm_num

theorem exists_fixedField_basis {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    {f : ℕ} (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f) :
    ∃ b : Fin f → K, (∀ j, σ (b j) = b j) ∧ (∀ j, b j ≠ 0) ∧
      ∀ e : K, σ e = e → e ∈ AddSubgroup.closure (Set.range b) := by
  let k := trialityFixedField K σ.toRingHom
  haveI : CharP k 2 :=
    ((Subfield.subtype k).charP_iff (Subfield.subtype_injective k) 2).2
      (inferInstance : CharP K 2)
  letI : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk' : Nat.card k = 2 ^ f := hk
  have hfin : Module.finrank (ZMod 2) k = f := by
    apply Nat.pow_right_injective (le_refl 2)
    change 2 ^ Module.finrank (ZMod 2) k = 2 ^ f
    rw [← hk', Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  let B : Module.Basis (Fin f) (ZMod 2) k := Module.finBasisOfFinrankEq (ZMod 2) k hfin
  refine ⟨fun j => (B j : K), ?_, ?_, ?_⟩
  · intro j
    have hmem : ((B j : k) : K) ∈ trialityFixedField K σ.toRingHom := (B j).2
    have := (mem_trialityFixedField (K := K) (σ := σ.toRingHom)).1 hmem
    simpa using this
  · intro j h
    exact B.ne_zero j (Subtype.ext (by simpa using h))
  · intro e he
    have hmem : e ∈ trialityFixedField K σ.toRingHom :=
      (mem_trialityFixedField (K := K) (σ := σ.toRingHom)).2 he
    let e' : k := ⟨e, hmem⟩
    have hcoe : e = ∑ j, (((B.repr e' j) • B j : k) : K) := by
      have h : e = Subfield.subtype k (∑ j, B.repr e' j • B j) := by
        rw [B.sum_repr]
        rfl
      rw [map_sum] at h
      exact h
    rw [hcoe]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    rcases w183_zmod_two_eq_zero_or_one (B.repr e' j) with hc | hc
    · rw [hc, zero_smul]
      simpa using AddSubgroup.zero_mem (AddSubgroup.closure (Set.range (fun j => (B j : K))))
    · rw [hc, one_smul]
      exact AddSubgroup.subset_closure (Set.mem_range_self j)

theorem family_mem_of_closure {G A : Type*} [Group G] [AddCommGroup A] (X : A → G)
    (hX : ∀ a c, X (a + c) = X a * X c) (H : Subgroup G) {s : Set A}
    (hs : ∀ a ∈ s, X a ∈ H) {e : A} (he : e ∈ AddSubgroup.closure s) : X e ∈ H := by
  have h0 : X 0 = 1 := by
    have h := hX 0 0
    rw [zero_add] at h
    have h' := congrArg (fun x => (X 0)⁻¹ * x) h
    simpa using h'.symm
  have hneg : ∀ a, X (-a) = (X a)⁻¹ := by
    intro a
    have h := hX a (-a)
    rw [add_neg_cancel, h0] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  refine AddSubgroup.closure_induction (p := fun e _ => X e ∈ H) (fun a ha => hs a ha) ?_ ?_ ?_ he
  · rw [h0]
    exact H.one_mem
  · intro a b _ _ ha hb
    rw [hX a b]
    exact H.mul_mem ha hb
  · intro a _ ha
    rw [hneg a]
    exact H.inv_mem ha

end CFSG.LocalAnalysis.WeakClosure81
