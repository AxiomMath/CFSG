module

public import CFSG.Quasithin.H13.NQCatNGTSwap
public import CFSG.Quasithin.H13.NQCatNGTSL3
public import CFSG.Quasithin.H13.NQCatNGTSp4
public import CFSG.Quasithin.EmptyFaithful.SzN2Sp

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.QuasithinUnique.Setup.X7a

variable {V : Type*} [CommGroup V] [Finite V]

theorem no_swap_sl3 {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {X : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL 3 K) →* ↥X}
    (hT : NatTransfer X U Z (StatedSL 3 K) π)
    {S M₀ M₁ : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S X)
    (hM₀ : S ≤ M₀ ∧ M₀ < X ∧ ∀ M' : Subgroup (MulAut V), M₀ ≤ M' → M' < X → M' = M₀)
    (hM₁ : S ≤ M₁ ∧ M₁ < X ∧ ∀ M' : Subgroup (MulAut V), M₁ ≤ M' → M' < X → M' = M₁)
    (hne : M₀ ≠ M₁) (g : MulAut V) (hgU : U.map g.toMonoidHom = U)
    (hgZ : Z.map g.toMonoidHom = Z) (hg : M₀.map (MulAut.conj g).toMonoidHom = M₁) : False := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set e := specialLinearGroupEquivStatedSL 3 K with he
  have hcoe : ∀ A : Matrix.SpecialLinearGroup (Fin 3) K,
      ((e A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A := fun A => rfl
  have hmem : ∀ (j : Fin 2) (γ : ↥(StatedSL 3 K)), γ ∈ (Q3 K j).map e.toMonoidHom →
      ∃ A ∈ Q3 K j, ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A := by
    rintro j _ ⟨A, hA, rfl⟩
    exact ⟨A, hA, rfl⟩
  refine no_swap_generic hT (U₀ := (LinearFlag.unitriangular 3 K).map
      e.toMonoidHom) ?_ (Q := fun j => (Q3 K j).map e.toMonoidHom) ?_ (Nat.card K) ?_ ?_ hS hM₀
    hM₁ hne g hgU hgZ hg
  · exact B113Lie.isSylowTwoOf_map_top e (SzN2.isSylowTwoOf_unitriangular (by norm_num))
  · exact (SzN2.sl3_residualOvergroupsAt ⟨f, hK⟩).map e
  · refine ⟨(LinearFlag.flagSpace 3 K 1).toAddSubgroup, ?_, ?_, fun γ hγ v hv => ?_⟩
    · intro h0
      have h1 : (Pi.single (0 : Fin 3) (1 : K)) ∈ (LinearFlag.flagSpace 3 K 1).toAddSubgroup :=
        Submodule.subset_span ⟨0, by decide, rfl⟩
      rw [h0, AddSubgroup.mem_bot] at h1
      have := congrFun h1 0
      simp at this
    · have h1 := card_flagSpace (K := K) (i := 1) (by norm_num)
      rw [pow_one] at h1
      exact h1.le
    · obtain ⟨A, hA, hγA⟩ := hmem 0 γ hγ
      rw [hγA]
      exact invariant_flagSpace_one hA hv
  · intro S₁ hS₁ hinv
    have hle := flagSpace_two_le_of_invariant hS₁ fun A hA w hw => by
      have := hinv (e A) ⟨A, hA, rfl⟩ w hw
      rwa [hcoe] at this
    have h2 : Nat.card (LinearFlag.flagSpace 3 K 2) ≤ Nat.card S₁ :=
      Nat.card_mono (Set.toFinite _) hle
    rw [card_flagSpace (by norm_num)] at h2
    have : Nat.card K < Nat.card K ^ 2 := by
      rw [pow_two]
      exact lt_mul_self (by omega)
    omega

theorem no_swap_sp4 {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {X : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSp 2 K) →* ↥X}
    (hT : NatTransfer X U Z (StatedSp 2 K) π)
    {S M₀ M₁ : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S X)
    (hM₀ : S ≤ M₀ ∧ M₀ < X ∧ ∀ M' : Subgroup (MulAut V), M₀ ≤ M' → M' < X → M' = M₀)
    (hM₁ : S ≤ M₁ ∧ M₁ < X ∧ ∀ M' : Subgroup (MulAut V), M₁ ≤ M' → M' < X → M' = M₁)
    (hne : M₀ ≠ M₁) (g : MulAut V) (hgU : U.map g.toMonoidHom = U)
    (hgZ : Z.map g.toMonoidHom = Z) (hg : M₀.map (MulAut.conj g).toMonoidHom = M₁) : False := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine no_swap_generic hT SzN2.isSylowTwoOf_unipotent
    (SzN2.sp4_residualOvergroupsAt ⟨f, hK⟩)
    (Nat.card K) ?_ ?_ hS hM₀ hM₁ hne g hgU hgZ hg
  · refine ⟨(SymplecticFlag.flag 2 K 1).toAddSubgroup, ?_, ?_, fun γ hγ v hv => ?_⟩
    · intro h0
      have h1 : (Pi.single (Sum.inl (0 : Fin 2)) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈
          (SymplecticFlag.flag 2 K 1).toAddSubgroup := by
        change _ ∈ SymplecticFlag.flag 2 K 1
        rw [SymplecticFlag.mem_flag_of_le (by norm_num), SymplecticFlag.mem_isoFlag]
        refine ⟨fun j => by simp, fun j hj => ?_⟩
        have hj0 : j ≠ 0 := by
          intro h
          rw [h] at hj
          simp at hj
        simp [hj0]
      rw [h0, AddSubgroup.mem_bot] at h1
      have := congrFun h1 (Sum.inl 0)
      simp at this
    · have h1 := card_sp_flag (K := K) (i := 1) (by norm_num)
      rw [pow_one] at h1
      exact h1.le
    · exact sp_invariant_flag_one hγ hv
  · intro S₁ hS₁ hinv
    have hle := sp_flag_two_le_of_invariant hS₁ hinv
    have h2 : Nat.card (SymplecticFlag.flag 2 K 2) ≤ Nat.card S₁ :=
      Nat.card_mono (Set.toFinite _) hle
    rw [card_sp_flag (by norm_num)] at h2
    have : Nat.card K < Nat.card K ^ 2 := by
      rw [pow_two]
      exact lt_mul_self (by omega)
    omega

end CFSG.Quasithin.H13.NQCat.NGT
