module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxStepC
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenPair
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative CFSG.ComponentClassification
open scoped commutatorElement

variable {F : Type} [Field F] {f m ε p : ℕ} {h : UnitaryFieldData 2 f F}

@[expose] noncomputable def weightPairBlock
    (τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε)
    (E : Set (Multiplicative (Fin m → ZMod p))) (a : HypIndex m ε) : Subgroup (hypSU h m ε) :=
  Subgroup.centralizer (τ '' E) ⊓ hypBlock h (weightClass E a ∪ weightClassPartner E a)

theorem weightPairBlock_subnormal
    (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} (a : HypIndex m ε) :
    CFSG.Assembly.IsSubnormal (weightPairBlock (h := h) τ E a)
      (Subgroup.centralizer (τ '' E)) :=
  CFSG.Assembly.IsSubnormal.step inf_le_left
    (normal_hypBlock_inf_centralizer (h := h) hp hζ hτ
      (isWeightClassUnion_weightClass_union_partner E a))
    (CFSG.Assembly.IsSubnormal.refl _)

theorem exists_diag_distinguishing
    (hp : p.Prime) (hp2 : p ≠ 2) (hε : ε ≤ 1) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hζb : h.bar ζ = ζ)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {a b : HypIndex m ε} (hab : a ≠ b)
    (hsep : ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → splitWeight a t = splitWeight b t) :
    ∃ g : hypSU h m ε, g ∈ weightPairBlock (h := h) τ E a ∧
      (∀ x y : HypIndex m ε, x ≠ y →
        (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
          Matrix (HypIndex m ε) (HypIndex m ε) F) x y = 0) ∧
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) a a ≠
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) b b := by
  classical
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0]; simp)
  have hcne : c ≠ c⁻¹ := ne_inv_of_bar_ne (h := h) hc
  have hcne' : (h.bar c)⁻¹ ≠ c⁻¹ := inv_bar_ne_inv (h := h) hc
  have hcne'' : (h.bar c)⁻¹ ≠ h.bar c := (ne_inv_of_bar_ne_bar (h := h) hc).symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζinv : ζ ≠ ζ⁻¹ := fun h' => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    ((hζ.pow_eq_one_iff_dvd 2).mp (by rw [pow_two]; nth_rewrite 2 [h']; exact mul_inv_cancel₀ hζ0)))
  have hζinv1 : ζ⁻¹ ≠ 1 := inv_ne_one.mpr hζ1
  have hζ1inv : (1 : F) ≠ ζ⁻¹ := (inv_ne_one.mpr hζ1).symm
  rcases a with i | k | i <;> rcases b with j | l | j
  ·
    have hij : i ≠ j := fun hh => hab (by rw [hh])
    obtain ⟨g, hg⟩ := exists_diagTwo (h := h) (ε := ε) i j hij hc0
    refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
    · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inl i) ∪
        weightClassPartner E (.inl i)) ?_ hg
      intro x hx
      exact diagTwo_eq_one_of_not_mem (h := h) (P := weightClass E (.inl i) ∪
        weightClassPartner E (.inl i))
        (Or.inl fun t ht => by simp [splitWeight_inl]) (Or.inl fun t ht => by simpa [splitWeight_inl, splitWeight_inr] using (hsep t ht).symm)
        (Or.inr fun t ht => by simp [splitWeight_inl, splitWeight_inr]) (Or.inr fun t ht => (congrArg Neg.neg (hsep t ht)).symm) hx
    · intro x y hxy
      rw [hg]
      exact Matrix.diagonal_apply_ne _ hxy
    · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagTwo_inl_self,
        diagTwo_inl_ne hij]
      exact hcne
  ·
    obtain ⟨g, hg⟩ := exists_diagOne (h := h) (ε := ε) i hζ0 hζb
    refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
    · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inl i) ∪
        weightClassPartner E (.inl i)) ?_ hg
      intro x hx
      exact diagOne_eq_one_of_not_mem (P := weightClass E (.inl i) ∪
        weightClassPartner E (.inl i)) (Or.inl fun t ht => by simp [splitWeight_inl]) (Or.inr fun t ht => by simp [splitWeight_inl]) hx
    · intro x y hxy
      rw [hg]
      exact Matrix.diagonal_apply_ne _ hxy
    · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagOne_inl_self,
        diagOne_z_apply]
      exact hζ1
  ·
    by_cases hij : i = j
    · subst hij
      obtain ⟨g, hg⟩ := exists_diagOne (h := h) (ε := ε) i hζ0 hζb
      refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
      · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inl i) ∪
          weightClassPartner E (.inl i)) ?_ hg
        intro x hx
        exact diagOne_eq_one_of_not_mem (P := weightClass E (.inl i) ∪
          weightClassPartner E (.inl i)) (Or.inl fun t ht => by simp [splitWeight_inl]) (Or.inr fun t ht => by simp [splitWeight_inl]) hx
      · intro x y hxy
        rw [hg]
        exact Matrix.diagonal_apply_ne _ hxy
      · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagOne_inl_self,
          diagOne_inr_self]
        exact hζinv
    · obtain ⟨g, hg⟩ := exists_diagTwo (h := h) (ε := ε) i j hij hc0
      refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
      · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inl i) ∪
          weightClassPartner E (.inl i)) ?_ hg
        intro x hx
        exact diagTwo_eq_one_of_not_mem (h := h) (P := weightClass E (.inl i) ∪
          weightClassPartner E (.inl i))
          (Or.inl fun t ht => by simp [splitWeight_inl])
          (Or.inr fun t ht => by
            have h := congrArg Neg.neg (hsep t ht)
            simp only [splitWeight_inl, splitWeight_inr, neg_neg] at h ⊢
            exact h.symm)
          (Or.inr fun t ht => by simp [splitWeight_inl, splitWeight_inr])
          (Or.inl fun t ht => by simpa [splitWeight_inl, splitWeight_inr] using (hsep t ht).symm) hx
      · intro x y hxy
        rw [hg]
        exact Matrix.diagonal_apply_ne _ hxy
      · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagTwo_inl_self,
          diagTwo_inr_ne hij]
        exact hc.symm
  ·
    obtain ⟨g, hg⟩ := exists_diagOne (h := h) (ε := ε) j hζ0 hζb
    refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
    · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inr (.inl k)) ∪
        weightClassPartner E (.inr (.inl k))) ?_ hg
      intro x hx
      exact diagOne_eq_one_of_not_mem (P := weightClass E (.inr (.inl k)) ∪
        weightClassPartner E (.inr (.inl k)))
        (Or.inl fun t ht => by
          have h := hsep t ht
          simp only [splitWeight_z, splitWeight_inl] at h
          simp only [splitWeight_z, splitWeight_inl]
          exact h.symm)
        (Or.inr fun t ht => by
          have h := hsep t ht
          simp only [splitWeight_z, splitWeight_inl] at h
          simp only [splitWeight_z, splitWeight_inr]
          simpa using (congrArg Neg.neg h).symm) hx
    · intro x y hxy
      rw [hg]
      exact Matrix.diagonal_apply_ne _ hxy
    · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagOne_z_apply,
        diagOne_inl_self]
      exact hζ1.symm
  ·
    have : Subsingleton (Fin ε) := Fin.subsingleton_iff_le_one.mpr hε
    exact absurd (by rw [Subsingleton.elim k l]) hab
  ·
    obtain ⟨g, hg⟩ := exists_diagOne (h := h) (ε := ε) j hζ0 hζb
    refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
    · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inr (.inl k)) ∪
        weightClassPartner E (.inr (.inl k))) ?_ hg
      intro x hx
      exact diagOne_eq_one_of_not_mem (P := weightClass E (.inr (.inl k)) ∪
        weightClassPartner E (.inr (.inl k)))
        (Or.inl fun t ht => by
          have h := hsep t ht
          simp only [splitWeight_z, splitWeight_inr] at h
          simp only [splitWeight_z, splitWeight_inl]
          exact neg_eq_zero.mp h.symm)
        (Or.inr fun t ht => by
          have h := hsep t ht
          simp only [splitWeight_z, splitWeight_inr] at h
          simp only [splitWeight_z, splitWeight_inr]
          simpa using h.symm) hx
    · intro x y hxy
      rw [hg]
      exact Matrix.diagonal_apply_ne _ hxy
    · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagOne_z_apply,
        diagOne_inr_self]
      exact hζ1inv
  ·
    by_cases hij : i = j
    · subst hij
      obtain ⟨g, hg⟩ := exists_diagOne (h := h) (ε := ε) i hζ0 hζb
      refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
      · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inr (.inr i)) ∪
          weightClassPartner E (.inr (.inr i))) ?_ hg
        intro x hx
        exact diagOne_eq_one_of_not_mem (P := weightClass E (.inr (.inr i)) ∪
          weightClassPartner E (.inr (.inr i))) (Or.inr fun t ht => by simp [splitWeight_inl, splitWeight_inr])
          (Or.inl fun t ht => by simp [splitWeight_inr]) hx
      · intro x y hxy
        rw [hg]
        exact Matrix.diagonal_apply_ne _ hxy
      · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagOne_inr_self,
          diagOne_inl_self]
        exact hζinv.symm
    · obtain ⟨g, hg⟩ := exists_diagTwo (h := h) (ε := ε) i j hij hc0
      refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
      · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inr (.inr i)) ∪
          weightClassPartner E (.inr (.inr i))) ?_ hg
        intro x hx
        exact diagTwo_eq_one_of_not_mem (h := h) (P := weightClass E (.inr (.inr i)) ∪
          weightClassPartner E (.inr (.inr i)))
          (Or.inr fun t ht => by simp [splitWeight_inl, splitWeight_inr])
          (Or.inl fun t ht => by simpa [splitWeight_inl, splitWeight_inr] using (hsep t ht).symm)
          (Or.inl fun t ht => by simp [splitWeight_inr])
          (Or.inr fun t ht => by
            have h := congrArg Neg.neg (hsep t ht)
            simp only [splitWeight_inl, splitWeight_inr, neg_neg] at h ⊢
            exact h.symm) hx
      · intro x y hxy
        rw [hg]
        exact Matrix.diagonal_apply_ne _ hxy
      · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagTwo_inr_self,
          diagTwo_inl_ne hij]
        exact hcne'
  ·
    obtain ⟨g, hg⟩ := exists_diagOne (h := h) (ε := ε) i hζ0 hζb
    refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
    · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inr (.inr i)) ∪
        weightClassPartner E (.inr (.inr i))) ?_ hg
      intro x hx
      exact diagOne_eq_one_of_not_mem (P := weightClass E (.inr (.inr i)) ∪
        weightClassPartner E (.inr (.inr i)))
        (Or.inr fun t ht => by simp [splitWeight_inr]) (Or.inl fun t ht => by simp [splitWeight_inr]) hx
    · intro x y hxy
      rw [hg]
      exact Matrix.diagonal_apply_ne _ hxy
    · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagOne_inr_self,
        diagOne_z_apply]
      exact hζinv1
  ·
    have hij : i ≠ j := fun hh => hab (by rw [hh])
    obtain ⟨g, hg⟩ := exists_diagTwo (h := h) (ε := ε) i j hij hc0
    refine ⟨g, ⟨mem_centralizer_of_diagonal (h := h) (ζ := ζ) hτ hg, ?_⟩, ?_, ?_⟩
    · refine mem_hypBlock_of_diagonal (h := h) (P := weightClass E (.inr (.inr i)) ∪
        weightClassPartner E (.inr (.inr i))) ?_ hg
      intro x hx
      exact diagTwo_eq_one_of_not_mem (h := h) (P := weightClass E (.inr (.inr i)) ∪
        weightClassPartner E (.inr (.inr i)))
        (Or.inr fun t ht => by simp [splitWeight_inl, splitWeight_inr])
        (Or.inr fun t ht => by simpa [splitWeight_inl, splitWeight_inr] using (neg_injective (hsep t ht)).symm)
        (Or.inl fun t ht => by simp [splitWeight_inr])
        (Or.inl fun t ht => by simpa [splitWeight_inl, splitWeight_inr] using (hsep t ht).symm) hx
    · intro x y hxy
      rw [hg]
      exact Matrix.diagonal_apply_ne _ hxy
    · rw [hg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, diagTwo_inr_self,
        diagTwo_inr_ne hij]
      exact hcne''


theorem exists_le_weightPairBlock_of_isComponentOf
    (hp : p.Prime) (hp2 : p ≠ 2) (hε : ε ≤ 1) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (hζb : h.bar ζ = ζ)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {J : Subgroup (hypSU h m ε)}
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer (τ '' E))) :
    ∃ a : HypIndex m ε, J ≤ weightPairBlock (h := h) τ E a := by
  classical
  by_cases hex : ∃ a : HypIndex m ε, J ≤ weightPairBlock (h := h) τ E a
  · exact hex
  exfalso
  push Not at hex
  have hdiag : ∀ u ∈ J, ∀ a b : HypIndex m ε, a ≠ b →
      (((u : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0 := by
    intro u hu a b hab
    by_cases hsep : ∃ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E ∧
        splitWeight a t ≠ splitWeight b t
    · obtain ⟨t, ht, hne⟩ := hsep
      exact mem_centralizer_apply_eq_zero_of_splitWeight_ne (h := h) hp hζ hτ (hJ.1 hu)
        (a := a) (b := b) ⟨t, ht, hne⟩
    · push Not at hsep
      obtain ⟨g, hgN, hgoff, hgne⟩ := exists_diag_distinguishing (h := h) hp hp2 hε hζ hζb hτ
        (E := E) hab hsep
      have hcommJN : ⁅J, weightPairBlock (h := h) τ E a⁆ = ⊥ := by
        rcases isComponentOf_le_or_commutator_eq_bot (G := hypSU h m ε) hJ
          (weightPairBlock_subnormal (h := h) hp hζ hτ a) with h | h
        · exact absurd h (hex a)
        · exact h
      have hcommut : ⁅u, g⁆ = 1 := by
        have hmem : ⁅u, g⁆ ∈ ⁅J, weightPairBlock (h := h) τ E a⁆ :=
          Subgroup.commutator_mem_commutator hu hgN
        rw [hcommJN] at hmem
        simpa using hmem
      have hmul : u * g = g * u := commutatorElement_eq_one_iff_mul_comm.mp hcommut
      have hmulM : ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) *
            ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) =
          ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) *
            ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) := by
        have h := congrArg (fun x : hypSU h m ε =>
          (((x : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F))) hmul
        simpa [Subgroup.coe_mul, Units.val_mul] using h
      have hentry : ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) a b *
            ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) b b =
          ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) a a *
            ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) a b := by
        have hent := congrFun (congrFun hmulM a) b
        rw [Matrix.mul_apply, Matrix.mul_apply] at hent
        have h1 : (∑ x, ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) a x *
              ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
                Matrix (HypIndex m ε) (HypIndex m ε) F)) x b) =
            ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) a b *
              ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
                Matrix (HypIndex m ε) (HypIndex m ε) F)) b b := by
          rw [Finset.sum_eq_single b]
          · intro x _ hxb
            rw [hgoff x b hxb, mul_zero]
          · intro hb
            exact absurd (Finset.mem_univ b) hb
        have h2 : (∑ x, ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) a x *
              ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
                Matrix (HypIndex m ε) (HypIndex m ε) F)) x b) =
            ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) a a *
              ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
                Matrix (HypIndex m ε) (HypIndex m ε) F)) a b := by
          rw [Finset.sum_eq_single a]
          · intro x _ hxa
            rw [hgoff a x (Ne.symm hxa), zero_mul]
          · intro ha
            exact absurd (Finset.mem_univ a) ha
        rw [h1, h2] at hent
        exact hent
      by_contra h0
      have h2 : ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) a b *
            ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) b b =
          ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) a b *
            ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
              Matrix (HypIndex m ε) (HypIndex m ε) F)) a a := by
        rw [hentry, mul_comm]
      have hba : ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) b b =
          ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) a a :=
        mul_left_cancel₀ h0 h2
      exact hgne (by
        rw [hba])
  have hcomm : ∀ u ∈ J, ∀ v ∈ J, u * v = v * u := fun u hu v hv =>
    mul_comm_of_offDiag_eq_zero (fun a b hab => hdiag u hu a b hab)
      (fun a b hab => hdiag v hv a b hab)
  exact LinSemisimple.false_of_isQuasisimple_of_commute hJ.2.2 hcomm

end CFSG.StandardType.SuSplitRootGen
