module

public import CFSG.RankThree.PartOne.CTP.StrongPLinear
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.BorelCoreCenter
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjoint

public section

namespace CFSG.RankThree.PartOne.StrongP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge.Minuscule

section Coefficient

variable {τ : Tag} {K : Type} [Field K]

theorem rootVec_coeff {ε : Fin τ.rank → ℤ} (hε : IsRoot τ ε) (γ : Fin τ.rank → ℤ) :
    rootVec τ K γ (Sum.inr ⟨ε, hε⟩) = if γ = ε then 1 else 0 := by
  classical
  by_cases hγ : IsRoot τ γ
  · rw [rootVec_eq_single_of_isRoot hγ, Finsupp.single_apply]
    by_cases h : γ = ε
    · subst h; simp
    · simp [h]
  · have : γ ≠ ε := fun h => hγ (h ▸ hε)
    simp [rootVec, hγ, this]

theorem hVec_coeff {ε : Fin τ.rank → ℤ} (hε : IsRoot τ ε) (j : Fin τ.rank) :
    hVec τ K j (Sum.inr ⟨ε, hε⟩) = 0 := by
  classical
  rw [hVec, Finsupp.single_apply]
  simp

theorem xOp_rootVec_coeff {i j : Fin τ.rank} (hij : i ≠ j) {ε : Fin τ.rank → ℤ}
    (hroot : IsRoot τ ε) (hε : ε = Pi.single j 1 + Pi.single i 1)
    (hnot : ¬ IsRoot τ (Pi.single j 1 - Pi.single i 1)) (c : K) :
    xOp τ K i c (rootVec τ K (Pi.single j 1)) (Sum.inr ⟨ε, hroot⟩) = c := by
  classical
  subst hε
  have h₁ : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ Pi.single i 1 := fun h => hij (by
    have := congrFun h j
    by_contra hne
    simp [Ne.symm hne] at this)
  have h₂ : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := fun h => by
    have := congrFun h j
    simp [Ne.symm hij] at this
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff (isRoot_single τ j) i h₁ h₂
  have hup : 1 ≤ stringUp τ i (Pi.single j 1) := by
    have := (hint 1).1 (by simpa using hroot)
    exact_mod_cast this.2
  have hdown : stringDown τ i (Pi.single j 1) = 0 := by
    by_contra hne
    apply hnot
    have := (hint (-1)).2 ⟨by omega, by omega⟩
    simpa [sub_eq_add_neg] using this
  rw [xOp_rootVec_of_ne' K i c (isRoot_single τ j) h₁ h₂, hdown, Finsupp.finsetSum_apply,
    Finset.sum_eq_single 1]
  · rw [Finsupp.smul_apply, rootVec_coeff hroot]
    simp
  · intro k _ hk
    have hne : (Pi.single j 1 + (k : ℤ) • Pi.single i 1 : Fin τ.rank → ℤ) ≠
        Pi.single j 1 + Pi.single i 1 := by
      intro h
      have := congrFun h i
      simp [Ne.symm hij] at this
      exact hk (by exact_mod_cast this)
    rw [Finsupp.smul_apply, rootVec_coeff hroot]
    simp only [hne, ↓reduceIte, smul_zero]
  · intro h
    exfalso
    exact h (Finset.mem_range.2 (by omega))

end Coefficient

section G2

variable {K : Type} [Field K]

abbrev g0 : Fin Tag.G2.rank := ⟨0, by decide⟩

abbrev g1 : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem g2_root_01 : IsRoot Tag.G2 (Pi.single g0 1 + Pi.single g1 1) := by
  have h := IsRoot.reflect (τ := Tag.G2) g0 (IsRoot.basis g1)
  have e : reflect Tag.G2 g0 (Pi.single g1 1) = Pi.single g0 1 + Pi.single g1 1 := by
    decide +kernel
  rwa [e] at h

theorem g2_not_root_10 : ¬ IsRoot Tag.G2 (Pi.single g1 1 - Pi.single g0 1) := by
  intro h
  rcases IsRoot.height_pos_or_neg h with h | h <;>
    simp [height, g0, g1] at h

theorem g2_not_root_01 : ¬ IsRoot Tag.G2 (Pi.single g0 1 - Pi.single g1 1) := by
  intro h
  rcases IsRoot.height_pos_or_neg h with h | h <;>
    simp [height, g0, g1] at h

theorem xUnit_G2_not_commute :
    ¬ Commute (xUnit Tag.G2 K g0 1) (xUnit Tag.G2 K g1 1) := by
  intro hc
  have h := congrArg (fun g : (Module.End K (RootModule Tag.G2 K))ˣ =>
    (g : Module.End K (RootModule Tag.G2 K)) (hVec Tag.G2 K g0)) hc.eq
  simp only [Units.val_mul, Module.End.mul_apply, coe_xUnit] at h
  have hne : g0 ≠ g1 := by decide
  have hne' : g1 ≠ g0 := by decide
  have key := congrArg (fun v : RootModule Tag.G2 K => v (Sum.inr ⟨_, g2_root_01⟩)) h
  simp only [xOp_hVec', map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at key
  have h1 : (Pi.single g0 1 : Fin Tag.G2.rank → ℤ) ≠ Pi.single g0 1 + Pi.single g1 1 := by
    intro h
    have := congrFun h g1
    simp [g0, g1] at this
  have h2 : (Pi.single g1 1 : Fin Tag.G2.rank → ℤ) ≠ Pi.single g0 1 + Pi.single g1 1 := by
    intro h
    have := congrFun h g0
    simp [g0, g1] at this
  have c00 : (Tag.G2.cartan g0 g0).natAbs = 2 := by decide
  have c01 : (Tag.G2.cartan g0 g1).natAbs = 1 := by decide
  rw [hVec_coeff, rootVec_coeff, rootVec_coeff,
    xOp_rootVec_coeff hne' g2_root_01 rfl g2_not_root_01 1,
    xOp_rootVec_coeff hne g2_root_01 (add_comm _ _) g2_not_root_10 1] at key
  simp only [h1, h2, ↓reduceIte, c00, c01] at key
  norm_num at key
  have : (1 : K) = 0 := by linear_combination -key
  exact one_ne_zero this

end G2

section Pair

variable {K : Type} [Field K] {p : ℕ} [CharP K p]

theorem xUnit_pow_one (τ : Tag) (i : Fin τ.rank) (n : ℕ) :
    (xUnit τ K i 1) ^ n = xUnit τ K i (n : K) := by
  induction n with
  | zero => simp [xUnit_zero]
  | succ n ih => rw [pow_succ, ih, ← xUnit_add]; push_cast; rfl

theorem xUnit_pow_char (τ : Tag) (i : Fin τ.rank) : (xUnit τ K i 1) ^ p = 1 := by
  rw [xUnit_pow_one, CharP.cast_eq_zero, xUnit_zero]

variable [Finite K]

theorem isPGroup_closure_xUnit (τ : Tag) (i j : Fin τ.rank) :
    IsPGroup p (Subgroup.closure ({⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩,
      ⟨xUnit τ K j 1, xUnit_mem_adjointGroup j 1⟩} : Set (adjointGroup τ K))) := by
  have hU : IsPGroup p (posUnipotent τ K) := ((positive_root_triangularity.{0, 0} τ).2 K p).2.1
  refine (hU.comap_subtype (K := adjointGroup τ K)).to_le ?_
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact xUnit_mem_posUnipotent i 1
  · exact xUnit_mem_posUnipotent j 1

theorem hasNoncommPair_adjointG2 : HasNoncommPair p (adjointGroup Tag.G2 K) := by
  refine ⟨⟨xUnit Tag.G2 K g0 1, xUnit_mem_adjointGroup g0 1⟩,
    ⟨xUnit Tag.G2 K g1 1, xUnit_mem_adjointGroup g1 1⟩, ?_, ?_, ?_,
    isPGroup_closure_xUnit Tag.G2 g0 g1⟩
  · exact Subtype.ext (by simpa using xUnit_pow_char (K := K) (p := p) Tag.G2 g0)
  · exact Subtype.ext (by simpa using xUnit_pow_char (K := K) (p := p) Tag.G2 g1)
  · intro h
    exact xUnit_G2_not_commute (K := K) (congrArg Subtype.val h)

theorem hasNoncommPair_adjointQuotient_G2 :
    HasNoncommPair p (↥(adjointGroup Tag.G2 K) ⧸ Subgroup.center ↥(adjointGroup Tag.G2 K)) := by
  refine HasNoncommPair.map (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup Tag.G2 K)))
    ((MonoidHom.ker_eq_bot_iff _).1 ?_) hasNoncommPair_adjointG2
  rw [QuotientGroup.ker_mk', center_adjointGroup_eq_bot]

end Pair

end CFSG.RankThree.PartOne.StrongP
