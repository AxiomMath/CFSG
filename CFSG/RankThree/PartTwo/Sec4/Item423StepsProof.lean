module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProofConfig
public import CFSG.RankThree.PartTwo.Sec4.Item462Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements

@[expose] def K423SLThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A L : Subgroup G) (a : G), Config423 G A L a →
    Nat.card (autThetaQuot A L) = 9 →
    thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥ →
    IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L) →
    (∀ x ∈ A, x ≠ 1 →
      ¬ (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField)) →
      Item462Proof.Alt423 A L

@[expose] def K423Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A L : Subgroup G) (a : G), Config423 G A L a →
    Nat.card (autThetaQuot A L) = 9 →
    thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥ →
    ¬ IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L) →
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≠ ⊥ →
    (∀ x ∈ A, ¬ InducesOuterTheta x L) →
      Item462Proof.Alt423 A L

end Statements

@[expose] def K423InnerCensus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46 X → IsQuasisimple X → Subgroup.center X = ⊥ →
    ¬ IsSLThreePiAny X →
    ∀ D : Subgroup X, Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D →
      Nat.card D = 9 →
    ∀ Y : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ Y →
      thetaAlpha 3 ((D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y) ≠ ⊥ →
        (Nonempty (X ≃* alternatingGroup (Fin 7)) ∧
            Nonempty (autIn (⊤ : Subgroup X) D ≃* Multiplicative (ZMod 4))) ∨
          (Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
            Nonempty (autIn (⊤ : Subgroup X) D ≃* QuaternionGroup 2)) ∨
          ((Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
              Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) ∧
            Nonempty (autIn (⊤ : Subgroup X) D ≃* Equiv.Perm (Fin 3)))

namespace Item423Proof

@[expose] def prodCongrRightMul {M N N' : Type*} [Mul M] [Mul N] [Mul N'] (e : N ≃* N') :
    M × N ≃* M × N' :=
  { (Equiv.refl M).prodCongr e.toEquiv with
    map_mul' := fun x y => Prod.ext rfl (map_mul e x.2 y.2) }

theorem not_inducesOuterTheta_one {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    ¬ InducesOuterTheta (1 : G) L := by
  rintro ⟨h1, hout⟩
  apply hout
  have e : (⟨1, h1⟩ : Subgroup.normalizer (L : Set G)) = 1 := rfl
  rw [e, map_one, map_one]
  exact Subgroup.one_mem _

variable {G : Type} [Group G] [Finite G]

theorem alt423_of_inner (h45 : Item4_5) (h46 : Item4_6) (hIn : K423InnerCensus)
    {A L : Subgroup G} {a : G} (h : Config423 G A L a)
    (hα : thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥)
    (hany : ¬ IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinner : ∀ x ∈ A, ¬ InducesOuterTheta x L) : Item462Proof.Alt423 A L := by
  have h3 : 3 ∣ Nat.card (Subgroup.center G) := by
    rw [← h.orderOf_a]
    exact Subgroup.orderOf_dvd_natCard _ h.a_mem_center
  have hL46 := h46 G h.sectionFourHyp h3 L h.mem_thetaComponents
  obtain ⟨hAL9, hsup, c₀, d, hc₀, hd, hA⟩ := h.exists_closure_eq h45 hZ hinner
  have hDmax := h.maximal_imageModTheta_inf hA hc₀ hd
  have hD9 : Nat.card (Sec8.imageModTheta L (A ⊓ L)) = 9 := by
    rw [h.card_imageModTheta_inf, hAL9]
  have hα' := hα
  rw [h.autThetaQuot_eq_map_conj h45 hsup] at hα'
  obtain ⟨eA⟩ := h.nonempty_autIn_equiv hA hc₀ hd
  obtain ⟨eT⟩ := h.nonempty_thetaImage_equiv hZ hA hc₀ hd
  rcases hIn _ hL46 h.isQuasisimple_L hZ hany _ hDmax hD9 _
      (Config423.range_conj_le_autThetaQuot_top L) hα' with
    ⟨⟨e⟩, ⟨eD⟩⟩ | ⟨⟨e⟩, ⟨eD⟩⟩ | ⟨hX, ⟨eD⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨eT.trans (prodCongrRightMul e)⟩, ⟨eA.trans eD⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨eT.trans (prodCongrRightMul e)⟩, ⟨eA.trans eD⟩⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ⟨eA.trans eD⟩⟩))))))
    rcases hX with hM | hJ
    · obtain ⟨e⟩ := hM
      exact Or.inl ⟨eT.trans (prodCongrRightMul e)⟩
    · obtain ⟨e⟩ := hJ
      exact Or.inr ⟨eT.trans (prodCongrRightMul e)⟩

theorem item4_23_of_outer (h45 : Item4_5) (h46 : Item4_6) (hSL : K423SLThree)
    (hCov : K423Cover) (hIn : K423InnerCensus)
    (h47 : ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
      3 ∣ Nat.card (Subgroup.center G) → ∀ L ∈ thetaComponents 3 G, ∀ x : G, orderOf x = 3 →
      InducesOuterTheta x L →
        KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField ∨
          IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L)) : Item4_23 := by
  intro G _ _ hS4 A hmax h27 c hcA hcZ hc1 L hL h9 hα
  have h := Config423.of_card h45 hS4 hmax h27 hcA hcZ hc1 hL h9
  show Item462Proof.Alt423 A L
  by_cases h8 : ∃ x ∈ A, x ≠ 1 ∧
      (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h8))))))
  have h8' : ∀ x ∈ A, x ≠ 1 →
      ¬ (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :=
    fun x hx hx1 hk => h8 ⟨x, hx, hx1, hk⟩
  by_cases hany : IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L)
  · exact hSL G A L c h h9 hα hany h8'
  have h3 : 3 ∣ Nat.card (Subgroup.center G) := by
    rw [← h.orderOf_a]
    exact Subgroup.orderOf_dvd_natCard _ h.a_mem_center
  have hinner : ∀ x ∈ A, ¬ InducesOuterTheta x L := by
    intro x hx hout
    by_cases hx1 : x = 1
    · rw [hx1] at hout
      exact not_inducesOuterTheta_one L hout
    have hx3 : orderOf x = 3 := orderOf_eq_prime (h.pow_three x hx) hx1
    rcases h47 G hS4 h3 L hL x hx3 hout with hk | hk | hk
    · exact h8' x hx hx1 (Or.inl hk)
    · exact h8' x hx hx1 (Or.inr hk)
    · exact hany hk
  by_cases hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥
  · exact alt423_of_inner h45 h46 hIn h hα hany hZ hinner
  · exact hCov G A L c h h9 hα hany hZ hinner

end Item423Proof

open Item423Proof

end CFSG.RankThree.PartTwo.Sec4
