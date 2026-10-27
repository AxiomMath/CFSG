module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Components

variable {X : Type} [Group X]

theorem uc22p22r_eq_top_of_isSimple [IsSimpleGroup X] {K' : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K')
    (hsub : CFSG.Open.IsSubnormal K' ⊤) : K' = ⊤ :=
  (CFSG.Open.IsSubnormal.eq_bot_or_top hsub).resolve_left (uc22p22r_ne_bot_of_equiv (MulEquiv.refl _) hq)

theorem uc22p22r_eq_top_of_quasisimple (hX : CFSG.Open.IsQuasisimple X) {K' : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K') (hsub : CFSG.Open.IsSubnormal K' ⊤) : K' = ⊤ := by
  haveI : Group.IsPerfect ↥K' := ⟨hq.1⟩
  exact (CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hX K' hsub).resolve_left
    (uc22p22r_ne_bot_of_equiv (MulEquiv.refl _) hq)

theorem uc22p22r_eq_of_le_isSimple {K' C : Subgroup X} (hC : IsSimpleGroup ↥C) (hq : CFSG.Open.IsQuasisimple ↥K')
    (hsub : CFSG.Open.IsSubnormal K' ⊤) (hle : K' ≤ C) : K' = C := by
  have h : CFSG.Open.IsSubnormal K' C := by
    simpa [inf_eq_left.2 hle] using CFSG.Open.IsSubnormal.inf_of_le hsub (le_top : C ≤ ⊤)
  exact (CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup h hC).resolve_left
    (uc22p22r_ne_bot_of_equiv (MulEquiv.refl _) hq)

theorem uc22p22r_components_of_szL2Product [Finite X] {n : ℕ} (h : IsSzL2Product X n) :
    ∃ C₁ C₂ : Subgroup X, ∀ K' : Subgroup X, CFSG.Open.IsQuasisimple ↥K' → CFSG.Open.IsSubnormal K' ⊤ →
      K' = C₁ ∨ K' = C₂ := by
  obtain ⟨A, B, _, _, ⟨f⟩, hA, hB⟩ := h
  have hsimp : ∀ {C : Type} [Group C], (IsSz C n ∨ IsL2 C n) → IsSimpleGroup C := by
    intro C _ hC
    rcases hC with hC | hC
    · exact uc22p22r_lieModel_isSimple_twistedB2 hC
    · exact uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hC
  haveI : IsSimpleGroup A := hsimp hA
  haveI : IsSimpleGroup B := hsimp hB
  set N₁ : Subgroup X := ((MonoidHom.snd A B).comp f.toMonoidHom).ker with hN₁
  set N₂ : Subgroup X := ((MonoidHom.fst A B).comp f.toMonoidHom).ker with hN₂
  have hsup : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = f.symm ((f x).1, 1) * f.symm (1, (f x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · show (f (f.symm ((f x).1, 1))).2 = 1
      simp
    · show (f (f.symm (1, (f x).2))).1 = 1
      simp
  refine ⟨N₁, N₂, fun K' hq hsub => ?_⟩
  have hK' : CFSG.Open.IsComponentOf K' ⊤ := ⟨le_top, hsub, hq⟩
  have hne : K' ≠ ⊥ := uc22p22r_ne_bot_of_equiv (MulEquiv.refl _) hq
  rcases uc22p22r_component_le_or_le hsup hK' with hle | hle
  · have hN : N₁ ≠ ⊥ := fun h0 => hne (le_bot_iff.1 (h0 ▸ hle))
    obtain ⟨g⟩ := uc22p22r_equiv_factor f (Subgroup.Normal.isSubnormal inferInstance) hN le_rfl
    exact Or.inl (uc22p22r_eq_of_le_isSimple g.isSimpleGroup hq hsub hle)
  · have hN : N₂ ≠ ⊥ := fun h0 => hne (le_bot_iff.1 (h0 ▸ hle))
    obtain ⟨g⟩ := uc22p22r_equiv_factor (f.trans MulEquiv.prodComm) (Subgroup.Normal.isSubnormal inferInstance) hN
      (fun x hx => hx)
    exact Or.inr (uc22p22r_eq_of_le_isSimple g.isSimpleGroup hq hsub hle)

theorem uc22p22r_components_of_suCentralSquare [Finite X] (h : IsSU3CentralSquare X) :
    ∃ C₁ C₂ : Subgroup X, ∀ K' : Subgroup X, CFSG.Open.IsQuasisimple ↥K' → CFSG.Open.IsSubnormal K' ⊤ →
      K' = C₁ ∨ K' = C₂ := by
  obtain ⟨K₁, K₂, hsup, hcomm, hK₁, hK₂, -⟩ := h
  haveI : K₁.Normal := uc22p22r_normal_of_commuting hsup hcomm
  haveI : K₂.Normal :=
    uc22p22r_normal_of_commuting (by rwa [sup_comm]) fun a ha b hb => (hcomm b hb a ha).symm
  have hc₁ : CFSG.Open.IsComponentOf K₁ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal ‹K₁.Normal›), hK₁.1⟩
  have hc₂ : CFSG.Open.IsComponentOf K₂ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal ‹K₂.Normal›), hK₂.1⟩
  refine ⟨K₁, K₂, fun K' hq hsub => ?_⟩
  have hK' : CFSG.Open.IsComponentOf K' ⊤ := ⟨le_top, hsub, hq⟩
  rcases uc22p22r_component_le_or_le hsup hK' with hle | hle
  · exact Or.inl (CFSG.ComponentClassification.LocalComponents.eq_of_le K' K₁ hK' hc₁ hle)
  · exact Or.inr (CFSG.ComponentClassification.LocalComponents.eq_of_le K' K₂ hK' hc₂ hle)

end Components

section Count


theorem uc22p22r_components_two (D : Data G) (h207 : S20_7 D) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) :
    ∃ C₁ C₂ : Subgroup (Bar2 L), ∀ K' : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥K' →
      CFSG.Open.IsSubnormal K' ⊤ → K' = C₁ ∨ K' = C₂ := by
  have hA : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ},
      (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus ∨ t = .twistedB2 ∨ t = .G2 ∨
        t = .trialityD4 ∨ t = .twistedF4) → LieModel (Bar2 L) t m 2 n →
      ∃ C₁ C₂ : Subgroup (Bar2 L), ∀ K' : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥K' →
        CFSG.Open.IsSubnormal K' ⊤ → K' = C₁ ∨ K' = C₂ := by
    intro t m n ht h
    haveI : IsSimpleGroup (Bar2 L) := uc22p22r_lieModel_isSimple ht h
    exact ⟨⊤, ⊤, fun K' hq hsub => Or.inl (uc22p22r_eq_top_of_isSimple hq hsub)⟩
  have hQ : CFSG.Open.IsQuasisimple (Bar2 L) →
      ∃ C₁ C₂ : Subgroup (Bar2 L), ∀ K' : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥K' →
        CFSG.Open.IsSubnormal K' ⊤ → K' = C₁ ∨ K' = C₂ :=
    fun hX => ⟨⊤, ⊤, fun K' hq hsub => Or.inl (uc22p22r_eq_top_of_quasisimple hX hq hsub)⟩
  rcases h207 h1930 L hL with ⟨n, -, h⟩ | h | h | h | h | h | ⟨n, -, h⟩ | h
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hA (by decide) h
    · exact hQ h.1
    · exact hQ h.1
    · exact hA (by decide) h
    · exact hA (by decide) h
  · exact hA (by decide) h
  · exact hA (by decide) h
  · exact hA (by decide) h
  · exact hA (by decide) h
  · exact hA (by decide) h
  · exact uc22p22r_components_of_szL2Product h
  · exact uc22p22r_components_of_suCentralSquare h

theorem uc22p22r_calC_card_le_two (D : Data G) (h207 : S20_7 D) (h1930 : H1930 D) {L K₁ K₂ K₃ : Subgroup G}
    (hL : L ∈ calL D.T D.M) (h₁ : K₁ ∈ calC L) (h₂ : K₂ ∈ calC L) (h₃ : K₃ ∈ calC L) :
    K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := by
  obtain ⟨C₁, C₂, hC⟩ := uc22p22r_components_two D h207 h1930 hL
  have himg : ∀ {K : Subgroup G}, K ∈ calC L → barImage L K = C₁ ∨ barImage L K = C₂ := by
    intro K hK
    obtain ⟨K', hK'eq, -, -, hq, hsub⟩ := uc22p22r_bar2_quasisimple_iso hK
    have hbar : barImage L K = K' := by
      rw [hK'eq]
      rfl
    rw [hbar]
    exact hC K' hq hsub
  rcases himg h₁ with e₁ | e₁ <;> rcases himg h₂ with e₂ | e₂ <;> rcases himg h₃ with e₃ | e₃ <;>
    first
    | exact Or.inl (uc22p22u_calC_ext h₁ h₂ (e₁.trans e₂.symm))
    | exact Or.inr (Or.inl (uc22p22u_calC_ext h₁ h₃ (e₁.trans e₃.symm)))
    | exact Or.inr (Or.inr (uc22p22u_calC_ext h₂ h₃ (e₂.trans e₃.symm)))

end Count

end CFSG.LocalAnalysis.UniquenessCase.UC22
