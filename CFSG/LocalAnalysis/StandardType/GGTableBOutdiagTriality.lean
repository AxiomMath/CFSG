module

public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

section OutCyclic

@[expose] def GGOutCyclic (R : Type*) [Group R] : Prop :=
  ∃ φ₀ : MulAut R, ∀ α : MulAut R,
    α ∈ ((MulAut.conj : R →* MulAut R).range ⊔ Subgroup.zpowers φ₀ : Subgroup (MulAut R))

theorem GGOutCyclic.ggOutdiagCyclic {R : Type} [Group R] (h : GGOutCyclic R) (I : Set (MulAut R)) :
    GGOutdiagCyclic R I := by
  obtain ⟨φ₀, hφ₀⟩ := h
  exact ⟨φ₀, fun α _ => hφ₀ α⟩

theorem ggOutCyclic_of_hom {C G' : Type*} [Group C] [Group G'] [IsCyclic G']
    (Θ : MulAut C →* G') (hΘ : Function.Surjective Θ)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) : GGOutCyclic C := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G')
  obtain ⟨φ₀, rfl⟩ := hΘ γ
  refine ⟨φ₀, fun α => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ (Θ α))
  have hmem : α * (φ₀ ^ k)⁻¹ ∈ (MulAut.conj : C →* MulAut C).range := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  have hα : α = α * (φ₀ ^ k)⁻¹ * φ₀ ^ k := by group
  rw [hα]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

theorem GGOutCyclic.of_mulEquiv {R C : Type*} [Group R] [Group C] (e : R ≃* C)
    (h : GGOutCyclic C) : GGOutCyclic R := by
  obtain ⟨φ₀, hφ₀⟩ := h
  set E := MulAut.congr e with hE
  refine ⟨E.symm φ₀, fun α => ?_⟩
  set S := ((MulAut.conj : R →* MulAut R).range ⊔ Subgroup.zpowers (E.symm φ₀)).map
    E.toMonoidHom with hS
  have hle : ((MulAut.conj : C →* MulAut C).range ⊔ Subgroup.zpowers φ₀) ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      refine ⟨MulAut.conj (e.symm c), Subgroup.mem_sup_left ⟨_, rfl⟩, ?_⟩
      ext x
      simp [hE, MulAut.congr_apply, MulAut.conj_apply]
    · rw [Subgroup.zpowers_le]
      exact ⟨E.symm φ₀, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), E.apply_symm_apply φ₀⟩
  obtain ⟨β, hβ, hβα⟩ := hle (hφ₀ (E α))
  rwa [show β = α from E.injective hβα] at hβ

end OutCyclic

section TriD4


theorem ggOutCyclic_triD4 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) :
    GGOutCyclic (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, hcyc, -, -, -, ⟨e₂⟩⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have := hcyc
  obtain ⟨e₁⟩ := centerQuot_twistedH_equiv K .D4 n σ.toRingHom hσ
  exact (ggOutCyclic_of_hom Θ hsurj hker).of_mulEquiv (e₁.trans e₂)

theorem largeEvenLabelAll_outdiag_triD4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .triD4) : LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := fun R _ I _ => GGOutdiagCyclic R I)
    (fun K _ _ hK => (ggOutCyclic_triD4 hn K hK).ggOutdiagCyclic _) hQ

@[expose] def GGOutdiagOpenLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∨ lab.tag = .twF4

theorem ggLNoncyclicInput_of_open
    (h : ∀ lab, LargeEvenInLambda2 lab → GGOutdiagOpenLabel lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I)) :
    GGLNoncyclicInput :=
  ggLNoncyclicInput_of_twisted fun lab hlab ht => by
    rcases ht with ht | ht | ht
    · exact h lab hlab (Or.inl ht)
    · exact (largeEvenLabelAll_outdiag_triD4 hlab ht).mono fun _ _ _ _ hO _ _ => hO
    · exact h lab hlab (Or.inr ht)

theorem ggLNoncyclicInput_of_twistedDiag' (hE6 : GGTwistedE6DiagInput)
    (hF4 : GGTwistedF4DiagInput) : GGLNoncyclicInput :=
  ggLNoncyclicInput_of_open fun _ hlab ht => by
    rcases ht with ht | ht
    · exact largeEvenLabelAll_outdiag_twE6 hE6 hlab ht
    · exact largeEvenLabelAll_outdiag_twF4 hF4 hlab ht

theorem ggTableBInputs_of_open
    (h₀ : ∀ lab, LargeEvenInLambda2 lab → GGOutdiagOpenLabel lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I))
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I) :
    GGLNoncyclicInput ∧ GGBstarInput ∧ GGStdSubPreInput := by
  have ha₀ := ggLNoncyclicInput_of_open h₀
  refine ⟨ha₀, ggBstarInput_of_labels ha₀ fun p lab hp hlab hs => ?_,
    ggStdSubPreInput_of_labels fun p lab hp hlab hs => ?_⟩
  · exact (h p lab hp hlab hs).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩
  · exact (h p lab hp hlab hs).mono fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

end TriD4

end CFSG.StandardType
