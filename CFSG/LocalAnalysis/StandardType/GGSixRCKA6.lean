module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6Label
public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6Classical
public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6PSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6F4
public import CFSG.LocalAnalysis.StandardType.GGPsiInnerDiagOfMarking
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.RCKA6

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType
open CFSG.Blueprint.Chevalley (adjointGroup Tag)

@[expose] def RCKLemmaP :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A D J : Subgroup X),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ → p.Prime → p ≠ 2 → IsElemAbelian p A → D ≤ A →
    Nat.card D = p ^ 2 → A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) → GGSixRCKJRow .A6 J →
    Subgroup.center ↥J = ⊥

private theorem rckGL_labelTag_of_rowA6 {lab : LargeEvenLabel}
    (h : ggSixRCKLabelRow lab = .A6) : lab.tag = .B2der := by
  cases h' : lab.tag <;> simp only [ggSixRCKLabelRow, h'] at h ⊢ <;>
    (try split_ifs at h) <;> simp_all

private theorem rckGL_quot_A6
    {X : Type} [Group X] {J : Subgroup X} (hrow : GGSixRCKJRow .A6 J) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨lab, _hlab, R, _hR, I, F, θ, _hsimple, _hna, hP, hmodel⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have htag : lab.tag = .B2der := rckGL_labelTag_of_rowA6 hP
  obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der htag hmodel
  exact ⟨θ.trans e⟩

theorem rckLemmaP_of_parts
    (hNo : ∀ {t : StatedLieTag}, (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → ∀ (X : Type)
        [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ D J : Subgroup X),
        GGPresentsG0 G₀ (ggU t n f).D t n f ψ → p.Prime → p ≠ 2 → D ≤ Subgroup.normalizer (G₀ : Set
        X) → (∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) → IsElemAbelian p D → Nat.card D = p ^ 2 →
        IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) → ¬ GGSixRCKJRow .A6
        J) (hCenter : RCKA6F4Center) : RCKLemmaP := by
  intro X _ _ t n f ψ p G₀ A D J hpres hp hp2 hA hDA hD2 hAN hmark hJ hZ hrow
  have hdiagA : ∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a :=
    ggPsiInnerDiag_of_marking hpres hmark hAN
  have hdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d := fun d hd => hdiagA d (hDA hd)
  have hD : IsElemAbelian p D := hA.mono hDA
  have hDN : D ≤ Subgroup.normalizer (G₀ : Set X) := hDA.trans hAN
  have hA6 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6)) :=
    rckGL_quot_A6 hrow
  have hJ' : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [inf_comm]
    exact hJ
  have rank_zero_absurd : ∀ (s : StatedLieTag),
      (s = .G2 ∨ s = .trialityD4 ∨ s = .twistedB2 ∨ s = .twistedG2 ∨ s = .twistedF4 ∨
        s = .Tits) → 2 ≤ (ggU s n f).D.rank → False := by
    intro s ht h2
    have h0 := lieUniversal_rank_eq_zero s n 2 f Nat.prime_two ht
    change 2 ≤ (lieUniversal s n 2 f Nat.prime_two).D.rank at h2
    rw [h0] at h2
    omega
  cases t with
  | PSL =>
    exact absurd hA6 (rck_A6_classical_noQuot (Or.inl rfl) X n f ψ p G₀ D J hpres hp hp2
      hDN hdiag hD hD2 hJ')
  | PSU =>
    exact absurd hA6 (rck_A6_classical_noQuot (Or.inr (Or.inl rfl)) X n f ψ p G₀ D J hpres hp
      hp2 hDN hdiag hD hD2 hJ')
  | PSp =>
    exact rck_A6_PSp_center X n f ψ p G₀ D J hpres hp hp2 hDN hdiag hD hD2 hJ' hZ hA6
  | POmegaOdd =>
    have h := hpres.1.1
    simp [StatedLieAdmissible] at h
  | POmegaPlus =>
    exact absurd hA6 (rck_A6_classical_noQuot (Or.inr (Or.inr (Or.inl rfl))) X n f ψ p G₀ D J
      hpres hp hp2 hDN hdiag hD hD2 hJ')
  | POmegaMinus =>
    exact absurd hA6 (rck_A6_classical_noQuot (Or.inr (Or.inr (Or.inr rfl))) X n f ψ p G₀ D J
      hpres hp hp2 hDN hdiag hD hD2 hJ')
  | F4 =>
    exact hCenter X n f ψ p G₀ D J hpres hp hp2 hDN hdiag hD hD2 hJ' hZ hrow
  | E6 =>
    exact absurd hrow (hNo (Or.inl rfl) X n f ψ p G₀ D J hpres hp hp2 hDN
      hdiag hD hD2 hJ')
  | E7 =>
    exact absurd hrow (hNo (Or.inr (Or.inl rfl)) X n f ψ p G₀ D J hpres hp hp2
      hDN hdiag hD hD2 hJ')
  | E8 =>
    exact absurd hrow (hNo (Or.inr (Or.inr (Or.inl rfl))) X n f ψ p G₀ D J
      hpres hp hp2 hDN hdiag hD hD2 hJ')
  | twistedE6 =>
    exact absurd hrow (hNo (Or.inr (Or.inr (Or.inr rfl))) X n f ψ p G₀ D J
      hpres hp hp2 hDN hdiag hD hD2 hJ')
  | G2 =>
    exact (rank_zero_absurd .G2 (Or.inl rfl) hpres.1.2).elim
  | trialityD4 =>
    exact (rank_zero_absurd .trialityD4 (Or.inr (Or.inl rfl)) hpres.1.2).elim
  | twistedB2 =>
    exact (rank_zero_absurd .twistedB2 (Or.inr (Or.inr (Or.inl rfl))) hpres.1.2).elim
  | twistedG2 =>
    exact (rank_zero_absurd .twistedG2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hpres.1.2).elim
  | twistedF4 =>
    exact (rank_zero_absurd .twistedF4
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hpres.1.2).elim
  | Tits =>
    exact (rank_zero_absurd .Tits (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      hpres.1.2).elim

theorem rckLemmaP_of_quot
    (hE : ∀ t : StatedLieTag,
      (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → A6Red.GGA6QuotNoJAt t)
    (hF : A6Red.GGA6QuotF4f) : RCKLemmaP :=
  rckLemmaP_of_parts
    (fun {_} ht X _ _ n f ψ p G₀ D J hG₀ hp hp2 hDN hdiag hD hD2 hJ =>
      rck_A6_exc_noRow_of_quot hE ht X n f ψ p G₀ D J hG₀ hp hp2 hDN hdiag hD hD2 hJ)
    (rck_A6F4Center_of_f
      (fun X _ _ n f ψ p G₀ D J hG₀ hp hp2 hDN hdiag hD hD2 hJ hrow =>
        rckF4_f_eq_one_of_quot hF X n f ψ p G₀ D J hG₀ hp hp2 hDN hdiag hD hD2 hJ hrow))

end CFSG.StandardType.RCKA6
