module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacCoverProducer
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedA12
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic

public section

namespace CFSG.StandardType.GGK0ExcB3Prod

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

@[expose] def GGK0ExcCore (lab : LargeEvenLabel) (p : ℕ) (L' : Type) [Group L'] [Finite L']
    (e : MulAut L') (D : GGKacDatum) : Prop :=
  GGKacValid lab p D ∧
    (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
      ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
        GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
    (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
      CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
        GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
    (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → p ∣ Nat.card J) ∧
    GGKacCompBij D L' e ∧ GGKacA12Comp D L' e

@[expose] def GGK0ExcCentre (lab : LargeEvenLabel) (p : ℕ) {R : Type} [Group R] (I : Set (MulAut R))
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (e : MulAut L') (D : GGKacDatum) : Prop :=
  GGKacCentred lab p → 2 ≤ D.rZ → ∃ E : Subgroup L', IsElemAbelian p E ∧
    Nat.card E = p ^ D.rZ ∧ E ≤ ggFixSub e ∧
    (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
    ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z

@[expose] def GGK0ExcTrivial : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∃ D : GGKacDatum, GGK0ExcCore lab p L' 1 D ∧ GGK0ExcCentre lab p I L' ψ 1 D

@[expose] def GGK0ExcRealizedCentre (Omega : Type) [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p → S p lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', orderOf e = p → ∀ phi ∈ I, (∀ l : L', phi (ψ l) = ψ (e l)) →
          ∀ ρ : MarkedRationalKacRealization Omega lab p R I phi,
            GGK0ExcCentre lab p I L' ψ e ρ.row.D

theorem ggK0ExcB3_of_producers (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hF4 : RationalProducerOn Omega .F4) (hE6 : RationalProducerOn Omega .E6)
    (hTwE6 : RationalProducerOn Omega .twE6) (hE7 : RationalProducerOn Omega .E7)
    (hE8 : RationalProducerOn Omega .E8)
    (htriv : GGK0ExcTrivial)
    (hcentre : GGK0ExcRealizedCentre Omega fun _ _ => True) : GGK0ExcB3 := by
  intro p lab hΛ hpair
  have hcov : LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L : Type) [Group L] [Finite L] (psi : L →* R), Function.Surjective psi →
        psi.ker ≤ Subgroup.center L → commutator L = ⊤ →
        ∀ e : MulAut L, orderOf e = p →
          (∃ phi ∈ I, ∀ l : L, phi (psi l) = psi (e l)) →
          ∃ phi ∈ I, (∀ l : L, phi (psi l) = psi (e l)) ∧
            Nonempty (MarkedRationalKacRealization Omega lab p R I phi) := by
    rcases hpair.2.2.2 with h | h | h | h | h
    · exact (coverProducerOn_of_rationalProducerOn Omega .E6 hE6) p lab hΛ hpair h
    · exact (coverProducerOn_of_rationalProducerOn Omega .twE6 hTwE6) p lab hΛ hpair h
    · exact (coverProducerOn_of_rationalProducerOn Omega .E7 hE7) p lab hΛ hpair h
    · exact (coverProducerOn_of_rationalProducerOn Omega .E8 hE8) p lab hΛ hpair h
    · exact (coverProducerOn_of_rationalProducerOn Omega .F4 hF4) p lab hΛ hpair h
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ ((largeEvenLabelAll_and
    (largeEvenLabelAll_and hcov (htriv p lab hΛ hpair))
    (hcentre p lab hΛ hpair trivial)) Q hQ)
  rintro R _ I F ⟨hq, ⟨hcv, htr⟩, hce⟩
  refine ⟨hq, ?_⟩
  intro L' _ _ ψ hψ hker hperf e hep hind
  by_cases he : e = 1
  · subst he
    obtain ⟨D, hC, hZ⟩ := htr L' ψ hψ hker hperf
    exact ⟨D, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hZ, hC.2.2.2.2.1, hC.2.2.2.2.2⟩
  · haveI : Fact p.Prime := ⟨hpair.1⟩
    have hord : orderOf e = p := orderOf_eq_prime hep he
    obtain ⟨phi, hphiI, hphi, ⟨ρ⟩⟩ := hcv L' ψ hψ hker hperf e hord hind
    have hComp := GGK0MarkedComponents.cover_comps_of_realization
      hpair.1 hpair.2.1 ρ ψ hψ hker e (by rw [← hord]; exact pow_orderOf_eq_one e) hphi
    have hDiv := GGK0MarkedArithmetic.cover_dvd_of_realization hpair ρ ψ hψ hker e hphi
    have hBij := GGK0MarkedComponents.cover_compBij_of_realization
      hpair.1 hpair.2.1 ρ ψ hψ hker e hphi
    have hZ := hce L' ψ hψ hker hperf e hord phi hphiI hphi ρ
    exact ⟨ρ.row.D, ρ.row.valid, hComp.1, hComp.2, hDiv, hZ, hBij,
      GGK0MarkedA12.a12_of_excPair hΛ hpair ρ ψ hψ hker e hord hphi⟩

theorem GGK0ExcRealizedCentre.mono {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, GGKacExcPair lab p → S p lab → S' p lab)
    (h : GGK0ExcRealizedCentre Omega S') : GGK0ExcRealizedCentre Omega S :=
  fun p lab hl hp hs => h p lab hl hp (hSS' p lab hp hs)

theorem GGK0ExcRealizedCentre.union {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {S₁ S₂ : ℕ → LargeEvenLabel → Prop} (h₁ : GGK0ExcRealizedCentre Omega S₁)
    (h₂ : GGK0ExcRealizedCentre Omega S₂) :
    GGK0ExcRealizedCentre Omega fun p lab => S₁ p lab ∨ S₂ p lab :=
  fun p lab hl hp hs => hs.elim (h₁ p lab hl hp) (h₂ p lab hl hp)

theorem ggK0ExcRealizedCentre_notCentred (Omega : Type) [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2] :
    GGK0ExcRealizedCentre Omega fun p lab => ¬ GGKacCentred lab p := by
  intro p lab hΛ hpair hnc Q hQ
  refine largeEvenRawDatum_mono ?_ hQ
  intro R _ I F hq
  refine ⟨hq, ?_⟩
  intro L' _ _ ψ hψ hker hperf e hord phi hphiI hphi ρ hcen
  exact absurd hcen hnc

end CFSG.StandardType.GGK0ExcB3Prod

end
