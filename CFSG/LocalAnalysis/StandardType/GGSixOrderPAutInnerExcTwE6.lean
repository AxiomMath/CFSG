module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSixE
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

theorem OrdPInnerExc.not_three_of_not_outdiag_twistedE6 {p n f : ℕ}
    (h : ¬ GGOutdiagPrimeConfig p .twistedE6 n f) : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1) :=
  fun h' => h (Or.inr (Or.inr (Or.inr ⟨rfl, h'.1, h'.2⟩)))

section TwE6


@[expose] def GGTwE6InndiagOrdPInnerInput : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1) →
    ∀ α ∈ LayerSixE.twInndiagAut f, α ^ p = 1 →
      α ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range

@[expose] def GGTwE6CenterTrivialInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ¬ 3 ∣ 2 ^ f + 1 → Subgroup.center (twistedE6Group 2 f) = ⊥

@[expose] def GGOrdPToralTwE6Input : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1) →
    (∃ A : Subgroup (twistedE6Group 2 f), IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (twistedE6Group 2 f) p

namespace OrdPInnerExc

theorem coprime_card_center_twistedE6 (hZ : GGTwE6CenterTrivialInput) {f p : ℕ} (hf : 1 ≤ f)
    (hp : p.Prime) (h : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1)) :
    Nat.Coprime (Nat.card (Subgroup.center (twistedE6Group 2 f))) p := by
  by_cases hp3 : p = 3
  · subst hp3
    rw [hZ f hf (fun h3 => h ⟨rfl, h3⟩), Subgroup.card_bot]
    exact Nat.coprime_one_left 3
  obtain ⟨π, -, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hle : π.ker.map (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype ≤
      (e6IsogenyT (GaloisField 2 (2 * f))).ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact RootDetectTwE6.mem_ker_e6IsogenyT_of_mem_ker f π hπval hx
  have hdvd : Nat.card π.ker ∣ Nat.card (e6IsogenyT (GaloisField 2 (2 * f))).ker := by
    rw [← Subgroup.card_subtype]
    exact Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card (e6IsogenyT (GaloisField 2 (2 * f))).ker ∣ 3 := by
    refine (Subgroup.card_dvd_of_le (ker_e6IsogenyT_le_center (GaloisField 2 (2 * f)))).trans ?_
    rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (GaloisField 2 (2 * f))).1]
    exact Nat.gcd_dvd_left 3 _
  rw [← hkerπ]
  exact Nat.Coprime.coprime_dvd_left (hdvd.trans hdvd2)
    ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))

theorem inner_twistedE6 (hI : GGTwE6InndiagOrdPInnerInput) (G : Type) [Group G] [Finite G]
    (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* G)
    (hS : GGSixFusionSetting p Bs G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (hout : ¬ GGOutdiagPrimeConfig p .twistedE6 n f) (c : G)
    (hcN : c ∈ Subgroup.normalizer (G₀ : Set G)) (hcp : c ^ p = 1)
    (hci : GGPsiInnerDiag (ggU .twistedE6 n f).D ψ c) : c ∈ G₀ := by
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, hperf, -⟩ := hS.presents
  have hC := hS.centralizer_eq_bot
  subst hrange
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨π, hπ, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hker.trans hkerπ.ge
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hcN hci
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN p
    rw [hcp] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  exact mem_range_of_induces_inner hπ hkerπ.le hkπ hperf hC hcN
    (hI f p hf hS.prime hS.1.2 (not_three_of_not_outdiag_twistedE6 hout) α hαD hαp) hα

end OrdPInnerExc

theorem ggOrdPToralUnivAt_twistedE6_of_input (h : GGOrdPToralTwE6Input) :
    GGOrdPToralUnivAt .twistedE6 := by
  intro n f p hadm hp hp2 hout hA
  change ∃ A : Subgroup (twistedE6Group 2 f), IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A at hA
  exact h f p hadm.2.1 hp hp2 (OrdPInnerExc.not_three_of_not_outdiag_twistedE6 hout) hA

theorem ggOrdPInnerConjAt_twistedE6_of_inputs (hI : GGTwE6InndiagOrdPInnerInput)
    (hZ : GGTwE6CenterTrivialInput) (hT : GGOrdPToralTwE6Input) :
    GGOrdPInnerConjAt .twistedE6 := by
  refine OrdPInnerExc.ggOrdPInnerConjAt_of_parts (OrdPInnerExc.inner_twistedE6 hI)
    (fun n f p hadm hp hout => ?_) (ggOrdPToralUnivAt_twistedE6_of_input hT)
  change Nat.Coprime (Nat.card (Subgroup.center (twistedE6Group 2 f))) p
  exact OrdPInnerExc.coprime_card_center_twistedE6 hZ hadm.2.1 hp
    (OrdPInnerExc.not_three_of_not_outdiag_twistedE6 hout)

end TwE6

end CFSG.StandardType
