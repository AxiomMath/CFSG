module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSTools
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def PCentralAbelian : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup K → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card K → PCentralAbelianAt K p

@[expose] def PCAAlt : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ p : ℕ, p.Prime → 5 ≤ p → PCentralAbelianAt (alternatingGroup (Fin n)) p

@[expose] def PCALie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card K → PCentralAbelianAt K p

@[expose] def PCASpor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    NativeSporadic.SporadicRep K → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card K → PCentralAbelianAt K p

@[expose] def PCALieDefAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p = ℓ → p ∣ Nat.card K → PCentralAbelianAt K p

@[expose] def PCALieCrossAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ ℓ → p ∣ Nat.card K → PCentralAbelianAt K p

@[expose] def PCASporAt (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* NativeSporadic.Carrier s) → PCentralAbelianAt K p

theorem pcaLie_of_tags (hDef : ∀ t, PCALieDefAt t) (hCross : ∀ t, PCALieCrossAt t) : PCALie := by
  intro K _ _ hs hnab t n ℓ f hadm hmodel p hp h5 hpK
  by_cases hpℓ : p = ℓ
  · exact hDef t K hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  · exact hCross t K hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK

section Spor

open CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem pcaSpor_offPair (hBM : SporadicBMData) (s : TauCeti.SporadicName) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hnot : ¬ SporadicOnePair s p) : PCASporAt s p := by
  intro K _ _ ⟨e⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card K = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
  have hN : Nat.card K ≠ 0 := Nat.card_pos.ne'
  apply PCentralAbelianAt.of_factorization_le (by omega)
  rcases offPair_carrier hBM s p hp (by omega) hnot with h | ⟨h, -⟩
  · by_contra hlt
    exact h (hcard ▸ (hp.pow_dvd_iff_le_factorization hN).2 (by omega))
  · by_contra hlt
    exact h (hcard ▸ (hp.pow_dvd_iff_le_factorization hN).2 (by omega))

theorem pcaSpor_of_pairs (hBM : SporadicBMData) (hHN : PCASporAt .HN 5) (hLy : PCASporAt .Ly 5)
    (hCo1 : PCASporAt .Co1 5) (hB : PCASporAt .B 5) (hM5 : PCASporAt .M 5) (hM7 : PCASporAt .M 7) :
    PCASpor := by
  intro K _ _ hs hnab ⟨s, ⟨e⟩⟩ p hp h5 hpK
  by_cases hone : SporadicOnePair s p
  · rcases hone with ⟨h3, -⟩ | ⟨hp5, hs'⟩ | ⟨hp7, hs'⟩
    · omega
    · subst hp5
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl | rfl | rfl | rfl
      · exact hCo1 K ⟨e⟩
      · exact hHN K ⟨e⟩
      · exact hLy K ⟨e⟩
      · exact hB K ⟨e⟩
      · exact hM5 K ⟨e⟩
    · subst hp7
      subst hs'
      exact hM7 K ⟨e⟩
  · exact pcaSpor_offPair hBM s hp h5 hone K ⟨e⟩

end Spor

section Dispatch

theorem pca_of_cases (hAlt : PCAAlt) (hLie : PCALie) (hSpor : PCASpor) : PCentralAbelian := by
  intro K _ _ hs hnab hcat p hp h5 hpK
  haveI : Fact p.Prime := ⟨hp⟩
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact PCentralAbelianAt.of_mulEquiv e (hAlt n hn5 p hp h5)
  · exact hLie K hs hnab t n ℓ f hadm hmodel p hp h5 hpK
  · exact hSpor K hs hnab hspor p hp h5 hpK

end Dispatch

end CFSG.LocalAnalysis.UniquenessCase.UCK
