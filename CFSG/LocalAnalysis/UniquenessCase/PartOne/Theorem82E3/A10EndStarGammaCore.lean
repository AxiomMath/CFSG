module

public import CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctor
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

variable {X : Type} [Group X] [Finite X] {p : ℕ}

private lemma glapPrimeCoreOf_eq_relPPrimeCore (hp : p.Prime) (H : Subgroup X) :
    GLAPPrimeCoreOf p H = relPPrimeCore p H := by
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    hp H]
  rfl

private lemma isBalancedWrt_one_of_balance (hp : p.Prime) {A : Subgroup X}
    (hA : IsElemAbelian p A)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ Y : Subgroup X,
      Y ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (Y : Set X) → Nat.Coprime (Nat.card Y) p →
      Y ≤ relPPrimeCore p (Subgroup.centralizer ({a} : Set X))) :
    IsBalancedWrt p 1 A := by
  intro D hD x hx hx1
  set U : Subgroup X := GLADelta p D ⊓ Subgroup.centralizer ({x} : Set X) with hU
  have hDne : D ≠ ⊥ := hD.ne_bot hp le_rfl
  have hcopΔ : Nat.Coprime (Nat.card (GLADelta p D)) p :=
    ((hp.coprime_iff_not_dvd).mpr (not_dvd_card_glaDelta hp hDne)).symm
  have hcopU : Nat.Coprime (Nat.card U) p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hcopΔ
  have hAx : A ≤ Subgroup.centralizer ({x} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hA ha hx
  have hUnorm : A ≤ Subgroup.normalizer (U : Set X) :=
    (le_inf (le_normalizer_glaDelta hA hD.1) (hAx.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hres := hbal x hx hx1 U inf_le_right hUnorm hcopU
  rw [glapPrimeCoreOf_eq_relPPrimeCore hp]
  exact hres

private lemma inf_centralizer_le_glaDelta (hp : p.Prime) {A : Subgroup X}
    (hA : IsElemAbelian p A)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ Y : Subgroup X,
      Y ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (Y : Set X) → Nat.Coprime (Nat.card Y) p →
      Y ≤ relPPrimeCore p (Subgroup.centralizer ({a} : Set X)))
    {W F : Subgroup X} (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) p) (hF : IsEkIn p 1 A F) :
    W ⊓ Subgroup.centralizer (F : Set X) ≤ GLADelta p F := by
  intro x hx
  simp only [GLADelta, Subgroup.mem_iInf]
  intro d hd hd1
  have hdA : d ∈ A := hF.1 hd
  have hAd : A ≤ Subgroup.centralizer ({d} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hA ha hdA
  have hxd : x ∈ W ⊓ Subgroup.centralizer ({d} : Set X) :=
    ⟨hx.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd) hx.2⟩
  have hUnorm : A ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer ({d} : Set X) : Subgroup X) : Set X) :=
    (le_inf hW (hAd.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hUcop : Nat.Coprime
      (Nat.card (W ⊓ Subgroup.centralizer ({d} : Set X) : Subgroup X)) p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hcop
  have hres := hbal d hdA hd1 (W ⊓ Subgroup.centralizer ({d} : Set X)) inf_le_right hUnorm hUcop
  rw [glapPrimeCoreOf_eq_relPPrimeCore hp]
  exact hres hxd

private lemma le_thetaClosure_of_invariant (hp : p.Prime) {n : ℕ} {A W : Subgroup X}
    (hA : IsElemAbelian p A) (hcardA : Nat.card A = p ^ n) (hn : 1 < n)
    (hW : A ≤ Subgroup.normalizer (W : Set X)) (hcop : Nat.Coprime (Nat.card W) p)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ Y : Subgroup X,
      Y ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (Y : Set X) → Nat.Coprime (Nat.card Y) p →
      Y ≤ relPPrimeCore p (Subgroup.centralizer ({a} : Set X))) :
    W ≤ thetaClosure p 1 A := by
  have hW' : ¬ p ∣ Nat.card W := (hp.coprime_iff_not_dvd).mp hcop.symm
  refine (le_iSup_inf_centralizer_isEkIn (k := 1) hp hA hcardA hn hW hW').trans ?_
  refine iSup₂_le fun F hF => ?_
  refine (inf_centralizer_le_glaDelta hp hA hbal hW hcop hF).trans ?_
  change GLADelta p F ≤ ⨆ (D : Subgroup X) (_ : IsEkIn p 1 A D), GLADelta p D
  exact le_iSup₂_of_le F hF le_rfl

theorem eq_bot_of_glbCore_eq_top
    (hSF : CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctorTheoremK)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {A : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian p A) (hcard : p ^ 3 ≤ Nat.card A)
    (hK : CFSG.SectionRank.IsKGroupCat X)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) p →
      W ≤ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set X)))
    (hcore : CFSG.pPrimeCore p X = ⊥) (hgen : CFSG.Open.GLBCore p 2 A = ⊤)
    {W : Subgroup X} (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) p) : W = ⊥ := by
  have hbal1 : IsBalancedWrt p 1 A := isBalancedWrt_one_of_balance hp hA hbal
  have hK' : ∀ D : Subgroup X, IsEkIn p 1 A D →
      CFSG.SectionRank.IsKGroupCat ↥(GLADelta p D) :=
    fun D _ => hK.subgroup (GLADelta p D)
  obtain ⟨⟨hcopθ, -⟩, -⟩ :=
    thetaClosure_complete hSF hp le_rfl hA hcard hbal1 hK'
  have hnormθ : Subgroup.normalizer (thetaClosure p 1 A : Set X) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    simpa using glbCore_le_normalizer_thetaClosure (p := p) (k := 1) hp le_rfl hA hbal1
  have hθbot : thetaClosure p 1 A = ⊥ := by
    have hle := CFSG.le_pPrimeCore_of_normal_coprime (p := p)
      (Subgroup.normalizer_eq_top_iff.mp hnormθ) hcopθ
    rw [hcore] at hle
    exact le_bot_iff.mp hle
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hcardA⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_card_eq
  have hn3 : 3 ≤ n := by
    rw [hcardA] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  have hWle : W ≤ thetaClosure p 1 A :=
    le_thetaClosure_of_invariant hp hA hcardA (by omega) hW hcop hbal
  rw [hθbot] at hWle
  exact le_bot_iff.mp hWle

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen
