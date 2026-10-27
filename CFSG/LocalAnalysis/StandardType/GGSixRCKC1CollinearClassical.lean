module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearLong
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCores

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.ComponentClassification.RankTwoOddLie (CenterPPrime)

theorem rckCollinearVia_PSL
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSL m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSL m g).D.roots) (hl : GGLongRoot (ggU .PSL m g).D β) :
    RCKCollinearVia (ggU .PSL m g) β := by
  rcases m with _ | k
  · exfalso
    have hβ' : β ∈ roots (SpecialLinear.isFiniteType_A 0) ∅ := hβ
    rw [SpecialLinear.roots_eq] at hβ'
    obtain ⟨i, j, hij, -⟩ := hβ'
    exact hij (Fin.ext (by omega))
  · have hZ : CenterPPrime (ggU .PSL (k + 1) g).K 2 :=
      rckGL1_centerPPrime_ggU (Or.inl rfl) hg (fun h => by cases h)
    have hC : ∀ u : (ggU .PSL (k + 1) g).K, _ := fun u =>
      (LieKnownR2.PSL.coreFour_PSL (m := k) (f := g) hβ u rfl rfl).1
    generalize hM : ggU .PSL (k + 1) g = M at β hβ hl hZ hC ⊢
    have hM' : M = ⟨Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g),
        SpecialLinear.rootDatum k (GaloisField 2 g)⟩ := by
      rw [← hM]
      simp only [ggU, lieUniversal]
    subst hM'
    have hirr : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible
        (SpecialLinear.rootDatum k (GaloisField 2 g)).cartan := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        intro S hS _ j
        exact j.elim0
      · exact CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A hk
    have hX : IsPGroup 2 ((SpecialLinear.rootDatum k (GaloisField 2 g)).rootGroup β) :=
      CFSG.LieType.Steinberg.isPGroup_of_isParametrization
        (CFSG.LieType.Steinberg.SL.isParametrization (m := k)
          (F := GaloisField 2 g)) hβ
    exact rckCollinearVia_of_long
      (SpecialLinear.isCTGroupDatum k (GaloisField 2 g))
      (SpecialLinear.steinbergExtras k (GaloisField 2 g))
      hirr rfl hZ hl hX hC

theorem rckCollinearVia_PSp_long
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSp m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSp m g).D.roots) (hl : GGLongRoot (ggU .PSp m g).D β) :
    RCKCollinearVia (ggU .PSp m g) β := by
  have hZ : CenterPPrime (ggU .PSp m g).K 2 :=
    rckGL1_centerPPrime_ggU (Or.inr (Or.inr (Or.inl rfl))) hg (fun h => by cases h)
  have hC : ∀ u : (ggU .PSp m g).K, _ := fun u =>
    (LieKnownR2.PSp.coreFour_PSp_long (n := m) (f := g) hl u rfl rfl).1
  generalize hM : ggU .PSp m g = M at β hβ hl hZ hC ⊢
  have hM' : M = ⟨CFSG.Open.StatedSp m (GaloisField 2 g),
      Symplectic.rootDatum m (GaloisField 2 g)⟩ := by
    rw [← hM]
    simp only [ggU, lieUniversal]
  subst hM'
  have hn0 : 0 < m := by
    obtain ⟨w, γ₀, hγ₀, -, -⟩ := hl
    obtain ⟨r, -⟩ :=
      CFSG.LieType.Universal.Symplectic.SpExtras.exists_stdVec_of_mem_roots hγ₀
    rcases r with i | i | ⟨i, _, _⟩ | ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact i.pos
  have hirr : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible
      (Symplectic.rootDatum m (GaloisField 2 g)).cartan :=
    CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanC hn0
  have hdiv : (Symplectic.rootDatum m (GaloisField 2 g)).divisible = ∅ := rfl
  have hX : IsPGroup 2 ((Symplectic.rootDatum m (GaloisField 2 g)).rootGroup β) :=
    GGRootSp.isPGroup_rootGroup hβ
  exact rckCollinearVia_of_long
    (Symplectic.isCTGroupDatum (n := m) (F := GaloisField 2 g))
    (Symplectic.steinbergExtras m (GaloisField 2 g))
    hirr hdiv hZ hl hX hC

theorem rckCollinearVia_PSU_long
    {m g : ℕ} (hg : 1 ≤ g) (hm : 4 ≤ m) (he : Even m) {β : Fin (ggU .PSU m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSU m g).D.roots) (hl : GGLongRoot (ggU .PSU m g).D β) :
    RCKCollinearVia (ggU .PSU m g) β := by
  have hF : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 :=
    card_galoisField_two_mul 2 g hg
  have hZ : CenterPPrime (ggU .PSU m g).K 2 :=
    rckGL1_centerPPrime_ggU (Or.inr (Or.inl rfl)) hg (fun h => by cases h)
  have hC : ∀ u : (ggU .PSU m g).K, _ := fun u =>
    (LieKnownR2.PSU.coreFour_PSU_long (n := m) (f := g) (by omega) hl u rfl rfl).1
  generalize hM : ggU .PSU m g = M at β hβ hl hZ hC ⊢
  have hM' : M = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) m, Unitary.rootDatum hF m⟩ := by
    rw [← hM]
    simp only [ggU, lieUniversal, hg, ↓reduceDIte]
  subst hM'
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
  have hct := Unitary.isCTGroupDatum hF m (by omega) ζ hζ
  have hext := Unitary.steinbergExtras hF m (by omega) ζ hζ
  obtain ⟨hc, hd⟩ := CFSG.ClassicalInvolution.ModelFacts.unitary_even he
  have hirr : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible
      (Unitary.rootDatum hF m).cartan := by
    show CFSG.ClassicalInvolution.ModelFacts.IsIrreducible (Unitary.cartan m)
    rw [hc]
    exact CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanC (by omega)
  have hdiv : (Unitary.rootDatum hF m).divisible = ∅ := by
    show Unitary.divisible m = ∅
    exact hd
  have hX : IsPGroup 2 ((Unitary.rootDatum hF m).rootGroup β) := by
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    exact CFSG.LieType.Steinberg.isPGroup_rootGroup
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF)
      (Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβ)
  exact rckCollinearVia_of_long hct hext hirr hdiv hZ hl hX hC

theorem rckCollinearVia_POmegaPlus
    {m g : ℕ} (hg : 1 ≤ g) (hm : 4 ≤ m) {β : Fin (ggU .POmegaPlus m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaPlus m g).D.roots) (hl : GGLongRoot (ggU .POmegaPlus m g).D β) :
    RCKCollinearVia (ggU .POmegaPlus m g) β := by
  have hn3 : 3 ≤ m := by omega
  have hZ : CenterPPrime (ggU .POmegaPlus m g).K 2 :=
    rckGL1_centerPPrime_ggU (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hg
      (fun h => by cases h)
  have hFin : Finite (ggU .POmegaPlus m g).K :=
    rckXF_finite_ggU (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hg
  have hC : ∀ u : (ggU .POmegaPlus m g).K, _ := fun u =>
    (LieKnownR2.POmega.coreFour_POmegaPlus_long (n := m) (f := g) hm hl u rfl rfl).1
  generalize hM : ggU .POmegaPlus m g = M at β hβ hl hZ hC hFin ⊢
  have hM' : M = ⟨spinGroup (Spin.quadPlus m (GaloisField 2 g)),
      Spin.plusDatum m (GaloisField 2 g) hn3⟩ := by
    rw [← hM]
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  subst hM'
  obtain ⟨hdiv, hirr, -⟩ :=
    LieKnownR2.POmega.Cores.spinPlus_highest (n := m) (F := GaloisField 2 g) hn3
  have hX : IsPGroup 2 ((Spin.plusDatum m (GaloisField 2 g) hn3).rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_of_isParametrization
      (CFSG.LieType.Steinberg.SpinPlus.isParametrization (n := m)
        (K := GaloisField 2 g) hn3) hβ
  exact rckCollinearVia_of_long
    (Spin.plusDatum_isCTGroupDatum (n := m) (K := GaloisField 2 g) hn3
      (Spin.plusDatum_iSup_eq_top m (GaloisField 2 g) hn3))
    (Spin.plusDatum_steinbergExtras (n := m) (K := GaloisField 2 g) hn3)
    hirr hdiv hZ hl hX hC

theorem rckCollinearVia_POmegaMinus_long
    {m g : ℕ} (hg : 1 ≤ g) (hm : 4 ≤ m) {β : Fin (ggU .POmegaMinus m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaMinus m g).D.roots) (hl : GGLongRoot (ggU .POmegaMinus m g).D β) :
    RCKCollinearVia (ggU .POmegaMinus m g) β := by
  have hZ : CenterPPrime (ggU .POmegaMinus m g).K 2 :=
    rckGL1_centerPPrime_ggU (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hg
      (fun _ => by omega)
  have hFin : Finite (ggU .POmegaMinus m g).K :=
    rckXF_finite_ggU (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hg
  have hC : ∀ u : (ggU .POmegaMinus m g).K, _ := fun u =>
    (LieKnownR2.POmega.coreFour_POmegaMinus_long (n := m) (f := g) hm hl u rfl rfl).1
  generalize hM : ggU .POmegaMinus m g = M at β hβ hl hZ hC hFin ⊢
  have hM' : M = ⟨spinGroup (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2),
      Spin.Twisted.minusDatum m (minusCoeffs_irr 2 g)⟩ := by
    rw [← hM]
    simp only [ggU, lieUniversal]
  subst hM'
  obtain ⟨hdiv, hirr, -⟩ :=
    LieKnownR2.POmega.Cores.spinMinus_highest (n := m) (F := GaloisField 2 g) hm
      (minusCoeffs_irr 2 g)
  have hX : IsPGroup 2 ((Spin.Twisted.minusDatum m (minusCoeffs_irr 2 g)).rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_minusRootGroup (n := m) (K := GaloisField 2 g)
      (minusCoeffs_irr 2 g) (p := 2) hβ
  exact rckCollinearVia_of_long
    (Spin.Twisted.minusDatum_isCTGroupDatum m (minusCoeffs_irr 2 g) hm)
    (Spin.Twisted.minusDatum_steinbergExtras m (minusCoeffs_irr 2 g))
    hirr hdiv hZ hl hX hC

end CFSG.StandardType.RCKC1
