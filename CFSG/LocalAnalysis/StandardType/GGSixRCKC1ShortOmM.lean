module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmMCentral
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.Open
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg
open CliffordAlgebra

theorem rckOmM_two_le
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .POmegaMinus m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaMinus m g).D.roots) : 2 ≤ m := by
  by_contra hle
  have hm1 : m ≤ 1 := by omega
  have hrank : (ggU .POmegaMinus m g).D.rank = 0 := by
    simp only [ggU, lieUniversal, Spin.Twisted.minusDatum]
    omega
  haveI : IsEmpty (Fin (ggU .POmegaMinus m g).D.rank) := by
    rw [hrank]; infer_instance
  exact ne_zero_of_mem_roots (ggU .POmegaMinus m g).D.isFiniteType
    (ggU .POmegaMinus m g).D.divisible hβ (Subsingleton.elim β 0)

private theorem rckSOmMG_cent_long {n : ℕ} {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {γ : Fin (minusDatum n hirr).rank → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    (hcoord : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    RCKLemmaHCent ⟨spinGroup (quadMinus n K b c), minusDatum n hirr⟩ γ := by
  intro x hx hx1 k hk
  change x ∈ minusRootGroup n hirr γ at hx
  rw [mem_minusRootGroup_long_iff n hirr hij s t hcoord] at hx
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h0 => hx1 (by rw [h0, ofAdd_zero, map_one])
  have hk_eq : (k : CliffordAlgebra (quadMinus n K b c)) *
      ((minusFrame n b c).longRoot hij s t (.ofAdd a) :
        CliffordAlgebra (quadMinus n K b c)) =
      ((minusFrame n b c).longRoot hij s t (.ofAdd a) :
        CliffordAlgebra (quadMinus n K b c)) * (k : CliffordAlgebra (quadMinus n K b c)) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hk
    have h2 := congrArg Subtype.val h
    simpa using h2
  have hcomm : Commute (k : CliffordAlgebra (quadMinus n K b c))
      (1 + a • (ι (quadMinus n K b c) ((minusFrame n b c).vec i s) *
        ι (quadMinus n K b c) ((minusFrame n b c).vec j t))) := by
    rw [← HypFrame.coe_longRoot]
    exact hk_eq
  intro y hy
  change y ∈ minusRootGroup n hirr γ at hy
  rw [mem_minusRootGroup_long_iff n hirr hij s t hcoord] at hy
  obtain ⟨a', rfl⟩ := hy
  have hky : Commute (k : CliffordAlgebra (quadMinus n K b c))
      (((minusFrame n b c).longRoot hij s t (.ofAdd a') :
        spinGroup (quadMinus n K b c)) : CliffordAlgebra (quadMinus n K b c)) := by
    rw [HypFrame.coe_longRoot]
    exact commute_one_add_smul_of_ne_zero ha hcomm a'
  exact Subtype.ext (by simpa using hky.symm.eq)

private theorem rckSOmMG_ht_two {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {γ : Fin (minusDatum 2 hirr).rank → ℤ} {i : Fin (2 - 1)} {s : Bool}
    (h : toStdB (2 - 1) γ = Pi.single i (boolSign s)) : ht γ = boolSign s := by
  have h1 := ht_of_toStdB_eq_single (n := 2 - 1) h
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  refine h1.trans ?_
  rw [hi]
  simp

private theorem rckSOmMG_ggLongRoot_two {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (minusDatum 2 hirr).rank → ℤ} (hβ : β ∈ (minusDatum 2 hirr).roots) :
    GGLongRoot (minusDatum 2 hirr) β := by
  have hmax : ∀ δ ∈ (minusDatum 2 hirr).roots, ht δ ≤ 1 := by
    intro δ hδ
    rcases exists_toStdB_eq_of_mem_roots (n := 2) hδ with ⟨i, j, hij, -⟩ | ⟨i, s', hδs⟩
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    · rw [rckSOmMG_ht_two hirr hδs]
      cases s' <;> simp [boolSign]
  rcases exists_toStdB_eq_of_mem_roots (n := 2) hβ with ⟨i, j, hij, -⟩ | ⟨i, s, hs⟩
  · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
  · cases s
    ·
      have hneg : toStdB (2 - 1) (-β) = Pi.single i (boolSign true) := by
        have h1 : toStdB (2 - 1) (-β) = -toStdB (2 - 1) β := toStdB_neg (n := 2 - 1) β
        refine h1.trans ?_
        rw [hs]
        have e1 : boolSign false = -1 := by simp [boolSign]
        have e2 : boolSign true = 1 := by simp [boolSign]
        rw [e1, e2, Pi.single_neg, neg_neg]
      have hht : ht (-β) = 1 := by
        rw [rckSOmMG_ht_two hirr hneg]
        simp [boolSign]
      refine ⟨(coxeterMatrix (minusDatum 2 hirr).isFiniteType).toCoxeterSystem.simple i, -β,
        ?_, fun δ hδ => ?_, ?_⟩
      · rw [minusDatum_roots, rootsB_eq]
        exact Or.inr ⟨i, 1, Or.inl rfl, by rw [hneg]; simp [boolSign]⟩
      · have h1 : ht δ ≤ 1 := hmax δ hδ
        rw [← hht] at h1
        exact h1
      · erw [weylAction_simple]
        apply toStdB_injective (n := 2 - 1)
        have hk : ¬ (i : ℕ) + 1 < 2 - 1 := by have := i.isLt; omega
        have hrefl := toStdB_reflection_short_of_not_lt (n := 2) (k := i) hk hneg
        refine Eq.trans ?_ hrefl.symm
        rw [hs]
        simp [shortWeylBool, boolSign]
    ·
      have hht : ht β = 1 := by
        rw [rckSOmMG_ht_two hirr hs]
        simp [boolSign]
      refine ⟨1, β, hβ, fun δ hδ => ?_, by simp⟩
      have h1 : ht δ ≤ 1 := hmax δ hδ
      rw [← hht] at h1
      exact h1

theorem rckLemmaHCore_OmM
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .POmegaMinus m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaMinus m g).D.roots) (hL : ¬ GGLongRoot (ggU .POmegaMinus m g).D β)
    (h2 : 2 • β ∉ (ggU .POmegaMinus m g).D.roots) : RCKLemmaHCore (ggU .POmegaMinus m g) β := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm2 : 2 ≤ m := rckOmM_two_le hg hβ
  have hmain : RCKLemmaHCore
      ⟨spinGroup (quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2),
        minusDatum m (minusCoeffs_irr 2 g)⟩ β := by
    have hβ' : β ∈ (minusDatum m (minusCoeffs_irr 2 g)).roots := by
      change β ∈ (ggU .POmegaMinus m g).D.roots
      exact hβ
    have hL' : ¬ GGLongRoot (minusDatum m (minusCoeffs_irr 2 g)) β := by
      change ¬ GGLongRoot (ggU .POmegaMinus m g).D β
      exact hL
    rcases exists_toStdB_eq_of_mem_roots (n := m) hβ' with
      ⟨i, j, hij, s, t, hst⟩ | ⟨i, s, hs⟩
    ·
      intro x hx hx1
      exact (GGRootNorm.pCoreOf_le _).trans
        (rckSOmMG_cent_long (minusCoeffs_irr 2 g) hij s t hst x hx hx1)
    ·
      have hm3 : 3 ≤ m := by
        by_contra hm
        have hm_eq : m = 2 := by omega
        subst hm_eq
        exact absurd (rckSOmMG_ggLongRoot_two (minusCoeffs_irr 2 g) hβ') hL'
      intro x hx hx1
      rw [show (minusDatum m (minusCoeffs_irr 2 g)).rootGroup β =
            (twShortRoot m (minusCoeffs_irr 2 g) i s).range from
          minusRootGroup_eq_short m (minusCoeffs_irr 2 g) i s hs] at hx
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hx
      have hp : Multiplicative.toAdd q ≠ 0 := by
        intro hp0
        have hq1 : q = 1 := by
          apply Multiplicative.toAdd.injective
          simp [hp0]
        apply hx1
        rw [← hq, hq1, map_one]
      have hle := rckSOmM_core_of_pCore (minusCoeffs_irr 2 g)
        (rckSOmM_pCore_le (i := i) (s := s) (minusCoeffs_irr 2 g) hm3 hp)
      rw [← hq]
      simpa [Spin.Twisted.minusDatum, minusRootGroup_eq_short m (minusCoeffs_irr 2 g) i s hs]
        using hle
  change RCKLemmaHCore
    ⟨spinGroup (quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2),
      minusDatum m (minusCoeffs_irr 2 g)⟩ β
  exact hmain

theorem rckK2NbrRootSubShortAt_OmM
    : RCKK2NbrRootSubShortAt .POmegaMinus := by
  intro X _ _ K R m g β ht hg hβ hL hS h2 hvia r hr hr1
  exact rckGL1_of_core ht hg (fun _ => rckOmM_two_le hg hβ)
    (rckLemmaHCore_OmM hg hβ hL h2) hvia hr hr1

end CFSG.StandardType.RCKC1
