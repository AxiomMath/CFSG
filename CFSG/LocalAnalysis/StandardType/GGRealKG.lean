module

public import CFSG.LocalAnalysis.StandardType.GGRealQFour
public import CFSG.LocalAnalysis.StandardType.GGRealKGTorusComponents
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpJr
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpSeven
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup

theorem ggReflRealizedIn_of_rootSL2 {G : Type} [Group G] [Finite G] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNT : GGNoTransvection p Bs) (hX : commutator X = ⊤) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : X ⧸ center X ≃* R) (hBsN : Bs ≤ normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range)
    (hT : GGTorusRootSL2 p r R I) : GGReflRealizedIn p Bs X :=
  ggReflRealizedIn_of_torusComponents hp hp2 hBs hSC hNT hX θ hBsN hBsI hr h3
    (ggTorusComponents_of_rootSL2 hT)

@[expose] def GGRealRootLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ≠ 2 ∧ 2 ≤ lab.n ∧ p ∣ 4 ^ lab.n - 1

theorem not_ggLabelIso_fieldTwo {a b : LargeEvenLabel} (h : GGLabelIso a b) (ha : 2 ≤ a.n)
    (hb : b = ⟨.E6, 0, 1⟩ ∨ b = ⟨.A, 8, 1⟩) : False := by
  obtain ⟨t, l, n⟩ := a
  dsimp only at ha
  rcases hb with rfl | rfl <;> simp [GGLabelIso] at h <;> omega

theorem ggRealRootLabel_three_dvd (n : ℕ) : 3 ∣ 4 ^ n - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 n

@[expose] def GGRealRootSL2On (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → GGRealRootLabel p lab →
    S p lab → LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I

theorem ggRealRootSL2On_typeA : GGRealRootSL2On fun p lab => GGTypeALabel p lab := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with ⟨h, hpn, hpl⟩ | ⟨h, hl3, hpn⟩ | ⟨h, hl2, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact TypeA.recipeLinear_rootSL2 hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl3 hpn
    subst h hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine TypeA.recipeLinear_rootSL2 hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl2 hpn
    subst h hl2
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine TypeA.recipeLinear_rootSL2 hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end CFSG.StandardType

end
