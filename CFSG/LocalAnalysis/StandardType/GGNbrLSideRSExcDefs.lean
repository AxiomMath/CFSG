module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem ggNbrLSideRSExc_four_pow_mod (k : ℕ) : 4 ^ k % 3 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ]; omega

theorem ggNbrLSideRSExc_three_dvd_two_pow_add_one_iff (e : ℕ) : 3 ∣ 2 ^ e + 1 ↔ Odd e := by
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · have h : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
    have h1 := ggNbrLSideRSExc_four_pow_mod k
    rw [h]
    constructor
    · intro hd
      omega
    · rintro ⟨m, hm⟩
      omega
  · have h : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
    have h1 := ggNbrLSideRSExc_four_pow_mod k
    rw [h]
    exact ⟨fun _ => ⟨k, rfl⟩, fun _ => by omega⟩

noncomputable abbrev GGNbrLSideRSExcComp
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) :
    Subgroup (ModGL τ L) :=
  rationalComponent S.ρ S.Γ (rootCharHom a) i

@[expose] def GGNbrLSideRSExcPSL3
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) (Q : ℕ) : Prop :=
  rootDiagUnit τ a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
    CFSG.IsQuasisimple ↥(GGNbrLSideRSExcComp S a i) ∧ 4 ≤ Q ∧ 3 ∣ Q - 1 ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Q ∧
      Nonempty (↥(GGNbrLSideRSExcComp S a i) ⧸ Subgroup.center ↥(GGNbrLSideRSExcComp S a i) ≃*
        projectiveSL 3 F)

@[expose] def GGNbrLSideRSExcU2 :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀), (2 : L) = 0 →
    ∀ (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) (Q : ℕ),
      GGNbrLSideRSExcPSL3 S a i Q →
        twistKind S.ρ (rootCharHom a) i = .inner ∧
        compRank (componentRoots (rootCharHom a) i) = 2 ∧
        (componentRoots (rootCharHom a) i).ncard = 6 ∧
        Q = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)

@[expose] def GGNbrLSideRSExcU3 :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀), (2 : L) = 0 →
    ∀ (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) (Q : ℕ),
      GGNbrLSideRSExcPSL3 S a i Q →
      twistKind S.ρ (rootCharHom a) i = .inner →
      compRank (componentRoots (rootCharHom a) i) = 2 →
      (componentRoots (rootCharHom a) i).ncard = 6 →
      ¬ 3 ∣ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) →
      ∀ y ∈ S.D.model, y ∈ Subgroup.centralizer {rootDiagUnit τ a} → y ^ 3 = 1 →
        ∀ α : MulAut (↥(GGNbrLSideRSExcComp S a i) ⧸ Subgroup.center ↥(GGNbrLSideRSExcComp S a i)),
          GGNbrLSideInduces (MulAut.conj y) (GGNbrLSideRSExcComp S a i) α →
            GGInnDiagPSL3 Q
              (↥(GGNbrLSideRSExcComp S a i) ⧸ Subgroup.center ↥(GGNbrLSideRSExcComp S a i)) α

@[expose] def GGNbrLSideRSExcU4 :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    rootDiagUnit τ a ∈ S.D.torus →
    compRank (componentRoots (rootCharHom a) i) = 2 →
    (componentRoots (rootCharHom a) i).ncard = 6 →
    2 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ τ.rank

@[expose] def GGNbrLSideRSExcLangDich :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀), (2 : L) = 0 →
    ∀ n : ℕ, S.D.q = 2 ^ n →
    ∀ (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) (Q : ℕ),
      GGNbrLSideRSExcPSL3 S a i Q →
      ∀ y ∈ S.D.model, y ∈ Subgroup.centralizer {rootDiagUnit τ a} → y ^ 3 = 1 →
        ∀ α : MulAut (↥(GGNbrLSideRSExcComp S a i) ⧸ Subgroup.center ↥(GGNbrLSideRSExcComp S a i)),
          GGNbrLSideInduces (MulAut.conj y) (GGNbrLSideRSExcComp S a i) α →
            GGInnDiagPSL3 Q
                (↥(GGNbrLSideRSExcComp S a i) ⧸ Subgroup.center ↥(GGNbrLSideRSExcComp S a i)) α ∨
              GGNbrLSideLargeRank ⟨.A, τ.rank, n⟩

theorem ggNbrLSideRSExc_langDich_of_U234
    (h2 : GGNbrLSideRSExcU2) (h3 : GGNbrLSideRSExcU3) (h4 : GGNbrLSideRSExcU4) :
    GGNbrLSideRSExcLangDich := by
  intro τ L _ _ p₀ S hL n hn a i Q hQ y hy hyc hy3 α hα
  obtain ⟨hk, hr2, hr6, hQs⟩ := h2 τ L p₀ S hL a i Q hQ
  obtain ⟨hT, -, -, -, hQ4, hQ3, -⟩ := id hQ
  by_cases hs : 3 ∣ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  · right
    have hs0 : 0 < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
      rcases Nat.eq_zero_or_pos
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) with h0 | h0
      · rw [h0, pow_zero] at hQs
        omega
      · exact h0
    have h3Q : 3 ∣ (2 ^ n) ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) - 1 := by
      rw [← hn, ← hQs]
      exact hQ3
    have h4' := h4 τ L p₀ S a i hT hr2 hr6
    exact ggNbrLSideLargeRank_of_pow (lab := ⟨.A, τ.rank, n⟩) hs0 hs h3Q
      (by simpa [ggNbrLSideRank] using h4')
  · left
    exact h3 τ L p₀ S hL a i Q hQ hk hr2 hr6 hs y hy hyc hy3 α hα

@[expose] def GGNbrLSideRSExcTransport
    (τ : Tag) {R : Type} [Group R] (I : Set (MulAut R)) (q : ℕ) : Prop :=
  ∀ φ ∈ I, ∀ ψ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → ψ ^ 3 = 1 → φ * ψ = ψ * φ →
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (p₀ : ℕ) (S : LangSetup τ L p₀)
      (a : Fin τ.rank → Lˣ) (e : R ≃* ↥S.Γ) (y : ModGL τ L),
      (2 : L) = 0 ∧ S.D.q = q ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧
      rootDiagUnit τ a ≠ 1 ∧ y ∈ S.D.model ∧ y ∈ Subgroup.centralizer {rootDiagUnit τ a} ∧
      y ^ 3 = 1 ∧
      (∀ r : R, ((e (φ r) : ↥S.Γ) : ModGL τ L) =
        rootDiagUnit τ a * ((e r : ↥S.Γ) : ModGL τ L) * (rootDiagUnit τ a)⁻¹) ∧
      (∀ r : R, ((e (ψ r) : ↥S.Γ) : ModGL τ L) = y * ((e r : ↥S.Γ) : ModGL τ L) * y⁻¹)

@[expose] def GGNbrLSideRSExcU1 :
    Prop :=
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    GGNbrLSideRSExcTransport Tag.G2
      (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false))
      (2 ^ n)) ∧
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    GGNbrLSideRSExcTransport Tag.F4
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false))
      (2 ^ n)) ∧
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    GGNbrLSideRSExcTransport Tag.E6
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K (LargeEvenChevH (LargeEvenCartanE 6) K false))
      (2 ^ n)) ∧
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    GGNbrLSideRSExcTransport Tag.E7
      (LargeEvenChevIDImage (LargeEvenCartanE 7) K (LargeEvenChevH (LargeEvenCartanE 7) K false))
      (2 ^ n)) ∧
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    GGNbrLSideRSExcTransport Tag.E8
      (LargeEvenChevIDImage (LargeEvenCartanE 8) K (LargeEvenChevH (LargeEvenCartanE 8) K false))
      (2 ^ n)) ∧
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    GGNbrLSideRSExcTransport Tag.E6
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) (2 ^ n)) ∧
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 3 →
    GGNbrLSideRSExcTransport Tag.D4
      (LargeEvenChevIDImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) (2 ^ n))

end CFSG.StandardType

end
