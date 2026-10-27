module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLDims
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPSL

public section

namespace CFSG.StandardType.LieKnownR2.PSL

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos

@[expose] def GGSixPSLPosExplicit :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSL n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    CFSG.StandardType.ClassicalPosition.GGSixPosHyp .PSL n f ψ p G₀ B₁ D J L x →
    ∃ (R Rm : Subgroup X) (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
      R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .PSL n f p ψ R Rm ∧ 1 ≤ f ∧ kJ + 1 < n ∧
      βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
        CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
        Odd (Nat.card (Subgroup.center ↥K)) →
        ∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
          βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kK + 1) f) K R βK

theorem psl_dim_of_jDim {f kJ k : ℕ}
    (hJ : (f = 1 ∧ 3 ≤ kJ) ∨ (f = 2 ∧ 2 ≤ kJ) ∨ (3 ≤ f ∧ 1 ≤ kJ)) (hlt : kJ < k) :
    (f = 1 ∧ 4 ≤ k) ∨ (2 ≤ f ∧ 3 ≤ k) ∨ (3 ≤ f ∧ 2 ≤ k) := by
  omega

theorem itemTwo_ggU_psl
    {f k : ℕ} (hdim : (f = 1 ∧ 4 ≤ k) ∨ (2 ≤ f ∧ 3 ≤ k) ∨ (3 ≤ f ∧ 2 ≤ k))
    {X : Type} [Group X] [Finite X] (φ : (ggU .PSL (k + 1) f).K →* X)
    (hker : φ.ker ≤ Subgroup.center (ggU .PSL (k + 1) f).K)
    {β : Fin (ggU .PSL (k + 1) f).D.rank → ℤ} (hβ : β ∈ (ggU .PSL (k + 1) f).D.roots)
    (u : (ggU .PSL (k + 1) f).K) {R : Subgroup X}
    (hR : R = ggRootSub (ggU .PSL (k + 1) f).D φ β u) :
    GGRootInnerAt φ.range R ∧ GGRootNoCentralAt φ.range R := by
  subst hR
  refine ⟨ggRootInnerAt_ggU_psl (m := k) (g := f) hdim φ hker hβ u, ?_⟩
  have hf : 1 ≤ f := by
    rcases hdim with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hk : 1 ≤ k := by
    rcases hdim with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hexc : ¬ (k = 2 ∧ f = 1) := by
    rintro ⟨rfl, rfl⟩
    rcases hdim with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hodd2 : Odd (Nat.card (GaloisField 2 f) - 1) := by
    rw [hcard]
    exact Nat.Even.sub_odd (m := 2 ^ f) (n := 1) Nat.one_le_two_pow
      ((even_two (α := ℕ)).pow_of_ne_zero (by omega)) odd_one
  have hdvd : Nat.card φ.ker ∣ Nat.card (GaloisField 2 f) - 1 :=
    (Subgroup.card_dvd_of_le hker).trans
      ((CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := k + 1) (by omega)
        (GaloisField 2 f)).trans (Nat.gcd_dvd_right _ _))
  exact CFSG.StandardType.LieKnownR2.SpecialLinearNC.ggRootNoCentralAt_specialLinear
    hk hf hexc φ hker (Odd.of_dvd_nat hodd2 hdvd) hβ u

theorem itemTwo_of_models
    {f kJ kK : ℕ} (hf : 1 ≤ f) (hlt : kJ < kK) {X : Type} [Group X] [Finite X]
    (φJ : Matrix.SpecialLinearGroup (Fin (kJ + 1)) (GaloisField 2 f) →* X)
    (hJker : φJ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (kJ + 1)) (GaloisField 2 f)))
    (hJns : ¬ Group.IsSolvable ↥φJ.range) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D : Subgroup X} (hB₁p : IsPGroup p B₁)
    (hB₁ : B₁ ≤ Subgroup.normalizer (φJ.range : Set X))
    (hBD : B₁ ⊓ Subgroup.centralizer (φJ.range : Set X) = D)
    (hcard : p ^ 4 ≤ Nat.card B₁) (hD : Nat.card D = p ^ 2)
    (φK : (ggU .PSL (kK + 1) f).K →* X)
    (hker : φK.ker ≤ Subgroup.center (ggU .PSL (kK + 1) f).K)
    {β : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ} (hβ : β ∈ (ggU .PSL (kK + 1) f).D.roots)
    (u : (ggU .PSL (kK + 1) f).K) {R : Subgroup X}
    (hR : R = ggRootSub (ggU .PSL (kK + 1) f).D φK β u) :
    GGRootInnerAt φK.range R ∧ GGRootNoCentralAt φK.range R :=
  itemTwo_ggU_psl
    (psl_dim_of_jDim (jDim_psl hf φJ hJker hJns hp hp2 hB₁p hB₁ hBD hcard hD) hlt)
    φK hker hβ u hR

theorem itemThree_of_models
    {f kJ m : ℕ} (hf : 1 ≤ f) (hlt : kJ < m) {X : Type} [Group X] [Finite X]
    (φJ : Matrix.SpecialLinearGroup (Fin (kJ + 1)) (GaloisField 2 f) →* X)
    (hJker : φJ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (kJ + 1)) (GaloisField 2 f)))
    (hJns : ¬ Group.IsSolvable ↥φJ.range) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D : Subgroup X} (hB₁p : IsPGroup p B₁)
    (hB₁ : B₁ ≤ Subgroup.normalizer (φJ.range : Set X))
    (hBD : B₁ ⊓ Subgroup.centralizer (φJ.range : Set X) = D)
    (hcard : p ^ 4 ≤ Nat.card B₁) (hD : Nat.card D = p ^ 2)
    (ψ : (ggU .PSL (m + 1) f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) f).K)
    {β : Fin (ggU .PSL (m + 1) f).D.rank → ℤ} (hβ : β ∈ (ggU .PSL (m + 1) f).D.roots)
    (u : (ggU .PSL (m + 1) f).K) {R : Subgroup X}
    (hR : R = ggRootSub (ggU .PSL (m + 1) f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) :=
  itemThree_ggU_psl
    (psl_dim_of_jDim (jDim_psl hf φJ hJker hJns hp hp2 hB₁p hB₁ hBD hcard hD) hlt)
    ψ hker hβ u hR

theorem ggSixLieKnownPos_PSL_of_explicit
    (hpos : GGSixPSLPosExplicit) : GGSixLieKnownPos .PSL := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hadm : StatedLieAdmissible .PSL n 2 f := h3.admissible
  have hn2 : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hH : CFSG.StandardType.ClassicalPosition.GGSixPosHyp .PSL (m + 1) f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  obtain ⟨R, Rm, kJ, βJ, hRJ, hRmJ, hpos0, hf, hkJ, hβJ, hvia, hnbr⟩ :=
    hpos X (m + 1) f ψ p G₀ B₁ D J L x hH
  obtain ⟨φJ, hφJrange, hφJker, uJ, hRJdef⟩ := hvia
  have hJns : ¬ Group.IsSolvable ↥φJ.range := by
    rw [hφJrange]
    haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr h15.2.2.1
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := h15.2.2.2
    haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
    exact Group.IsPerfect.not_isSolvable ↥J
  have hB₁p : IsPGroup p B₁ := by
    intro b
    refine ⟨1, Subtype.ext ?_⟩
    simpa using h9.2 b b.2
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    obtain ⟨kK, βK, hlt, hβK, hviaK⟩ := hnbr e he hene K hKG hKcomp hJK hKne hKodd
    obtain ⟨φK, hφKrange, hφKker, uK, hRK⟩ := hviaK
    have hmain := itemTwo_of_models hf hlt φJ hφJker hJns h5 h6 hB₁p
      (hφJrange ▸ h13) (hφJrange ▸ h14) h10 h12 φK hφKker hβK uK hRK
    rwa [hφKrange] at hmain
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    obtain ⟨β, hβ, hlong, u, hRβ, hRmβ⟩ := hpos0
    exact itemThree_of_models hf (by omega) φJ hφJker hJns h5 h6 hB₁p
      (hφJrange ▸ h13) (hφJrange ▸ h14) h10 h12 ψ h2 hβ u hRβ Y hY hYnorG hYnorR hcomm

theorem ggSixLieKnown_PSL_of_explicit
    (hpos : GGSixPSLPosExplicit) : GGSixLieKnown .PSL :=
  ggSixLieKnown_of_pos_PSL (ggSixLieKnownPos_PSL_of_explicit hpos)

theorem ggSixLieKnown_PSL :
    GGSixLieKnown .PSL :=
  ggSixLieKnown_PSL_of_explicit (fun X _ _ n f ψ p G₀ B₁ D J L x hH =>
    CFSG.StandardType.ClassicalPosition.ggSixPSLPosExplicit_holds n f ψ p G₀ B₁ D J L x hH)

end CFSG.StandardType.LieKnownR2.PSL
