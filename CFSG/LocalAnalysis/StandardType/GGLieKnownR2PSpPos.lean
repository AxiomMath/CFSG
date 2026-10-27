module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSUPos
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLPos

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.LieKnownR2.PSp

@[expose] def GGSixPSpPosExplicit :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    CFSG.StandardType.ClassicalPosition.GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x →
  ∃ (R Rm : Subgroup X),
        R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .PSp n f p ψ R Rm ∧ 1 ≤ f ∧
        ((∃ (mJ : ℕ) (βJ : Fin (ggU .PSp mJ f).D.rank → ℤ), mJ < n ∧
            βJ ∈ (ggU .PSp mJ f).D.roots ∧ GGRootVia (ggU .PSp mJ f) J R βJ ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              ∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), mJ < mK ∧
                βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK) ∨
          (∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ), kJ + 1 ≤ n ∧
            βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
                βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
              (∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), kJ + 1 ≤ mK ∧
                βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK)) ∨
          (∃ (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ), m'J ≤ n ∧
            βJ ∈ (ggU .PSU m'J f).D.roots ∧ GGRootVia (ggU .PSU m'J f) J R βJ ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              (∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
                βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
                GGRootVia (ggU .PSU m'K f) K R βK) ∨
              (∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), m'J ≤ mK ∧
                βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK)))

private theorem l10sdsp_card_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 := by
  have h := Polynomial.SplittingField.adjoin_rootSet
    (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2))
  have hpoly : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)) = 0 := by simp
  have hempty : (Polynomial.X ^ 2 ^ 0 - Polynomial.X :
      Polynomial (ZMod 2)).rootSet (GaloisField 2 0) = ∅ := by
    ext x
    simp only [Polynomial.mem_rootSet, hpoly, ne_eq, not_true_eq_false, false_and,
      Set.mem_empty_iff_false]
  change Algebra.adjoin (ZMod 2) ((Polynomial.X ^ 2 ^ 0 - Polynomial.X :
    Polynomial (ZMod 2)).rootSet (GaloisField 2 0)) = ⊤ at h
  rw [hempty, Algebra.adjoin_empty] at h
  have hsurj : Function.Surjective (algebraMap (ZMod 2) (GaloisField 2 0)) := by
    intro x
    have : x ∈ (⊥ : Subalgebra (ZMod 2) (GaloisField 2 0)) := by rw [h]; trivial
    exact Algebra.mem_bot.mp this
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap (ZMod 2) (GaloisField 2 0)).injective,
    hsurj⟩), Nat.card_zmod]

private theorem l10sdsp_ns_of_component {X : Type} [Group X] {J G₀ D : Subgroup X}
    (h : CFSG.Assembly.IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    ¬ Group.IsSolvable ↥J := by
  haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr h.2.2.1
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := h.2.2.2
  haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  exact Group.IsPerfect.not_isSolvable ↥J

private theorem l10sdsp_innerNoCentral_sp
    {f mK : ℕ} (hf : 1 ≤ f) (hmK : 2 ≤ mK) (hne : (mK, 2 ^ f) ≠ (2, 2))
    {X : Type} [Group X] [Finite X]
    (φK : (ggU .PSp mK f).K →* X)
    (hker : φK.ker ≤ Subgroup.center (ggU .PSp mK f).K)
    {βK : Fin (ggU .PSp mK f).D.rank → ℤ} (hβK : βK ∈ (ggU .PSp mK f).D.roots)
    (uK : (ggU .PSp mK f).K) :
    GGRootInnerAt φK.range (ggRootSub (ggU .PSp mK f).D φK βK uK) ∧
      GGRootNoCentralAt φK.range (ggRootSub (ggU .PSp mK f).D φK βK uK) :=
  ⟨ggRootInnerAt_ggU_psp hmK φK hker hβK uK,
   ggRootNoCentralAt_ggU_psp ⟨Nat.prime_two, hf, hmK, hne⟩ φK hker hβK uK⟩

private theorem l10sdsp_innerNoCentral_su
    {f m'K : ℕ} (hm'K : 3 ≤ m'K) (hne : ¬ (m'K = 3 ∧ f = 1))
    {X : Type} [Group X] [Finite X]
    (φK : (ggU .PSU m'K f).K →* X)
    (hker : φK.ker ≤ Subgroup.center (ggU .PSU m'K f).K)
    {βK : Fin (ggU .PSU m'K f).D.rank → ℤ} (hβK : βK ∈ (ggU .PSU m'K f).D.roots)
    (hlong : GGLongRoot (ggU .PSU m'K f).D βK)
    (uK : (ggU .PSU m'K f).K) :
    GGRootInnerAt φK.range (ggRootSub (ggU .PSU m'K f).D φK βK uK) ∧
      GGRootNoCentralAt φK.range (ggRootSub (ggU .PSU m'K f).D φK βK uK) :=
  ⟨PSU.ggRootInnerAt_ggU_psu hm'K hne φK hker hβK (Or.inl hlong) uK,
   PSU.ggRootNoCentralAt_ggU_psu hm'K hne φK hker hβK (Or.inl hlong) uK⟩

theorem jDim_sp
    {m f : ℕ} {X : Type} [Group X] (φ : (ggU .PSp m f).K →* X)
    (hns : ¬ Group.IsSolvable ↥φ.range) : 1 ≤ m ∧ (m = 1 → 2 ≤ f) := by
  constructor
  · by_contra hm
    have hm0 : m = 0 := by omega
    subst hm0
    haveI : Subsingleton ((ggU .PSp 0 f).K) :=
      inferInstanceAs (Subsingleton (StatedSp 0 (GaloisField 2 f)))
    haveI : Subsingleton ↥φ.range := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      exact Subtype.ext (by rw [← hx, ← hy, Subsingleton.elim x y])
    exact hns inferInstance
  · intro hm1
    by_contra hf
    subst hm1
    have hf01 : f = 0 ∨ f = 1 := by omega
    have hK : Nat.card (GaloisField 2 f) = 2 := by
      rcases hf01 with rfl | rfl
      · exact l10sdsp_card_galoisField_two_zero
      · simpa using GaloisField.card 2 1 (by norm_num)
    haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      CFSG.StandardType.isSolvable_specialLinear_of_card_eq_two (ι := Fin 2)
        (Q := GaloisField 2 f) (by simp) hK
    haveI : Group.IsSolvable (StatedSp 1 (GaloisField 2 f)) :=
      Group.isSolvable_of_surjective
        (f := (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
          (GaloisField 2 f)).toMonoidHom)
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
          (GaloisField 2 f)).surjective
    haveI : Group.IsSolvable ((ggU .PSp 1 f).K) :=
      inferInstanceAs (Group.IsSolvable (StatedSp 1 (GaloisField 2 f)))
    exact hns (Group.isSolvable_of_surjective φ.rangeRestrict_surjective)

theorem ggSixLieKnownPos_PSp_of_explicit
    (hpos : GGSixPSpPosExplicit) : GGSixLieKnownPos .PSp := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hadm : StatedLieAdmissible .PSp n 2 f := h3.admissible
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hH : CFSG.StandardType.ClassicalPosition.GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hf, hcases⟩ := hpos X n f ψ p G₀ B₁ D J L x hH
  have hB₁p : IsPGroup p B₁ := by
    intro b
    refine ⟨1, Subtype.ext ?_⟩
    simpa using h9.2 b b.2
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    rcases hcases with hcase1 | hcase2 | hcase3
    · obtain ⟨mJ, βJ, -, hβJ, hviaJ, hnbr⟩ := hcase1
      obtain ⟨φJ, hφJrange, hφJker, uJ, hRJdef⟩ := hviaJ
      obtain ⟨mK, βK, hlt, hβK, hviaK⟩ := hnbr e he hene K hKG hKcomp hJK hKne hKodd
      obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
      have hJns : ¬ Group.IsSolvable ↥φJ.range := by
        rw [hφJrange]
        exact l10sdsp_ns_of_component h15
      have hJpos : 1 ≤ mJ ∧ (mJ = 1 → 2 ≤ f) := jDim_sp φJ hJns
      have hmK2 : 2 ≤ mK := by omega
      have hne : (mK, 2 ^ f) ≠ (2, 2) := by
        intro hpair
        obtain ⟨hmK2', hpow⟩ := Prod.mk.inj hpair
        have hmJ1 : mJ = 1 := by omega
        have hf2 : 2 ≤ f := hJpos.2 hmJ1
        have hlt2 : 2 < 2 ^ f := by
          calc 2 = 2 ^ 1 := by norm_num
            _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have hmain := l10sdsp_innerNoCentral_sp hf hmK2 hne φK hφKker hβK uK
      rw [hφKrange, ← hRKdef] at hmain
      exact hmain
    · obtain ⟨kJ, βJ, hkJ, hβJ, hviaJ, hnbr⟩ := hcase2
      obtain ⟨φJ, hφJrange, hφJker, uJ, hRJdef⟩ := hviaJ
      have hJns : ¬ Group.IsSolvable ↥φJ.range := by
        rw [hφJrange]
        exact l10sdsp_ns_of_component h15
      have hdimJ := PSL.jDim_psl hf φJ hφJker hJns h5 h6 hB₁p
        (hφJrange ▸ h13) (hφJrange ▸ h14) h10 h12
      rcases hnbr e he hene K hKG hKcomp hJK hKne hKodd with
        ⟨kK, βK, hlt, hβK, hviaK⟩ | ⟨mK, βK, hle, hβK, hviaK⟩
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hmain := PSL.itemTwo_of_models hf hlt φJ hφJker hJns h5 h6 hB₁p
          (hφJrange ▸ h13) (hφJrange ▸ h14) h10 h12 φK hφKker hβK uK hRKdef
        rw [hφKrange] at hmain
        exact hmain
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hkJ1 : 1 ≤ kJ := by
          rcases hdimJ with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
        have hmK2 : 2 ≤ mK := by omega
        have hne : (mK, 2 ^ f) ≠ (2, 2) := by
          intro hpair
          obtain ⟨hmK2', hpow⟩ := Prod.mk.inj hpair
          have hkJeq : kJ = 1 := by omega
          have hf2 : 2 ≤ f := by
            rcases hdimJ with ⟨hf1, h3⟩ | ⟨hf2, h2⟩ | ⟨h3f, h1⟩ <;> omega
          have hlt2 : 2 < 2 ^ f := by
            calc 2 = 2 ^ 1 := by norm_num
              _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
          omega
        have hmain := l10sdsp_innerNoCentral_sp hf hmK2 hne φK hφKker hβK uK
        rw [hφKrange, ← hRKdef] at hmain
        exact hmain
    · obtain ⟨m'J, βJ, -, hβJ, hviaJ, hnbr⟩ := hcase3
      obtain ⟨φJ, hφJrange, hφJker, uJ, hRJdef⟩ := hviaJ
      have hJns : ¬ Group.IsSolvable ↥φJ.range := by
        rw [hφJrange]
        exact l10sdsp_ns_of_component h15
      have hJdim := PSU.jDim_selfDual_psu φJ hJns
      rcases hnbr e he hene K hKG hKcomp hJK hKne hKodd with
        ⟨m'K, βK, hlt, hβK, hlong, hviaK⟩ | ⟨mK, βK, hle, hβK, hviaK⟩
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hm'K3 : 3 ≤ m'K := by omega
        have hne : ¬ (m'K = 3 ∧ f = 1) := by
          rintro ⟨hm'K3', hf1⟩
          have hm'J2 : m'J = 2 := by omega
          have hf2 : 2 ≤ f := hJdim.2 (by omega)
          omega
        have hmain := l10sdsp_innerNoCentral_su hm'K3 hne φK hφKker hβK hlong uK
        rw [hφKrange, ← hRKdef] at hmain
        exact hmain
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hmK2 : 2 ≤ mK := by omega
        have hne : (mK, 2 ^ f) ≠ (2, 2) := by
          intro hpair
          obtain ⟨hmK2', hpow⟩ := Prod.mk.inj hpair
          have hm'J2 : m'J = 2 := by omega
          have hf2 : 2 ≤ f := hJdim.2 (by omega)
          have hlt2 : 2 < 2 ^ f := by
            calc 2 = 2 ^ 1 := by norm_num
              _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
          omega
        have hmain := l10sdsp_innerNoCentral_sp hf hmK2 hne φK hφKker hβK uK
        rw [hφKrange, ← hRKdef] at hmain
        exact hmain
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    obtain ⟨β, hβ, -, u, hRβ, hRmβ⟩ := hpos0
    exact itemThree_ggU_psp hn2 ψ h2 hβ u hRβ Y hY hYnorG hYnorR hcomm

theorem ggSixLieKnown_PSp_of_explicit
    (hpos : GGSixPSpPosExplicit) : GGSixLieKnown .PSp :=
  ggSixLieKnown_of_pos_PSp (ggSixLieKnownPos_PSp_of_explicit hpos)

end CFSG.StandardType.LieKnownR2.PSp
