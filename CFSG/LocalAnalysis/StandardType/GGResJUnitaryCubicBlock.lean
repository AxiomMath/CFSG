module

public import CFSG.LocalAnalysis.StandardType.GGHalfShear
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGResJScalarPairing
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUFrame
public import CFSG.LocalAnalysis.StandardType.GGResJCubicBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3UniRec
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentUniLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniScalar
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryActorNormalization
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.LargeExtraspecial.S97RZStar
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTv
public import CFSG.LocalAnalysis.StandardType.GGFFLocal

public section

namespace CFSG.StandardType.ResJUnitaryCubicBlock

open CFSG.StandardType
open CFSG.StandardType.ResJCubicBlock
open CFSG.LocalAnalysis.ComponentInitial
open scoped BigOperators

variable {K E : Type} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {s : ℕ} [NeZero s] {f : ℕ}

@[expose] noncomputable def Hform (τ : E →+* E) (u v : Fin s → E) : E :=
  ∑ i, τ (u i) * v i

@[expose] noncomputable def Bform (τ : E →+* E) (u v : Fin s → E) : K :=
  Algebra.trace K E (Hform τ u v)

omit [Fintype E] [FiniteDimensional K E] in
lemma bar_on_K (hKdata : UnitaryFieldData 2 f K) (hEdata : UnitaryFieldData 2 (3 * f) E)
    (c : K) :
    hEdata.bar (algebraMap K E c) = algebraMap K E (hKdata.bar c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, ← map_pow]
  congr 1
  have hc : c ^ 2 ^ (2 * f) = c := by
    rw [← hKdata.card, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hpow : 2 ^ (3 * f) = 2 ^ (2 * f) * 2 ^ f := by
    rw [show 3 * f = 2 * f + f by ring, pow_add]
  rw [hpow, pow_mul, hc]

omit [FiniteDimensional K E] in
lemma trace_frob (a : E) :
    Algebra.trace K E (frob (K := K) (E := E) a) = Algebra.trace K E a := by
  let σ : E ≃ₐ[K] E := FiniteField.frobeniusAlgEquivOfAlgebraic K E
  have hfrob : frob (K := K) (E := E) a = σ a := by
    rw [frob_apply]
    rfl
  rw [hfrob]
  exact Algebra.trace_eq_of_algEquiv σ a

omit [Fintype E] [FiniteDimensional K E] in
lemma frob_mul (a b : E) :
    frob (K := K) (E := E) (a * b) = frob (K := K) (E := E) a * frob (K := K) (E := E) b := by
  rw [frob_apply, frob_apply, frob_apply, mul_pow]

omit [Fintype E] [FiniteDimensional K E] in
lemma bar_frob (hEdata : UnitaryFieldData 2 (3 * f) E) (a : E) :
    hEdata.bar (frob (K := K) (E := E) a) = frob (K := K) (E := E) (hEdata.bar a) := by
  rw [frob_apply (K := K) (E := E), UnitaryFieldData.bar_apply,
    UnitaryFieldData.bar_apply, frob_apply (K := K) (E := E)]
  rw [← pow_mul, ← pow_mul]
  congr 1
  rw [mul_comm]

omit [FiniteDimensional K E] in
lemma frobFirst_isometry_B (hEdata : UnitaryFieldData 2 (3 * f) E)
    (u v : Fin s → E) :
    Bform (K := K) (E := E) hEdata.bar
        (frobFirst (K := K) (E := E) (s := s) u)
        (frobFirst (K := K) (E := E) (s := s) v) =
      Bform (K := K) (E := E) hEdata.bar u v := by
  change Algebra.trace K E (∑ i, hEdata.bar (frobFirst u i) * frobFirst v i) =
    Algebra.trace K E (∑ i, hEdata.bar (u i) * v i)
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : i = 0
  · subst hi
    rw [frobFirst_apply, if_pos rfl, frobFirst_apply, if_pos rfl]
    rw [← frob_apply (K := K) (E := E), ← frob_apply (K := K) (E := E)]
    rw [bar_frob hEdata]
    rw [← frob_mul]
    exact trace_frob _
  · rw [frobFirst_apply, if_neg hi, frobFirst_apply, if_neg hi]

omit [Fintype K] in
lemma bar_zeta_mul (hKdata : UnitaryFieldData 2 f K) (h3q : 3 ∣ 2 ^ f + 1)
    {ζ : K} (hζ3 : ζ ^ 3 = 1) :
    hKdata.bar ζ * ζ = 1 := by
  have hbζ : hKdata.bar ζ = ζ ^ 2 :=
    CFSG.LieType.SeitzGeneration.bar_eq_sq_of_cube hKdata h3q hζ3
  rw [hbζ]
  calc ζ ^ 2 * ζ = ζ ^ 3 := by ring
    _ = 1 := hζ3

omit [Fintype E] [FiniteDimensional K E] in
lemma zetaLin_isometry_B (hKdata : UnitaryFieldData 2 f K)
    (hEdata : UnitaryFieldData 2 (3 * f) E)
    (h3q : 3 ∣ 2 ^ f + 1) {ζ : K} (hζ3 : ζ ^ 3 = 1)
    (u v : Fin s → E) :
    Bform (K := K) (E := E) hEdata.bar
        (zetaLin (ζ := ζ) (K := K) (E := E) (s := s) u)
        (zetaLin (ζ := ζ) (K := K) (E := E) (s := s) v) =
      Bform (K := K) (E := E) hEdata.bar u v := by
  change Algebra.trace K E
      (∑ i, hEdata.bar (zetaLin (ζ := ζ) (K := K) (E := E) (s := s) u i) *
        zetaLin (ζ := ζ) (K := K) (E := E) (s := s) v i) =
    Algebra.trace K E (∑ i, hEdata.bar (u i) * v i)
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : i = 0
  · subst hi
    rw [zetaLin_apply, if_pos rfl, zetaLin_apply, if_pos rfl]
    have hbζ : hKdata.bar ζ * ζ = 1 := bar_zeta_mul hKdata h3q hζ3
    have hbE : hEdata.bar (algebraMap K E ζ) = algebraMap K E (hKdata.bar ζ) :=
      bar_on_K hKdata hEdata ζ
    congr 1
    calc hEdata.bar (algebraMap K E ζ * u 0) * (algebraMap K E ζ * v 0)
        = (algebraMap K E (hKdata.bar ζ) * hEdata.bar (u 0)) *
            (algebraMap K E ζ * v 0) := by rw [map_mul, hbE]
      _ = (algebraMap K E (hKdata.bar ζ) * algebraMap K E ζ) *
            (hEdata.bar (u 0) * v 0) := by ring
      _ = algebraMap K E (hKdata.bar ζ * ζ) * (hEdata.bar (u 0) * v 0) := by rw [map_mul]
      _ = hEdata.bar (u 0) * v 0 := by rw [hbζ, map_one, one_mul]
  · rw [zetaLin_apply, if_neg hi, zetaLin_apply, if_neg hi]


@[expose] noncomputable def unitarySUV (B : (Fin s → E) → (Fin s → E) → K) : Subgroup (SLV K E s) where
  carrier := {g | ∀ x y, B ((g : GLV K E s) x) ((g : GLV K E s) y) = B x y}
  one_mem' := by
    intro x y
    simp
  mul_mem' := by
    intro g h hg hh x y
    change B (((g * h : SLV K E s) : GLV K E s) x)
      (((g * h : SLV K E s) : GLV K E s) y) = B x y
    rw [SpecialLinearGroup.coe_mul]
    change B ((g : GLV K E s) ((h : GLV K E s) x))
      ((g : GLV K E s) ((h : GLV K E s) y)) = B x y
    rw [hg, hh]
  inv_mem' := by
    intro g hg x y
    change B (((g⁻¹ : SLV K E s) : GLV K E s) x)
      (((g⁻¹ : SLV K E s) : GLV K E s) y) = B x y
    rw [SpecialLinearGroup.coe_inv]
    have h := hg (((g⁻¹ : SLV K E s) : GLV K E s) x)
      (((g⁻¹ : SLV K E s) : GLV K E s) y)
    simpa [LinearEquiv.apply_symm_apply] using h.symm

omit [Fintype E] [FiniteDimensional K E] [NeZero s] in
theorem mem_unitarySUV {B : (Fin s → E) → (Fin s → E) → K} {g : SLV K E s} :
    g ∈ unitarySUV B ↔ ∀ x y, B ((g : GLV K E s) x) ((g : GLV K E s) y) = B x y :=
  Iff.rfl

@[expose] noncomputable def conjUnitarySUV (B : (Fin s → E) → (Fin s → E) → K) (Y : GLV K E s)
    (hY : ∀ x y, B (Y x) (Y y) = B x y) (g : unitarySUV B) : unitarySUV B where
  val := conjSL (K := K) (E := E) (s := s) Y (g : SLV K E s)
  property := by
    intro x y
    change B ((conjSL (K := K) (E := E) (s := s) Y (g : SLV K E s) : GLV K E s) x)
      ((conjSL (K := K) (E := E) (s := s) Y (g : SLV K E s) : GLV K E s) y) = B x y
    rw [conjSL_coe]
    have hYinv : B ((Y⁻¹ : GLV K E s) x) ((Y⁻¹ : GLV K E s) y) = B x y := by
      have h := hY ((Y⁻¹ : GLV K E s) x) ((Y⁻¹ : GLV K E s) y)
      simpa [LinearEquiv.apply_symm_apply] using h.symm
    calc B ((Y * (g : GLV K E s) * Y⁻¹) x) ((Y * (g : GLV K E s) * Y⁻¹) y)
        = B (Y ((g : GLV K E s) ((Y⁻¹ : GLV K E s) x)))
            (Y ((g : GLV K E s) ((Y⁻¹ : GLV K E s) y))) := by
          simp [LinearEquiv.mul_apply]
      _ = B ((g : GLV K E s) ((Y⁻¹ : GLV K E s) x))
            ((g : GLV K E s) ((Y⁻¹ : GLV K E s) y)) := hY _ _
      _ = B ((Y⁻¹ : GLV K E s) x) ((Y⁻¹ : GLV K E s) y) := g.2 _ _
      _ = B x y := hYinv

omit [Fintype E] [FiniteDimensional K E] [NeZero s] in
@[simp] theorem conjUnitarySUV_coe (B : (Fin s → E) → (Fin s → E) → K) (Y : GLV K E s)
    (hY : ∀ x y, B (Y x) (Y y) = B x y) (g : unitarySUV B) :
    ((conjUnitarySUV B Y hY g : unitarySUV B) : SLV K E s) =
      conjSL (K := K) (E := E) (s := s) Y (g : SLV K E s) := rfl

lemma nSL_mem_unitarySUV (hEdata : UnitaryFieldData 2 (3 * f) E)
    (hdeg : Module.finrank K E = 3) :
    nSL (K := K) (E := E) (s := s) hdeg ∈
      unitarySUV (K := K) (E := E) (s := s) (Bform (K := K) (E := E) hEdata.bar) := by
  intro x y
  change Bform (K := K) (E := E) hEdata.bar
      (((nSL (K := K) (E := E) (s := s) hdeg : SLV K E s) : GLV K E s) x)
      (((nSL (K := K) (E := E) (s := s) hdeg : SLV K E s) : GLV K E s) y) =
    Bform (K := K) (E := E) hEdata.bar x y
  rw [nSL_coe, frobEquiv_apply, frobEquiv_apply]
  exact frobFirst_isometry_B hEdata x y

lemma zSL_mem_unitarySUV (hKdata : UnitaryFieldData 2 f K)
    (hEdata : UnitaryFieldData 2 (3 * f) E) (hdeg : Module.finrank K E = 3)
    (h3q : 3 ∣ 2 ^ f + 1) {ζ : K} (hζ3 : ζ ^ 3 = 1) :
    zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg ∈
      unitarySUV (K := K) (E := E) (s := s) (Bform (K := K) (E := E) hEdata.bar) := by
  intro x y
  change Bform (K := K) (E := E) hEdata.bar
      (((zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg : SLV K E s) : GLV K E s) x)
      (((zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg : SLV K E s) : GLV K E s) y) =
    Bform (K := K) (E := E) hEdata.bar x y
  rw [zSL_coe, zetaEquiv_apply, zetaEquiv_apply]
  exact zetaLin_isometry_B hKdata hEdata h3q hζ3 x y

theorem unitary_cubic_block_noTr_false {G : Type} [Group G] [Finite G]
    {J Bs : Subgroup G}
    (hKdata : UnitaryFieldData 2 f K) (hEdata : UnitaryFieldData 2 (3 * f) E)
    (hdeg : Module.finrank K E = 3) (h3q : 3 ∣ 2 ^ f + 1) (hs : 2 ≤ s)
    {ζ : K} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (B : (Fin s → E) → (Fin s → E) → K)
    (hB : B = Bform (K := K) (E := E) hEdata.bar)
    (φ : unitarySUV (K := K) (E := E) (s := s) B →* J)
    (_hφ : Function.Surjective φ)
    (hker : ∀ g : unitarySUV (K := K) (E := E) (s := s) B, φ g = 1 →
      ∃ a : K, ∀ v : Fin s → E, ((g : SLV K E s) : GLV K E s) v = a • v)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNT : CFSG.StandardType.GGNoTransvection 3 Bs)
    (Y : Bs → GLV K E s) (y : Bs → Fin s → E)
    (hy0 : ∀ b i, y b i ≠ 0)
    (hYdiag : ∀ b, Y b = diagEquiv (K := K) (E := E) (s := s) (y b) (hy0 b))
    (hYunitary : ∀ b x y, B (Y b x) (Y b y) = B x y)
    (hYact : ∀ b : Bs, ∀ g : unitarySUV (K := K) (E := E) (s := s) B,
      (b : G) * ((φ g : J) : G) * (b : G)⁻¹ =
        ((φ (conjUnitarySUV B (Y b) (hYunitary b) g) : J) : G))
    (lam : Bs → ℕ)
    (hlam : ∀ b i, (y b i) ^ (Fintype.card K - 1) = (algebraMap K E ζ) ^ (lam b))
    (hlam0 : ∃ b : Bs, lam b % 3 ≠ 0) : False := by
  classical
  subst B
  let nSU : unitarySUV (K := K) (E := E) (s := s) (Bform (K := K) (E := E) hEdata.bar) :=
    ⟨nSL (K := K) (E := E) (s := s) hdeg, nSL_mem_unitarySUV hEdata hdeg⟩
  let zSU : unitarySUV (K := K) (E := E) (s := s) (Bform (K := K) (E := E) hEdata.bar) :=
    ⟨zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg,
      zSL_mem_unitarySUV hKdata hEdata hdeg h3q hζ3⟩
  let nJ : J := φ nSU
  let zJ : J := φ zSU
  let n : G := (nJ : G)
  let z : G := (zJ : G)
  have hz3 : z ^ 3 = 1 := by
    have hz3J : zJ ^ 3 = 1 := by
      dsimp [zJ]
      rw [← map_pow]
      have hzSU3 : zSU ^ 3 = 1 := by
        simpa [zSU] using
          zSL_pow_three (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg
      rw [hzSU3, map_one]
    dsimp [z]
    simpa using congrArg (fun x : J => (x : G)) hz3J
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hz1J : zJ = 1 := by
      apply Subtype.ext
      simpa [z] using hz1
    obtain ⟨a, ha⟩ := hker zSU (by simpa [zJ] using hz1J)
    exact zSL_not_scalar (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg hs hζ1
      ⟨a, fun v => by simpa [zSU] using ha v⟩
  have hz_comm : ∀ b : Bs, (b : G) * z = z * (b : G) := by
    intro b
    have hYz : (Y b) * (zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg : GLV K E s) =
        (zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg : GLV K E s) * (Y b) := by
      rw [hYdiag b]
      simpa [zSL] using
        (diagEquiv_mul_zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s)
          (y := y b) (hy0 := hy0 b) (hζ3 := hζ3) (hdeg := hdeg))
    have hconjzSU : conjUnitarySUV (Bform (K := K) (E := E) hEdata.bar) (Y b) (hYunitary b) zSU =
        zSU := by
      apply Subtype.ext
      rw [conjUnitarySUV_coe]
      apply Subtype.ext
      rw [conjSL_coe]
      change (Y b) * (zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg : GLV K E s) * (Y b)⁻¹ =
        (zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg : GLV K E s)
      rw [hYz]
      group
    have hbz : (b : G) * z * (b : G)⁻¹ = z := by
      have hact_z := hYact b zSU
      rw [hconjzSU] at hact_z
      simpa [z, zJ] using hact_z
    calc (b : G) * z = ((b : G) * z * (b : G)⁻¹) * (b : G) := by group
      _ = z * (b : G) := by rw [hbz]
  have hnzn : n * z * n⁻¹ = z := by
    have hnzSU : nSU * zSU * nSU⁻¹ = zSU := by
      apply Subtype.ext
      simpa [nSU, zSU] using
        nSL_conj_zSL (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg
    have hnzJ : nJ * zJ * nJ⁻¹ = zJ := by
      calc nJ * zJ * nJ⁻¹ = φ (nSU * zSU * nSU⁻¹) := by
            simp [nJ, zJ, map_mul, map_inv]
        _ = φ zSU := by rw [hnzSU]
        _ = zJ := rfl
    dsimp [n, z]
    simpa using congrArg (fun x : J => (x : G)) hnzJ
  have hconj : ∀ b : Bs, n * (b : G) * n⁻¹ = z ^ (lam b) * (b : G) := by
    intro b
    have hEconj : frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b) *
        (frobEquiv (K := K) (E := E) (s := s) hdeg)⁻¹ =
        (zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b) * (Y b) := by
      rw [hYdiag b]
      exact frobEquiv_conj_diagEquiv (ζ := ζ) (K := K) (E := E) (s := s)
        (hζ3 := hζ3) hdeg (y b) (hy0 b) (lam b) (fun i => hlam b i)
    have h1 : frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b) =
        (zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b) *
          (Y b) * frobEquiv (K := K) (E := E) (s := s) hdeg := by
      calc frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b) =
          (frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b) *
            (frobEquiv (K := K) (E := E) (s := s) hdeg)⁻¹) *
            frobEquiv (K := K) (E := E) (s := s) hdeg := by group
        _ = ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b) *
              (Y b)) * frobEquiv (K := K) (E := E) (s := s) hdeg := by rw [hEconj]
    have hstep : (Y b) * frobEquiv (K := K) (E := E) (s := s) hdeg =
        ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b))⁻¹ *
          frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b) := by
      calc (Y b) * frobEquiv (K := K) (E := E) (s := s) hdeg =
          ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b))⁻¹ *
            ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b) *
              (Y b) * frobEquiv (K := K) (E := E) (s := s) hdeg) := by group
        _ = ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b))⁻¹ *
              (frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b)) := by rw [← h1]
        _ = ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b))⁻¹ *
              frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b) := by group
    have hYconj : (Y b) * frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b)⁻¹ =
        ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b))⁻¹ *
          frobEquiv (K := K) (E := E) (s := s) hdeg := by
      calc (Y b) * frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b)⁻¹ =
          (((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b))⁻¹ *
            frobEquiv (K := K) (E := E) (s := s) hdeg * (Y b)) * (Y b)⁻¹ := by rw [hstep]
        _ = ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg) ^ (lam b))⁻¹ *
              frobEquiv (K := K) (E := E) (s := s) hdeg := by group
    have hconjSL : conjSL (K := K) (E := E) (s := s) (Y b)
        (nSL (K := K) (E := E) (s := s) hdeg) =
        ((zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg) ^ (lam b))⁻¹ *
          nSL (K := K) (E := E) (s := s) hdeg := by
      apply Subtype.ext
      rw [conjSL_coe]
      change (Y b) * (frobEquiv (K := K) (E := E) (s := s) hdeg) * (Y b)⁻¹ =
        (((zSL (K := K) (E := E) (s := s) ζ hζ3 hdeg) ^ (lam b) : SLV K E s) : GLV K E s)⁻¹ *
          frobEquiv (K := K) (E := E) (s := s) hdeg
      rw [SpecialLinearGroup.coe_pow]
      simpa [zSL_coe] using hYconj
    have hconjSU : conjUnitarySUV (Bform (K := K) (E := E) hEdata.bar) (Y b) (hYunitary b) nSU =
        ((zSU ^ (lam b))⁻¹) * nSU := by
      apply Subtype.ext
      simpa [nSU, zSU, Subgroup.coe_pow] using hconjSL
    have hbn : (b : G) * n * (b : G)⁻¹ = (z ^ (lam b))⁻¹ * n := by
      have hact_n := hYact b nSU
      rw [hconjSU] at hact_n
      simpa [n, nJ, z, zJ, map_mul, map_pow, map_inv] using hact_n
    have hcomm_bn : (b : G) * n * (b : G)⁻¹ * n⁻¹ = (z ^ (lam b))⁻¹ := by
      rw [hbn]
      group
    have hcomm_nb : n * (b : G) * n⁻¹ * (b : G)⁻¹ = z ^ (lam b) := by
      calc n * (b : G) * n⁻¹ * (b : G)⁻¹ =
          ((b : G) * n * (b : G)⁻¹ * n⁻¹)⁻¹ := by group
        _ = ((z ^ (lam b))⁻¹)⁻¹ := by rw [hcomm_bn]
        _ = z ^ (lam b) := by simp
    calc n * (b : G) * n⁻¹ =
        (n * (b : G) * n⁻¹ * (b : G)⁻¹) * (b : G) := by group
      _ = z ^ (lam b) * (b : G) := by rw [hcomm_nb]
  have hz_cent : z ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hz_comm ⟨b, hb⟩
  have hzBs : z ∈ Bs := hSC z hz_cent hz3
  have hcomm : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b := by
    intro b hb c hc
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hexp : ∀ b ∈ Bs, b ^ 3 = 1 := hBs.2
  have hn_conj_mem : ∀ b : Bs, n * (b : G) * n⁻¹ ∈ Bs := by
    intro b
    rw [hconj b]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hzBs (lam b)) b.2
  have hn_norm : n ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using hn_conj_mem ⟨b, hb⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have himg : ∀ b ∈ Bs, n * b * n⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
    intro b hb
    rw [hconj ⟨b, hb⟩]
    simp [mul_assoc]
  obtain ⟨b0, hlam0'⟩ := hlam0
  have hz_order : orderOf z = 3 := orderOf_eq_prime hz3 hz_ne
  have hzpow_ne : z ^ (lam b0) ≠ 1 := by
    intro h
    have hdvd : orderOf z ∣ lam b0 := (orderOf_dvd_iff_pow_eq_one).mpr h
    rw [hz_order] at hdvd
    exact hlam0' (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  have hmove : ∃ b ∈ Bs, n * b * n⁻¹ ≠ b := by
    refine ⟨b0, b0.2, ?_⟩
    intro hfix
    have hzpow_eq : z ^ (lam b0) * b0 = b0 := by
      rw [← hconj b0]
      exact hfix
    have hzpow1 : z ^ (lam b0) = 1 := by
      have h1 : z ^ (lam b0) * b0 = 1 * b0 := by simpa using hzpow_eq
      exact mul_right_cancel h1
    exact hzpow_ne hzpow1
  exact (GGHalf.not_noTransvection_of_shear hcomm hexp hn_norm hzBs hz_ne hnzn himg hmove) hNT


end CFSG.StandardType.ResJUnitaryCubicBlock

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.LineU CFSG.LocalAnalysis.ComponentInitial

theorem GGResHyp.exists_lineJLabel_A3_of_compatible_unitary_marking_coprime
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ ¬ 3 ∣ lab.rank + 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel .A3 lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_hsimple₀, _hnonab₀, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hS, hN, hBsI⟩ := hP₀
  have htag : tag = .twA := hS.1
  have h3n : 3 ∣ 2 ^ n + 1 := hS.2.1
  have hcop : ¬ 3 ∣ rank + 1 := hS.2.2
  subst htag
  have hraw0 := hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨_hsimple, _hnonab, θ, hP⟩ := hQ
  obtain ⟨_hS', hN', hBsI'⟩ := hP
  let d : ℕ := rank + 1
  have hd_def : d = rank + 1 := rfl
  let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (LargeEvenGUSet (Fin d) F (2 ^ n))
  have hrank2 : 2 ≤ rank := hΛ.2.1
  have hd3 : 3 ≤ d := by omega
  have hf1 : 1 ≤ n := hΛ.1
  have hp : Nat.Prime 3 := by norm_num
  have hpq : 3 ∣ 2 ^ n + 1 := h3n
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    omega
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN' = ggGamma J hN0 := by ext b; rfl
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN0)
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    refine ⟨ggBeta J θ hN' b, ggBeta_mem J θ hN' hBsI' b, fun l => ?_⟩
    rw [ggBeta_ggQuotHom J hN' θ b l, hgamma]
  let rU : ℕ := ggUnitaryTorusRank 3 d
  have hT : GGTorusLift 3 rU R := by
    have h := ggTorusLift_unitary (K := F) (n := n) (d := d) (p := 3)
      hFcard hf1 hd3 hdq hp hpq
    simpa [rU, R] using h
  have hTB : GGTorusTBGroup 3 rU R I J (ggQuotHom θ) A := by
    refine ⟨ggQuotHom_surjective θ, ?_, hperfJ, hAe, hAI, ?_, ?_, ?_⟩
    · rw [ker_ggQuotHom θ]
    · simpa [A, rU] using
        GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
    · have hE27 := GGResHyp.cube_le_card_gamma_of_A3 hH hD
      simpa [A] using hE27
    · simpa [A, hgamma] using GGResHyp.gamma_J_selfCent hH
  have hcop_d : ¬ 3 ∣ d := by simpa [hd_def] using hcop
  by_cases hd4 : d = 4
  · have hrequal : rank = 3 := by omega
    have hHas : GGHasLabel ⟨.twA, rank, n⟩ (J ⧸ Subgroup.center J) := by
      unfold GGHasLabel
      refine largeEvenRawDatum_mono ?_ hraw0
      intro R' _ I' F' hQ'
      obtain ⟨-, -, θ', -⟩ := hQ'
      exact ⟨θ'⟩
    refine ⟨⟨.twA, 3, n⟩, ?_, ?_, ?_⟩
    · simpa [hrequal] using hΛ
    · unfold ggResLineJLabel
      exact Or.inr ⟨Or.inl rfl, rfl, h3n⟩
    · simpa [hrequal] using hHas
  · have hd5 : 5 ≤ d := by
      have hne3 : d ≠ 3 := by
        intro h
        exact hcop_d (h.symm ▸ (dvd_refl 3 : (3 : ℕ) ∣ 3))
      omega
    have hd6 : (d, n) ≠ (6, 1) := by
      intro h
      have := congrArg Prod.fst h
      omega
    have hcov : UnitaryCoverAt n d F :=
      LineU.unitaryUniversalCover_holds n d F hFcard hd5 hd6
    obtain ⟨φ, hφs, hφker, hdiagA⟩ :=
      LineU.exists_diagModel_coprime (L' := ↥J) (K := F) (n := n) (d := d) (p := 3)
        (hK := hFcard) (hn := hf1) (hd := hd3) (hp := hp) (hpq := hpq) (hpd := hcop_d)
        (hcov := hcov) (ψ := ggQuotHom θ) (hψ := ggQuotHom_surjective θ)
        (hker := le_of_eq (ker_ggQuotHom θ)) (hperf := hperfJ) (hA := hAe) (hAI := hAI)
    have hdiag : ∀ a ∈ (ggGamma J hN0).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t := by
      simpa [A] using hdiagA
    let hUfield : UnitaryFieldData 2 n F := TableBU.unitaryFieldData_of_card hFcard hf1
    have hM : UnitTB.Model φ := ⟨hUfield, hφs, hφker⟩
    have hcardAut : Nat.card (ggAutomizer J Bs) = d.factorial :=
      card_ggAutomizer_eq_factorial_of_unitaryModel
        (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0)
        (ψ := φ) hM hFcard (by norm_num : 3 ≠ 2) hpq (by omega : 4 ≤ d) hdiag
    have h24 : Nat.card (ggAutomizer J Bs) = 24 :=
      ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
    have hfact : d.factorial = 24 := hcardAut.symm.trans h24
    have h120 : 120 ≤ d.factorial := by
      have h := Nat.factorial_le hd5
      have h5fact : Nat.factorial 5 = 120 := by norm_num
      rwa [h5fact] at h
    omega

section
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem GGResHyp.actual_J_not_unitary_highDiv_for_A3
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧
        3 ∣ lab.rank + 1 ∧ 9 ≤ lab.rank + 1) 3 Bs J) :
    False := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_hsimple₀, _hnonab₀, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hS, hN, hBsI⟩ := hP₀
  have htag : tag = .twA := hS.1
  have h3n : 3 ∣ 2 ^ n + 1 := hS.2.1
  have hdiv : 3 ∣ rank + 1 := hS.2.2.1
  have hge9 : 9 ≤ rank + 1 := hS.2.2.2
  subst htag
  have hraw0 := hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨_hsimple, _hnonab, θ, hP⟩ := hQ
  obtain ⟨_hS', hN', hBsI'⟩ := hP
  let d : ℕ := rank + 1
  have hd_def : d = rank + 1 := rfl
  let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (LargeEvenGUSet (Fin d) F (2 ^ n))
  have hrank2 : 2 ≤ rank := hΛ.2.1
  have hd9 : 9 ≤ d := by simpa [hd_def] using hge9
  have hd5 : 5 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  have h3d : 3 ∣ d := by simpa [hd_def] using hdiv
  have hf1 : 1 ≤ n := hΛ.1
  have hp : Nat.Prime 3 := by norm_num
  have hpq : 3 ∣ 2 ^ n + 1 := h3n
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    omega
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN' = ggGamma J hN0 := by ext b; rfl
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN0)
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    refine ⟨ggBeta J θ hN' b, ggBeta_mem J θ hN' hBsI' b, fun l => ?_⟩
    rw [ggBeta_ggQuotHom J hN' θ b l, hgamma]
  let rU : ℕ := ggUnitaryTorusRank 3 d
  have hT : GGTorusLift 3 rU R := by
    have h := ggTorusLift_unitary (K := F) (n := n) (d := d) (p := 3)
      hFcard hf1 hd3 hdq hp hpq
    simpa [rU, R] using h
  have hTB : GGTorusTBGroup 3 rU R I J (ggQuotHom θ) A := by
    refine ⟨ggQuotHom_surjective θ, ?_, hperfJ, hAe, hAI, ?_, ?_, ?_⟩
    · rw [ker_ggQuotHom θ]
    · simpa [A, rU] using
        GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
    · have hE27 := GGResHyp.cube_le_card_gamma_of_A3 hH hD
      simpa [A] using hE27
    · simpa [A] using GGResHyp.gamma_J_selfCent hH
  have hpow : 3 ^ (d - 3) ≤ Nat.card A := by
    have h := GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
    simpa [A, rU, ggUnitaryTorusRank, h3d] using h
  have hle : d / 3 + 2 ≤ d - 3 := by omega
  have hcard : 3 ^ (d / 3 + 2) ≤ Nat.card A :=
    (Nat.pow_le_pow_right (by norm_num) hle).trans hpow
  have hd6 : (d, n) ≠ (6, 1) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hcov : UnitaryCoverAt n d F :=
    LineU.unitaryUniversalCover_holds n d F hFcard hd5 hd6
  obtain ⟨φ, hφs, hφker, hdiagA⟩ :=
    LineU.exists_diagModel (L' := ↥J) (K := F) (n := n) (d := d) (p := 3)
      (hK := hFcard) (hn := hf1) (hd := hd5) (hp := hp) (hpq := hpq) (hpd := h3d)
      (hcov := hcov) (ψ := ggQuotHom θ) (hψ := ggQuotHom_surjective θ)
      (hker := le_of_eq (ker_ggQuotHom θ)) (hperf := hperfJ)
      (hA := hAe) (hAI := hAI) (hcard := hcard)
  have hdiag : ∀ a ∈ (ggGamma J hN0).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t := by
    simpa [A] using hdiagA
  let hUfield : UnitaryFieldData 2 n F := TableBU.unitaryFieldData_of_card hFcard hf1
  have hM : UnitTB.Model φ := ⟨hUfield, hφs, hφker⟩
  have hcardAut : Nat.card (ggAutomizer J Bs) = d.factorial :=
    card_ggAutomizer_eq_factorial_of_unitaryModel
      (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0)
      (ψ := φ) hM hFcard (by norm_num : 3 ≠ 2) hpq (by omega : 4 ≤ d) hdiag
  have h24 : Nat.card (ggAutomizer J Bs) = 24 :=
    ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
  have hfact : d.factorial = 24 := hcardAut.symm.trans h24
  have h9fact : Nat.factorial 9 ≤ d.factorial := Nat.factorial_le hd9
  have h9 : Nat.factorial 9 = 362880 := by norm_num
  rw [h9] at h9fact
  omega


section SU6ActualActors

open CFSG.LinearGroups CFSG.StandardType.ResJUnitaryActor CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.SemisimpleCentralizers.Held
open scoped Matrix

namespace ResJUnitaryActor

@[expose] def GeneralUnitaryActorsConclusion
    {G : Type} [Group G] (Bs J : Subgroup G) (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (d f : ℕ) (lab : LargeEvenLabel),
    S 3 lab ∧ lab.tag = .twA ∧ d = lab.rank + 1 ∧ f = lab.n ∧
    lab = ⟨.twA, d - 1, f⟩ ∧
    2 ≤ f ∧ 3 ≤ d ∧ Nat.card F = (2 ^ f) ^ 2 ∧
    ∃ (θ : ↥J ⧸ Subgroup.center ↥J ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ f)))
      (φ : LargeEvenSUGroup (Fin d) F (2 ^ f) →* ↥J)
      (hU : UnitaryFieldData 2 f F)
      (A : ↥Bs → GL (Fin d) F)
      (ρ : ↥Bs →* ProjGenLinGroup (Fin d) F)
      (hN : Bs ≤ Subgroup.normalizer (J : Set G))
      (hAGU : ∀ b, A b ∈ LargeEvenGUSet (Fin d) F (2 ^ f))
      (hAiso : ∀ b (x y : Fin d → F),
        stdHermForm hU d (((A b : Matrix (Fin d) (Fin d) F)) *ᵥ x)
          (((A b : Matrix (Fin d) (Fin d) F)) *ᵥ y) = stdHermForm hU d x y),
      Function.Surjective φ ∧
      (∀ g, φ g = 1 → ∃ c : Fˣ,
        (g : GL (Fin d) F) = GeneralLinearGroup.scalar (Fin d) c) ∧
      (∀ g, ggQuotHom θ (φ g) = LargeEvenProjMk _ g) ∧
      (∀ b, A b ∈ primeFormUnitary hU (1 : Matrix (Fin d) (Fin d) F)) ∧
      (∀ b, TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ f))
        ⟨A b, TableBUE.gu_subset_normalizer hU (hAGU b)⟩ =
          ggBeta J θ hN b) ∧
      (∀ (b : ↥Bs) (g : ↥(LargeEvenSUGroup (Fin d) F (2 ^ f))),
        (b : G) * (φ g : G) * (b : G)⁻¹ =
          φ (conjSU hU (A b) (hAiso b) g)) ∧
      (∀ b, ProjGenLinGroup.mk (A b) = ρ b)

end ResJUnitaryActor

open ResJUnitaryActor

private theorem mem_scalars_of_projConj_eq_one_general
    {F : Type} [Field F] [Finite F] {d f : ℕ}
    (hU : UnitaryFieldData 2 f F) (hFcard : Nat.card F = (2 ^ f) ^ 2)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ f) ≠ (3, 2))
    {M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ f) : Set (GL (Fin d) F))}
    (hM : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ f)) M = 1) :
    (M : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
  classical
  let H : Subgroup (GL (Fin d) F) := LargeEvenSUGroup (Fin d) F (2 ^ f)
  have hperf : Group.IsPerfect H :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU
      (p := 2) (f := f) hFcard hd hdq
  have hker : (LargeEvenProjMk H).ker ≤ Subgroup.center H :=
    TableBUE.ker_projMk_le_center
  have hcomm : ∀ g ∈ H, Commute (M : GL (Fin d) F) g := by
    intro g hg
    have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq
      (LargeEvenProjMk H) hker hperf
      (H.normalizerMonoidHom M).toMonoidHom (MonoidHom.id H) (fun u => by
        have h1 := congrArg (fun ψ : MulAut (LargeEvenProj H) =>
          ψ (LargeEvenProjMk H u)) hM
        exact h1) ⟨g, hg⟩
    have h2 := congrArg Subtype.val key
    change (M : GL (Fin d) F) * g * (M : GL (Fin d) F)⁻¹ = g at h2
    calc (M : GL (Fin d) F) * g
        = (M : GL (Fin d) F) * g * (M : GL (Fin d) F)⁻¹ * (M : GL (Fin d) F) := by group
      _ = g * (M : GL (Fin d) F) := by rw [h2]
  exact CFSG.StandardType.GGL45TG.SU.mem_scalars_of_commute_su
    (h := hU) (n := f) (d := d) hd (M : GL (Fin d) F) hcomm

theorem GGInnerDiagOnLabel.exists_general_unitary_cover_actors
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hMark : GGInnerDiagOnLabel S 3 Bs J)
    (hS : ∀ lab : LargeEvenLabel, S 3 lab →
      lab.tag = .twA ∧ 3 ≤ lab.rank + 1 ∧ lab.n ≠ 1) :
    GeneralUnitaryActorsConclusion Bs J S := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_hsimple₀, _hnonab₀, _θ₀, hP₀⟩ := hQ₀
  obtain ⟨hSlab, _hN, _hBsI⟩ := hP₀
  have htag : tag = .twA := (hS ⟨tag, rank, n⟩ hSlab).1
  have hd3 : 3 ≤ rank + 1 := (hS ⟨tag, rank, n⟩ hSlab).2.1
  have hn1 : n ≠ 1 := (hS ⟨tag, rank, n⟩ hSlab).2.2
  subst htag
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨_hsimple, _hnonab, θ, hP⟩ := hQ
  obtain ⟨hSlab', hN', hBsI'⟩ := hP
  have hf1 : 1 ≤ n := hΛ.1
  have hf2 : 2 ≤ n := by omega
  let d := rank + 1
  let f := n
  have hd3' : 3 ≤ d := hd3
  have hf2' : 2 ≤ f := hf2
  have hFcard' : Nat.card F = (2 ^ f) ^ 2 := hFcard
  let hU : UnitaryFieldData 2 f F :=
    TableBU.unitaryFieldData_of_card hFcard' (by omega : 1 ≤ f)
  have hdq : (d, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 ^ 1 := by simpa using congrArg Prod.snd h
    exact hn1 (by simpa [f] using Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2)
  obtain ⟨φ, hφs, _hφker, hφcomp⟩ :=
    CFSG.StandardType.GGL45TG.SU.exists_cover_unitary
      (K := F) (n := f) (d := d) hU hd3' hf2' hperfJ θ
  let H : Subgroup (GL (Fin d) F) := LargeEvenSUGroup (Fin d) F (2 ^ f)
  let I : Set (MulAut (LargeEvenProj H)) :=
    LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin d) F (2 ^ f))
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := hN'
  have hSgu : LargeEvenGUSet (Fin d) F (2 ^ f) ⊆
      Subgroup.normalizer (H : Set (GL (Fin d) F)) := TableBUE.gu_subset_normalizer hU
  obtain ⟨τ, hτq, hτ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv hFcard'
  have hYexists : ∀ b : ↥Bs, ∃ (Y : GL (Fin d) F) (hY : Y ∈ LargeEvenGUSet (Fin d) F (2 ^ f)),
      TableB.projConj H ⟨Y, hSgu hY⟩ = ggBeta J θ hN0 b := by
    intro b
    have hψbI : ggBeta J θ hN0 b ∈ I := ggBeta_mem J θ hN0 hBsI' b
    obtain ⟨Y, hYGU, hYeq⟩ := TableB.exists_eq_projConj hSgu hψbI
    exact ⟨Y, hYGU, hYeq.symm⟩
  let Y : ↥Bs → GL (Fin d) F := fun b => Classical.choose (hYexists b)
  have hYchoice : ∀ b, ∃ hY : Y b ∈ LargeEvenGUSet (Fin d) F (2 ^ f),
      TableB.projConj H ⟨Y b, hSgu hY⟩ = ggBeta J θ hN0 b :=
    fun b => Classical.choose_spec (hYexists b)
  have hYGU : ∀ b, Y b ∈ LargeEvenGUSet (Fin d) F (2 ^ f) :=
    fun b => Classical.choose (hYchoice b)
  have hYproj : ∀ b, TableB.projConj H
      ⟨Y b, hSgu (hYGU b)⟩ = ggBeta J θ hN0 b :=
    fun b => Classical.choose_spec (hYchoice b)
  have hAexists : ∀ b : ↥Bs, ∃ A : GL (Fin d) F,
      A ∈ heldGU d F τ hτ ∧
      (∀ g : GL (Fin d) F, A * g * A⁻¹ = Y b * g * (Y b)⁻¹) :=
    fun b => CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_heldGU_of_GUSet
      hτq hFcard' hτ (Y b) (hYGU b)
  let A : ↥Bs → GL (Fin d) F := fun b => Classical.choose (hAexists b)
  have hAheld : ∀ b, A b ∈ heldGU d F τ hτ :=
    fun b => (Classical.choose_spec (hAexists b)).1
  have hAconj : ∀ b (g : GL (Fin d) F),
      A b * g * (A b)⁻¹ = Y b * g * (Y b)⁻¹ :=
    fun b => (Classical.choose_spec (hAexists b)).2
  have hAprime : ∀ b, A b ∈ primeFormUnitary hU (1 : Matrix (Fin d) (Fin d) F) :=
    fun b => CFSG.LocalAnalysis.GLTheoremA.S265F3.mem_primeFormUnitary_of_heldGU
      hU hτq (hAheld b)
  have hAGU : ∀ b, A b ∈ LargeEvenGUSet (Fin d) F (2 ^ f) :=
    fun b => q1CentUni_heldGU_subset_guSet τ hτ hτq (hAheld b)
  have hAiso : ∀ b (x y : Fin d → F),
      stdHermForm hU d (((A b : Matrix (Fin d) (Fin d) F)) *ᵥ x)
        (((A b : Matrix (Fin d) (Fin d) F)) *ᵥ y) = stdHermForm hU d x y := by
    intro b x y
    rw [stdHermForm_eq_gramForm hU d]
    exact (gramForm_isometry_iff hU (1 : Matrix (Fin d) (Fin d) F) (A b)).mpr (by
      simpa using (mem_primeFormUnitary.mp (hAprime b))) x y
  have hAproj : ∀ b, TableB.projConj H
      ⟨A b, hSgu (hAGU b)⟩ = ggBeta J θ hN0 b := by
    intro b
    rw [show TableB.projConj H ⟨A b, hSgu (hAGU b)⟩ =
        TableB.projConj H ⟨Y b, hSgu (hYGU b)⟩ from ?_]
    · exact hYproj b
    · ext r
      induction r using QuotientGroup.induction_on with
      | H g =>
        rw [TableB.projConj_mk, TableB.projConj_mk]
        congr 1
        apply Subtype.ext
        exact hAconj b g
  have hψeq : ∀ b (g : LargeEvenSUGroup (Fin d) F (2 ^ f)),
      ggQuotHom θ ((ggGamma J hN0 b) (φ g)) =
        ggQuotHom θ (φ (conjSU hU (A b) (hAiso b) g)) := by
    intro b g
    calc
      ggQuotHom θ ((ggGamma J hN0 b) (φ g))
          = ggBeta J θ hN0 b (ggQuotHom θ (φ g)) :=
            (ggBeta_ggQuotHom J hN0 θ b (φ g)).symm
      _ = ggBeta J θ hN0 b (LargeEvenProjMk H g) := by
            have hcompg : ggQuotHom θ (φ g) = LargeEvenProjMk H g := by
              simpa [ggQuotHom] using hφcomp g
            rw [hcompg]
      _ = TableB.projConj H ⟨A b, hSgu (hAGU b)⟩ (LargeEvenProjMk H g) := by
            rw [← hAproj b]
      _ = LargeEvenProjMk H (conjSU hU (A b) (hAiso b) g) := by
            change TableB.projConj H ⟨A b, hSgu (hAGU b)⟩
              (g : LargeEvenProj H) =
                LargeEvenProjMk H (conjSU hU (A b) (hAiso b) g)
            rw [TableB.projConj_mk]
            congr 1
            apply Subtype.ext
            change (A b : GL (Fin d) F) * (g : GL (Fin d) F) * (A b)⁻¹ =
              (conjSU hU (A b) (hAiso b) g : GL (Fin d) F)
            exact (conjSU_coe_GL (h := hU) (Y := A b) (hY := hAiso b) (g := g)).symm
      _ = ggQuotHom θ (φ (conjSU hU (A b) (hAiso b) g)) := by
            have hcompγ : ggQuotHom θ (φ (conjSU hU (A b) (hAiso b) g)) =
                LargeEvenProjMk H (conjSU hU (A b) (hAiso b) g) := by
              simpa [ggQuotHom] using hφcomp (conjSU hU (A b) (hAiso b) g)
            exact hcompγ.symm
  have hperfSU : commutator (LargeEvenSUGroup (Fin d) F (2 ^ f)) = ⊤ := by
    have hperf : Group.IsPerfect (LargeEvenSUGroup (Fin d) F (2 ^ f)) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU
        (p := 2) (f := f) hFcard' hd3' hdq
    exact hperf.commutator_eq_top
  have hperfSUtype : commutator (↥(LargeEvenSUGroup (Fin d) F (2 ^ f))) = ⊤ :=
    hperfSU
  have hcenter : ∀ b (g : ↥(LargeEvenSUGroup (Fin d) F (2 ^ f))),
      ((ggGamma J hN0 b) (φ g))⁻¹ * φ (conjSU hU (A b) (hAiso b) g) ∈
        Subgroup.center (↥J) := by
    intro b g
    have hmem : ((ggGamma J hN0 b) (φ g))⁻¹ *
        φ (conjSU hU (A b) (hAiso b) g) ∈ (ggQuotHom θ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq b g, inv_mul_cancel]
    simpa [ker_ggQuotHom] using hmem
  let γhom : (b : ↥Bs) → LargeEvenSUGroup (Fin d) F (2 ^ f) →*
      LargeEvenSUGroup (Fin d) F (2 ^ f) := fun b =>
    { toFun := conjSU hU (A b) (hAiso b)
      map_one' := conjSU_one hU (A b) (hAiso b)
      map_mul' := conjSU_mul hU (A b) (hAiso b) }
  have hcenter' : ∀ (b : ↥Bs) (g : ↥(LargeEvenSUGroup (Fin d) F (2 ^ f))),
      (((ggGamma J hN0 b).toMonoidHom).comp φ g)⁻¹ *
        (φ.comp (γhom b)) g ∈ Subgroup.center (↥J) := by
    intro b g
    change ((ggGamma J hN0 b) (φ g))⁻¹ *
      φ (conjSU hU (A b) (hAiso b) g) ∈ Subgroup.center (↥J)
    exact hcenter b g
  have hYact : ∀ (b : ↥Bs) (g : ↥(LargeEvenSUGroup (Fin d) F (2 ^ f))),
      (b : G) * (φ g : G) * (b : G)⁻¹ =
        φ (conjSU hU (A b) (hAiso b) g) := by
    intro b g
    have heq : ((ggGamma J hN0 b).toMonoidHom).comp φ =
        φ.comp (γhom b) :=
      CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center
        (S := ↥(LargeEvenSUGroup (Fin d) F (2 ^ f))) hperfSUtype _ _
        (fun s => hcenter' b s)
    have hg := DFunLike.congr_fun heq g
    change (ggGamma J hN0 b) (φ g) = φ (conjSU hU (A b) (hAiso b) g) at hg
    exact congrArg Subtype.val hg
  have hmk_mul : ∀ b c : ↥Bs,
      ProjGenLinGroup.mk (A (b * c)) =
        ProjGenLinGroup.mk (A b) * ProjGenLinGroup.mk (A c) := by
    intro b c
    have hprodeq : TableB.projConj H
        ⟨A (b * c), hSgu (hAGU (b * c))⟩ =
        TableB.projConj H
          ⟨A b * A c, mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))⟩ := by
      have hprod : (⟨A b * A c,
          mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))⟩ :
            Subgroup.normalizer (H : Set (GL (Fin d) F))) =
          ⟨A b, hSgu (hAGU b)⟩ * ⟨A c, hSgu (hAGU c)⟩ := Subtype.ext rfl
      rw [hAproj (b * c), hprod, map_mul (ggBeta J θ hN0),
        map_mul (TableB.projConj H), hAproj b, hAproj c]
    have hker : TableB.projConj H
        ⟨A (b * c) * (A b * A c)⁻¹,
          mul_mem (hSgu (hAGU (b * c)))
            (inv_mem (mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))))⟩ = 1 := by
      change TableB.projConj H
        ((⟨A (b * c), hSgu (hAGU (b * c))⟩ :
            Subgroup.normalizer (H : Set (GL (Fin d) F))) *
          (⟨A b * A c,
            mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))⟩ :
              Subgroup.normalizer (H : Set (GL (Fin d) F)))⁻¹) = 1
      rw [map_mul (TableB.projConj H), map_inv (TableB.projConj H), hprodeq, mul_inv_cancel]
    have hscal : (A (b * c) * (A b * A c)⁻¹ : GL (Fin d) F) ∈
        LargeEvenScalars (Fin d) F :=
      mem_scalars_of_projConj_eq_one_general (d := d) (f := f) hU hFcard' hd3' hdq
        (M := ⟨A (b * c) * (A b * A c)⁻¹,
          mul_mem (hSgu (hAGU (b * c)))
            (inv_mem (mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))))⟩) hker
    rw [largeEvenScalars_def] at hscal
    obtain ⟨z, hz⟩ := hscal
    have hcenter : A (b * c) * (A b * A c)⁻¹ ∈
        Subgroup.center (GL (Fin d) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨z, hz⟩
    have hmk : ProjGenLinGroup.mk (A (b * c) * (A b * A c)⁻¹) = 1 := by
      rw [ProjGenLinGroup.mk_eq_one]
      exact hcenter
    calc ProjGenLinGroup.mk (A (b * c))
        = ProjGenLinGroup.mk (A (b * c) * (A b * A c)⁻¹ * (A b * A c)) := by group
      _ = ProjGenLinGroup.mk (A (b * c) * (A b * A c)⁻¹) *
            ProjGenLinGroup.mk (A b * A c) := map_mul _ _ _
      _ = ProjGenLinGroup.mk (A b * A c) := by rw [hmk, one_mul]
      _ = ProjGenLinGroup.mk (A b) * ProjGenLinGroup.mk (A c) := map_mul _ _ _
  have hmk_one : ProjGenLinGroup.mk (A 1) = 1 := by
    have hproj1 : TableB.projConj H ⟨A 1, hSgu (hAGU 1)⟩ = 1 := by
      rw [hAproj 1, map_one]
    have hscal : (A 1 : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F :=
      mem_scalars_of_projConj_eq_one_general (d := d) (f := f) hU hFcard' hd3' hdq
        (M := ⟨A 1, hSgu (hAGU 1)⟩) hproj1
    rw [largeEvenScalars_def] at hscal
    obtain ⟨z, hz⟩ := hscal
    have hcenter : A 1 ∈ Subgroup.center (GL (Fin d) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨z, hz⟩
    rw [ProjGenLinGroup.mk_eq_one]
    exact hcenter
  let ρ : ↥Bs →* ProjGenLinGroup (Fin d) F :=
    { toFun := fun b => ProjGenLinGroup.mk (A b)
      map_one' := hmk_one
      map_mul' := hmk_mul }
  have hlab_eq : (⟨.twA, rank, n⟩ : LargeEvenLabel) = ⟨.twA, d - 1, f⟩ := by
    dsimp [d, f]
  refine ⟨F, hFfield, hFfinite, d, f, ⟨.twA, rank, n⟩, hSlab', rfl, rfl, rfl,
    hlab_eq, hf2', hd3', hFcard', θ, φ, hU, A, ρ, hN0, hAGU, hAiso,
    hφs, ?_, hφcomp, hAprime, hAproj, hYact, fun b => rfl⟩
  intro g hg
  have h1 : LargeEvenProjMk H g = 1 := by
    rw [← hφcomp g, hg]
    exact map_one (ggQuotHom θ)
  have hgker : g ∈ (LargeEvenProjMk H).ker := by
    rw [MonoidHom.mem_ker]
    exact h1
  rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hgker
  rw [Subgroup.mem_subgroupOf] at hgker
  rw [largeEvenScalars_def] at hgker
  obtain ⟨c, hc⟩ := hgker
  exact ⟨c, hc.symm⟩


theorem GGInnerDiagOnLabel.exists_SU6_cover_actors
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
        3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1) 3 Bs J) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ),
      2 ≤ n ∧ 3 ∣ 2 ^ n + 1 ∧ Nat.card F = (2 ^ n) ^ 2 ∧
      ∃ (θ : ↥J ⧸ Subgroup.center ↥J ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ n)))
        (φ : LargeEvenSUGroup (Fin 6) F (2 ^ n) →* ↥J)
        (hU : UnitaryFieldData 2 n F)
        (A : ↥Bs → GL (Fin 6) F)
        (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F)
        (hN : Bs ≤ Subgroup.normalizer (J : Set G))
        (hAGU : ∀ b, A b ∈ LargeEvenGUSet (Fin 6) F (2 ^ n))
        (hAiso : ∀ b (x y : Fin 6 → F),
          stdHermForm hU 6 (((A b : Matrix (Fin 6) (Fin 6) F)) *ᵥ x)
            (((A b : Matrix (Fin 6) (Fin 6) F)) *ᵥ y) = stdHermForm hU 6 x y),
        Function.Surjective φ ∧
        (∀ g, φ g = 1 → ∃ c : Fˣ,
          (g : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c) ∧
        (∀ g, ggQuotHom θ (φ g) = LargeEvenProjMk _ g) ∧
        (∀ b, A b ∈ primeFormUnitary hU (1 : Matrix (Fin 6) (Fin 6) F)) ∧
        (∀ b, TableB.projConj (LargeEvenSUGroup (Fin 6) F (2 ^ n))
          ⟨A b, TableBUE.gu_subset_normalizer hU (hAGU b)⟩ =
            ggBeta J θ hN b) ∧
        (∀ (b : ↥Bs) (g : ↥(LargeEvenSUGroup (Fin 6) F (2 ^ n))),
          (b : G) * (φ g : G) * (b : G)⁻¹ =
            φ (conjSU hU (A b) (hAiso b) g)) ∧
        (∀ b, ProjGenLinGroup.mk (A b) = ρ b) := by
  classical
  let Sold : ℕ → LargeEvenLabel → Prop := fun _ lab =>
    lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1
  have hSold : ∀ lab, Sold 3 lab →
      lab.tag = .twA ∧ 3 ≤ lab.rank + 1 ∧ lab.n ≠ 1 := by
    intro lab h
    exact ⟨h.1, by rw [h.2.1]; norm_num, h.2.2.2⟩
  have hMark' : GGInnerDiagOnLabel Sold 3 Bs J := hMark
  have hgen := GGInnerDiagOnLabel.exists_general_unitary_cover_actors
    (S := Sold) hMark' hSold
  unfold ResJUnitaryActor.GeneralUnitaryActorsConclusion at hgen
  obtain ⟨F, hFfield, hFfinite, d, f, lab, hSlab, _htag, hd_eq, hf_eq, _hlab_eq,
    hf2, _hd3, hFcard, θ, φ, hU, A, ρ, hN, hAGU, hAiso,
    hφs, hφker, hφcomp, hAprime, hAproj, hYact, hρ⟩ := hgen
  have hrank5 : lab.rank = 5 := hSlab.2.1
  have h3lab : 3 ∣ 2 ^ lab.n + 1 := hSlab.2.2.1
  have hd6 : d = 6 := by omega
  clear hd_eq
  subst d
  have h3f : 3 ∣ 2 ^ f + 1 := by
    simpa [hf_eq] using h3lab
  exact ⟨F, hFfield, hFfinite, f, hf2, h3f, hFcard,
    θ, φ, hU, A, ρ, hN, hAGU, hAiso, hφs, hφker, hφcomp,
    hAprime, hAproj, hYact, hρ⟩


end SU6ActualActors

end

section A3Recognition

open Matrix CFSG CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType.TypeA.PGLTor

theorem GGResHyp.actual_J_not_unitary_six_for_rank3_qplus_large
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    {T : CFSG.StandardType.GGResLineJType}
    (hH : CFSG.StandardType.GGResHyp 3 B Bs x L D J y Ksub)
    (hD : CFSG.StandardType.GGResLineJDatum 3 Bs J T)
    (hT : T = .A3 ∨ T = .B3 ∨ T = .C3)
    (hMark : CFSG.StandardType.GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
        3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1) 3 Bs J) :
    False := by
  classical
  obtain ⟨F, hFfield, hFfinite, n, hn2, h3n, hFcard, θ, φ, hU, A, ρ, hN,
    hAGU, hAiso, hφs, hφker, hφcomp, hAprime, hAproj, hYact, hmk⟩ :=
    CFSG.StandardType.GGInnerDiagOnLabel.exists_SU6_cover_actors hMark
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hAnorm : ∀ b : ↥Bs,
      A b ∈ Subgroup.normalizer
        (CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n) :
          Set (GL (Fin 6) F)) :=
    fun b => CFSG.StandardType.TableBUE.gu_subset_normalizer hU (hAGU b)
  have hE27 :=
    CFSG.StandardType.ResJSU6Scalar.exists_E27_lifts_actual_of_rank3
      (F := F) (n := n) (θ := θ) (hN := hN) (ρ := ρ) (A := A) (T := T)
      (hAnorm := hAnorm) (hmk := hmk) hH hD hT hFcard (by omega) h3n hAproj
  obtain ⟨Etilde, hEtilde_le, hEtilde_elem, hEtilde_cent, hEtilde_card⟩ := hE27
  have hpK : 3 ∣ Nat.card F - 1 := by
    rw [hFcard]
    have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      conv_lhs => rw [show (1 : ℕ) = 1 ^ 2 by norm_num]
      rw [Nat.sq_sub_sq]
    rw [hsq]
    exact dvd_mul_of_dvd_left h3n _
  haveI : Finite Etilde := Subtype.finite
  have hToral : CFSG.StandardType.TypeA.PGLTor.IsToral
      (CFSG.StandardType.ResJSU6Scalar.Actor.actorFull ρ) :=
    CFSG.StandardType.TypeA.PGLTor.isToral_of_E27_central
      (K := F) (n := 6) (G := CFSG.StandardType.ResJSU6Scalar.Actor.actorFull ρ)
      (E := Etilde) hpK
      (CFSG.StandardType.ResJSU6Scalar.Actor.actorFull_isProjElem ρ hE)
      hEtilde_le hEtilde_elem hEtilde_cent hEtilde_card (by norm_num)
  haveI : NeZero (6 : ℕ) := ⟨by norm_num⟩
  obtain ⟨Q, hQunitary, hQdiag⟩ :=
    CFSG.StandardType.SUTorus.exists_unitary_frame
      (h := hU) (p := 3) (by norm_num) (by norm_num) h3n
      (CFSG.StandardType.ResJSU6Scalar.Actor.actorFull_isProjElem ρ hE) hToral
  have hQiso : ∀ x y : Fin 6 → F,
      stdHermForm hU 6
        (((Q : Matrix (Fin 6) (Fin 6) F)) *ᵥ x)
        (((Q : Matrix (Fin 6) (Fin 6) F)) *ᵥ y) = stdHermForm hU 6 x y := by
    intro x y
    rw [stdHermForm_eq_gramForm hU 6]
    exact (gramForm_isometry_iff hU (1 : Matrix (Fin 6) (Fin 6) F) Q).mpr
      (by simpa using (mem_primeFormUnitary.mp hQunitary)) x y
  have hQinvIso : ∀ x y : Fin 6 → F,
      stdHermForm hU 6
        ((((Q⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) *ᵥ x)
        ((((Q⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) *ᵥ y) =
        stdHermForm hU 6 x y := by
    intro x y
    have h := hQiso
      (((Q⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ x)
      (((Q⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ y)
    simpa [Matrix.mulVec_mulVec] using h.symm
  let γ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n)) →*
      ↥(CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n)) :=
    { toFun := CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso
      map_one' := CFSG.StandardType.ResJUnitaryActor.conjSU_one hU Q hQiso
      map_mul' := CFSG.StandardType.ResJUnitaryActor.conjSU_mul hU Q hQiso }
  have hγ_apply : ∀ z, γ z =
      CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso z := fun _ => rfl
  have hγsurj : Function.Surjective
      (fun g => CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso g) := by
    intro x
    refine ⟨CFSG.StandardType.ResJUnitaryActor.conjSU hU Q⁻¹ hQinvIso x, ?_⟩
    apply Subtype.ext
    rw [show (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso
        (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q⁻¹ hQinvIso x) : GL (Fin 6) F) =
        Q * (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q⁻¹ hQinvIso x : GL (Fin 6) F) * Q⁻¹
      from CFSG.StandardType.ResJUnitaryActor.conjSU_coe_GL hU Q hQiso _]
    rw [show (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q⁻¹ hQinvIso x : GL (Fin 6) F) =
        Q⁻¹ * (x : GL (Fin 6) F) * Q
      from CFSG.StandardType.ResJUnitaryActor.conjSU_coe_GL hU Q⁻¹ hQinvIso x]
    group
  let ψ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n)) →* ↥J :=
    φ.comp γ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hφs y
    obtain ⟨z, hz⟩ := hγsurj x
    refine ⟨z, ?_⟩
    have hψ_apply : ψ z = φ (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso z) := by
      calc ψ z = φ (γ z) := rfl
        _ = φ (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso z) := by
            rw [hγ_apply z]
    have hz' : CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso z = x := by
      simpa using hz
    rw [hψ_apply, hz']
    exact hx
  have hψker : ∀ g : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n)),
      ψ g = 1 → ∃ c : F,
        ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal (fun _ => c) := by
    intro g hg
    have hg' : φ (γ g) = 1 := by
      simpa [ψ, MonoidHom.comp_apply] using hg
    obtain ⟨c, hc⟩ := hφker _ hg'
    refine ⟨(c : F), ?_⟩
    have hc' : (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso g : GL (Fin 6) F) =
        GeneralLinearGroup.scalar (Fin 6) c := by
      simpa [hγ_apply g] using hc
    have hconj : Q * (g : GL (Fin 6) F) * Q⁻¹ =
        GeneralLinearGroup.scalar (Fin 6) c := by
      calc Q * (g : GL (Fin 6) F) * Q⁻¹
          = (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso g : GL (Fin 6) F) :=
              (CFSG.StandardType.ResJUnitaryActor.conjSU_coe_GL hU Q hQiso g).symm
        _ = GeneralLinearGroup.scalar (Fin 6) c := hc'
    have hgGL : (g : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c := by
      calc (g : GL (Fin 6) F) = Q⁻¹ * (Q * (g : GL (Fin 6) F) * Q⁻¹) * Q := by group
        _ = Q⁻¹ * GeneralLinearGroup.scalar (Fin 6) c * Q := by rw [hconj]
        _ = GeneralLinearGroup.scalar (Fin 6) c * Q⁻¹ * Q := by
            rw [← CFSG.StandardType.TypeA.PGLTor.scalar_mul_comm c Q⁻¹]
        _ = GeneralLinearGroup.scalar (Fin 6) c := by group
    simpa [GeneralLinearGroup.coe_scalar] using
      congrArg (fun x : GL (Fin 6) F => (x : Matrix (Fin 6) (Fin 6) F)) hgGL
  have hM : CFSG.StandardType.UnitTB.Model ψ := ⟨hU, hψs, hψker⟩
  have hdiag : ∀ a ∈ (CFSG.StandardType.ggGamma J hN).range,
      ∃ t : Fin 6 → F, CFSG.StandardType.LineU.ActsDiagU ψ a t := by
    rintro a ⟨b, rfl⟩
    have hbUnitary : A b ∈ primeFormUnitary hU
        (1 : Matrix (Fin 6) (Fin 6) F) := hAprime b
    have hbNorm : A b ∈ Subgroup.normalizer
        (CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n) :
          Set (GL (Fin 6) F)) := hAnorm b
    have hQnorm : Q ∈ Subgroup.normalizer
        (CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n) :
          Set (GL (Fin 6) F)) :=
      CFSG.StandardType.SUTorus.mem_normalizer_of_mem_primeFormUnitary hU hQunitary
    let D : GL (Fin 6) F := Q⁻¹ * A b * Q
    have hDnorm : D ∈ Subgroup.normalizer
        (CFSG.Assembly.LargeEvenSUGroup (Fin 6) F (2 ^ n) :
          Set (GL (Fin 6) F)) := by
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hQnorm) hbNorm) hQnorm
    have hAbmem : A b ∈ CFSG.StandardType.ResJSU6Scalar.Actor.actorFull ρ :=
      (CFSG.StandardType.ResJSU6Scalar.Actor.actorLift ρ A hmk b).2
    obtain ⟨d, hd⟩ := hQdiag (A b) hAbmem hbUnitary
    have hDmat : ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        diagonal (fun i => (d i : F)) := by
      dsimp only [D]
      rw [hd]
      exact CFSG.SectionRank.OddCover.coe_diagHom d
    refine ⟨fun i => (d i : F), ?_⟩
    refine ⟨D, hDnorm, hDmat, fun s => ?_⟩
    have hcomp :
        CFSG.StandardType.ResJUnitaryActor.conjSU hU (A b) (hAiso b)
            (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s) =
          CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso
            (CFSG.StandardType.LineU.conjN D hDnorm s) := by
      apply Subtype.ext
      calc (CFSG.StandardType.ResJUnitaryActor.conjSU hU (A b) (hAiso b)
            (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s) : GL (Fin 6) F)
          = A b * (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s : GL (Fin 6) F) *
              (A b)⁻¹ :=
            CFSG.StandardType.ResJUnitaryActor.conjSU_coe_GL hU (A b) (hAiso b) _
        _ = A b * (Q * (s : GL (Fin 6) F) * Q⁻¹) * (A b)⁻¹ := by
            rw [CFSG.StandardType.ResJUnitaryActor.conjSU_coe_GL]
        _ = Q * (D * (s : GL (Fin 6) F) * D⁻¹) * Q⁻¹ := by
            dsimp only [D]; group
        _ = Q * (CFSG.StandardType.LineU.conjN D hDnorm s : GL (Fin 6) F) * Q⁻¹ := rfl
        _ = (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso
              (CFSG.StandardType.LineU.conjN D hDnorm s) : GL (Fin 6) F) :=
            (CFSG.StandardType.ResJUnitaryActor.conjSU_coe_GL hU Q hQiso _).symm
    have hψ_apply_s : ψ s =
        φ (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s) := by
      calc ψ s = φ (γ s) := rfl
        _ = φ (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s) := by
            rw [hγ_apply s]
    calc (CFSG.StandardType.ggGamma J hN b) (ψ s)
        = (CFSG.StandardType.ggGamma J hN b)
            (φ (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s)) := by
          rw [hψ_apply_s]
      _ = φ (CFSG.StandardType.ResJUnitaryActor.conjSU hU (A b) (hAiso b)
            (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s)) := by
          apply Subtype.ext
          simpa [CFSG.StandardType.ggGamma_coe] using
            hYact b (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso s)
      _ = φ (CFSG.StandardType.ResJUnitaryActor.conjSU hU Q hQiso
            (CFSG.StandardType.LineU.conjN D hDnorm s)) := by rw [hcomp]
      _ = ψ (CFSG.StandardType.LineU.conjN D hDnorm s) := rfl
  have hcardAut : Nat.card (CFSG.StandardType.ggAutomizer J Bs) = Nat.factorial 6 :=
    CFSG.StandardType.card_ggAutomizer_eq_factorial_of_unitaryModel
      (p := 3) (n := n) (d := 6) (F := F) (G := G) (X := J)
      (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN)
      (ψ := ψ) hM hFcard (by norm_num : 3 ≠ 2) h3n (by norm_num : 4 ≤ 6) hdiag
  have hcard : Nat.card (CFSG.StandardType.ggAutomizer J Bs) = 24 ∨
      Nat.card (CFSG.StandardType.ggAutomizer J Bs) = 48 := by
    rcases hT with rfl | rfl | rfl
    · exact Or.inl (CFSG.StandardType.ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD)
    · exact Or.inr (CFSG.StandardType.ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD)
    · exact Or.inr (CFSG.StandardType.ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD)
  rcases hcard with hcard | hcard
  · exact (by norm_num : (Nat.factorial 6 : ℕ) ≠ 24) (hcardAut.symm.trans hcard)
  · exact (by norm_num : (Nat.factorial 6 : ℕ) ≠ 48) (hcardAut.symm.trans hcard)

theorem GGResHyp.actual_J_not_unitary_six_for_A3_qplus_large
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : CFSG.StandardType.GGResHyp 3 B Bs x L D J y Ksub)
    (hD : CFSG.StandardType.GGResLineJDatum 3 Bs J .A3)
    (hMark : CFSG.StandardType.GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
        3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_unitary_six_for_rank3_qplus_large
    (T := .A3) hH hD (Or.inl rfl) hMark


end A3Recognition

section A3FieldTwoRecognition

open Matrix CFSG CFSG.Assembly CFSG.StandardType
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType.Line63.H5
open CFSG.StandardType.LineU CFSG.SectionRank.OddCover
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LinearGroups
open scoped Matrix

noncomputable section


theorem GGResHyp.lineJDatum_red
    [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J T) :
    GGResLineJDatum 3 (redMkB (GGResHyp.Bs_le_normalizer_J hH)).range
      (redMkL J).range T := by
  classical
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  have hN : Bs ≤ N := GGResHyp.Bs_le_normalizer_J hH
  let B' : Subgroup ↥N := Bs.subgroupOf N
  let J' : Subgroup ↥N := J.subgroupOf N
  have hBmap : B'.map N.subtype = Bs := Subgroup.map_subgroupOf_eq_of_le hN
  have hJmap : J'.map N.subtype = J :=
    Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer
  let e0 : ↥B' ≃* ↥Bs := Subgroup.subgroupOfEquivOfLe hN
  have he1body : (B'.equivMapOfInjective N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr hBmap) = e0 := by
    ext b
    rfl
  have h0 := F4AutWeyl.ggAutomizer_map_eq (f := N.subtype)
    N.subtype_injective J' B' hBmap
  rw [hJmap, he1body] at h0
  have haut : ggAutomizer J' B' =
      (ggAutomizer J Bs).map (MulAut.congr e0.symm).toMonoidHom := by
    have h1 := congrArg (Subgroup.map (MulAut.congr e0.symm).toMonoidHom) h0
    rw [Subgroup.map_map] at h1
    have hcomp : (MulAut.congr e0.symm).toMonoidHom.comp
        (MulAut.congr e0).toMonoidHom = MonoidHom.id (MulAut ↥B') := by
      ext φ
      simp [MulAut.congr_apply]
    rw [hcomp, Subgroup.map_id] at h1
    exact h1.symm
  have hD' : GGResLineJDatum 3 B' J' T :=
    GGResLineJDatum.transport T e0.symm haut hD
  let Z : Subgroup ↥N := (twoCenter J).subgroupOf N
  haveI : Z.Normal := twoCenter_normal (L := J)
  have hZ2 : IsPGroup 2 Z := (isPGroup_twoCenter J).comap_subtype
  have hodd : ¬ 3 ∣ Nat.card Z := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    rw [hk]
    intro h
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hBsp : IsPGroup 3 B' :=
    (CFSG.StandardType.isPGroup_of_isElemAbelian hH.1.2.1.2.1).comap_subtype
  have hZJ : Z ≤ J' := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz).1
  have hres := ggResLineJDatum_map_mk'_of_coprime (G := ↥N) (N := Z)
    (Bs := B') (J := J') T hodd hBsp hZJ hD'
  have hBeq : B'.map (QuotientGroup.mk' Z) = (redMkB hN).range := by
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨(b : G), hN b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
  have hJeq : J'.map (QuotientGroup.mk' Z) = (redMkL J).range := by
    ext q
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨(j : G), Subgroup.mem_subgroupOf.mp hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(j : G), Subgroup.le_normalizer j.2⟩,
        Subgroup.mem_subgroupOf.mpr j.2, rfl⟩
  rw [hBeq, hJeq] at hres
  exact hres

theorem GGResHyp.lineJDatum_A3_red
    [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3) :
    GGResLineJDatum 3 (redMkB (GGResHyp.Bs_le_normalizer_J hH)).range
      (redMkL J).range .A3 :=
  GGResHyp.lineJDatum_red hH hD

theorem GGResHyp.card_automizer_red_A3
    [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3) :
    Nat.card (ggAutomizer (redMkL J).range
      (redMkB (GGResHyp.Bs_le_normalizer_J hH)).range) = 24 :=
  ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl (GGResHyp.lineJDatum_A3_red hH hD)

theorem GGResHyp.exists_redUnitarySixTwoActors
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF4 : Nat.card F = 4)
      (hU : UnitaryFieldData 2 1 F)
      (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ 1)))
      (φ : ↥(unitarySU 2 1 F 6) →* RedGrp J)
      (hφ1 : ∀ s, φ s ∈ (redMkL J).range)
      (hrange : φ.range = (redMkL J).range)
      (hφk : ∀ s, φ s = 1 → ∃ c : Fˣ,
        (s : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c)
      (A : ↥Bs → GL (Fin 6) F)
      (hAGU : ∀ b, A b ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1))
      (hAN : ∀ b, A b ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin 6) F (2 ^ 1) : Set (GL (Fin 6) F)))
      (hAprime : ∀ b, A b ∈ primeFormUnitary hU (1 : Matrix (Fin 6) (Fin 6) F))
      (hAproj : ∀ b, TableB.projConj (LargeEvenSUGroup (Fin 6) F (2 ^ 1))
        ⟨A b, hAN b⟩ = ggBeta J θ hN b)
      (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F)
      (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b)
      (hActs : ∀ b, ActsAs φ (redMkB hN b) (A b)),
    True := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_R₀, _, _I₀, _F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_hsimple₀, _hnonab₀, _θ₀, hP₀⟩ := hQ₀
  have hlabel : (⟨tag, rank, n⟩ : LargeEvenLabel) = ⟨.twA, 5, 1⟩ := hP₀.1
  have htag : tag = .twA := congrArg LargeEvenLabel.tag hlabel
  have hrank : rank = 5 := congrArg LargeEvenLabel.rank hlabel
  have hn : n = 1 := congrArg LargeEvenLabel.n hlabel
  subst htag
  subst hrank
  subst hn
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨_hsimple, _hnonab, θ, hS, hNmark, hBI⟩ := hQ
  have hF4 : Nat.card F = 4 := by simpa using hFcard
  have hU : UnitaryFieldData 2 1 F := TableBU.unitaryFieldData_of_card hFcard le_rfl
  have hcov : CFSG.StandardType.Line63.UnitaryCoverOddAt 1 6 F :=
    CFSG.StandardType.LineU.unitaryCoverOddAt_six_two F hF4
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := exists_redCover hcov hperfJ θ
  have hrange : φ.range = (redMkL J).range := by
    apply le_antisymm
    · intro z hz
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hz
      rw [← hs]
      exact hφ1 s
    · intro z hz
      obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hz
      obtain ⟨s, hs⟩ := hφ2 l
      exact ⟨s, hs.trans hl⟩
  have hφk : ∀ s : ↥(unitarySU 2 1 F 6), φ s = 1 → ∃ c : Fˣ,
      (s : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c := by
    intro s hs
    have h1 : LargeEvenProjMk (unitarySU 2 1 F 6) s = 1 := by
      have h := hφ3 s (1 : ↥J) (by rw [hs, map_one])
      rw [map_one] at h
      exact h.symm
    have hker : s ∈ (LargeEvenProjMk (unitarySU 2 1 F 6)).ker := MonoidHom.mem_ker.mpr h1
    have hmem : s ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (unitarySU 2 1 F 6) := by
      rw [show (LargeEvenProjMk (unitarySU 2 1 F 6)).ker =
          (LargeEvenScalars (Fin 6) F).subgroupOf (unitarySU 2 1 F 6) from
        QuotientGroup.ker_mk' _] at hker
      exact hker
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  let H : Subgroup (GL (Fin 6) F) := LargeEvenSUGroup (Fin 6) F (2 ^ 1)
  have hSgu : LargeEvenGUSet (Fin 6) F (2 ^ 1) ⊆
      Subgroup.normalizer (H : Set (GL (Fin 6) F)) :=
    TableBUE.gu_subset_normalizer (d := 6) hU
  have hdq : (6, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h6 : (6 : ℕ) = 3 := congrArg Prod.fst h
    omega
  obtain ⟨τ, hτq, hτ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv hFcard
  let I : Set (MulAut (LargeEvenProj H)) :=
    LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin 6) F (2 ^ 1))
  have hYexists : ∀ b : ↥Bs, ∃ (Y : GL (Fin 6) F) (hY : Y ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1)),
      TableB.projConj H ⟨Y, hSgu hY⟩ = ggBeta J θ hN b := by
    intro b
    have hψbI : ggBeta J θ hN b ∈ I := ggBeta_mem J θ hN hBI b
    obtain ⟨Y, hYGU, hYeq⟩ := TableB.exists_eq_projConj hSgu hψbI
    exact ⟨Y, hYGU, hYeq.symm⟩
  let Y : ↥Bs → GL (Fin 6) F := fun b => Classical.choose (hYexists b)
  have hYchoice : ∀ b, ∃ hY : Y b ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1),
      TableB.projConj H ⟨Y b, hSgu hY⟩ = ggBeta J θ hN b :=
    fun b => Classical.choose_spec (hYexists b)
  have hYGU : ∀ b, Y b ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1) :=
    fun b => Classical.choose (hYchoice b)
  have hYproj : ∀ b, TableB.projConj H
      ⟨Y b, hSgu (hYGU b)⟩ = ggBeta J θ hN b :=
    fun b => Classical.choose_spec (hYchoice b)
  have hAexists : ∀ b : ↥Bs, ∃ A : GL (Fin 6) F,
      A ∈ heldGU 6 F τ hτ ∧
      (∀ g : GL (Fin 6) F, A * g * A⁻¹ = Y b * g * (Y b)⁻¹) :=
    fun b => CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_heldGU_of_GUSet
      hτq hFcard hτ (Y b) (hYGU b)
  let A : ↥Bs → GL (Fin 6) F := fun b => Classical.choose (hAexists b)
  have hAheld : ∀ b, A b ∈ heldGU 6 F τ hτ :=
    fun b => (Classical.choose_spec (hAexists b)).1
  have hAconj : ∀ b (g : GL (Fin 6) F),
      A b * g * (A b)⁻¹ = Y b * g * (Y b)⁻¹ :=
    fun b => (Classical.choose_spec (hAexists b)).2
  have hAprime : ∀ b, A b ∈ primeFormUnitary hU (1 : Matrix (Fin 6) (Fin 6) F) :=
    fun b => CFSG.LocalAnalysis.GLTheoremA.S265F3.mem_primeFormUnitary_of_heldGU
      hU hτq (hAheld b)
  have hAGU : ∀ b, A b ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1) :=
    fun b => CFSG.StandardType.q1CentUni_heldGU_subset_guSet τ hτ hτq (hAheld b)
  have hAiso : ∀ b (x y : Fin 6 → F),
      stdHermForm hU 6 (((A b : Matrix (Fin 6) (Fin 6) F)) *ᵥ x)
        (((A b : Matrix (Fin 6) (Fin 6) F)) *ᵥ y) = stdHermForm hU 6 x y := by
    intro b x y
    rw [stdHermForm_eq_gramForm hU 6]
    exact (gramForm_isometry_iff hU (1 : Matrix (Fin 6) (Fin 6) F) (A b)).mpr (by
      simpa using (mem_primeFormUnitary.mp (hAprime b))) x y
  have hAproj : ∀ b, TableB.projConj H
      ⟨A b, hSgu (hAGU b)⟩ = ggBeta J θ hN b := by
    intro b
    rw [show TableB.projConj H ⟨A b, hSgu (hAGU b)⟩ =
        TableB.projConj H ⟨Y b, hSgu (hYGU b)⟩ from ?_]
    · exact hYproj b
    · ext r
      induction r using QuotientGroup.induction_on with
      | H g =>
        rw [TableB.projConj_mk, TableB.projConj_mk]
        congr 1
        apply Subtype.ext
        exact hAconj b g
  have h3n : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hmk_mul : ∀ b c : ↥Bs,
      ProjGenLinGroup.mk (A (b * c)) =
        ProjGenLinGroup.mk (A b) * ProjGenLinGroup.mk (A c) := by
    intro b c
    have hprodeq : TableB.projConj H
        ⟨A (b * c), hSgu (hAGU (b * c))⟩ =
        TableB.projConj H
          ⟨A b * A c, mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))⟩ := by
      have hprod : (⟨A b * A c,
          mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))⟩ :
            Subgroup.normalizer (H : Set (GL (Fin 6) F))) =
          ⟨A b, hSgu (hAGU b)⟩ * ⟨A c, hSgu (hAGU c)⟩ := Subtype.ext rfl
      rw [hAproj (b * c), hprod, map_mul (ggBeta J θ hN),
        map_mul (TableB.projConj H), hAproj b, hAproj c]
    have hker : TableB.projConj H
        ⟨A (b * c) * (A b * A c)⁻¹,
          mul_mem (hSgu (hAGU (b * c)))
            (inv_mem (mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))))⟩ = 1 := by
      change TableB.projConj H
        ((⟨A (b * c), hSgu (hAGU (b * c))⟩ :
            Subgroup.normalizer (H : Set (GL (Fin 6) F))) *
          (⟨A b * A c,
            mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))⟩ :
              Subgroup.normalizer (H : Set (GL (Fin 6) F)))⁻¹) = 1
      rw [map_mul (TableB.projConj H), map_inv (TableB.projConj H), hprodeq, mul_inv_cancel]
    have hscal : (A (b * c) * (A b * A c)⁻¹ : GL (Fin 6) F) ∈
        LargeEvenScalars (Fin 6) F :=
      TableBUE.mem_scalars_of_projConj_eq_one
        (M := ⟨A (b * c) * (A b * A c)⁻¹,
          mul_mem (hSgu (hAGU (b * c)))
            (inv_mem (mul_mem (hSgu (hAGU b)) (hSgu (hAGU c))))⟩)
        hU hFcard (by norm_num) hdq (p := 3) (by norm_num) h3n hker
    rw [largeEvenScalars_def] at hscal
    obtain ⟨z, hz⟩ := hscal
    have hcenter : A (b * c) * (A b * A c)⁻¹ ∈
        Subgroup.center (GL (Fin 6) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨z, hz⟩
    have hmk : ProjGenLinGroup.mk (A (b * c) * (A b * A c)⁻¹) = 1 := by
      rw [ProjGenLinGroup.mk_eq_one]
      exact hcenter
    calc ProjGenLinGroup.mk (A (b * c))
        = ProjGenLinGroup.mk (A (b * c) * (A b * A c)⁻¹ * (A b * A c)) := by group
      _ = ProjGenLinGroup.mk (A (b * c) * (A b * A c)⁻¹) *
            ProjGenLinGroup.mk (A b * A c) := map_mul _ _ _
      _ = ProjGenLinGroup.mk (A b * A c) := by rw [hmk, one_mul]
      _ = ProjGenLinGroup.mk (A b) * ProjGenLinGroup.mk (A c) := map_mul _ _ _
  have hmk_one : ProjGenLinGroup.mk (A 1) = 1 := by
    have hproj1 : TableB.projConj H ⟨A 1, hSgu (hAGU 1)⟩ = 1 := by
      rw [hAproj 1, map_one]
    have hscal : (A 1 : GL (Fin 6) F) ∈ LargeEvenScalars (Fin 6) F :=
      TableBUE.mem_scalars_of_projConj_eq_one
        (M := ⟨A 1, hSgu (hAGU 1)⟩) hU hFcard (by norm_num) hdq
        (p := 3) (by norm_num) h3n hproj1
    rw [largeEvenScalars_def] at hscal
    obtain ⟨z, hz⟩ := hscal
    have hcenter : A 1 ∈ Subgroup.center (GL (Fin 6) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨z, hz⟩
    rw [ProjGenLinGroup.mk_eq_one]
    exact hcenter
  let ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F :=
    { toFun := fun b => ProjGenLinGroup.mk (A b)
      map_one' := hmk_one
      map_mul' := hmk_mul }
  have hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b := fun b => rfl
  have hActs : ∀ b : ↥Bs, ActsAs φ (redMkB hN b) (A b) := by
    intro b
    have hAN : A b ∈ Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) :=
      hSgu (hAGU b)
    refine ⟨hAN, fun s => ?_⟩
    set nb : ↥(Subgroup.normalizer (J : Set G)) := ⟨(b : G), hN b.2⟩ with hnb
    have hnb' : redMkB hN b = redMk J nb := rfl
    rw [hnb']
    set φ₀ : ↥(unitarySU 2 1 F 6) →* ↥(redMkL J).range := φ.codRestrict _ hφ1 with hφ₀
    set f₁ : ↥(unitarySU 2 1 F 6) →* ↥(redMkL J).range :=
      (MulAut.conjNormal (redMk J nb)).toMonoidHom.comp φ₀ with hf₁
    set f₂ : ↥(unitarySU 2 1 F 6) →* ↥(redMkL J).range :=
      φ₀.comp (conjNHom (A b) hAN) with hf₂
    have hf : f₁ = f₂ := by
      refine TypeA.eq_of_inv_mul_mem_center hcov.1 f₁ f₂ fun s' => ?_
      obtain ⟨l₁, hl₁⟩ := MonoidHom.mem_range.mp (hφ1 s')
      obtain ⟨l₂, hl₂⟩ := MonoidHom.mem_range.mp (hφ1 (conjN (A b) hAN s'))
      have hψ₁ : ggQuotHom θ l₁ = LargeEvenProjMk H s' :=
        hφ3 s' l₁ hl₁.symm
      have hψ₂ : ggQuotHom θ l₂ = LargeEvenProjMk H (conjN (A b) hAN s') :=
        hφ3 (conjN (A b) hAN s') l₂ hl₂.symm
      set z : ↥J := (J.normalizerMonoidHom nb l₁)⁻¹ * l₂ with hz
      have hzψ : ggQuotHom θ z = 1 := by
        have h1 : ggQuotHom θ (J.normalizerMonoidHom nb l₁) =
            ggLAut J θ nb (ggQuotHom θ l₁) := by
          rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
        have h2 : ggLAut J θ nb (LargeEvenProjMk H s') =
            LargeEvenProjMk H (conjN (A b) hAN s') := by
          have hAproj' : TableB.projConj H ⟨A b, hAN⟩ = ggBeta J θ hN b := hAproj b
          have hgl : ggLAut J θ nb = TableB.projConj H ⟨A b, hAN⟩ := by
            rw [hAproj']
            rfl
          rw [hgl]
          change TableB.projConj H ⟨A b, hAN⟩
            ((⟨(s' : GL (Fin 6) F), s'.2⟩ : H) : LargeEvenProj H) =
            ((⟨(conjN (A b) hAN s' : GL (Fin 6) F),
              (conjN (A b) hAN s').2⟩ : H) : LargeEvenProj H)
          rw [TableB.projConj_mk]
          rfl
        rw [hz, map_mul, map_inv, h1, hψ₁, h2, hψ₂, inv_mul_cancel]
      have hzc : z ∈ Subgroup.center ↥J := by
        rw [← ker_ggQuotHom θ]
        exact hzψ
      have hval : (((f₁ s')⁻¹ * f₂ s' : ↥(redMkL J).range) : RedGrp J) = redMkL J z := by
        have e1 : ((f₁ s' : ↥(redMkL J).range) : RedGrp J) =
            redMkL J (J.normalizerMonoidHom nb l₁) := by
          rw [← redMk_conj, hl₁]
          simp [hf₁, hφ₀]
        have e2 : ((f₂ s' : ↥(redMkL J).range) : RedGrp J) = redMkL J l₂ := by
          rw [hl₂]
          simp [hf₂, hφ₀, coe_conjNHom]
        rw [Subgroup.coe_mul, Subgroup.coe_inv, e1, e2, hz, map_mul, map_inv]
      have hu : (f₁ s')⁻¹ * f₂ s' = (⟨redMkL J z, ⟨z, rfl⟩⟩ : ↥(redMkL J).range) :=
        Subtype.ext hval
      rw [hu, Subgroup.mem_center_iff]
      rintro ⟨v, l₃, rfl⟩
      apply Subtype.ext
      show redMkL J l₃ * redMkL J z = redMkL J z * redMkL J l₃
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc l₃]
    have h := congrArg (fun f : ↥(unitarySU 2 1 F 6) →* ↥(redMkL J).range =>
      ((f s : ↥(redMkL J).range) : RedGrp J)) hf
    simpa [hf₁, hf₂, hφ₀, coe_conjNHom] using h
  have hAN : ∀ b, A b ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin 6) F (2 ^ 1) : Set (GL (Fin 6) F)) :=
    fun b => hSgu (hAGU b)
  exact ⟨F, hFfield, hFfinite, hF4, hU, θ, φ, hφ1, hrange, hφk, A, hAGU, hAN,
    hAprime, hAproj, ρ, hmk, hActs, trivial⟩

theorem GGResHyp.actual_J_not_unitary_six_two_for_rank3
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A3 ∨ T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs J) :
    False := by
  classical
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨F, hFfield, hFfinite, hF4, hU, θ, φ, hφ1, hrange, hφk, A, hAGU, hAN,
    hAprime, hAproj, ρ, hmk, hActs, _hTrue⟩ := exists_redUnitarySixTwoActors hH hMark hN
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  have hActsEq : ∀ b s,
      redMkB hN b * φ s * (redMkB hN b)⁻¹ = φ (LineU.conjN (A b) (hAN b) s) := by
    intro b s
    obtain ⟨hNorm, hAct⟩ := hActs b
    exact hAct s
  have hFcard : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF4]; norm_num
  have h3n : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hBs : CFSG.Open.IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2

  let X : Subgroup (RedGrp J) := (redMkL J).range
  let Bsbar : Subgroup (RedGrp J) := (redMkB hN).range
  have hXnormal : X.Normal := redL_normal (L := J)
  have hNbar : Bsbar ≤ Subgroup.normalizer (X : Set (RedGrp J)) := by
    haveI : X.Normal := hXnormal
    have htop : Subgroup.normalizer (X : Set (RedGrp J)) = ⊤ :=
          Subgroup.normalizer_eq_top X
    intro z _
    rw [htop]
    exact Subgroup.mem_top z
  have hBsbar : CFSG.Open.IsElemAbelian 3 Bsbar := isElemAbelian_redB hN hBs
  have hSCbar : ∀ g ∈ Subgroup.centralizer (Bsbar : Set (RedGrp J)), g ^ 3 = 1 → g ∈ Bsbar :=
    redSC hN hBs hSC
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥Bsbar := Subtype.finite
  obtain ⟨Etilde, hEtilde_le, hEtilde_elem, hEtilde_cent, hEtilde_card⟩ :=
    CFSG.StandardType.ResJSU6Scalar.exists_E27_lifts_actual_of_rank3
      (F := F) (n := 1) (θ := θ) (hN := hN) (ρ := ρ) (A := A) (T := T)
      (hAnorm := fun b => hAN b)
      (hmk := hmk) hH hD hT hFcard (by norm_num) h3n
      (fun b => hAproj b)
  haveI : Finite ↥Etilde := Subtype.finite
  have hToral : TypeA.PGLTor.IsToral (CFSG.StandardType.ResJSU6Scalar.Actor.actorFull ρ) :=
    CFSG.StandardType.TypeA.PGLTor.isToral_of_E27_central
      (K := F) (n := 6)
      (G := CFSG.StandardType.ResJSU6Scalar.Actor.actorFull ρ)
      (E := Etilde) (by rw [hFcard]; norm_num)
      (CFSG.StandardType.ResJSU6Scalar.Actor.actorFull_isProjElem ρ hBs)
      hEtilde_le hEtilde_elem hEtilde_cent hEtilde_card (by norm_num)
  obtain ⟨Q, hQprime, hQdiag⟩ :=
    SUTorus.exists_unitary_frame (h := hU) (n := 6) (f := 1) (p := 3)
      (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2)
      (by norm_num : 3 ∣ 2 ^ 1 + 1)
      (Ĝ := CFSG.StandardType.ResJSU6Scalar.Actor.actorFull ρ)
      (CFSG.StandardType.ResJSU6Scalar.Actor.actorFull_isProjElem ρ hBs) hToral
  have hQN : Q ∈ Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) :=
    primeForm_mem_normalizer hU hQprime
  let φX : ↥(unitarySU 2 1 F 6) →* ↥X :=
    φ.codRestrict (redMkL J).range hφ1
  let ψ : ↥(unitarySU 2 1 F 6) →* ↥X := φX.comp (conjNHom Q hQN)
  have hφXsurj : Function.Surjective φX := by
    intro z
    have hz : (z : RedGrp J) ∈ φ.range := by
      rw [hrange]
      exact z.2
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hz
    exact ⟨s, Subtype.ext hs⟩
  have hconj_surj : Function.Surjective (conjNHom Q hQN) := by
    intro s
    have hQinvN : Q⁻¹ ∈ Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) :=
      Subgroup.inv_mem _ hQN
    refine ⟨conjN Q⁻¹ hQinvN s, ?_⟩
    apply Subtype.ext
    rw [coe_conjNHom, coe_conjN, coe_conjN]
    group
  have hM : UnitTB.Model ψ := by
    refine ⟨hU, ?_, ?_⟩
    · intro z
      obtain ⟨s, hs⟩ := hφXsurj z
      obtain ⟨t, ht⟩ := hconj_surj s
      refine ⟨t, ?_⟩
      have hst : ψ t = φX s := by
        show φX (conjNHom Q hQN t) = φX s
        rw [ht]
      rw [hst]
      exact hs
    · intro s hs
      have hs' : φ (conjNHom Q hQN s) = 1 := by
        have hval : ((ψ s : ↥X) : RedGrp J) = 1 := congrArg Subtype.val hs
        simpa [ψ, φX] using hval
      obtain ⟨c, hc⟩ := hφk (conjNHom Q hQN s) hs'
      refine ⟨(c : F), ?_⟩
      have hQscal : (Q : GL (Fin 6) F) * (s : GL (Fin 6) F) * Q⁻¹ =
          GeneralLinearGroup.scalar (Fin 6) c := by
        simpa [conjNHom, coe_conjN] using hc
      have hs_eq : (s : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c := by
        calc (s : GL (Fin 6) F) = Q⁻¹ * (Q * (s : GL (Fin 6) F) * Q⁻¹) * Q := by group
          _ = Q⁻¹ * GeneralLinearGroup.scalar (Fin 6) c * Q := by rw [hQscal]
          _ = GeneralLinearGroup.scalar (Fin 6) c * Q⁻¹ * Q := by
                rw [TypeA.PGLTor.scalar_mul_comm c Q⁻¹]
          _ = GeneralLinearGroup.scalar (Fin 6) c := by group
      rw [hs_eq]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      · simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.diagonal_apply_ne _ hij]
  have hdiag : ∀ a ∈ (ggGamma X hNbar).range,
      ∃ t : Fin 6 → F, LineU.ActsDiagU ψ a t := by
    rintro ⟨a, ha⟩ ha'
    obtain ⟨bbar, hbbar⟩ := MonoidHom.mem_range.mp ha'
    rw [← hbbar]
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp bbar.2
    have hbbar_eq : bbar = (⟨redMkB hN b, ⟨b, rfl⟩⟩ : Bsbar) := Subtype.ext hb.symm
    rw [hbbar_eq]
    let Bb : CFSG.StandardType.ResJSU6Scalar.Actor.actorFull ρ :=
      CFSG.StandardType.ResJSU6Scalar.Actor.actorLift ρ A hmk b
    obtain ⟨d, hd⟩ := hQdiag Bb Bb.2 (by simpa [Bb, idGram] using hAprime b)
    let D : GL (Fin 6) F := Q⁻¹ * A b * Q
    have hDmat : (D : Matrix (Fin 6) (Fin 6) F) = diagonal (fun i => (d i : F)) := by
      rw [show D = diagHom 6 d from hd, coe_diagHom]
    have hDN : D ∈ Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) := by
      dsimp only [D]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hQN)
        (hAN b)) hQN
    refine ⟨fun i => (d i : F), D, hDN, hDmat, fun s => ?_⟩
    apply Subtype.ext
    calc ((ggGamma X hNbar (⟨redMkB hN b, ⟨b, rfl⟩⟩ : Bsbar) (ψ s) : X) : RedGrp J)
        = (redMkB hN b : RedGrp J) * (ψ s : RedGrp J) * (redMkB hN b : RedGrp J)⁻¹ := rfl
      _ = redMkB hN b * φ (conjNHom Q hQN s) * (redMkB hN b)⁻¹ := rfl
      _ = φ (conjN (A b) (hAN b) (conjNHom Q hQN s)) :=
        hActsEq b (conjNHom Q hQN s)
      _ = φ (conjNHom Q hQN (conjN D hDN s)) := by
        congr 1
        apply Subtype.ext
        change (A b : GL (Fin 6) F) * (Q * (s : GL (Fin 6) F) * Q⁻¹) * (A b)⁻¹ =
          Q * (D * (s : GL (Fin 6) F) * D⁻¹) * Q⁻¹
        dsimp only [D]
        group
      _ = ((ψ (conjN D hDN s) : X) : RedGrp J) := rfl
  have h720 : Nat.card (ggAutomizer X Bsbar) = Nat.factorial 6 :=
    card_ggAutomizer_eq_factorial_of_unitaryModel
      (p := 3) (n := 1) (d := 6) (Bs := Bsbar) (X := X)
      hBsbar hSCbar hNbar hM hFcard (by norm_num) h3n (by norm_num) hdiag
  have hcard : Nat.card (ggAutomizer X Bsbar) = 24 ∨
      Nat.card (ggAutomizer X Bsbar) = 48 := by
    rcases hT with rfl | rfl | rfl
    · exact Or.inl (ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl
        (GGResHyp.lineJDatum_red hH hD))
    · exact Or.inr (ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl
        (GGResHyp.lineJDatum_red hH hD))
    · exact Or.inr (ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl
        (GGResHyp.lineJDatum_red hH hD))
  rcases hcard with hcard | hcard
  · exact (by norm_num : (Nat.factorial 6 : ℕ) ≠ 24) (h720.symm.trans hcard)
  · exact (by norm_num : (Nat.factorial 6 : ℕ) ≠ 48) (h720.symm.trans hcard)

theorem GGResHyp.actual_J_not_unitary_six_two_for_A3
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_unitary_six_two_for_rank3
    (T := .A3) hH hD (Or.inl rfl) hMark

theorem GGResHyp.actual_J_not_unitary_six_for_B3C3_qplus
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    False := by
  classical
  let S1 : ℕ → LargeEvenLabel → Prop := fun _ lab => lab = ⟨.twA, 5, 1⟩
  let S2 : ℕ → LargeEvenLabel → Prop := fun _ lab =>
    lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1
  have hS : ∀ lab : LargeEvenLabel,
      (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) → S1 3 lab ∨ S2 3 lab := by
    intro lab h
    by_cases hn : lab.n = 1
    · left
      obtain ⟨tag, rank, n⟩ := lab
      dsimp [S1]
      simp_all
    · right
      exact ⟨h.1, h.2.1, h.2.2, hn⟩
  have hSplit : GGInnerDiagOnLabel (fun _ lab => S1 3 lab ∨ S2 3 lab) 3 Bs J :=
    GGInnerDiagOnLabel.mono_label
      (S := fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)
      (T := fun _ lab => S1 3 lab ∨ S2 3 lab) hS hMark
  rcases GGInnerDiagOnLabel.elim_or hSplit with h1 | h2
  · exact GGResHyp.actual_J_not_unitary_six_two_for_rank3 hH hD (Or.inr hT) h1
  · exact GGResHyp.actual_J_not_unitary_six_for_rank3_qplus_large hH hD (Or.inr hT) h2

end

end A3FieldTwoRecognition

end CFSG.StandardType

end
