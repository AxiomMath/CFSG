module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.StandardType
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem rckRLomm_longCoroot_self {n : ℕ} {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    longCoroot i j s t i s + longCoroot i j s t j t = 2 := by
  simp [longCoroot, hij, hij.symm]

private theorem rckRLomm_scalars_of_long {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    (hcoord : toStdB (n - 1) β = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ∃ ε : Multiplicative K ≃* (minusDatum n hirr).rootGroup β,
      (∀ a : K, (ε (Multiplicative.ofAdd a) : spinGroup (quadMinus n K b c)) =
        (minusFrame n b c).longRoot hij s t (.ofAdd a)) ∧
      RCKRootLineScalars ((minusDatum n hirr).rootGroup β) K ε := by
  have hroot : (minusDatum n hirr).rootGroup β = ((minusFrame n b c).longRoot hij s t).range :=
    minusRootGroup_eq_long n hirr hij s t hcoord
  let g : Multiplicative K →* spinGroup (quadMinus n K b c) :=
    (minusFrame n b c).longRoot hij s t
  have hg : Function.Injective g :=
    HypFrame.longRoot_injective ((minusFrame n b c).toHypFrame :
        HypFrame (quadMinus n K b c) (n - 1)) hij s t
  let φ : Multiplicative K →* (minusDatum n hirr).rootGroup β :=
    { toFun := fun a => ⟨g a, by
        rw [hroot]
        exact ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun a b => Subtype.ext (map_mul g a b) }
  have hφbij : Function.Bijective φ := by
    refine ⟨?_, fun x => ?_⟩
    · intro a b hab
      exact hg (congrArg Subtype.val hab)
    · have hx : (x : spinGroup (quadMinus n K b c)) ∈
        ((minusFrame n b c).longRoot hij s t).range := by
        rw [← hroot]
        exact x.2
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, Subtype.ext ha⟩
  let ε : Multiplicative K ≃* (minusDatum n hirr).rootGroup β :=
    MulEquiv.ofBijective φ hφbij
  have hε : ∀ a : K, (ε (Multiplicative.ofAdd a) : spinGroup (quadMinus n K b c)) =
      (minusFrame n b c).longRoot hij s t (.ofAdd a) := fun _ => rfl
  refine ⟨ε, hε, fun l hl => ?_⟩
  obtain ⟨r, hr⟩ := (Function.Injective.bijective_of_finite
    (CharTwo.sq_injective (R := K))).2 l
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hl (by simpa using hr.symm)
  let τ : Kˣ := Units.mk0 r hr0
  have hpow : ((τ ^ (2 : ℤ) : Kˣ) : K) = l := by
    rw [zpow_two, Units.val_mul, Units.val_mk0]
    simpa [pow_two] using hr
  refine ⟨(minusFrame n b c).longTorus hij s t τ, fun u => ?_⟩
  have hconj := (minusFrame n b c).longTorus_conj_longRoot hij s t τ hij s t u
  rw [hε u, hε (l * u), hconj, rckRLomm_longCoroot_self hij s t, hpow]

theorem rckK1I_rootLine_POmegaMinus
    {n f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 2 f) :
    0 < (ggU .POmegaMinus n f).D.rank ∧ RCKRootLineAll (ggU .POmegaMinus n f) f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 4 ≤ n := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  change 0 < (Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)).rank ∧
    RCKRootLineAll (⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
      Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ : LieUniversal) f
  refine ⟨?_, ?_⟩
  · simp only [Spin.Twisted.minusDatum]
    omega
  · intro β hβ hlong
    obtain ⟨i, j, hij, s, t, hcoord⟩ :=
      CFSG.StandardType.RootCentOmega.exists_long_of_ggLongRoot_minus (minusCoeffs_irr 2 f) hn hlong
    obtain ⟨ε, -, hsc⟩ := rckRLomm_scalars_of_long hn (minusCoeffs_irr 2 f) hij s t hcoord
    exact ⟨GaloisField 2 f, inferInstance, inferInstance, ε, hcard, hsc⟩

end CFSG.StandardType.RCKK1I
