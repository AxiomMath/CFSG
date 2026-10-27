module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameDiag
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE8Five

local instance noOffE8FiveFactFiveLR : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRankLR : NeZero Tag.E8.rank := ⟨by decide⟩

section LangRational

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem exists_langTorsionHom {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {ζ : Lˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {lam : ZMod 5}
    (hq : ((Nat.card K : ℕ) : ZMod 5) * lam = 1) {g₀ : ModGL Tag.E8 L}
    (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) :
    ∃ ι : Multiplicative (NoOffRest.eigE8 5 lam) →* adjointGroup Tag.E8 K,
      Function.Injective ι ∧ ∀ s : NoOffRest.eigE8 5 lam,
        adjEmb Tag.E8 K L (ι (Multiplicative.ofAdd s)) =
          g₀ * frameElt ζ hζ lam (Multiplicative.ofAdd s) * g₀⁻¹ := by
  classical
  let n : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W
  let F : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr)
  have hFg₀ : F g₀ = g₀ * n := hg₀
  let ψ : Multiplicative (NoOffRest.eigE8 5 lam) →* ModGL Tag.E8 L :=
    (MulAut.conj g₀).toMonoidHom.comp (frameElt ζ hζ lam)
  let X : Subgroup (ModGL Tag.E8 L) := ψ.range
  have frameElt_coe : ∀ s : Multiplicative (NoOffRest.eigE8 5 lam),
      frameElt ζ hζ lam s = ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) :=
    fun s => rfl
  have hXC : X ≤ adjointGroup Tag.E8 L := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨s, rfl⟩ := hx
    have hd : frameElt ζ hζ lam s ∈ adjointGroup Tag.E8 L := by
      rw [frameElt_coe]
      exact CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_adjointGroup_E8 _
    show (MulAut.conj g₀) (frameElt ζ hζ lam s) ∈ adjointGroup Tag.E8 L
    rw [MulAut.conj_apply]
    exact mul_mem (mul_mem hg₀C hd) (inv_mem hg₀C)
  have hX5 : ∀ x ∈ X, x ^ 5 = 1 := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨s, rfl⟩ := hx
    have hd5 : frameElt ζ hζ lam s ^ 5 = 1 := by
      rw [frameElt_coe]
      exact ExcFrames.frameDiag_pow ζ hζ _
    show ((MulAut.conj g₀).toMonoidHom (frameElt ζ hζ lam s)) ^ 5 = 1
    rw [← map_pow, hd5, map_one]
  have hXF : ∀ x ∈ X, F x = x := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨s, rfl⟩ := hx
    have hsd : ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) ∈
        NoOffRest.eigE8 5 lam := (Multiplicative.toAdd s).2
    have htor : ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) ∈
        twistedTorus n Fr :=
      (frameDiag_mem_twistedTorus_iff hFr hζo hζ hq _).2 hsd
    have htd : n * F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5)) * n⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) :=
      (mem_twistedTorus.1 htor).2
    change F (g₀ * frameElt ζ hζ lam s * g₀⁻¹) = g₀ * frameElt ζ hζ lam s * g₀⁻¹
    rw [frameElt_coe s, map_mul, map_mul, map_inv, hFg₀]
    have hconf : (g₀ * n) * F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5)) *
          (g₀ * n)⁻¹ =
        g₀ * (n * F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5)) *
          n⁻¹) * g₀⁻¹ := by group
    rw [hconf, htd]
  have hP : IsPGroup 5 X := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact hX5 x x.2
  haveI : Finite X := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have frameElt_injective : Function.Injective (frameElt ζ hζ lam) := by
    intro a b hab
    have hdet : IsUnit (((Tag.E8).symmetrizedCartan.det : ℤ) : ZMod 5) :=
      ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) (by norm_num)
    have hdi := ExcFrames.frameDiag_injective (τ := Tag.E8) (ζ := ζ) hζo hζ hdet
    have h : ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd a : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd b : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) := by
      rw [← frameElt_coe a, ← frameElt_coe b]
      exact hab
    exact Subtype.ext (hdi h)
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : frameElt ζ hζ lam a = frameElt ζ hζ lam b := (MulAut.conj g₀).injective hab
    exact frameElt_injective h1
  have hrat := finite_fixed_subgroup_rational (τ := Tag.E8) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩))
    Fr hFr X hXC hXF
  have hXK : X ≤ (adjEmb Tag.E8 K L).range := by
    rw [adjEmb_range]
    exact hrat.2 5 Nat.prime_five (by norm_num) X le_rfl hP
  let φ : Multiplicative (NoOffRest.eigE8 5 lam) →* (adjEmb Tag.E8 K L).range :=
    { toFun := fun s => ⟨ψ s, hXK (show ψ s ∈ X from MonoidHom.mem_range.2 ⟨s, rfl⟩)⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun a b => Subtype.ext (map_mul ψ a b) }
  have hInj : Function.Injective (adjEmb Tag.E8 K L) := adjEmb_injective
  let e : adjointGroup Tag.E8 K ≃* (adjEmb Tag.E8 K L).range := MonoidHom.ofInjective hInj
  let ι : Multiplicative (NoOffRest.eigE8 5 lam) →* adjointGroup Tag.E8 K :=
    e.symm.toMonoidHom.comp φ
  refine ⟨ι, ?_, ?_⟩
  · intro a b hab
    have h1 : φ a = φ b := e.symm.injective hab
    exact hψinj (congrArg Subtype.val h1)
  · intro s
    have hιs : adjEmb Tag.E8 K L (ι (Multiplicative.ofAdd s)) = ψ (Multiplicative.ofAdd s) :=
      MonoidHom.apply_ofInjective_symm hInj (φ (Multiplicative.ofAdd s))
    rw [hιs]
    rfl

end LangRational

end NoOffE8Five

end CFSG.StandardType
