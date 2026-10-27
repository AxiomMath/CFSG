module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus


private theorem lk0xttdat_finite_ggFixGp {f : ℕ} (hf : 1 ≤ f) :
    Finite ↥(ggFixGp .twistedE6 f) := by
  classical
  let K := GaloisField 2 (2 * f)
  letI : Algebra K GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : CharP K 2 := inferInstance
  haveI : CharP GGL 2 := inferInstance
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega : 2 * f ≠ 0)]
    rw [← pow_mul, Nat.mul_comm]
  let σ : K →+* K := iterateFrobenius K 2 f
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  obtain ⟨hfin, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order (ℓ := 2) (f := f)
      Nat.prime_two hf K hK σ hσ GGL (ggFrobT f) (ggFrobT_apply f)
  rw [show ggFixGp .twistedE6 f = twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) from rfl]
  exact hfin

theorem exists_twE6_datum {f : ℕ} (hf : 1 ≤ f) {w : WeylGroup (langTag .twistedE6)}
    {g : ModGL (langTag .twistedE6) GGL} (hg : g ∈ adjointGroup (langTag .twistedE6) GGL)
    (hlang : ggPhi .twistedE6 f g = g * canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w) :
    ∃ (Δ : LangDatum (langTag .twistedE6) GGL)
      (ρ : Equiv.Perm (Fin (langTag .twistedE6).rank → ℤ)),
      FrobRootMap Δ ρ ∧ Finite Δ.model ∧ Δ.Φ = ggPhi .twistedE6 f ∧ Δ.q = 2 ^ f ∧
      Δ.n = canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w ∧ Δ.g0 = g ∧
      Δ.model = (ggFixGp .twistedE6 f).map (MulAut.conj g⁻¹).toMonoidHom ∧
      (∀ γ, IsRoot (langTag .twistedE6) γ → ρ γ = w • ggGraphLat .twistedE6 γ) := by
  have ht : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  let hΦ : IsSteinbergEnd (langTag .twistedE6) GGL (2 ^ f) (ggPhi .twistedE6 f) :=
    CFSG.StandardType.LieCore.isSteinbergEnd_ggPhi ht f
  let Δ : LangDatum (langTag .twistedE6) GGL :=
    CFSG.StandardType.LieCore.langDatumOfPosition hΦ w g hg hlang
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved (langTag .twistedE6) GGL Δ
  have hmodel : Δ.model = (ggFixGp .twistedE6 f).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [LangDescent.model_eq Δ, ggFixGp_eq_fix Δ rfl]
    rfl
  have hFinModel : Finite Δ.model := by
    rw [hmodel]
    haveI : Finite ↥(ggFixGp .twistedE6 f) := lk0xttdat_finite_ggFixGp hf
    refine Finite.of_surjective
      (fun x : ↥(ggFixGp .twistedE6 f) =>
        (⟨(MulAut.conj g⁻¹).toMonoidHom x,
          Subgroup.mem_map.2 ⟨x, x.2, rfl⟩⟩ :
          ↥((ggFixGp .twistedE6 f).map (MulAut.conj g⁻¹).toMonoidHom))) ?_
    rintro ⟨y, hy⟩
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  refine ⟨Δ, ρ, hρ, hFinModel, rfl, rfl, rfl, rfl, hmodel, ?_⟩
  intro γ hγ
  exact CFSG.StandardType.LieCore.ggLie_frobRootMap_eq_on_roots (Or.inr (Or.inr rfl)) hf hΦ w g hg hlang hρ hγ

end CFSG.StandardType.LieKnownR2.ExcPos
