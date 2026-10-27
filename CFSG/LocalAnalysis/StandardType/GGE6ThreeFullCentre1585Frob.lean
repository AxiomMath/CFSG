module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Defs

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrv4h2_rootChar_frobLinear_eq {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ}
    (S : LangSetup τ L p₀) (F : (Fin τ.rank → ℤ) ≃ₗ[ℤ] (Fin τ.rank → ℤ))
    (hF : ∀ v, IsRoot τ v → F v = S.ρ v) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (x : Fin τ.rank → ℤ) :
    rootChar a (F x) = rootChar a x ^ S.D.q := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hFx : F x = ∑ i, x i • F (Pi.single i 1) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
  conv_lhs => rw [hFx]
  rw [rootChar_sum]
  conv_rhs => rw [hx]
  rw [rootChar_sum, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, hF (Pi.single i 1) (isRoot_single τ i),
    S.frob.rootChar_eq a hT (Pi.single i 1) (isRoot_single τ i)]
  rw [← zpow_natCast (rootChar a (Pi.single i 1)) S.D.q, ← zpow_mul]
  rw [rootChar_zsmul]
  rw [← zpow_natCast (rootChar a (Pi.single i 1) ^ (x i : ℤ)) S.D.q, ← zpow_mul, mul_comm]

theorem rootChar_frobLinear_of_mem_model
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (b : Fin ρ.tau.rank → Omegaˣ)
    (hb : rootDiagUnit ρ.tau b ∈ ρ.setup.D.model) (v : Fin ρ.tau.rank → ℤ) :
    rootChar b (ρ.frobLinear v) = rootChar b v ^ (2 ^ lab.n : ℕ) := by
  have hmem := (LangDatum.mem_model ρ.setup.D).1 hb
  have htor : rootDiagUnit ρ.tau b ∈ ρ.setup.D.torus := by
    change rootDiagUnit ρ.tau b ∈
      CFSG.RankThree.PartOne.KE.twistedTorusOf ρ.setup.D.n ρ.setup.D.Φ
    exact CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mpr
      ⟨rootDiagUnit_mem_torusGroup b, hmem.2⟩
  have h := ltrv4h2_rootChar_frobLinear_eq ρ.setup ρ.frobLinear ρ.frob_roots htor v
  rwa [ρ.q_eq] at h

end CFSG.StandardType.E6Centralizer1585

end
