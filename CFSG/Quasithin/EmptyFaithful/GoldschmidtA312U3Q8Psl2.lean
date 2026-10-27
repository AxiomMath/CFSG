module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Act
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Foundations
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import Certificates.Certificate8026Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.A312U3

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

theorem no_quatPair_pgl2 {F : Type*} [Field F]
    (i j : GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)) : ¬ QuatPair i j := by
  rintro ⟨-, h2, hd, hij⟩
  obtain ⟨I, rfl⟩ := QuotientGroup.mk_surjective i
  obtain ⟨J, rfl⟩ := QuotientGroup.mk_surjective j
  have hI : I ^ 2 ∉ Subgroup.center (GL (Fin 2) F) := fun hmem =>
    h2 (by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hmem)
  have hJ : J * I * J⁻¹ * I ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hij, inv_mul_cancel]
  have hJ2 := gl2_sq_mem_center I J hI hJ
  apply h2
  rw [← hd, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr hJ2

theorem subsingleton_ringEquiv_of_card_prime {K : Type*} [Field K] [Finite K] {r : ℕ}
    [Fact r.Prime] (hK : Nat.card K = r) : Subsingleton (K ≃+* K) := by
  have hchar : CharP K r := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  let ι : ZMod r →+* K := ZMod.castHom (dvd_refl r) K
  have hinj : Function.Injective ι := ι.injective
  have hsurj : Function.Surjective ι := by
    have hc : Nat.card K ≤ Nat.card (ZMod r) := by rw [hK, Nat.card_zmod]
    exact (Function.Injective.bijective_of_nat_card_le hinj hc).2
  refine ⟨fun σ τ => ?_⟩
  ext x
  obtain ⟨n, rfl⟩ := hsurj x
  have h1 : σ (ι n) = ι n := DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp ι) ι) n
  have h2 : τ (ι n) = ι n := DFunLike.congr_fun (RingHom.ext_zmod (τ.toRingHom.comp ι) ι) n
  rw [h1, h2]

theorem pgl2InnerAutPSL2_bijective {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    (hK : Nat.card K = r) (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Function.Bijective (pgl2InnerAutPSL2 K hodd hcard) := by
  refine ⟨pgl2InnerAutPSL2_injective K hodd hcard, fun α => ?_⟩
  have := subsingleton_ringEquiv_of_card_prime hK
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K (p := r) (f := 1)
    (by rw [pow_one]; exact hK) hodd hcard α
  have hr : x.right = 1 := Subsingleton.elim _ _
  have hxx : x = SemidirectProduct.inl x.left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hr, map_one, mul_one]
  refine ⟨x.left, ?_⟩
  rw [← pGammaL2ToMulAutPSL2_inl K hodd hcard, ← hxx]
  exact hx

theorem su3_not_psl2_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)}
    {H : Subgroup (GL (Fin 3) K)} (h : QCtx p K M H) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = r)
    (e : H ⧸ Subgroup.center H ≃* StatedProj (StatedSL 2 K')) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have hodd : IsOddPrimePower (Nat.card K') :=
    ⟨r, 1, hr, hr.odd_of_ne_two (by omega), le_rfl, by rw [hK', pow_one]⟩
  have hcard : 3 < Nat.card K' := by omega
  obtain ⟨c, d, hcd⟩ := exists_quaternion_pair hp2 hK M h.odd
  have hpair := quatPair_qAct hK h hcd
  let eP : H ⧸ Subgroup.center H ≃* PSL2 K' :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K').symm
  have hpair2 := hpair.map (MulAut.congr eP).toMonoidHom (MulAut.congr eP).injective
  let ee : PGL2 K' ≃* MulAut (PSL2 K') :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 K' hodd hcard)
      (pgl2InnerAutPSL2_bijective hK' hodd hcard)
  have hpair3 := hpair2.map ee.symm.toMonoidHom ee.symm.injective
  exact no_quatPair_pgl2 _ _ hpair3

end CFSG.Quasithin.A312U3
