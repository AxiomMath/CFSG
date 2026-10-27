module

public import CFSG.RankThree.PartOne.KLC.TwF4Torus
public import CFSG.RankThree.PartOne.KLC.Assembly
public import CFSG.RankThree.PartOne.KEXC.ReeModel
public import CFSG.RankThree.PartOne.KLR.SectorSixTwelve
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KEXC.TorusParam
public import CFSG.RankThree.PartOne.KLC.TwistedTorusRank
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.LargeReeOrder
open CFSG.Assembly.LowTwoRank (StatedLieTag)


section PRank

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]

theorem two_le_pRank_reeGamma (D : ReeFrameData K L a) (w : WeylGroup ReeTag.F4.tag) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL ReeTag.F4.tag L)
    (hφ : Function.Injective φ)
    (hφF : φ.range ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma K a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  have hθ : ∀ z, ∃ γ : ReeTag.F4.reeGamma K a, thetaGamma L a γ = g₀ * φ z * g₀⁻¹ := by
    intro z
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ (hφF ⟨z, rfl⟩)
    exact D.exists_theta_of_fixed hadj hfix
  choose ψ hψ using hθ
  have hinjθ := thetaGamma_injective (K := K) L (a := a)
  let Ψ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ReeTag.F4.reeGamma K a :=
    { toFun := ψ
      map_one' := by
        apply hinjθ
        rw [hψ, map_one, map_one]
        group
      map_mul' := fun z z' => by
        apply hinjθ
        rw [map_mul (thetaGamma L a) (ψ z) (ψ z'), hψ (z * z'), hψ z, hψ z', map_mul φ z z']
        group }
  have hΨinj : Function.Injective Ψ := by
    intro z z' hzz
    have h1 : g₀ * φ z * g₀⁻¹ = g₀ * φ z' * g₀⁻¹ := by
      rw [← hψ z, ← hψ z']
      exact congrArg _ hzz
    have h2 : φ z = φ z' := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    exact hφ h2
  have hpL : (p : L) ≠ 0 := fun h0 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    ((CharP.cast_eq_zero_iff L 2 p).1 h0)).symm
  have hcard : Nat.card ((rootsOfUnity p L) × (rootsOfUnity p L)) = p ^ 2 := by
    rw [Nat.card_prod, card_rootsOfUnity_eq hp hpL, sq]
  have hpow : ∀ z : (rootsOfUnity p L) × (rootsOfUnity p L), z ^ p = 1 := fun z =>
    Prod.ext (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 z.1.2))
      (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 z.2.2))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b) hpow hcard Ψ
    hΨinj (H := ⊤) le_top

end PRank

section Casts

theorem int_dvd_sub_one {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q - 1) : (p : ℤ) ∣ (q : ℤ) - 1 := by
  have := Int.natCast_dvd_natCast.2 h
  rwa [Nat.cast_sub hq, Nat.cast_one] at this

theorem int_dvd_sub_add_one {p q r : ℕ} (hr : r ≤ q) (h : p ∣ q - r + 1) :
    (p : ℤ) ∣ (q : ℤ) - r + 1 := by
  have := Int.natCast_dvd_natCast.2 h
  rwa [Nat.cast_add, Nat.cast_sub hr, Nat.cast_one] at this

end Casts

section Main

theorem reeModel_of_lieModel {T : Type} [Group T] {n f : ℕ}
    (hM : LieModel T .twistedF4 n 2 f) : n = 0 ∧ ReeTitsModel T .twistedF4 2 f :=
  CFSG.Blueprint.LieModel.reeTitsModel hM (by decide)

theorem lieGoodComponentFixT_twistedF4_of :
    LieGoodComponentFixT .twistedF4 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, hRee⟩ := reeModel_of_lieModel hM
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_gamma_of_model hRee
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hx' : orderOf (e x) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hxp hx1
  have hy2' : (e y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hxy' : e x * e y = e y * e x := by rw [← map_mul, ← map_mul, hxy]
  have hpr' : CFSG.pRank p (ReeTag.F4.reeGamma K a) = 1 := by
    rw [← pRank_congr_mulEquiv e hp.one_lt]
    exact hpr
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := hx' ▸ orderOf_dvd_natCard (e x)
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK'
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hsix : (p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1) → False := by
    intro h
    apply not_two_dvd_card_centralizer_of_sixTwelve ha hK' hp hp3 h (e x) hx'
    have htc : e y ∈ Subgroup.centralizer ({e x} : Set (ReeTag.F4.reeGamma K a)) :=
      Subgroup.mem_centralizer_singleton_iff.2 hxy'.symm
    have ht2' : orderOf (e y) = 2 := orderOf_eq_prime hy2' hy1'
    have := Subgroup.orderOf_dvd_natCard _ htc
    rw [ht2'] at this
    exact this
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK').2 p hp hp3 hdvd with
    h1 | h2 | h3 | h4 | h5
  · obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_phi1 (L := AlgebraicClosure K) D.isFrob hp hp2
      (by exact_mod_cast int_dvd_sub_one hq1 h1)
    have := two_le_pRank_reeGamma D wPhi1 hp hp2 Φ hΦ hΦF
    omega
  · obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_phi2 (L := AlgebraicClosure K) D.isFrob hp hp2
      (by exact_mod_cast Int.natCast_dvd_natCast.2 h2)
    have := two_le_pRank_reeGamma D wPhi2 hp hp2 Φ hΦ hΦF
    omega
  · rcases dvd_phi4_cases hp hp3 h3 with ⟨hpp, -⟩ | ⟨hpm, -⟩
    · obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_phi4p (L := AlgebraicClosure K) D.isFrob hp hp2
        (by exact_mod_cast Int.natCast_dvd_natCast.2 hpp)
      have := two_le_pRank_reeGamma D wPhi4p hp hp2 Φ hΦ hΦF
      omega
    · obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_phi4m (L := AlgebraicClosure K) D.isFrob hp hp2
        (by exact_mod_cast int_dvd_sub_add_one hle hpm)
      have := two_le_pRank_reeGamma D wPhi4m hp hp2 Φ hΦ hΦF
      omega
  · exact hsix (Or.inl h4)
  · exact hsix (Or.inr h5)

theorem lieGoodComponentFixT_twistedF4 :
    LieGoodComponentFixT .twistedF4 := by
  exact lieGoodComponentFixT_twistedF4_of

end Main

end CFSG.RankThree.PartOne.KLC
