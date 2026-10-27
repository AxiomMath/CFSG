module

public import CFSG.RankThree.PartOne.KEXC.ReeModel
public import CFSG.RankThree.PartOne.KEXC.Torsion
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorSixTwelve
public import CFSG.RankThree.PartOne.S11d.FieldFFTwo
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import Certificates.Certificate18000
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KEXC.TorusParam
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.LargeReeOrder

section Arith

theorem not_dvd_pow_sub_one {p a : ℕ} [Fact p.Prime] (hpa : p = 2 * a + 1) :
    ¬ p ∣ 2 ^ (2 * a + 1) - 1 := by
  intro h
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have h2 := (ZMod.natCast_eq_zero_iff _ p).2 h
  rw [Nat.cast_sub h1] at h2
  push_cast at h2
  rw [← hpa, ZMod.pow_card] at h2
  have : (1 : ZMod p) = 0 := by linear_combination h2
  exact one_ne_zero this

theorem dvd_three_of_dvd_pow_add_one {p a : ℕ} [Fact p.Prime] (hpa : p = 2 * a + 1)
    (h : p ∣ 2 ^ (2 * a + 1) + 1) : p ∣ 3 := by
  have h2 := (ZMod.natCast_eq_zero_iff _ p).2 h
  push_cast at h2
  rw [← hpa, ZMod.pow_card] at h2
  have : ((3 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h2
  exact (ZMod.natCast_eq_zero_iff 3 p).1 this

end Arith

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem exists_elemAbelian_gamma_of_sector {w : WeylGroup ReeTag.F4.tag} {m : ℕ}
    {U : Fin 2 → Fin 4 → ℤ} (hP : ParamData a L D.F w m U) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpm : p ∣ m) :
    ∃ T : Subgroup (ReeTag.F4.reeGamma K a), IsElementaryAbelian p T ∧ Nat.card T = p ^ 2 := by
  classical
  obtain ⟨Φ, hinj, -, -, hfix⟩ := hP.param
  obtain ⟨E₀, hE₀Φ, hE₀, hE₀c⟩ := exists_elemAbelian_of_injective hp hp2 hpm Φ hinj
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
  have hE₀F : E₀ ≤ twistedFixed D.F n := fun x hx => by
    obtain ⟨z, rfl⟩ := hE₀Φ hx
    exact hfix z
  obtain ⟨T, hmem, -, hcard⟩ := exists_twisted_embedding D hg₀adj hFg₀ E₀ hE₀F
  have hθmul : ∀ γ₁ γ₂ : ReeTag.F4.reeGamma K a, thetaGamma L a (γ₁ * γ₂) =
      thetaGamma L a γ₁ * thetaGamma L a γ₂ := fun _ _ => map_mul _ _ _
  have hE₀comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₀.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : E₀) ⟨y, hy⟩)
  have hE₀pow : ∀ x ∈ E₀, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  refine ⟨T, ?_, by rw [hcard, hE₀c]⟩
  rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
    apply Subtype.ext
    show γ₁ * γ₂ = γ₂ * γ₁
    apply thetaGamma_injective L
    rw [hθmul, hθmul]
    obtain ⟨A, hA⟩ : ∃ A, A = g₀⁻¹ * thetaGamma L a γ₁ * g₀ := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = g₀⁻¹ * thetaGamma L a γ₂ * g₀ := ⟨_, rfl⟩
    have hAE : A ∈ E₀ := hA ▸ (hmem γ₁).1 h₁
    have hBE : B ∈ E₀ := hB ▸ (hmem γ₂).1 h₂
    have hc := hE₀comm _ hAE _ hBE
    have hθ1 : thetaGamma L a γ₁ = g₀ * A * g₀⁻¹ := by rw [hA]; group
    have hθ2 : thetaGamma L a γ₂ = g₀ * B * g₀⁻¹ := by rw [hB]; group
    rw [hθ1, hθ2]
    calc g₀ * A * g₀⁻¹ * (g₀ * B * g₀⁻¹) = g₀ * (A * B) * g₀⁻¹ := by group
      _ = g₀ * (B * A) * g₀⁻¹ := by rw [hc]
      _ = g₀ * B * g₀⁻¹ * (g₀ * A * g₀⁻¹) := by group
  · intro γ hγ
    have e1 := (hmem γ).1 hγ
    have hpow := hE₀pow _ e1
    apply thetaGamma_injective L
    rw [map_pow, map_one]
    have hcp : (g₀⁻¹ * thetaGamma L a γ * g₀) ^ p = g₀⁻¹ * thetaGamma L a γ ^ p * g₀ := by
      have := conj_pow (a := g₀⁻¹) (b := thetaGamma L a γ) (i := p)
      simpa using this
    rw [hcp] at hpow
    calc thetaGamma L a γ ^ p = g₀ * (g₀⁻¹ * thetaGamma L a γ ^ p * g₀) * g₀⁻¹ := by group
      _ = 1 := by rw [hpow]; group

end Rank

theorem two_le_pRank_of_elemAbelian {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : 1 < p)
    {T : Subgroup X} (hT : IsElementaryAbelian p T) (hc : Nat.card T = p ^ 2) :
    2 ≤ CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank hp le_top
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p T).1 hT) hc

theorem largeReeNoInvolution_holds :
    LargeReeNoInvolution := by
  intro X _ _ p hp hp5 hLie hrank d t hd ht hcomm
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hR : ReeTitsModel X .twistedF4 2 p := by
    rcases hLie with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, hR⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact hR
    · exact absurd ht' (by decide)
  obtain ⟨a, K, _, _, _, ha, hpa, hK, ⟨e⟩⟩ := exists_gamma_of_model hR
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hpa]
  have hdΓ : orderOf (e d) = p := by rw [MulEquiv.orderOf_eq]; exact hd
  have htΓ : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hcommΓ : e t * e d = e d * e t := by rw [← map_mul, ← map_mul, hcomm]
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := hdΓ ▸ orderOf_dvd_natCard (e d)
  have hsix : (p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1) → False := by
    intro h
    have h2 := not_two_dvd_card_centralizer_of_sixTwelve ha hK' hp hp3 h (e d) hdΓ
    apply h2
    have htc : e t ∈ Subgroup.centralizer ({e d} : Set (ReeTag.F4.reeGamma K a)) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcommΓ
    have := Subgroup.orderOf_dvd_natCard _ htc
    rw [htΓ] at this
    exact this
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK'
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK').2 p hp hp3 hdvd with
    h1 | h2 | h3 | h4 | h5
  · exact not_dvd_pow_sub_one hpa h1
  · have := dvd_three_of_dvd_pow_add_one hpa h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  ·
    have hTex : ∃ T : Subgroup (ReeTag.F4.reeGamma K a), IsElementaryAbelian p T ∧
        Nat.card T = p ^ 2 := by
      rcases dvd_phi4_cases hp hp3 h3 with ⟨hpp, -⟩ | ⟨hpm, -⟩
      · exact exists_elemAbelian_gamma_of_sector D (torusParam_phi4p D.isFrob) hp hp2 hpp
      · exact exists_elemAbelian_gamma_of_sector D (torusParam_phi4m D.isFrob) hp hp2 hpm
    obtain ⟨T, hT, hTc⟩ := hTex
    have hrk := two_le_pRank_of_elemAbelian hp.one_lt (T := T.map e.symm.toMonoidHom)
      (by
        rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]
        exact CFSG.SectionRank.isElemAbelian_map
          ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p T).1 hT) _)
      (by rw [Subgroup.card_map_of_injective e.symm.injective, hTc])
    omega
  · exact hsix (Or.inl h4)
  · exact hsix (Or.inr h5)

end CFSG.RankThree.PartOne.KEXC
