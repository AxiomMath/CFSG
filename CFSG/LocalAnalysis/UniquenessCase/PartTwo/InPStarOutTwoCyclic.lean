module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarCriteria
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OuterInnerKernel
public import CFSG.GroupTheory.HuppertProduct.Quotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ClassicalInvolution

variable {G : Type} [Group G] [Finite G]

theorem inPStar_of_le_normalizer_of_outTwoCyclic {D : Data G} {V₀ X E : Subgroup G}
    (hX : X ∈ calC D.M) (hMX : D.M ≤ normalizer (X : Set G)) (hEX : E ≤ X)
    (hEN : E ≤ normalizer ((D.T ⊓ X : Subgroup G) : Set G))
    (hout : Nobq.OutTwoCyclic (Bar2 X)) (hE : F11.InP11 D E) :
    InPStar D V₀ E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM : X ≤ D.M := CFSG.Open.IsSubnormal.le hX.1
  set C : Subgroup G := F08.CentOverO2 D.M X with hCdef
  set T₀ : Subgroup G := (D.T ⊓ X) ⊔ (D.T ⊓ C) with hT₀def
  have hO2X : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hMC : D.M ≤ normalizer (C : Set G) := by
    rw [hCdef, centOverO2_eq_ker_map hMX]
    exact CFSG.GroupTheory.FT63ChII.le_normalizer_map_subtype
      (R := D.M) ((rhoL X).comp (Subgroup.inclusion hMX)).ker
  have hO2T : pCoreOf 2 X ≤ D.T := by
    have hMO2 : D.M ≤ normalizer (pCoreOf 2 X : Set G) :=
      hMX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
    haveI : (Subgroup.comap D.M.subtype (pCoreOf 2 X)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hMO2
    obtain ⟨Q, hQ⟩ := D.sylowM.exists_sylow_eq_subgroupOf
    have hle := IsPGroup.le_sylow_of_normal (p := 2) (G := ↥D.M)
      ((isPGroup_pCoreOf X).comap_subtype (K := D.M)) Q
    intro x hx
    have hxM : x ∈ D.M := hXM (hO2X hx)
    have hxsub : (⟨x, hxM⟩ : ↥D.M) ∈ (pCoreOf 2 X).subgroupOf D.M := hx
    have hxQ := hle hxsub
    rw [hQ] at hxQ
    exact hxQ
  have hTA : D.T ≤ normalizer ((D.T ⊓ X : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (fun t ht => hMX (D.sylowM.le ht))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTC : D.T ≤ normalizer ((D.T ⊓ C : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer ((D.sylowM.le).trans hMC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTT₀ : D.T ≤ normalizer (T₀ : Set G) := by
    rw [hT₀def]
    exact CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hTA hTC
  have hEC : E ≤ normalizer ((D.T ⊓ C : Subgroup G) : Set G) := by
    have hstep : ∀ e ∈ E, ∀ x ∈ D.T ⊓ C, e * x * e⁻¹ ∈ D.T ⊓ C := by
      intro e he x hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
      have heX : e ∈ X := hEX he
      have heM : e ∈ D.M := hXM heX
      have hcomm : x * e * x⁻¹ * e⁻¹ ∈ pCoreOf 2 X :=
        (mem_centOverO2_iff.mp hxC).2 e heX
      have hcomm' : e * x * e⁻¹ * x⁻¹ ∈ pCoreOf 2 X := by
        have hinv := (pCoreOf 2 X).inv_mem hcomm
        simpa [mul_assoc] using hinv
      have hcommT : e * x * e⁻¹ * x⁻¹ ∈ D.T := hO2T hcomm'
      have hconjT : e * x * e⁻¹ ∈ D.T := by
        have h : e * x * e⁻¹ = (e * x * e⁻¹ * x⁻¹) * x := by group
        rw [h]
        exact D.T.mul_mem hcommT hxT
      have hconjC : e * x * e⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hMC heM) x).mp hxC
      exact Subgroup.mem_inf.mpr ⟨hconjT, hconjC⟩
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hstep e he x, fun hx => ?_⟩
    have h := hstep e⁻¹ (E.inv_mem he) (e * x * e⁻¹) hx
    simpa [mul_assoc] using h
  have hET₀ : E ≤ normalizer (T₀ : Set G) := by
    rw [hT₀def]
    exact CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hEN hEC
  have hTnorm : D.T ≤ normalizer (X : Set G) := fun t ht => hMX (D.sylowM.le ht)
  let φ : ↥D.T →* Outer (Bar2 X) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X))).comp
      ((rhoL X).comp (Subgroup.inclusion hTnorm))
  haveI : Finite (MulAut (Bar2 X)) := Nobq.finite_mulAut_of_finite (Bar2 X)
  haveI : Finite (Outer (Bar2 X)) :=
    Finite.of_surjective
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X)))
      (QuotientGroup.mk'_surjective _)
  let Cφ : Subgroup (Outer (Bar2 X)) := φ.range
  have hφ2 : IsPGroup 2 Cφ := by
    obtain ⟨n, hn⟩ := D.sylowM.isPGroup.exists_card_dvd_pow
    have hdvd : Nat.card Cφ ∣ Nat.card ↥D.T := by
      rw [← Subgroup.card_ker_mul_card_range φ]
      exact dvd_mul_left _ _
    exact IsPGroup.of_card_dvd_pow (hdvd.trans hn)
  haveI : IsCyclic Cφ := hout Cφ hφ2
  let φ' : ↥D.T →* Cφ :=
    { toFun := fun u => ⟨φ u, ⟨u, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  refine inPStar_of_inP11_of_le_normalizer (D := D) (V₀ := V₀) (X := E) (T₀ := T₀)
    hE ?_ hTT₀ hET₀ φ' ?_
  · rw [hT₀def]
    exact sup_le inf_le_left inf_le_left
  · intro u hu
    have hu1 : φ u = 1 := by
      have := congrArg Subtype.val hu
      simpa [φ'] using this
    have hq : QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X))
        (rhoL X (Subgroup.inclusion hTnorm u)) = 1 := by
      simpa [φ] using hu1
    have hmem : rhoL X (Subgroup.inclusion hTnorm u) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
      have hker := MonoidHom.mem_ker.mpr hq
      rwa [QuotientGroup.ker_mk'] at hker
    have hinc : (Subgroup.inclusion hTnorm u : ↥(normalizer (X : Set G))) =
        ⟨(u : G), hMX (D.sylowM.le u.2)⟩ := Subtype.ext rfl
    have hin : rhoL X ⟨(u : G), hMX (D.sylowM.le u.2)⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
      rw [← hinc]
      exact hmem
    exact mem_T0_of_rhoL_mem_inner hX hMX u.2 hin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
