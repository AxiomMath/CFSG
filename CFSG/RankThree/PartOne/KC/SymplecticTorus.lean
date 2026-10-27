module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spScalarKernel (r : ℕ) (K : Type) [Field K] : Subgroup (gsp r K) :=
  (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) : Kˣ →* GL (Fin r ⊕ Fin r) K).range.comap
    (gsp r K).subtype

theorem mem_spScalarKernel {A : gsp r K} :
    A ∈ spScalarKernel r K ↔ ∃ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) =
      Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

variable (r K) in
@[expose] noncomputable def spCentralizerD (t : MulAut (StatedProj (StatedSp r K))) :
    Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  (conjAut r K).range ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))

variable (r K) in
@[expose] noncomputable def spCenterN (t : MulAut (StatedProj (StatedSp r K))) :
    Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  (Subgroup.center ↥(spCentralizerD r K t)).map (spCentralizerD r K t).subtype

@[expose] noncomputable def spBlockImage (x : StatedSp r K) (a : K[X]) :
    Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  (spBlockGSp x a).map (conjAut r K)

instance spScalarKernel_normal : (spScalarKernel r K).Normal where
  conj_mem A hA g := by
    obtain ⟨c, hc⟩ := mem_spScalarKernel.mp hA
    have h : g * A * g⁻¹ = A := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc,
        ← (commute_scalar_gl c (g : GL (Fin r ⊕ Fin r) K)).eq, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [h]
    exact hA

theorem mem_spScalarKernel_iff_conjAut [Finite K] (hr : 1 ≤ r) {A : gsp r K} :
    conjAut r K A = 1 ↔ A ∈ spScalarKernel r K := by
  rw [conjAut_eq_one_iff hr, mem_spScalarKernel]

theorem spScalarKernel_eq_ker [Finite K] (hr : 1 ≤ r) :
    spScalarKernel r K = (conjAut r K).ker :=
  Subgroup.ext fun _ => (mem_spScalarKernel_iff_conjAut hr).symm

end CFSG.RankThree.PartOne.KCSpComm

namespace CFSG.RankThree.PartOne

open Polynomial CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

theorem symplectic_cross_prime_isotypic_local_core_torus {ℓ f r p : ℕ} {K : Type} [Field K]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hq : 3 < ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B)
    (t : MulAut (StatedProj (StatedSp r K)))
    (ht : t ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range) (htp : orderOf t = p) :
    (∃! x : StatedSp r K, orderOf x = p ∧ MulAut.conj (proj r K x) = t) ∧
    ∀ x : StatedSp r K, orderOf x = p → MulAut.conj (proj r K x) = t →
      ((spCentralizerD r K t =
          (Subgroup.centralizer ({spXg x} : Set (gsp r K))).map (conjAut r K) ∧
        ∀ A : gsp r K, conjAut r K A = 1 ↔ A ∈ spScalarKernel r K) ∧
      (∀ A : gsp r K, A ∈ spCenterUnits x ↔
        ∃ hz : ((gspLin r K A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
            Module.End K (Fin r ⊕ Fin r → K)) ∈ commutant (spEnd x),
          (⟨((gspLin r K A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
            Module.End K (Fin r ⊕ Fin r → K)), hz⟩ : commutant (spEnd x)) ∈
            Subalgebra.center K (commutant (spEnd x))) ∧
      (∀ a : SpBlockIdx x,
        spBlockImage x (a.1 : K[X]) ≤ inner (StatedProj (StatedSp r K)) ∧
        CFSG.IsComponent ((spBlockImage x (a.1 : K[X])).subgroupOf
          (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))))) ∧
      (∀ a b : SpBlockIdx x, (b.1 : K[X]) = reciprocalPolynomial (a.1 : K[X]) →
        spBlockImage x (b.1 : K[X]) = spBlockImage x (a.1 : K[X])) ∧
      (∀ a b : SpBlockIdx x, (b.1 : K[X]) ≠ (a.1 : K[X]) →
        (b.1 : K[X]) ≠ reciprocalPolynomial (a.1 : K[X]) →
        ∀ g ∈ spBlockImage x (a.1 : K[X]), ∀ g' ∈ spBlockImage x (b.1 : K[X]),
          Commute g g') ∧
      ⁅spCentralizerD r K t, spCentralizerD r K t⁆ =
        ⨆ a : SpBlockIdx x, spBlockImage x (a.1 : K[X]) ∧
      CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))) ≤
        Subgroup.centralizer ((⁅spCentralizerD r K t, spCentralizerD r K t⁆ :
          Subgroup (MulAut (StatedProj (StatedSp r K)))) :
            Set (MulAut (StatedProj (StatedSp r K)))) ∧
      (spCentralizerD r K t ⊓ Subgroup.centralizer ((⁅spCentralizerD r K t,
          spCentralizerD r K t⁆ : Subgroup (MulAut (StatedProj (StatedSp r K)))) :
            Set (MulAut (StatedProj (StatedSp r K)))) = spCenterN r K t ∧
        spCenterN r K t = (spCenterUnits x).map (conjAut r K) ∧
        ∃ e : (spCenterUnits x ⧸ (spScalarKernel r K).subgroupOf (spCenterUnits x)) ≃*
            ↥(spCenterN r K t),
          ∀ z : spCenterUnits x, ((e (QuotientGroup.mk z) : ↥(spCenterN r K t)) :
            MulAut (StatedProj (StatedSp r K))) = conjAut r K z) ∧
      ((∀ a ∈ spCenterN r K t ⊓ (B ⊓ Subgroup.centralizer ({t} :
            Set (MulAut (StatedProj (StatedSp r K))))),
          ∀ b ∈ spCenterN r K t ⊓ (B ⊓ Subgroup.centralizer ({t} :
            Set (MulAut (StatedProj (StatedSp r K))))), a * b = b * a) ∧
        ((spCenterN r K t ⊓ (B ⊓ Subgroup.centralizer ({t} :
            Set (MulAut (StatedProj (StatedSp r K)))))).subgroupOf
          (B ⊓ Subgroup.centralizer ({t} :
            Set (MulAut (StatedProj (StatedSp r K)))))).Normal)) := by
  have hr1 : 1 ≤ r := by omega
  have : NeZero r := ⟨by omega⟩
  obtain ⟨huniq, hdata⟩ := exists_unique_lift hℓ hf hr hK hq hp hp3 hpℓ t ht htp
  refine ⟨huniq, ?_⟩
  intro x hxo hxt
  obtain ⟨D, blocks⟩ := hdata x hxo hxt
  have hinfin : Finite K := D.finite
  have hS := spProjSetting D blocks B hB
  have facts := D.blockFacts blocks
  have ht' : conjAut r K (spXg x) = t := (conjAut_statedSp x).trans hxt
  subst ht'
  have hN : spCentralizerD r K (conjAut r K (spXg x)) =
      (Subgroup.centralizer ({spXg x} : Set (gsp r K))).map (conjAut r K) := hS.N_eq
  have key : ∀ N' : Subgroup (MulAut (StatedProj (StatedSp r K))),
      spCentralizerD r K (conjAut r K (spXg x)) = N' →
      spCenterN r K (conjAut r K (spXg x)) = (Subgroup.center ↥N').map N'.subtype := by
    intro N' hN'
    subst hN'
    rfl
  have hQ := key _ hN
  have hQ' : spCenterN r K (conjAut r K (spXg x)) =
      (spCenterUnits x).map (conjAut r K) := by
    rw [hQ]
    exact hS.center_image_eq
  have hker : (conjAut r K).ker = spScalarKernel r K := (spScalarKernel_eq_ker hr1).symm
  refine ⟨⟨hN, fun A => mem_spScalarKernel_iff_conjAut hr1⟩, fun A => mem_spCenterUnits,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    refine ⟨?_, hS.isComponent_image a⟩
    have := Subgroup.map_mono (f := conjAut r K) (hS.F_le_Hs a)
    rwa [map_ker_multiplier] at this
  · intro a b hb
    have hrr : ∀ c ∈ primaryFactors (spEnd x),
        reciprocalPolynomial (reciprocalPolynomial c) = c :=
      fun c hc => D.primaryData.reciprocal_reciprocal hc
    have h1 := specialBlock_reciprocal facts hrr a.1 b.1 hb a.2 b.2
    show (spBlockGSp x (b.1 : K[X])).map (conjAut r K) =
      (spBlockGSp x (a.1 : K[X])).map (conjAut r K)
    unfold spBlockGSp
    rw [h1]
  · rintro a b hba hbd _ ⟨A, hA, rfl⟩ _ ⟨A', hA', rfl⟩
    have h1 := commute_specialBlock_of_ne blocks a.1 b.1 hba hbd hA hA'
    have h2 : A * A' = A' * A :=
      gspLin_injective (by rw [map_mul, map_mul]; exact h1.eq)
    show conjAut r K A * conjAut r K A' = conjAut r K A' * conjAut r K A
    rw [← map_mul, ← map_mul, h2]
  · rw [hN]
    exact hS.commutator_image_eq
  · rw [hN]
    exact hS.core_le_centralizer_derived hp
  · refine ⟨?_, hQ', ?_⟩
    · rw [hQ, hN]
      exact hS.inf_centralizer_derived_eq_center
    · obtain ⟨e0, he0⟩ := exists_quotient_equiv (conjAut r K) (spCenterUnits x)
      refine ⟨((QuotientGroup.quotientMulEquivOfEq (by rw [hker])).trans e0).trans
        (MulEquiv.subgroupCongr hQ'.symm), fun z => ?_⟩
      exact he0 z
  · rw [hQ]
    exact ⟨fun a ha b hb => ProjSetting.center_inf_comm (Subgroup.mem_inf.mp ha).1
      (Subgroup.mem_inf.mp hb).1, hS.center_inf_normal⟩

end CFSG.RankThree.PartOne
