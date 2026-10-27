module

public import CFSG.RankThree.GF2n.Parrott.FusionE16Transport
public import CFSG.RankThree.GF2n.Parrott.FusionE16Model
public import CFSG.Sporadic.Co2Smith.GlC0JankoA
public import Certificates.Certificate946005
public import Certificates.Certificate946017
public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.Sporadic.Co2Smith (x45P)
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.FusionE16

private theorem map_x_eq_u_zero {X : Type} [Group X] {x : X} (hx : orderOf x = 2)
    (e : ↥(Subgroup.centralizer ({x} : Set X)) ≃*
      ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)))
    (cfg : E16Config ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)))
    (hZ : ∀ z ∈ Subgroup.center
        ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)), z = 1 ∨ z = cfg.u 0)
    (hxC : x ∈ Subgroup.centralizer ({x} : Set X)) :
    e ⟨x, hxC⟩ = cfg.u 0 := by
  have hcen : e ⟨x, hxC⟩ ∈ Subgroup.center
      ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨c, rfl⟩ := e.surjective h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  rcases hZ _ hcen with h1 | h1
  · exfalso
    have : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({x} : Set X))) = 1 :=
      e.injective (by simpa using h1)
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1, orderOf_one] at hx
    omega
  · exact h1

private theorem exists_conj_eq_u_one {X : Type} [Group X] {x : X} (hx : orderOf x = 2)
    (e : ↥(Subgroup.centralizer ({x} : Set X)) ≃*
      ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)))
    (cfg : E16Config ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)))
    (hconj : ∀ j ∈ CFSG.pCore 2
        ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)),
      orderOf j = 2 → j ≠ cfg.u 0 → ∃ c, c * j * c⁻¹ = cfg.u 1)
    (hxC : x ∈ Subgroup.centralizer ({x} : Set X))
    (hex : e ⟨x, hxC⟩ = cfg.u 0) (g : X)
    (hg : g⁻¹ * x * g ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({x} : Set X)))
    (hne : g⁻¹ * x * g ≠ x) :
    ∃ c, (e.symm c : X) * (g⁻¹ * x * g) * ((e.symm c : X))⁻¹ =
      (e.symm (cfg.u 1) : X) := by
  obtain ⟨j₁, hj₁, hj₁y⟩ := Subgroup.mem_map.mp hg
  have hy2 : orderOf (g⁻¹ * x * g) = 2 := by
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq, hx]
  have hj : e j₁ ∈ CFSG.pCore 2
      ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)) := by
    rw [← pCore_map_iso 2 e]
    exact Subgroup.mem_map_of_mem _ hj₁
  have hj2 : orderOf (e j₁) = 2 := by
    have hj₁y' : (j₁ : X) = g⁻¹ * x * g := hj₁y
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hj₁y', hy2]
  have hjne : e j₁ ≠ cfg.u 0 := by
    rw [← hex]
    intro h
    apply hne
    have h' := e.injective h
    have hj₁y' : (j₁ : X) = g⁻¹ * x * g := hj₁y
    rw [← hj₁y', h']
  obtain ⟨c, hc⟩ := hconj _ hj hj2 hjne
  refine ⟨c, ?_⟩
  let C : Subgroup X := Subgroup.centralizer ({x} : Set X)
  let ψ : ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)) →* X :=
    C.subtype.comp e.symm.toMonoidHom
  have h1 : ψ c * (g⁻¹ * x * g) * (ψ c)⁻¹ = ψ (cfg.u 1) := by
    have h := congrArg ψ hc
    rw [map_mul, map_mul, map_inv] at h
    have h2 : ψ (e j₁) = g⁻¹ * x * g := by
      show ((e.symm (e j₁) : C) : X) = _
      rw [MulEquiv.symm_apply_apply]
      exact hj₁y
    rwa [h2] at h
  simpa [ψ] using h1

theorem weaklyClosed_pCore_centralizer_of_equiv_x45P
    {X : Type} [Group X] [Finite X] {x : X} (hx : orderOf x = 2)
    (e : ↥(Subgroup.centralizer ({x} : Set X)) ≃*
        ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup))) :
    ∀ g : X, g⁻¹ * x * g ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({x} : Set X)) →
      g⁻¹ * x * g = x := by
  intro g hg
  by_contra hne'
  obtain ⟨cfg, -, hZ, hconj⟩ := exists_modelE16Config
  set C : Subgroup X := Subgroup.centralizer ({x} : Set X) with hC
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let ψ : ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)) →* X :=
    C.subtype.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.coe_injective.comp e.symm.injective
  have hex : e ⟨x, hxC⟩ = cfg.u 0 := map_x_eq_u_zero hx e cfg hZ hxC
  have hxψ : x = ψ (cfg.u 0) := by
    rw [← hex]
    simp [ψ]
  have hrange : ψ.range = C := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact (e.symm h).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp [ψ]⟩
  obtain ⟨cfg', hc0, hc1⟩ := E16Config.exists_transport cfg ψ hψ hxψ hrange
  obtain ⟨c, hc⟩ := exists_conj_eq_u_one hx e cfg hconj hxC hex g hg hne'
  have h1 : ψ c * (g⁻¹ * x * g) * (ψ c)⁻¹ = ψ (cfg.u 1) := by
    simpa [ψ] using hc
  have hconj' : IsConj (cfg'.u 0) (cfg'.u 1) := by
    rw [hc0, hc1]
    refine isConj_iff.mpr ⟨ψ c * g⁻¹, ?_⟩
    rw [← h1]
    group
  exact cfg'.false_of_isConj hconj'

end CFSG.RankThree.GF2n.Parrott
