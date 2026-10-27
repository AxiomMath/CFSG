module

public import CFSG.LocalAnalysis.StandardType.GGStdPosNoTriv
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusNorm
public import CFSG.LocalAnalysis.StandardType.GGStdPosCore
public import CFSG.LocalAnalysis.StandardType.GGStdPosTrans
import TauCeti.GroupTheory.Coxeter.Geometric
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

theorem ggStdPos_eq_one_of_psi_mem_centralizer {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    (h2 : 2 ≤ D.rank) {p : ℕ} {ν : GGWeyl D →* K}
    (hR2 : ∀ (u : GGWeyl D) (i : Fin D.rank) (w : GGWeyl D),
      (∀ h ∈ ggTorusRootKer D p (weylAction D.isFiniteType u (Pi.single i 1)),
        ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center K) →
      w = 1 ∨ w = u * (coxeterMatrix D.isFiniteType).simple i * u⁻¹)
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G}
    (hBs : GGKGPosStdPos D ψ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {w : GGWeyl D}
    (hw : ψ (ν w) ∈ Subgroup.centralizer (Bs : Set G)) : w = 1 := by
  have key : ∀ i, w = 1 ∨ w = (coxeterMatrix D.isFiniteType).simple i := by
    intro i
    have h1 := hR2 1 i w fun h hh => by
      obtain ⟨hhT, hhp, -⟩ := hh
      have hhB : ψ h ∈ Bs := hC3 _
        (ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hBs h hhT)
        (by rw [← map_pow, hhp, map_one])
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← Subgroup.mem_centralizer_iff.mp hw _ hhB]
      group
    simpa only [one_mul, inv_one, mul_one] using h1
  rcases key ⟨0, by omega⟩ with h0 | h0
  · exact h0
  rcases key ⟨1, by omega⟩ with h1 | h1
  · exact h1
  have hinj := (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_injective
  rw [CoxeterMatrix.toCoxeterSystem_simple] at hinj
  exact absurd (congrArg Fin.val (hinj (h0.symm.trans h1))) (by simp)

theorem ggStdPos_comap_centralizer_eq {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [Finite F]
    [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) (h2 : 2 ≤ D.rank) {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    {ν : GGWeyl D →* K} (hν : GGWeylLift D ν)
    (hR2 : ∀ (u : GGWeyl D) (i : Fin D.rank) (w : GGWeyl D),
      (∀ h ∈ ggTorusRootKer D p (weylAction D.isFiniteType u (Pi.single i 1)),
        ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center K) →
      w = 1 ∨ w = u * (coxeterMatrix D.isFiniteType).simple i * u⁻¹)
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G}
    (hBs : GGKGPosStdPos D ψ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    (Subgroup.centralizer (Bs : Set G)).comap ψ = ggTorus D := by
  refine le_antisymm (fun k hk => ?_) fun h hh =>
    ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hBs h hh
  have hnt := ggStdPos_noTrivRoot hct hext hBU hE hdiv ψ hker hBs hC3 hζ hζ1
  have hfree : ∀ β, ¬ (β ∈ D.roots ∧
      D.rootGroup β ≤ (Subgroup.centralizer (Bs : Set G)).comap ψ) := by
    rintro β ⟨hβ, hle⟩
    obtain ⟨b, hb, z, hz, hne⟩ := hnt β hβ
    exact hne (by rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp (hle hz)) b hb,
      mul_inv_cancel_right])
  have hS := ggStdPos_centralizer_eq hct hext hBU
    (ggStdPos_transitive_of_chevalleyExtras hct hE hdiv) ψ hker (Bs : Set G) hBs
  have hkN : k ∈ Subgroup.normalizer (ggTorus D : Set K) :=
    (hS.le.trans (sup_le inf_le_right (iSup₂_le fun β hβ => absurd hβ (hfree β)))) hk
  obtain ⟨h, hh, w, rfl⟩ :=
    (ggStdPos_mem_normalizer_ggTorus_iff hct hext hBU hE hdiv hζ1 hν k).mp hkN
  have hwC : ψ (ν w) ∈ Subgroup.centralizer (Bs : Set G) := by
    have h3 := mul_mem (inv_mem (ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hBs h hh))
      (Subgroup.mem_comap.mp hk)
    rwa [map_mul, inv_mul_cancel_left] at h3
  rw [ggStdPos_eq_one_of_psi_mem_centralizer hct hext hBU hE h2 hR2 ψ hker hBs hC3 hwC, map_one,
    mul_one]
  exact hh

end CFSG.StandardType

end
