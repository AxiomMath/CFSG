module

public import CFSG.LocalAnalysis.StandardType.GGStdPosAutCent
public import CFSG.LocalAnalysis.StandardType.GGStdPosWeylNorm
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem ggStdPosAut_conj_mem_centralizer {G : Type*} [Group G] {Bs : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {y : G}
    (hy : y ∈ Subgroup.centralizer (Bs : Set G)) :
    g * y * g⁻¹ ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro b hb
  have hb' := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) b).mp hb
  rw [inv_inv] at hb'
  calc b * (g * y * g⁻¹) = g * ((g⁻¹ * b * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * b * g)) * g⁻¹ := by rw [hy _ hb']
    _ = g * y * g⁻¹ * b := by group

private theorem ggStdPosAut_mem_normalizer_comap {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    {Bs : Subgroup G} {k : K} (hk : ψ k ∈ Subgroup.normalizer (Bs : Set G)) :
    k ∈ Subgroup.normalizer ((Subgroup.centralizer (Bs : Set G)).comap ψ : Set K) := by
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact ggStdPosAut_conj_mem_centralizer hk (Subgroup.mem_comap.mp hc)
  · have h1 := ggStdPosAut_conj_mem_centralizer (inv_mem hk) (Subgroup.mem_comap.mp hc)
    rw [map_mul, map_mul, map_inv, show (ψ k)⁻¹ * (ψ k * ψ c * (ψ k)⁻¹) * (ψ k)⁻¹⁻¹ = ψ c by
      group] at h1
    exact Subgroup.mem_comap.mpr h1

theorem ggStdPos_exists_autWeyl {K : Type*} [Group K] {D : UniversalRootDatum K}
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
    {G : Type} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G}
    (hBs : GGKGPosStdPos D ψ Bs) (hN : Bs ≤ Subgroup.normalizer (ψ.range : Set G))
    (hpow : ∀ b ∈ Bs, b ^ p = 1)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    ∃ ε : GGWeyl D ≃* ↥(ggAutomizer ψ.range Bs), ∀ (w : GGWeyl D) (b : ↥Bs),
      ((ε w : MulAut ↥Bs) b : G) = ψ (ν w) * b * (ψ (ν w))⁻¹ := by
  have hS5 : ∀ w, ψ (ν w) ∈ Subgroup.normalizer (Bs : Set G) := fun w =>
    ggStdPos_psi_mem_normalizer hct hext hBU hE ψ hker hBs hN hpow hC3
      (ggStdPos_actsAs_weylLift hν w)
  let ε₀ : GGWeyl D →* MulAut ↥Bs :=
    Bs.normalizerMonoidHom.comp ((ψ.comp ν).codRestrict _ hS5)
  have hε₀ : ∀ w (b : ↥Bs), ((ε₀ w b : ↥Bs) : G) = ψ (ν w) * b * (ψ (ν w))⁻¹ :=
    fun _ _ => rfl
  have hmem : ∀ w, ε₀ w ∈ ggAutomizer ψ.range Bs := fun w =>
    Subgroup.subset_closure ⟨ψ (ν w), ⟨ν w, rfl⟩, hS5 w, hε₀ w⟩
  let ε₁ : GGWeyl D →* ↥(ggAutomizer ψ.range Bs) := ε₀.codRestrict _ hmem
  have hinj : Function.Injective ε₁ := by
    refine (injective_iff_map_eq_one ε₁).mpr fun w hw => ?_
    refine ggStdPos_eq_one_of_psi_mem_centralizer hct hext hBU hE h2 hR2 ψ hker hBs hC3
      (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    have h3 := congrArg (fun φ : ↥(ggAutomizer ψ.range Bs) =>
      (((φ : MulAut ↥Bs) ⟨b, hb⟩ : ↥Bs) : G)) hw
    change ψ (ν w) * b * (ψ (ν w))⁻¹ = b at h3
    exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  have hcomap := ggStdPos_comap_centralizer_eq hct hext hBU hE hdiv h2 hζ hζ1 hν hR2 ψ hker hBs
    hC3
  have hle : ggAutomizer ψ.range Bs ≤ ε₀.range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨g, ⟨k, rfl⟩, hgN, hφg⟩
    have hkN : k ∈ Subgroup.normalizer (ggTorus D : Set K) := by
      rw [← hcomap]
      exact ggStdPosAut_mem_normalizer_comap ψ hgN
    obtain ⟨h, hh, w, rfl⟩ :=
      (ggStdPos_mem_normalizer_ggTorus_iff hct hext hBU hE hdiv hζ1 hν k).mp hkN
    refine ⟨w, MulEquiv.ext fun b => Subtype.ext ?_⟩
    have hb' : ψ (ν w) * b * (ψ (ν w))⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hS5 w) b).mp b.2
    have hc := Subgroup.mem_centralizer_iff.mp
      (ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hBs h hh) _ hb'
    rw [hε₀, hφg, map_mul]
    calc ψ (ν w) * b * (ψ (ν w))⁻¹ = ψ h * (ψ (ν w) * b * (ψ (ν w))⁻¹) * (ψ h)⁻¹ := by
          rw [← hc, mul_inv_cancel_right]
      _ = ψ h * ψ (ν w) * b * (ψ h * ψ (ν w))⁻¹ := by group
  have hsurj : Function.Surjective ε₁ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨w, hw⟩ := hle hφ
    exact ⟨w, Subtype.ext hw⟩
  exact ⟨MulEquiv.ofBijective ε₁ ⟨hinj, hsurj⟩, hε₀⟩

end CFSG.StandardType

end
