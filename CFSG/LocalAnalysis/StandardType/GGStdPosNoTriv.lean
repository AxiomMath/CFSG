module

public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerTorus
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

theorem ggStdPos_noTrivRoot {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ} {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {ζ : Fˣ}
    (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) : GGKGPosNoTrivRoot D ψ Bs := by
  rintro γ (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩)
  swap
  · rw [hdiv] at hj
    exact absurd hj (Set.notMem_empty j)
  have hα : Pi.single j 1 ∈ D.roots := single_mem_roots j
  have hpar := hE.param (Pi.single j 1) hα
  have hm := actsAs_nrep hct w
  set m := nrep hct w
  set e := PsiDiag.torusElt x j ζ
  have heT : e ∈ ggTorus D :=
    ggRootKer_mem_ggTorus_of_scalar hE fun β hβ => ⟨_, PsiDiag.torusElt_conj hE j ζ hβ⟩
  have hep : e ^ p = 1 := by
    let τ : Fˣ →* K := MonoidHom.mk' (fun s => PsiDiag.torusElt x j s)
      (ggRootKer_torusElt_mul hE j)
    change τ ζ ^ p = 1
    rw [← map_pow, hζ, map_one]
  obtain ⟨h, hh⟩ : ∃ h, h = m * e * m⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = m * x (Pi.single j 1) 1 * m⁻¹ := ⟨_, rfl⟩
  have hhB : ψ h ∈ Bs := by
    rw [hh]
    refine hC3 _ (ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hBs _
      (ggStdPos_conj_mem_ggTorus_of_actsAs heT hm)) ?_
    rw [← map_pow, conj_pow, hep, mul_one, mul_inv_cancel, map_one]
  have hzX : z ∈ D.rootGroup (weylAction D.isFiniteType w (Pi.single j 1)) := by
    rw [hz]
    exact hm.conj_mem hα ((hpar.1 _).mpr ⟨1, rfl⟩)
  refine ⟨ψ h, hhB, z, hzX, fun hfix => hζ1 ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : F, s = ((ζ ^ (2 : ℤ) : Fˣ) : F) := ⟨_, rfl⟩
  have he : ∀ a, e * x (Pi.single j 1) a * e⁻¹ = x (Pi.single j 1) (s * a) := fun a => by
    rw [PsiDiag.torusElt_conj hE j ζ hα, coroot_single, D.isFiniteType.apply_self j, hs]
  have hsub : ∀ a b : F,
      x (Pi.single j 1) a * (x (Pi.single j 1) b)⁻¹ = x (Pi.single j 1) (a - b) := fun a b => by
    rw [mul_inv_eq_iff_eq_mul, ← hpar.2.1, sub_add_cancel]
  have hu : h * z * h⁻¹ * z⁻¹ ∈ Subgroup.center K := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hfix, mul_inv_cancel]
  have e1 : h * z * h⁻¹ * z⁻¹ = m * x (Pi.single j 1) (s - 1) * m⁻¹ := by
    calc h * z * h⁻¹ * z⁻¹ =
        m * ((e * x (Pi.single j 1) 1 * e⁻¹) * (x (Pi.single j 1) 1)⁻¹) * m⁻¹ := by
          rw [hh, hz]
          group
      _ = m * x (Pi.single j 1) (s - 1) * m⁻¹ := by rw [he, mul_one, hsub]
  rw [e1] at hu
  have hxc : x (Pi.single j 1) (s - 1) ∈ Subgroup.center K := by
    have h1 := Subgroup.Normal.conj_mem inferInstance _ hu m⁻¹
    rwa [show m⁻¹ * (m * x (Pi.single j 1) (s - 1) * m⁻¹) * m⁻¹⁻¹ = x (Pi.single j 1) (s - 1) by
      group] at h1
  have hfx : e * x (Pi.single j 1) (s - 1) * e⁻¹ = x (Pi.single j 1) (s - 1) := by
    rw [Subgroup.mem_center_iff.mp hxc e, mul_inv_cancel_right]
  rw [he] at hfx
  have h1 : (s - 1) * (s - 1) = 0 := by linear_combination hpar.2.2 hfx
  have h2 : (ζ : F) * ζ = 1 := by
    have h3 := sub_eq_zero.mp (mul_self_eq_zero.mp h1)
    rwa [hs, zpow_two, Units.val_mul] at h3
  apply Units.ext
  apply CharTwo.sq_injective (R := F)
  show (ζ : F) ^ 2 = ((1 : Fˣ) : F) ^ 2
  rw [sq, sq, h2, Units.val_one, one_mul]

end CFSG.StandardType

end
