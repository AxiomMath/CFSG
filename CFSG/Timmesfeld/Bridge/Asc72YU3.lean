module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitaryCoord
public import CFSG.Models.BenderSuzuki

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

namespace YU3

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

theorem adjust_mul_self {G : Type*} [Group G] [Finite G] {R R₀ : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hR₀ : R₀ ≠ R) (α : MulAut G) (hαα : α * α = 1) (hαR : α • R = R) {r : G}
    (hr : r ∈ (R : Subgroup G)) (hrR₀ : ((MulAut.conj r)⁻¹ * α) • R₀ = R₀) :
    ((MulAut.conj r)⁻¹ * α) * ((MulAut.conj r)⁻¹ * α) = 1 := by
  set γ := (MulAut.conj r)⁻¹ * α with hγdef
  have hαα' : ∀ g, α (α g) = g := fun g => by
    rw [← MulAut.mul_apply, hαα, MulAut.one_apply]
  have hγsq : ∀ g, γ (γ g) = (r⁻¹ * (α r)⁻¹) * g * (r⁻¹ * (α r)⁻¹)⁻¹ := by
    intro g
    have e1 : ∀ y, γ y = r⁻¹ * α y * r := fun y => by
      rw [hγdef, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    rw [e1, e1, map_mul, map_mul, map_inv, hαα']
    group
  have hcR : r⁻¹ * (α r)⁻¹ ∈ (R : Subgroup G) :=
    (R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem hr)
      ((R : Subgroup G).inv_mem (InvInner.apply_mem_of_smul_eq hαR hr))
  have hc1 : r⁻¹ * (α r)⁻¹ = 1 := by
    apply Omega.eq_one_of_mem_normalizer hSE hR₀ hcR
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rw [Sylow.smul_def]
    apply Omega.smul_eq_of_mapsTo
    intro s hs
    have h1 : γ (γ s) ∈ (R₀ : Subgroup G) :=
      InvInner.apply_mem_of_smul_eq hrR₀ (InvInner.apply_mem_of_smul_eq hrR₀ hs)
    rw [hγsq] at h1
    rw [MulAut.conj_apply]
    exact h1
  ext g
  rw [MulAut.mul_apply, hγsq, hc1, one_mul, inv_one, mul_one, MulAut.one_apply]

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem fix_center_root (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hαα : α * α = 1) (hαS : α • S = S) :
    ∀ x ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), α x = x := by
  classical
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hconjU : ∀ (k : Kˣ) (z : hermitianUnipotentCoord J),
      hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹ =
        U (hermitianTorusAction J k z) := unitaryCoverTorus_conj_root J hJ
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  have hHN : unitaryCoverTorus J hJ ≤
      Subgroup.normalizer (((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) : Set _) := by
    rw [hS]
    exact unitaryCoverTorus_le_normalizer J hJ
  rw [← hS] at hNR hcard
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  have hHN₁ : unitaryCoverTorus J hJ ≤ Subgroup.normalizer
      ((((hermitianWeylPSU J hJ • S : Sylow 2 _)) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    rintro _ ⟨k, rfl⟩
    rw [Omega.mem_normalizer_conj_smul_iff]
    have h := weyl_conj_torus J hJ (Units.map J.conj.toMonoidHom k)⁻¹
    have hk : (Units.map J.conj.toMonoidHom (Units.map J.conj.toMonoidHom k)⁻¹)⁻¹ = k := by
      ext
      simp [J.conj_involutive (k : K)]
    rw [hk] at h
    have h2 : (hermitianWeylPSU J hJ)⁻¹ * hermitianTorusPSU J hJ k * hermitianWeylPSU J hJ =
        hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
      rw [← h]
      group
    rw [h2]
    exact hHN ⟨_, rfl⟩
  obtain ⟨r, hr, hrS⟩ := Omega.exists_conj_adjust hSE hcard hS₁ α hαS
  set γ := (MulAut.conj r)⁻¹ * α with hγdef
  have hαeq : α = MulAut.conj r * γ := by rw [hγdef, mul_inv_cancel_left]
  have hγS : γ • S = S := by
    rw [hγdef, mul_smul, hαS, inv_smul_eq_iff, Omega.conj_smul_self hr]
  have hγγ : γ * γ = 1 := adjust_mul_self hSE hS₁ α hαα hαS hr hrS
  have hγH : ∀ k : Kˣ, ∃ k' : Kˣ, γ (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k' := by
    intro k
    have h1 := Omega.mem_normalizer_smul (α := γ) (hHN ⟨k, rfl⟩)
    have h2 := Omega.mem_normalizer_smul (α := γ) (hHN₁ ⟨k, rfl⟩)
    rw [hγS] at h1
    rw [hrS] at h2
    obtain ⟨k', hk'⟩ := Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2
    exact ⟨k', hk'.symm⟩
  have hRS : ∀ z, U z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := fun z => by
    rw [hS]
    exact ⟨z, rfl⟩
  have hex : ∀ z : hermitianUnipotentCoord J, ∃ z', γ (U z) = U z' := by
    intro z
    have h := InvInner.apply_mem_of_smul_eq hγS (hRS z)
    rw [hS] at h
    obtain ⟨z', hz'⟩ := h
    exact ⟨z', hz'.symm⟩
  choose ψf hψf using hex
  let ψ : hermitianUnipotentCoord J →* hermitianUnipotentCoord J :=
    { toFun := ψf
      map_one' := by
        apply hU
        rw [← hψf, map_one, map_one]
      map_mul' := fun z z' => by
        apply hU
        rw [← hψf, map_mul, map_mul, map_mul, hψf, hψf] }
  have hψU : ∀ z, U (ψ z) = γ (U z) := fun z => (hψf z).symm
  have hψψ : ∀ z, ψ (ψ z) = z := fun z => hU (by
    rw [hψU, hψU]
    change (γ * γ) (U z) = U z
    rw [hγγ, MulAut.one_apply])
  have hψtor : ∀ k : Kˣ, ∃ k' : Kˣ,
      ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z) := by
    intro k
    obtain ⟨k', hk'⟩ := hγH k
    refine ⟨k', fun z => hU ?_⟩
    calc U (ψ (hermitianTorusAction J k z)) = γ (U (hermitianTorusAction J k z)) := hψU _
      _ = γ (hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹) := by
          rw [hconjU]
      _ = γ (hermitianTorusPSU J hJ k) * γ (U z) * (γ (hermitianTorusPSU J hJ k))⁻¹ := by
          rw [map_mul, map_mul, mulAut_apply_inv]
      _ = hermitianTorusPSU J hJ k' * U (ψ z) * (hermitianTorusPSU J hJ k')⁻¹ := by
          rw [hk', hψU]
      _ = U (hermitianTorusAction J k' (ψ z)) := hconjU k' (ψ z)
  have hψcen := UnitaryCoordAut.center_fixed J (2 ^ f) hKcard hfixed hq4 hJ ψ hψψ hψtor
  intro x hx
  have hxS := (mem_sylowCenter.mp hx).1
  have hxc := (mem_sylowCenter.mp hx).2
  rw [hS] at hxS
  obtain ⟨z, rfl⟩ := hxS
  have hz0 : z.1.1 = 0 := by
    rw [← mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ z, ← hS]
    exact hx
  have hγx : γ (U z) = U z := by rw [← hψU, hψcen z hz0]
  rw [hαeq, MulAut.mul_apply, hγx, MulAut.conj_apply, hUdef, hxc r hr, mul_inv_cancel_right]

theorem fix_center_of_mulEquiv_psu3 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) (T : Sylow 2 X) (α : MulAut X) (hαα : α * α = 1)
    (hαT : ∀ s ∈ (T : Subgroup X), α s ∈ T) {x : X} (hxT : x ∈ (T : Subgroup X))
    (hxc : ∀ y ∈ (T : Subgroup X), Commute x y) : α x = x := by
  classical
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : BenderSuzuki.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  let e₃ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e₂.symm
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  let TM : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    T.mapSurjective (f := e₃.toMonoidHom) e₃.surjective
  have hmemTM : ∀ y, y ∈ (TM : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      e₃.symm y ∈ (T : Subgroup X) := fun y => by
    change y ∈ (T : Subgroup X).map e₃.toMonoidHom ↔ _
    exact AutTransport.mem_map_iff' e₃
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S TM
  have hmemS : ∀ y, g * y * g⁻¹ ∈ (TM : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      y ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := fun y => by
    rw [← hg, Omega.mem_conj_smul_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  set β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MulAut.conj g)⁻¹ * MulAut.congr e₃ α * MulAut.conj g with hβdef
  have hβ : ∀ y, β y = g⁻¹ * e₃ (α (e₃.symm (g * y * g⁻¹))) * g := fun y => by
    rw [hβdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
      MulAut.conj_apply, MulAut.congr_apply]
    rfl
  have hαα' : ∀ t, α (α t) = t := fun t => by rw [← MulAut.mul_apply, hαα, MulAut.one_apply]
  have hββ : β * β = 1 := by
    ext y
    rw [MulAut.mul_apply, hβ, hβ, MulAut.one_apply,
      show g * (g⁻¹ * e₃ (α (e₃.symm (g * y * g⁻¹))) * g) * g⁻¹ =
        e₃ (α (e₃.symm (g * y * g⁻¹))) by group, MulEquiv.symm_apply_apply, hαα',
      MulEquiv.apply_symm_apply]
    group
  have hβS : β • S = S := by
    refine Omega.smul_eq_of_mapsTo fun s hs => ?_
    have h1 : e₃.symm (g * s * g⁻¹) ∈ (T : Subgroup X) := (hmemTM _).mp ((hmemS s).mpr hs)
    have h2 : e₃ (α (e₃.symm (g * s * g⁻¹))) ∈
        (TM : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [hmemTM, MulEquiv.symm_apply_apply]
      exact hαT _ h1
    rw [hβ]
    apply (hmemS _).mp
    rw [show g * (g⁻¹ * e₃ (α (e₃.symm (g * s * g⁻¹))) * g) * g⁻¹ =
      e₃ (α (e₃.symm (g * s * g⁻¹))) by group]
    exact h2
  have hgx : g * (g⁻¹ * e₃ x * g) * g⁻¹ = e₃ x := by group
  have hy : g⁻¹ * e₃ x * g ∈
      sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [mem_sylowCenter]
    refine ⟨(hmemS _).mp (by rw [hgx, hmemTM, MulEquiv.symm_apply_apply]; exact hxT), ?_⟩
    intro t ht
    have ht' : e₃.symm (g * t * g⁻¹) ∈ (T : Subgroup X) := (hmemTM _).mp ((hmemS t).mpr ht)
    have hc := (hxc _ ht').map e₃
    rw [MulEquiv.apply_symm_apply] at hc
    have h1 : (g * t * g⁻¹) * e₃ x = e₃ x * (g * t * g⁻¹) := hc.eq.symm
    calc t * (g⁻¹ * e₃ x * g) = g⁻¹ * ((g * t * g⁻¹) * e₃ x) * g := by group
      _ = g⁻¹ * (e₃ x * (g * t * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * e₃ x * g * t := by group
  have h := fix_center_root J f hf hKcard hfixed hJ S hS β hββ hβS _ hy
  rw [hβ, hgx, MulEquiv.symm_apply_apply] at h
  have h2 : e₃ (α x) = e₃ x := by
    calc e₃ (α x) = g * (g⁻¹ * e₃ (α x) * g) * g⁻¹ := by group
      _ = e₃ x := by rw [h]; group
  exact e₃.injective h2

end YU3

end CFSG.Timmesfeld.Bridge.Asc72
