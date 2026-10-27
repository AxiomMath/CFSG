module

public import CFSG.LocalAnalysis.StandardType.GGE0PSUFrame
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.SemisimpleCentralizers
  CFSG.StandardType.ClassicalPosition
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.Universal.Unitary (conjTr antidiag)

private lemma range_conj_specialUnitary {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    (P : GL (Fin n) F)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      antidiag n) :
    ((MulAut.conj P).toMonoidHom.comp (Unitary.SU σ n).subtype).range =
      Unitary.SUid σ n := by
  have h : (MulAut.conj P).toMonoidHom.comp (Unitary.SU σ n).subtype =
      (Unitary.SUid σ n).subtype.comp (Unitary.conjEquiv (σ := σ) P hP).toMonoidHom := by
    ext A
    simp [MulAut.conj_apply, Unitary.coe_conjEquiv]
  rw [h, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (Unitary.conjEquiv (σ := σ) P hP).surjective,
    Subgroup.map_top, Subgroup.range_subtype]

private lemma specialUnitary_eq_heldGU_inf_detKer {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    (hτ : ∀ x, σ (σ x) = x) :
    Unitary.SUid σ n =
      Held.heldGU n F σ hτ ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin n) F →* Fˣ).ker := by
  rw [← CFSG.Open.StatedAPI.statedSL_eq_ker_det]
  ext A
  simp only [Unitary.SUid, Held.mem_heldGU, CFSG.Open.StatedAPI.mem_statedSL_iff,
    Subgroup.mem_inf, conjTr]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

private lemma centralizer_liftSet_eq {F : Type} [Field F] {n : ℕ} {X U : Type}
    [Group X] [Group U] (j : U →* GL (Fin n) F) (ψ : U →* X) {b : X}
    {s' : GL (Fin n) F} (hs : IsGLLift j ψ s' b) :
    Subgroup.centralizer
        {t : GL (Fin n) F | t ∈ Subgroup.zpowers s' ∧
          ∃ d ∈ Subgroup.zpowers b, IsGLLift j ψ t d} =
      Subgroup.centralizer ({s'} : Set (GL (Fin n) F)) := by
  set S : Set (GL (Fin n) F) :=
    {t | t ∈ Subgroup.zpowers s' ∧ ∃ d ∈ Subgroup.zpowers b, IsGLLift j ψ t d} with hS
  have hs'S : s' ∈ S :=
    ⟨Subgroup.mem_zpowers s', b, Subgroup.mem_zpowers b, hs⟩
  have hclS : Subgroup.closure S = Subgroup.zpowers s' := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro t ht
      exact ht.1
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure hs'S
  rw [← Subgroup.centralizer_closure (S : Set (GL (Fin n) F)), hclS,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private lemma exists_isComponentOf_conj_specialUnitary {F : Type} [Field F] {σ : F ≃+* F}
    {n : ℕ} {X : Type} [Group X] [Finite X]
    (ψ : ↥(Unitary.SU σ n) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {P : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      antidiag n)
    {b : X} {s : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU σ n).subtype ψ s b) {C₀ : Subgroup X}
    (hC₀ : IsComponentOf C₀ (ψ.range ⊓ Subgroup.centralizer {b})) :
    ∃ J' : Subgroup ↥(Unitary.SU σ n),
      CFSG.Assembly.IsQuasisimple ↥J' ∧
      IsComponentOf (J'.map ((MulAut.conj P).toMonoidHom.comp (Unitary.SU σ n).subtype))
        (Subgroup.centralizer {P * s * P⁻¹} ⊓ Unitary.SUid σ n) ∧
      J'.map ψ = C₀ := by
  let s' : GL (Fin n) F := P * s * P⁻¹
  let j : ↥(Unitary.SU σ n) →* GL (Fin n) F :=
    (MulAut.conj P).toMonoidHom.comp (Unitary.SU σ n).subtype
  have hji : Function.Injective j :=
    (MulAut.conj P).injective.comp Subtype.coe_injective
  have hs' : IsGLLift j ψ s' b := by
    intro u
    obtain ⟨u', hu'j, hu'b⟩ := hs u
    refine ⟨u', ?_, hu'b⟩
    change (MulAut.conj P) ((Unitary.SU σ n).subtype u') =
      (P * s * P⁻¹) * (MulAut.conj P) ((Unitary.SU σ n).subtype u) * (P * s * P⁻¹)⁻¹
    have h := congrArg (MulAut.conj P) hu'j
    simpa [MulAut.conj_apply, map_mul, map_inv] using h
  have hlift : ∀ d ∈ Subgroup.zpowers b, ∃ t : GL (Fin n) F,
      t ∈ Subgroup.zpowers s' ∧ IsGLLift j ψ t d := by
    intro d hd
    have hd' : d ∈ Submonoid.powers b := mem_powers_iff_mem_zpowers.mpr hd
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff d b).mp hd'
    exact ⟨s' ^ k, Subgroup.npow_mem_zpowers s' k, hs'.pow k⟩
  have hJ : IsComponentOf C₀
      (ψ.range ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X)) := by
    convert hC₀ using 2
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨J', hJ'comp, hJ'ψ⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift j hji ψ hψ
      (fun t => t ∈ Subgroup.zpowers s') (D := Subgroup.zpowers b) hJ hlift
  have hcent := centralizer_liftSet_eq (j := j) (ψ := ψ) (s' := s') hs'
  have hrj : j.range = Unitary.SUid σ n := range_conj_specialUnitary (σ := σ) P hP
  have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hji).mpr hJ'comp
  rw [Subgroup.map_comap_eq] at h
  rw [hcent, hrj, inf_comm] at h
  exact ⟨J', hJ'comp.2.2, h, hJ'ψ⟩

theorem ggE0Comp_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X] [Finite X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {P : GL (Fin n) F}
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    {b : X} {s : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ s b) {C₀ : Subgroup X}
    (hC₀ : IsComponentOf C₀ (ψ.range ⊓ Subgroup.centralizer {b})) :
    ∃ J' : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n),
      CFSG.Assembly.IsQuasisimple ↥J' ∧
      IsComponentOf (J'.map ((MulAut.conj P).toMonoidHom.comp
          (Unitary.SU (unitaryInvolution F 2 f) n).subtype))
        (Subgroup.centralizer {P * s * P⁻¹} ⊓
          Held.heldGU n F (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc)) ∧
      J'.map ψ = C₀ := by
  let σ : F ≃+* F := unitaryInvolution F 2 f
  let hτ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hc
  let s' : GL (Fin n) F := P * s * P⁻¹
  let j : ↥(Unitary.SU σ n) →* GL (Fin n) F :=
    (MulAut.conj P).toMonoidHom.comp (Unitary.SU σ n).subtype
  let GU : Subgroup (GL (Fin n) F) := Held.heldGU n F σ hτ
  let C : Subgroup (GL (Fin n) F) := Subgroup.centralizer ({s'} : Set (GL (Fin n) F))
  let K : Subgroup (GL (Fin n) F) := (Matrix.GeneralLinearGroup.det : GL (Fin n) F →* Fˣ).ker
  have hSUid : Unitary.SUid σ n = GU ⊓ K := specialUnitary_eq_heldGU_inf_detKer (σ := σ) hτ
  obtain ⟨J', hJ'q, hJ'comp, hJ'ψ⟩ :=
    exists_isComponentOf_conj_specialUnitary (σ := σ) ψ hψ hP hs hC₀
  have hcomp0 : IsComponentOf (J'.map j) (C ⊓ GU ⊓ K) := by
    simpa only [C, GU, K, j, s', hSUid, inf_assoc, inf_left_comm, inf_comm] using hJ'comp
  have hab : ∀ a ∈ C ⊓ GU, ∀ b ∈ C ⊓ GU, a * b * a⁻¹ * b⁻¹ ∈ C ⊓ GU ⊓ K := by
    intro a ha b hb
    have hH : a * b * a⁻¹ * b⁻¹ ∈ C ⊓ GU :=
      (C ⊓ GU).mul_mem ((C ⊓ GU).mul_mem ((C ⊓ GU).mul_mem ha hb)
        ((C ⊓ GU).inv_mem ha)) ((C ⊓ GU).inv_mem hb)
    refine Subgroup.mem_inf.mpr ⟨hH, ?_⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    simp
  have hout : IsComponentOf (J'.map j) (C ⊓ GU) := by
    have := (isComponentOf_iff_of_normal_of_commutator_le (H := C ⊓ GU) (N := C ⊓ GU ⊓ K)
      inf_le_left hab).mpr hcomp0
    simpa only [C, GU, K, j, s'] using this
  exact ⟨J', hJ'q, hout, hJ'ψ⟩

end CFSG.StandardType
