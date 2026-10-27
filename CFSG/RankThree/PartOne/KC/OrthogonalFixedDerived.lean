module

public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

section Defs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def supportedFixedDerived (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    Subgroup (V ≃ₗ[K] V) :=
  ((orthDerived (Q.comp (fixedSpace x).subtype)).comap (restrictFixed Q x)).map
    (supportedBlock Q x (X - 1)).subtype

@[expose] noncomputable def fixedComponentImage (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    Subgroup (ProjOrthDerived Q) :=
  ((supportedFixedDerived Q x).subgroupOf (orthDerived Q)).map
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))

theorem mem_supportedFixedDerived {Q : QuadraticForm K V} {x g : V ≃ₗ[K] V} :
    g ∈ supportedFixedDerived Q x ↔ ∃ hg : g ∈ supportedBlock Q x (X - 1),
      restrictFixed Q x ⟨g, hg⟩ ∈ orthDerived (Q.comp (fixedSpace x).subtype) := by
  simp only [supportedFixedDerived, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem supportedFixedDerived_le_supportedBlock {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} :
    supportedFixedDerived Q x ≤ supportedBlock Q x (X - 1) := fun _ hg =>
  (mem_supportedFixedDerived.mp hg).1

theorem supportedFixedDerived_le_isometryCentralizer {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} :
    supportedFixedDerived Q x ≤ isometryCentralizer Q x :=
  supportedFixedDerived_le_supportedBlock.trans (supportedBlock_le_isometryCentralizer _)

end Defs

section Conj

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem conj_mem_supportedBlock {m f : V ≃ₗ[K] V} {h : K[X]} (hm : m ∈ isometryCentralizer Q x)
    (hf : f ∈ supportedBlock Q x h) : m * f * m⁻¹ ∈ supportedBlock Q x h := by
  have hmc : m ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hm).2
  have hmc' : m⁻¹ ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := inv_mem hmc
  refine mem_supportedBlock.mpr ⟨mul_mem (mul_mem hm
    (supportedBlock_le_isometryCentralizer h hf)) (inv_mem hm), fun r hr => ?_⟩
  have hr' : m⁻¹ r ∈ othersSpace x.toLinearMap h := mem_othersSpace_of_apply hmc' hr
  show m (f (m⁻¹ r)) = r
  rw [(mem_supportedBlock.mp hf).2 _ hr']
  exact m.apply_symm_apply r

theorem OddOrderIsometry.supportedFixedDerived_eq {p : ℕ} (hx : OddOrderIsometry Q p x) :
    supportedFixedDerived Q x =
      ⁅supportedBlock Q x (X - 1), supportedBlock Q x (X - 1)⁆ := by
  have hrange : (restrictFixed Q x).range =
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) := by
    ext g
    constructor
    · rintro ⟨f, rfl⟩
      exact restrictFixed_mem_orthogonalGroup f
    · intro hg
      exact restrictFixed_surjective hx g hg
  set D : Subgroup ↥(supportedBlock Q x (X - 1)) :=
    ⁅(⊤ : Subgroup ↥(supportedBlock Q x (X - 1))), ⊤⁆ with hD
  have h1 : (orthDerived (Q.comp (fixedSpace x).subtype)).comap (restrictFixed Q x) = D := by
    have : orthDerived (Q.comp (fixedSpace x).subtype) = D.map (restrictFixed Q x) := by
      rw [hD, Subgroup.map_commutator, Subgroup.map_top, hrange]
    rw [this, Subgroup.comap_map_eq_self_of_injective (restrictFixed_injective hx)]
  unfold supportedFixedDerived
  rw [h1, hD, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem OddOrderIsometry.supportedFixedDerived_le_orthDerived {p : ℕ}
    (hx : OddOrderIsometry Q p x) : supportedFixedDerived Q x ≤ orthDerived Q := by
  rw [hx.supportedFixedDerived_eq]
  have hle : supportedBlock Q x (X - 1) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _ hg)).1
  exact Subgroup.commutator_mono hle hle

theorem OddOrderIsometry.conj_mem_supportedFixedDerived {p : ℕ} (hx : OddOrderIsometry Q p x)
    {m f : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) (hf : f ∈ supportedFixedDerived Q x) :
    m * f * m⁻¹ ∈ supportedFixedDerived Q x := by
  rw [hx.supportedFixedDerived_eq] at hf ⊢
  have hle : (supportedBlock Q x (X - 1)).map (MulAut.conj m).toMonoidHom ≤
      supportedBlock Q x (X - 1) := by
    rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_supportedBlock hm hg
  have h1 : ⁅supportedBlock Q x (X - 1), supportedBlock Q x (X - 1)⁆.map
      (MulAut.conj m).toMonoidHom ≤ ⁅supportedBlock Q x (X - 1), supportedBlock Q x (X - 1)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 ⟨f, hf, rfl⟩

end Conj

section Image

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem fixedComponentImage_le_centralizerImage :
    fixedComponentImage Q x ≤ centralizerImage Q x :=
  Subgroup.map_mono fun _ hf => supportedFixedDerived_le_isometryCentralizer hf

theorem OddOrderIsometry.normal_fixedComponentImage (hx : OddOrderIsometry Q p x) :
    ((fixedComponentImage Q x).subgroupOf (centralizerImage Q x)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff fixedComponentImage_le_centralizerImage]
  intro j n hj hn
  obtain ⟨f, hf, rfl⟩ := hj
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨m * f * m⁻¹, ?_, by simp⟩
  exact hx.conj_mem_supportedFixedDerived
    (hm : (m : V ≃ₗ[K] V) ∈ isometryCentralizer Q x) hf

end Image

section Quasisimple

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem isQuasisimple_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    CFSG.IsQuasisimple ↥(orthDerived Q) := by
  obtain ⟨hperf, hcenter, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  let e : ↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q) ≃* ProjOrthDerived Q :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  refine ⟨hperf, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

variable {p : ℕ} {x : V ≃ₗ[K] V}

noncomputable def supportedFixedDerivedEquiv (hx : OddOrderIsometry Q p x) :
    ↥(supportedFixedDerived Q x) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := by
  set Fd := (orthDerived (Q.comp (fixedSpace x).subtype)).comap (restrictFixed Q x) with hFd
  let ψ : ↥Fd →* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    ((restrictFixed Q x).comp Fd.subtype).codRestrict _ (fun f => f.2)
  have hψ : Function.Bijective ψ := by
    refine ⟨fun a b hab => ?_, fun g => ?_⟩
    · exact Subtype.ext (restrictFixed_injective hx (congrArg Subtype.val hab))
    · obtain ⟨f, hf⟩ := restrictFixed_surjective hx g.1 (orthDerived_le_orthogonalGroup g.2)
      exact ⟨⟨f, by rw [hFd, Subgroup.mem_comap, hf]; exact g.2⟩, Subtype.ext hf⟩
  exact (Subgroup.equivMapOfInjective Fd (supportedBlock Q x (X - 1)).subtype
    (supportedBlock Q x (X - 1)).subtype_injective).symm.trans (MulEquiv.ofBijective ψ hψ)

theorem OddOrderIsometry.isQuasisimple_supportedFixedDerived (hx : OddOrderIsometry Q p x)
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) :
    CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm
    (isQuasisimple_orthDerived hx.polarBilin_fixed_nondegenerate hT)

theorem OddOrderIsometry.isQuasisimple_fixedComponentImage (hx : OddOrderIsometry Q p x)
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) :
    CFSG.IsQuasisimple ↥(fixedComponentImage Q x) := by
  unfold fixedComponentImage
  exact isQuasisimple_map_projective hx.supportedFixedDerived_le_orthDerived
    (hx.isQuasisimple_supportedFixedDerived hT)

theorem OddOrderIsometry.mem_supportedFixedDerived_of_odd_pow (hx : OddOrderIsometry Q p x)
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x (X - 1)) {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1) :
    g ∈ supportedFixedDerived Q x := by
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts
      hx.polarBilin_fixed_nondegenerate hT
  refine mem_supportedFixedDerived.mpr ⟨hg, hodd _ (restrictFixed_mem_orthogonalGroup ⟨g, hg⟩) ?_⟩
  have h1 : (restrictFixed Q x ⟨g, hg⟩) ^ n = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(supportedBlock Q x (X - 1))) ^ n = 1 := Subtype.ext hgn
    rw [this, map_one]
  have hd : orderOf (restrictFixed Q x ⟨g, hg⟩) ∣ n := orderOf_dvd_of_pow_eq_one h1
  exact hn.of_dvd_nat hd

end Quasisimple

end CFSG.RankThree.PartOne.KCOrthogonal
