module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs
public import CFSG.LocalAnalysis.StandardType.GGPDSectionAbstract

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPD_section {K : Type} [Field K] {d : ℕ}
    {A : Subgroup (Matrix.GeneralLinearGroup (Fin d) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))}
    (hexp : ∀ a : ↥A, a ^ 3 = 1)
    (hcomm : ∀ u ∈ A.comap
        (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
      ∀ v ∈ A.comap (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
        u * v = v * u)
    {z : Matrix.GeneralLinearGroup (Fin d) K}
    (hz : ∀ y ∈ A.comap (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
      z * y * z⁻¹ ∈
          A.comap (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))) ∧
        QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) (z * y * z⁻¹) =
          (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) y)⁻¹) :
    ∃ τ : ↥A →* Matrix.GeneralLinearGroup (Fin d) K,
      (∀ a, QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) (τ a) = a) ∧
        ∀ a, z * τ a * z⁻¹ = (τ a)⁻¹ := by
  classical
  let π := QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
  let E : Subgroup (Matrix.GeneralLinearGroup (Fin d) K) := A.comap π
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2) }
  let q : ↥E →* ↥A :=
    { toFun := fun y => ⟨π y.1, y.2⟩
      map_one' := by ext; simpa using map_one π
      map_mul' := fun y₁ y₂ => by ext; simpa using map_mul π y₁.1 y₂.1 }
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
      (a : Matrix.GeneralLinearGroup (Fin d) K ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change π g ∈ A
      rw [hg]
      exact a.2
    · exact Subtype.ext hg
  have hzinv : ∀ y ∈ E, z⁻¹ * y * z ∈ E := by
    intro y hy
    change π (z⁻¹ * y * z) ∈ A
    have hconj : π z * π y * (π z)⁻¹ = (π y)⁻¹ :=
      by simpa only [map_mul, map_inv] using (hz y hy).2
    have hkey : (π z)⁻¹ * π y * π z = (π y)⁻¹ := by
      have hb : π y = (π z)⁻¹ * (π y)⁻¹ * π z := by
        calc π y = (π z)⁻¹ * (π z * π y * (π z)⁻¹) * π z := by group
          _ = (π z)⁻¹ * (π y)⁻¹ * π z := by rw [hconj]
      calc (π z)⁻¹ * π y * π z
          = ((π z)⁻¹ * (π y)⁻¹ * π z)⁻¹ := by group
        _ = (π y)⁻¹ := by rw [← hb]
    have hval : π (z⁻¹ * y * z) = (π y)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      exact hkey
    rw [hval]
    exact A.inv_mem hy
  have hzE : z ∈ Subgroup.normalizer (E : Set (Matrix.GeneralLinearGroup (Fin d) K)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact (hz h hh).1
    · intro hh
      have hh' := hzinv (z * h * z⁻¹) hh
      simpa [mul_assoc] using hh'
  let f : MulAut ↥E := E.normalizerMonoidHom ⟨z, hzE⟩
  have hf_apply : ∀ y : ↥E,
      ((f y : ↥E) : Matrix.GeneralLinearGroup (Fin d) K) =
        z * (y : Matrix.GeneralLinearGroup (Fin d) K) * z⁻¹ := by
    intro y
    change ((E.normalizerMonoidHom ⟨z, hzE⟩ y : ↥E) :
        Matrix.GeneralLinearGroup (Fin d) K) =
      z * (y : Matrix.GeneralLinearGroup (Fin d) K) * z⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfix : ∀ y ∈ q.ker, f y = y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyc : y.1 ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K) := by
      have h1 : π y.1 = 1 := by
        exact Subtype.ext_iff.mp hy
      exact (QuotientGroup.eq_one_iff y.1).mp h1
    have hzc : z * y.1 = y.1 * z := (Subgroup.mem_center_iff.mp hyc) z
    apply Subtype.ext
    rw [hf_apply y, hzc]
    group
  have hinv : ∀ y : ↥E, q (f y) = (q y)⁻¹ := by
    intro y
    apply Subtype.ext
    change π ((f y : ↥E) : Matrix.GeneralLinearGroup (Fin d) K) =
      (π (y : Matrix.GeneralLinearGroup (Fin d) K))⁻¹
    rw [hf_apply y]
    exact (hz y.1 y.2).2
  obtain ⟨s, hqs, -, hev⟩ :=
    ggPD_exists_section_of_inversion_equivariant (E := ↥E) (A := ↥A)
      q hq f hfix hinv hexp
  refine ⟨E.subtype.comp s, ?_, ?_⟩
  · intro a
    have h := Subtype.ext_iff.mp (hqs a)
    change π ((s a : ↥E) : Matrix.GeneralLinearGroup (Fin d) K) =
      (a : Matrix.GeneralLinearGroup (Fin d) K ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
    exact h
  · intro a
    have h := congrArg Subtype.val (hev a)
    change z * ((s a : ↥E) : Matrix.GeneralLinearGroup (Fin d) K) * z⁻¹ =
      (((s a : ↥E) : Matrix.GeneralLinearGroup (Fin d) K))⁻¹
    rw [hf_apply (s a), map_inv] at h
    exact h

end CFSG.StandardType

end
