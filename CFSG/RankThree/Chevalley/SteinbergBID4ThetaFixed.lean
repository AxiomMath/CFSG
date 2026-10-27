module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.RankThree.Chevalley.SteinbergBID4Triality

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {Ω : Type} [Field Ω]

theorem d4Rho_eq_perm (k : Fin Tag.D4.rank) : d4Rho k = TwistTag.D4.perm k := by
  fin_cases k <;> rfl

variable (Ω) in
@[expose] def d4DiagramMap : ModGL Tag.D4 Ω := diagramMap TwistTag.D4 Ω

theorem d4DiagramMap_conj_xUnit (k : Fin Tag.D4.rank) (c : Ω) :
    d4DiagramMap Ω * xUnit Tag.D4 Ω k c * (d4DiagramMap Ω)⁻¹ = xUnit Tag.D4 Ω (d4Rho k) c := by
  rw [d4Rho_eq_perm]
  exact diagramMap_mul_xUnit_mul_inv TwistTag.D4 Ω k c

theorem d4DiagramMap_conj_yUnit (k : Fin Tag.D4.rank) (c : Ω) :
    d4DiagramMap Ω * yUnit Tag.D4 Ω k c * (d4DiagramMap Ω)⁻¹ = yUnit Tag.D4 Ω (d4Rho k) c := by
  rw [d4Rho_eq_perm]
  exact diagramMap_mul_yUnit_mul_inv TwistTag.D4 Ω k c

theorem d4Res_d4Triality (g : subsystemGroup Tag.E6 Ω d4Support) :
    d4Res Ω (d4Triality Ω g) = d4DiagramMap Ω * d4Res Ω g * (d4DiagramMap Ω)⁻¹ := by
  have h : (d4Res Ω).comp (d4Triality Ω).toMonoidHom =
      (MulAut.conj (d4DiagramMap Ω)).toMonoidHom.comp (d4Res Ω) := by
    refine d4Q_hom_ext (fun k c => ?_) (fun k c => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, d4Triality_xUnit, d4Res_xUnit,
        MulAut.conj_apply, d4DiagramMap_conj_xUnit]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, d4Triality_yUnit, d4Res_yUnit,
        MulAut.conj_apply, d4DiagramMap_conj_yUnit]
  exact DFunLike.congr_fun h g

theorem d4Res_d4Triality_pow (e : ℕ) (g : subsystemGroup Tag.E6 Ω d4Support) :
    d4Res Ω ((d4Triality Ω ^ e : MulAut (subsystemGroup Tag.E6 Ω d4Support)) g) =
      d4DiagramMap Ω ^ e * d4Res Ω g * (d4DiagramMap Ω ^ e)⁻¹ := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', MulAut.mul_apply, d4Res_d4Triality, ih, pow_succ']
    group

theorem baseChangeGL_eq_entrywise {τ : Tag} (Fr : Ω →+* Ω) (g : ModGL τ Ω) :
    baseChangeGL Fr g = Units.map (entrywiseHom Fr) g :=
  Units.ext rfl

variable (Ω) in
@[expose] def d4Theta (Fr : Ω →+* Ω) (e : ℕ) :
    subsystemGroup Tag.E6 Ω d4Support →* subsystemGroup Tag.E6 Ω d4Support :=
  ((d4Triality Ω ^ e : MulAut (subsystemGroup Tag.E6 Ω d4Support)).toMonoidHom).comp
    (d4QBaseChange Ω Fr)

theorem d4Theta_apply (Fr : Ω →+* Ω) (e : ℕ) (g : subsystemGroup Tag.E6 Ω d4Support) :
    d4Theta Ω Fr e g = (d4Triality Ω ^ e : MulAut (subsystemGroup Tag.E6 Ω d4Support))
      (d4QBaseChange Ω Fr g) :=
  rfl

theorem d4Res_d4Theta (Fr : Ω →+* Ω) (e : ℕ) (g : subsystemGroup Tag.E6 Ω d4Support) :
    d4Res Ω (d4Theta Ω Fr e g) = d4DiagramMap Ω ^ e *
      Units.map (entrywiseHom Fr) (d4Res Ω g) * (d4DiagramMap Ω ^ e)⁻¹ := by
  rw [d4Theta_apply, d4Res_d4Triality_pow, d4Res_baseChangeGL, baseChangeGL_eq_entrywise]

variable (Ω) in
@[expose] def d4ThetaFixed (Fr : Ω →+* Ω) (e : ℕ) : Subgroup (subsystemGroup Tag.E6 Ω d4Support) :=
  MonoidHom.eqLocus (d4Theta Ω Fr e) (MonoidHom.id _)

theorem mem_d4ThetaFixed {Fr : Ω →+* Ω} {e : ℕ} {g : subsystemGroup Tag.E6 Ω d4Support} :
    g ∈ d4ThetaFixed Ω Fr e ↔ d4Theta Ω Fr e g = g :=
  Iff.rfl

theorem units_map_eq_of_sq_eq_one (Fr : Ω →+* Ω) {a : Ωˣ} (ha : a ^ 2 = 1) :
    Units.map Fr.toMonoidHom a = a := by
  have ha' : (a : Ω) * a = 1 := by
    rw [← sq, ← Units.val_pow_eq_pow_val, ha, Units.val_one]
  apply Units.ext
  change Fr (a : Ω) = a
  rcases mul_self_eq_one_iff.1 ha' with h | h
  · rw [h, map_one]
  · rw [h, map_neg, map_one]

theorem d4QBaseChange_eq_of_d4Res_eq_one (Fr : Ω →+* Ω) {z : subsystemGroup Tag.E6 Ω d4Support}
    (hz : d4Res Ω z = 1) : d4QBaseChange Ω Fr z = z := by
  obtain ⟨a, b, d, ha, hb, hd, -, he⟩ := (d4Res_eq_one_iff_mem_d4KernelSet z).1 hz
  apply Subtype.ext
  change baseChangeGL Fr (z : ModGL Tag.E6 Ω) = z
  rw [he, map_mul, map_mul, baseChangeGL_torusElt, baseChangeGL_torusElt, baseChangeGL_torusElt,
    units_map_eq_of_sq_eq_one Fr ha, units_map_eq_of_sq_eq_one Fr hb,
    units_map_eq_of_sq_eq_one Fr hd]

theorem d4Theta_eq_of_d4Res_eq_one (Fr : Ω →+* Ω) (e : ℕ) {z : subsystemGroup Tag.E6 Ω d4Support}
    (hz : d4Res Ω z = 1) :
    d4Theta Ω Fr e z = (d4Triality Ω ^ e : MulAut (subsystemGroup Tag.E6 Ω d4Support)) z := by
  rw [d4Theta_apply, d4QBaseChange_eq_of_d4Res_eq_one Fr hz]

theorem d4Res_d4Triality_pow_eq_one (e : ℕ) {z : subsystemGroup Tag.E6 Ω d4Support}
    (hz : d4Res Ω z = 1) :
    d4Res Ω ((d4Triality Ω ^ e : MulAut (subsystemGroup Tag.E6 Ω d4Support)) z) = 1 := by
  rw [d4Res_d4Triality_pow, hz, mul_one, mul_inv_cancel]

theorem d4Theta_ne_self (Fr : Ω →+* Ω) {e : ℕ} (he : e = 1 ∨ e = 2)
    {z : subsystemGroup Tag.E6 Ω d4Support} (hz : d4Res Ω z = 1) (hz1 : z ≠ 1) :
    d4Theta Ω Fr e z ≠ z := by
  by_cases h2 : ringChar Ω = 2
  · exact absurd ((MonoidHom.ker_eq_bot_iff _).2 (d4Res_injective_of_ringChar_eq_two h2) ▸
      (MonoidHom.mem_ker.2 hz) : z ∈ (⊥ : Subgroup _)) (by rwa [Subgroup.mem_bot])
  obtain ⟨-, h1, h2', -⟩ := d4Triality_cycles_kernel h2 hz hz hz1 hz1
  rw [d4Theta_eq_of_d4Res_eq_one Fr e hz]
  rcases he with rfl | rfl
  · rw [pow_one]
    exact h1
  · rw [pow_two, MulAut.mul_apply]
    exact h2'

theorem eq_one_of_mem_d4ThetaFixed_of_d4Res_eq_one (Fr : Ω →+* Ω) {e : ℕ} (he : e = 1 ∨ e = 2)
    {z : subsystemGroup Tag.E6 Ω d4Support} (hz : d4Res Ω z = 1)
    (hzΘ : z ∈ d4ThetaFixed Ω Fr e) : z = 1 := by
  by_contra h1
  exact d4Theta_ne_self Fr he hz h1 hzΘ

theorem d4Res_injOn_d4ThetaFixed (Fr : Ω →+* Ω) {e : ℕ} (he : e = 1 ∨ e = 2)
    {g g' : subsystemGroup Tag.E6 Ω d4Support} (hg : g ∈ d4ThetaFixed Ω Fr e)
    (hg' : g' ∈ d4ThetaFixed Ω Fr e) (h : d4Res Ω g = d4Res Ω g') : g = g' := by
  have hz : d4Res Ω (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h1 := eq_one_of_mem_d4ThetaFixed_of_d4Res_eq_one Fr he hz
    (mul_mem (inv_mem hg) hg')
  exact inv_mul_eq_one.1 h1

theorem finite_ker_d4Res : Finite (d4Res Ω).ker := by
  by_cases h2 : ringChar Ω = 2
  · rw [(MonoidHom.ker_eq_bot_iff _).2 (d4Res_injective_of_ringChar_eq_two h2)]
    infer_instance
  · exact Finite.of_equiv _ (d4KernelEquiv h2).toEquiv

theorem exists_mem_d4ThetaFixed_d4Res_eq (Fr : Ω →+* Ω) {e : ℕ} (he : e = 1 ∨ e = 2)
    {y : ModGL Tag.D4 Ω} (hy : y ∈ adjointGroup Tag.D4 Ω)
    (hS : d4DiagramMap Ω ^ e * Units.map (entrywiseHom Fr) y *
      (d4DiagramMap Ω ^ e)⁻¹ = y) :
    ∃ g ∈ d4ThetaFixed Ω Fr e, d4Res Ω g = y := by
  have : Finite (d4Res Ω).ker := finite_ker_d4Res
  rw [← range_d4Res] at hy
  obtain ⟨g, rfl⟩ := hy
  set c := d4Theta Ω Fr e g * g⁻¹ with hc
  have hcZ : d4Res Ω c = 1 := by
    rw [hc, map_mul, map_inv, d4Res_d4Theta, hS, mul_inv_cancel]
  let φ : (d4Res Ω).ker → (d4Res Ω).ker := fun z => ⟨d4Theta Ω Fr e z * (z.1)⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, d4Theta_eq_of_d4Res_eq_one Fr e z.2,
      d4Res_d4Triality_pow_eq_one e z.2, MonoidHom.mem_ker.1 z.2, inv_one, one_mul]⟩
  have hcomm : ∀ (z : subsystemGroup Tag.E6 Ω d4Support), d4Res Ω z = 1 →
      ∀ x : subsystemGroup Tag.E6 Ω d4Support, z * x = x * z := fun z hz x =>
    (Subgroup.mem_center_iff.1 (mem_center_of_d4Res_eq_one hz) x).symm
  have hφ : Function.Injective φ := by
    intro z z' h
    have h' : d4Theta Ω Fr e z * (z.1)⁻¹ = d4Theta Ω Fr e z' * (z'.1)⁻¹ :=
      congrArg Subtype.val h
    have hz'z : d4Res Ω ((z'.1)⁻¹ * z) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 z.2, MonoidHom.mem_ker.1 z'.2, inv_one,
        one_mul]
    have hfix : d4Theta Ω Fr e ((z'.1)⁻¹ * z) =
        (z'.1)⁻¹ * z := by
      have hc1 := hcomm _ (by rw [map_mul, map_inv, d4Theta_eq_of_d4Res_eq_one Fr e z'.2,
        d4Res_d4Triality_pow_eq_one e z'.2, MonoidHom.mem_ker.1 z'.2, inv_one, one_mul] :
          d4Res Ω (d4Theta Ω Fr e z' * (z'.1)⁻¹) = 1)
      rw [map_mul, map_inv]
      calc (d4Theta Ω Fr e z')⁻¹ * d4Theta Ω Fr e z
          = (d4Theta Ω Fr e z')⁻¹ * (d4Theta Ω Fr e z * (z.1)⁻¹) * z := by group
        _ = (d4Theta Ω Fr e z')⁻¹ * (d4Theta Ω Fr e z' * (z'.1)⁻¹) * z := by rw [h']
        _ = (z'.1)⁻¹ * z := by group
    have h1 := eq_one_of_mem_d4ThetaFixed_of_d4Res_eq_one Fr he hz'z hfix
    exact Subtype.ext (inv_mul_eq_one.1 h1).symm
  obtain ⟨z, hzc⟩ := (Finite.injective_iff_surjective.1 hφ) ⟨c⁻¹, by
    rw [MonoidHom.mem_ker, map_inv, hcZ, inv_one]⟩
  have hzc' : d4Theta Ω Fr e z * (z.1)⁻¹ = c⁻¹ := congrArg Subtype.val hzc
  refine ⟨g * z, ?_, by rw [map_mul, MonoidHom.mem_ker.1 z.2, mul_one]⟩
  rw [mem_d4ThetaFixed, map_mul]
  have hΘz : d4Theta Ω Fr e z = c⁻¹ * z := by rw [← hzc', inv_mul_cancel_right]
  have hΘg : d4Theta Ω Fr e g = c * g := by rw [hc, inv_mul_cancel_right]
  rw [hΘz, hΘg, ← mul_assoc, mul_assoc c, ← hcomm _ (by rw [map_inv, hcZ, inv_one]) g,
    ← mul_assoc, mul_inv_cancel, one_mul]

theorem d4Res_mem_fixed_iff (Fr : Ω →+* Ω) {e : ℕ} (he : e = 1 ∨ e = 2) (y : ModGL Tag.D4 Ω) :
    (∃ g ∈ d4ThetaFixed Ω Fr e, d4Res Ω g = y) ↔ y ∈ adjointGroup Tag.D4 Ω ∧
      d4DiagramMap Ω ^ e * Units.map (entrywiseHom Fr) y *
        (d4DiagramMap Ω ^ e)⁻¹ = y := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨d4Res_mem_adjointGroup g, by rw [← d4Res_d4Theta, mem_d4ThetaFixed.1 hg]⟩
  · rintro ⟨hy, hS⟩
    exact exists_mem_d4ThetaFixed_d4Res_eq Fr he hy hS

end CFSG.RankThree.Chevalley
