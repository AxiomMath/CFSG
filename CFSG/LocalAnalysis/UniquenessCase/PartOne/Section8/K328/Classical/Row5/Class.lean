module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.Open.StatedZModTwo
public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open CFSG.LinearAlgebra

private def k328r5c_W {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.ker (z ^ 2 + z + 1)

private theorem k328r5c_mem_W {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {z : Module.End (ZMod 2) V} {v : V} : v ∈ k328r5c_W z ↔ z (z v) + z v + v = 0 := by
  simp [k328r5c_W, pow_two, LinearMap.mem_ker]

private theorem k328r5c_mem_W_of_commute {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {z g : Module.End (ZMod 2) V} (hg : Commute g z) {w : V} (hw : w ∈ k328r5c_W z) :
    g w ∈ k328r5c_W z := by
  have h : Commute g (z ^ 2 + z + 1) :=
    ((hg.pow_right 2).add_right hg).add_right (Commute.one_right g)
  rw [k328r5c_W, LinearMap.mem_ker] at hw ⊢
  have := LinearMap.congr_fun h.eq w
  simp only [Module.End.mul_apply] at this
  rw [← this, hw, map_zero]

private noncomputable def k328r5c_zW {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) : Module.End (ZMod 2) ↥(k328r5c_W z) :=
  LinearMap.restrict z (fun _ hw => k328r5c_mem_W_of_commute (Commute.refl z) hw)

private theorem k328r5c_zW_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) (w : ↥(k328r5c_W z)) :
    ((k328r5c_zW z w : ↥(k328r5c_W z)) : V) = z w :=
  rfl

private theorem k328r5c_zW_rel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) : k328r5c_zW z ^ 2 + k328r5c_zW z + 1 = 0 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  simp only [pow_two, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
    Submodule.coe_add, k328r5c_zW_apply, LinearMap.zero_apply, Submodule.coe_zero]
  exact k328r5c_mem_W.1 w.2

private noncomputable instance k328r5c_instModule {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (z : Module.End (ZMod 2) V) : Module OmegaField ↥(k328r5c_W z) :=
  Module.compHom ↥(k328r5c_W z) (omegaHom (k328r5c_zW z) (k328r5c_zW_rel z))

private theorem k328r5c_smul_def {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) (c : OmegaField) (w : ↥(k328r5c_W z)) :
    c • w = omegaHom (k328r5c_zW z) (k328r5c_zW_rel z) c w :=
  rfl

private theorem k328r5c_omega_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) (w : ↥(k328r5c_W z)) :
    (omega : OmegaField) • w = k328r5c_zW z w := by
  rw [k328r5c_smul_def, omegaHom_omega]

private theorem k328r5c_algebraMap_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) (a : ZMod 2) (w : ↥(k328r5c_W z)) :
    algebraMap (ZMod 2) OmegaField a • w = a • w := by
  rw [k328r5c_smul_def, omegaHom_algebraMap, Module.algebraMap_end_apply]

private instance k328r5c_instTower {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) : IsScalarTower (ZMod 2) OmegaField ↥(k328r5c_W z) := by
  refine ⟨fun c x v => ?_⟩
  rw [Algebra.smul_def, mul_smul, k328r5c_algebraMap_smul]

private theorem k328r5c_commute_omegaHom {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {a b : Module.End (ZMod 2) U} (hb : b ^ 2 + b + 1 = 0) (hab : Commute a b) (c : OmegaField) :
    Commute a (omegaHom b hb c) := by
  obtain ⟨x, y, rfl⟩ := omegaField_eq c
  rw [map_add, map_mul, omegaHom_algebraMap, omegaHom_algebraMap, omegaHom_omega]
  exact (Algebra.commute_algebraMap_right _ _).add_right
    ((Algebra.commute_algebraMap_right _ _).mul_right hab)

private noncomputable def k328r5c_gW {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z g : Module.End (ZMod 2) V) (hg : Commute g z) : Module.End (ZMod 2) ↥(k328r5c_W z) :=
  LinearMap.restrict g (fun _ hw => k328r5c_mem_W_of_commute hg hw)

private theorem k328r5c_gW_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z g : Module.End (ZMod 2) V) (hg : Commute g z) (w : ↥(k328r5c_W z)) :
    ((k328r5c_gW z g hg w : ↥(k328r5c_W z)) : V) = g w :=
  rfl

private theorem k328r5c_gW_commute {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z g : Module.End (ZMod 2) V) (hg : Commute g z) :
    Commute (k328r5c_gW z g hg) (k328r5c_zW z) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  exact LinearMap.congr_fun hg.eq _

private noncomputable def k328r5c_resF {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z g : Module.End (ZMod 2) V) (hg : Commute g z) : Module.End OmegaField ↥(k328r5c_W z) where
  toFun := k328r5c_gW z g hg
  map_add' := map_add _
  map_smul' c w := by
    have := LinearMap.congr_fun
      (k328r5c_commute_omegaHom (k328r5c_zW_rel z) (k328r5c_gW_commute z g hg) c).eq w
    simpa [k328r5c_smul_def] using this

private theorem k328r5c_resF_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z g : Module.End (ZMod 2) V) (hg : Commute g z) (w : ↥(k328r5c_W z)) :
    k328r5c_resF z g hg w = k328r5c_gW z g hg w :=
  rfl

private noncomputable def k328r5c_delta {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) {M : Type*} [Monoid M] (ρ : M →* Module.End (ZMod 2) V)
    (hρ : ∀ m, Commute (ρ m) z) : M →* OmegaField where
  toFun m := LinearMap.det (k328r5c_resF z (ρ m) (hρ m))
  map_one' := by
    have : k328r5c_resF z (ρ 1) (hρ 1) = 1 :=
      LinearMap.ext fun w => Subtype.ext (by
        rw [k328r5c_resF_apply, k328r5c_gW_apply, map_one]
        rfl)
    rw [this]
    exact LinearMap.det.map_one
  map_mul' m n := by
    have : k328r5c_resF z (ρ (m * n)) (hρ _) =
        k328r5c_resF z (ρ m) (hρ m) * k328r5c_resF z (ρ n) (hρ n) :=
      LinearMap.ext fun w => Subtype.ext (by
        rw [k328r5c_resF_apply, k328r5c_gW_apply, map_mul]
        rfl)
    rw [this]
    exact LinearMap.det.map_mul _ _

private theorem k328r5c_delta_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) {M : Type*} [Monoid M] (ρ : M →* Module.End (ZMod 2) V)
    (hρ : ∀ m, Commute (ρ m) z) (m : M) (hm : ρ m = z) :
    k328r5c_delta z ρ hρ m = omega ^ Module.finrank OmegaField ↥(k328r5c_W z) := by
  show LinearMap.det (k328r5c_resF z (ρ m) (hρ m)) = _
  have : k328r5c_resF z (ρ m) (hρ m) = (omega : OmegaField) • LinearMap.id :=
    LinearMap.ext fun w => Subtype.ext (by
      rw [k328r5c_resF_apply, k328r5c_gW_apply, hm, LinearMap.smul_apply, LinearMap.id_apply,
        k328r5c_omega_smul]
      rfl)
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

private theorem k328r5c_omega_order : orderOf (omega : OmegaField) = 3 := by
  have hω3 : (omega : OmegaField) ^ 3 = 1 := by
    linear_combination (omega + 1) * omega_sq + omega * omegaField_two_eq_zero
  have hω1 : (omega : OmegaField) ≠ 1 := fun h => by
    have := omega_sq
    rw [h] at this
    exact one_ne_zero (by linear_combination (-1 : OmegaField) * this)
  exact orderOf_eq_prime hω3 hω1

private theorem k328r5c_three_dvd_finrank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) {G : Type*} [Group G] (ρ : G →* Module.End (ZMod 2) V)
    (hρ : ∀ g, Commute (ρ g) z) (hperf : commutator G = ⊤) (g₀ : G) (hg₀ : ρ g₀ = z) :
    3 ∣ Module.finrank OmegaField ↥(k328r5c_W z) := by
  have h1 : k328r5c_delta z ρ hρ g₀ = 1 := by
    have h := Abelianization.commutator_subset_ker (k328r5c_delta z ρ hρ).toHomUnits
      (hperf ▸ Subgroup.mem_top g₀)
    simpa [MonoidHom.mem_ker, Units.ext_iff] using h
  rw [k328r5c_delta_self z ρ hρ g₀ hg₀] at h1
  rw [← k328r5c_omega_order]
  exact orderOf_dvd_of_pow_eq_one h1

private theorem k328r5c_z_cube {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) (hz3 : z ^ 3 = 1) (v : V) : z (z (z v)) = v := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_two, ← pow_succ, hz3,
    Module.End.one_apply]


private theorem k328r5c_finrank_W {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V = 7)
    (z : Module.End (ZMod 2) V) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {G : Type*} [Group G]
    (ρ : G →* Module.End (ZMod 2) V) (hρ : ∀ g, Commute (ρ g) z) (hperf : commutator G = ⊤)
    (g₀ : G) (hg₀ : ρ g₀ = z) : Module.finrank (ZMod 2) ↥(k328r5c_W z) = 6 := by
  have h3 := k328r5c_three_dvd_finrank z ρ hρ hperf g₀ hg₀
  have hmul := Module.finrank_mul_finrank (ZMod 2) OmegaField ↥(k328r5c_W z)
  rw [finrank_omegaField] at hmul
  have hle : Module.finrank (ZMod 2) ↥(k328r5c_W z) ≤ 7 :=
    hdim ▸ Submodule.finrank_le (k328r5c_W z)
  have hn : Module.finrank OmegaField ↥(k328r5c_W z) = 0 ∨
      Module.finrank OmegaField ↥(k328r5c_W z) = 3 := by
    omega
  rcases hn with h0 | h3'
  · exfalso
    have hW : k328r5c_W z = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    apply hz1
    refine LinearMap.ext fun v => ?_
    have hv : z v - v ∈ k328r5c_W z := by
      rw [k328r5c_mem_W]
      simp only [map_sub]
      rw [k328r5c_z_cube z hz3 v]
      abel
    rw [hW, Submodule.mem_bot, sub_eq_zero] at hv
    simpa using hv
  · omega

private def k328r5c_C {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.ker (z - 1)

private theorem k328r5c_mem_C {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {z : Module.End (ZMod 2) V} {v : V} : v ∈ k328r5c_C z ↔ z v = v := by
  simp [k328r5c_C, LinearMap.mem_ker, sub_eq_zero]

private theorem k328r5c_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem k328r5c_zz_of_mem_W {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {z : Module.End (ZMod 2) V} {w : V} (hw : w ∈ k328r5c_W z) : z (z w) = z w + w := by
  have hmem := k328r5c_mem_W.1 hw
  calc z (z w) = z (z w) + (z w + w + (z w + w)) := by rw [k328r5c_add_self, add_zero]
    _ = (z (z w) + z w + w) + (z w + w) := by abel
    _ = z w + w := by rw [hmem, zero_add]

private theorem k328r5c_isCompl {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (z : Module.End (ZMod 2) V) (hz3 : z ^ 3 = 1) :
    IsCompl (k328r5c_W z) (k328r5c_C z) := by
  have h2 : ∀ x : V, x + x = 0 := k328r5c_add_self
  constructor
  · rw [Submodule.disjoint_def]
    intro v hvW hvC
    rw [k328r5c_mem_W] at hvW
    rw [k328r5c_mem_C] at hvC
    rw [hvC, hvC, h2, zero_add] at hvW
    exact hvW
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have e1 : z (z (z v)) = v := k328r5c_z_cube z hz3 v
    have hw : z (z v) + z v ∈ k328r5c_W z := by
      rw [k328r5c_mem_W]
      simp only [map_add, e1]
      calc _ = (z v + z v) + (v + v) + (z (z v) + z (z v)) := by abel
        _ = 0 := by simp only [h2]
    have hc : z (z v) + z v + v ∈ k328r5c_C z := by
      rw [k328r5c_mem_C]
      simp only [map_add, e1]
      abel
    have hv : (z (z v) + z v) + (z (z v) + z v + v) = v := by
      calc _ = (z (z v) + z (z v)) + (z v + z v) + v := by abel
        _ = v := by rw [h2, h2, zero_add, zero_add]
    have := Submodule.add_mem_sup hw hc
    rwa [hv] at this

private noncomputable def k328r5c_ob : Module.Basis (Fin 2) (ZMod 2) OmegaField :=
  (AdjoinRoot.powerBasis' omegaPoly_monic).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, omegaPoly_natDegree]))

private theorem k328r5c_ob_apply (i : Fin 2) : k328r5c_ob i = omega ^ (i : ℕ) := by
  simp [k328r5c_ob, Module.Basis.reindex_apply, AdjoinRoot.powerBasis'_gen]

private theorem k328r5c_exists_basis {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V = 6)
    (z : Module.End (ZMod 2) V) (hz : z ^ 2 + z + 1 = 0) :
    ∃ (B : Module.Basis (Fin 6) (ZMod 2) V) (b : Fin 3 → V),
      B 0 = b 0 ∧ B 1 = z (b 0) ∧ B 2 = b 1 ∧ B 3 = z (b 1) ∧ B 4 = b 2 ∧ B 5 = z (b 2) := by
  let _ : Module OmegaField V := Module.compHom V (omegaHom z hz)
  have hsm : ∀ (c : OmegaField) (v : V), c • v = omegaHom z hz c v := fun _ _ => rfl
  have hω : ∀ v : V, (omega : OmegaField) • v = z v := fun v => by rw [hsm, omegaHom_omega]
  have halg : ∀ (a : ZMod 2) (v : V), algebraMap (ZMod 2) OmegaField a • v = a • v :=
    fun a v => by rw [hsm, omegaHom_algebraMap, Module.algebraMap_end_apply]
  have : IsScalarTower (ZMod 2) OmegaField V :=
    ⟨fun c x v => by rw [Algebra.smul_def, mul_smul, halg]⟩
  have : Module.Finite OmegaField V := Module.Finite.of_restrictScalars_finite (ZMod 2) OmegaField V
  have hn : Module.finrank OmegaField V = 3 := by
    have := Module.finrank_mul_finrank (ZMod 2) OmegaField V
    rw [finrank_omegaField, hdim] at this
    omega
  let b : Module.Basis (Fin 3) OmegaField V := Module.finBasisOfFinrankEq OmegaField V hn
  let e : Fin 2 × Fin 3 ≃ Fin 6 := (Equiv.prodComm (Fin 2) (Fin 3)).trans finProdFinEquiv
  let B : Module.Basis (Fin 6) (ZMod 2) V := (k328r5c_ob.smulTower b).reindex e
  have hB : ∀ (i : Fin 2) (j : Fin 3), B (e (i, j)) = omega ^ (i : ℕ) • b j := fun i j => by
    simp [B, Module.Basis.reindex_apply, Module.Basis.smulTower_apply, k328r5c_ob_apply]
  have hB0 : ∀ j : Fin 3, B (e (0, j)) = b j := fun j => by rw [hB]; simp
  have hB1 : ∀ j : Fin 3, B (e (1, j)) = z (b j) := fun j => by rw [hB]; simp [hω]
  exact ⟨B, b, hB0 0, hB1 0, hB0 1, hB1 1, hB0 2, hB1 2⟩


private theorem k328r5c_symm_last : (finSumFinEquiv.symm (6 : Fin 7) : Fin 6 ⊕ Fin 1) = Sum.inr 0 :=
  rfl

private theorem k328r5c_exists_equiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V = 7)
    (z : Module.End (ZMod 2) V) (hz3 : z ^ 3 = 1)
    (hW : Module.finrank (ZMod 2) ↥(k328r5c_W z) = 6) :
    ∃ S : (Fin 7 → ZMod 2) ≃ₗ[ZMod 2] V,
      z (S (Pi.single 0 1)) = S (Pi.single 1 1) ∧
      z (S (Pi.single 1 1)) = S (Pi.single 0 1 + Pi.single 1 1) ∧
      z (S (Pi.single 2 1)) = S (Pi.single 3 1) ∧
      z (S (Pi.single 3 1)) = S (Pi.single 2 1 + Pi.single 3 1) ∧
      z (S (Pi.single 4 1)) = S (Pi.single 5 1) ∧
      z (S (Pi.single 5 1)) = S (Pi.single 4 1 + Pi.single 5 1) ∧
      z (S (Pi.single 6 1)) = S (Pi.single 6 1) := by
  have hcompl := k328r5c_isCompl z hz3
  have hC1 : Module.finrank (ZMod 2) ↥(k328r5c_C z) = 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  obtain ⟨B, b, b0, b1, b2, b3, b4, b5⟩ :=
    k328r5c_exists_basis hW (k328r5c_zW z) (k328r5c_zW_rel z)
  let BC : Module.Basis (Fin 1) (ZMod 2) ↥(k328r5c_C z) := Module.finBasisOfFinrankEq _ _ hC1
  let BV : Module.Basis (Fin 7) (ZMod 2) V :=
    ((B.prod BC).map (Submodule.prodEquivOfIsCompl _ _ hcompl)).reindex finSumFinEquiv
  have hBW : ∀ i : Fin 6, BV i.castSucc = ((B i : ↥(k328r5c_W z)) : V) := fun i => by
    simp [BV, Module.Basis.reindex_apply]
  have hBC : BV (Fin.last 6) = ((BC 0 : ↥(k328r5c_C z)) : V) := by
    simp [BV, Module.Basis.reindex_apply, k328r5c_symm_last]
  have hS : ∀ k, BV.equivFun.symm (Pi.single k 1) = BV k := fun k => by
    simp [Module.Basis.equivFun_symm_apply, Pi.single_apply]
  have hzW : ∀ w : ↥(k328r5c_W z), z (z (w : V)) = z (w : V) + (w : V) := fun w =>
    k328r5c_zz_of_mem_W w.2
  have hzC : z ((BC 0 : ↥(k328r5c_C z)) : V) = ((BC 0 : ↥(k328r5c_C z)) : V) :=
    k328r5c_mem_C.1 (BC 0).2
  have e0 : BV 0 = ((b 0 : ↥(k328r5c_W z)) : V) := by rw [← b0]; exact hBW 0
  have e1 : BV 1 = z ((b 0 : ↥(k328r5c_W z)) : V) := by
    rw [show BV 1 = ((B 1 : ↥(k328r5c_W z)) : V) from hBW 1, b1]
    rfl
  have e2 : BV 2 = ((b 1 : ↥(k328r5c_W z)) : V) := by rw [← b2]; exact hBW 2
  have e3 : BV 3 = z ((b 1 : ↥(k328r5c_W z)) : V) := by
    rw [show BV 3 = ((B 3 : ↥(k328r5c_W z)) : V) from hBW 3, b3]
    rfl
  have e4 : BV 4 = ((b 2 : ↥(k328r5c_W z)) : V) := by rw [← b4]; exact hBW 4
  have e5 : BV 5 = z ((b 2 : ↥(k328r5c_W z)) : V) := by
    rw [show BV 5 = ((B 5 : ↥(k328r5c_W z)) : V) from hBW 5, b5]
    rfl
  have e6 : BV 6 = ((BC 0 : ↥(k328r5c_C z)) : V) := hBC
  refine ⟨BV.equivFun.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [map_add, hS]
  · rw [e0, e1]
  · rw [e0, e1, hzW (b 0), add_comm]
  · rw [e2, e3]
  · rw [e2, e3, hzW (b 1), add_comm]
  · rw [e4, e5]
  · rw [e4, e5, hzW (b 2), add_comm]
  · rw [e6]
    exact hzC

private def k328r5c_zStd : GL (Fin 7) (ZMod 2) :=
  ⟨blockDiag3 (ZMod 2) 7 (rhoOmega (ZMod 2)) (rhoOmega (ZMod 2)) (rhoOmega (ZMod 2)),
    blockDiag3 (ZMod 2) 7 (rhoOmega (ZMod 2) ^ 2) (rhoOmega (ZMod 2) ^ 2)
      (rhoOmega (ZMod 2) ^ 2),
    by decide +kernel, by decide +kernel⟩

private theorem k328r5c_zStd_col :
    k328r5c_zStd.val.mulVec (Pi.single 0 1) = Pi.single 1 1 ∧
    k328r5c_zStd.val.mulVec (Pi.single 1 1) = Pi.single 0 1 + Pi.single 1 1 ∧
    k328r5c_zStd.val.mulVec (Pi.single 2 1) = Pi.single 3 1 ∧
    k328r5c_zStd.val.mulVec (Pi.single 3 1) = Pi.single 2 1 + Pi.single 3 1 ∧
    k328r5c_zStd.val.mulVec (Pi.single 4 1) = Pi.single 5 1 ∧
    k328r5c_zStd.val.mulVec (Pi.single 5 1) = Pi.single 4 1 + Pi.single 5 1 ∧
    k328r5c_zStd.val.mulVec (Pi.single 6 1) = Pi.single 6 1 := by
  decide +kernel

private theorem k328r5c_core (z : GL (Fin 7) (ZMod 2)) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (X : Subgroup (GL (Fin 7) (ZMod 2))) (hzX : z ∈ X) (hXC : ∀ x ∈ X, x * z = z * x)
    (hXperf : ⁅X, X⁆ = X) : ∃ g : GL (Fin 7) (ZMod 2), g * z * g⁻¹ = k328r5c_zStd := by
  let T : Matrix (Fin 7) (Fin 7) (ZMod 2) ≃ₐ[ZMod 2] Module.End (ZMod 2) (Fin 7 → ZMod 2) :=
    Matrix.toLinAlgEquiv'
  let ρ : ↥X →* Module.End (ZMod 2) (Fin 7 → ZMod 2) :=
    (T.toMonoidHom).comp ((Units.coeHom _).comp X.subtype)
  let zE : Module.End (ZMod 2) (Fin 7 → ZMod 2) := T z.val
  have hzE3 : zE ^ 3 = 1 := by
    show T z.val ^ 3 = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hz3, Units.val_one, map_one]
  have hzE1 : zE ≠ 1 := fun h =>
    hz1 (Units.ext (T.injective (by rw [Units.val_one, map_one]; exact h)))
  have hρ : ∀ g : ↥X, Commute (ρ g) zE := fun g => by
    show T (g.1.val) * T z.val = T z.val * T g.1.val
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hXC g.1 g.2]
  have hperf : commutator ↥X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subtype_commutator, hXperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hdim : Module.finrank (ZMod 2) (Fin 7 → ZMod 2) = 7 := Module.finrank_fin_fun (ZMod 2)
  have hW := k328r5c_finrank_W hdim zE hzE3 hzE1 ρ hρ hperf ⟨z, hzX⟩ rfl
  obtain ⟨S, h0, h1, h2, h3, h4, h5, h6⟩ := k328r5c_exists_equiv hdim zE hzE3 hW
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := k328r5c_zStd_col
  let P : GL (Fin 7) (ZMod 2) :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv S)
  have hP : T P.val = (S : (Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 7 → ZMod 2)) :=
    congrArg Units.val
      (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
        (LinearMap.GeneralLinearGroup.ofLinearEquiv S))
  have hrel : zE * (S : (Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 7 → ZMod 2)) =
      (S : (Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 7 → ZMod 2)) * T k328r5c_zStd.val := by
    refine (Pi.basisFun (ZMod 2) (Fin 7)).ext fun k => ?_
    simp only [Pi.basisFun_apply, Module.End.mul_apply]
    show zE (S (Pi.single k 1)) = S (k328r5c_zStd.val.mulVec (Pi.single k 1))
    fin_cases k
    · simpa [c0] using h0
    · simpa [c1] using h1
    · simpa [c2] using h2
    · simpa [c3] using h3
    · simpa [c4] using h4
    · simpa [c5] using h5
    · simpa [c6] using h6
  have hmat : z.val * P.val = P.val * k328r5c_zStd.val :=
    T.injective (by rw [map_mul, map_mul, hP]; exact hrel)
  refine ⟨P⁻¹, ?_⟩
  have hGL : z * P = P * k328r5c_zStd := Units.ext hmat
  rw [inv_inv, mul_assoc, hGL, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem k328r5c_map_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (A B C : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    ι.mapMatrix (blockDiag3 (ZMod 2) 7 A B C) =
      blockDiag3 F 7 (ι.mapMatrix A) (ι.mapMatrix B) (ι.mapMatrix C) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, blockDiag3, Matrix.of_apply]
  split_ifs <;> simp [Matrix.one_apply]

private theorem k328r5c_map_rho {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) : ι.mapMatrix (rhoOmega (ZMod 2)) = rhoOmega F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rhoOmega]

private theorem k328r5c_map_zStd {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    Matrix.GeneralLinearGroup.map ι k328r5c_zStd = z₀ := by
  apply Units.ext
  rw [hz]
  show ι.mapMatrix (blockDiag3 (ZMod 2) 7 (rhoOmega (ZMod 2)) (rhoOmega (ZMod 2))
    (rhoOmega (ZMod 2))) = _
  rw [k328r5c_map_blockDiag3, k328r5c_map_rho]

private theorem k328r5c_map_symm {F : Type} [Field F] (e : ZMod 2 ≃+* F) (g : GL (Fin 7) F) :
    Matrix.GeneralLinearGroup.map e.toRingHom
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  exact e.apply_symm_apply _

theorem row5_class (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ t₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (ht : (t₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    ClassLeaf (StatedSL 7 F) z₀ := by
  have _ := ht
  intro z _ hzo X _ hzX hXC hXperf
  have hcard : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; exact hF
  have hH : ∀ g : GL (Fin 7) F, g ∈ StatedSL 7 F := fun g => by
    rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hcard 7]
    trivial
  let e : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF
  let φ : GL (Fin 7) (ZMod 2) →* GL (Fin 7) F := Matrix.GeneralLinearGroup.map e.toRingHom
  let ψ : GL (Fin 7) F →* GL (Fin 7) (ZMod 2) := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  have hφψ : ∀ g, φ (ψ g) = g := k328r5c_map_symm e
  have hψ : Function.Injective ψ := Function.LeftInverse.injective hφψ
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  obtain ⟨g, hg⟩ := k328r5c_core (ψ z) (by rw [← map_pow, hz3, map_one])
    (fun h => hz1 (hψ (h.trans (map_one ψ).symm))) (X.map ψ) (Subgroup.mem_map_of_mem ψ hzX)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hXC hx) z rfl).symm])
    (by rw [← Subgroup.map_commutator, hXperf])
  refine ⟨φ g, hH _, Or.inl ?_⟩
  calc φ g * z * (φ g)⁻¹ = φ (g * ψ z * g⁻¹) := by rw [map_mul, map_mul, map_inv, hφψ]
    _ = z₀ := by rw [hg]; exact k328r5c_map_zStd e.toRingHom z₀ hz

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
