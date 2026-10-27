module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSet
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Involutions
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolution

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

section Basic

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem cj_inj {s t : Xg h} : cj h s = cj h t ↔ s = t := conj_inj h

theorem conj_hom_injective : Function.Injective (MulAut.conj : Xg h →* MulAut (Xg h)) :=
  fun _ _ e => (cj_inj h).1 e

instance finite_Xg [CharP K 2] : Finite (Xg h) := finite_gramSU_miyamotoJ4 h

instance finite_autXg [CharP K 2] : Finite (MulAut (Xg h)) :=
  Finite.of_injective (fun φ : MulAut (Xg h) => (φ : Xg h → Xg h)) fun _ _ e =>
    MulEquiv.ext (congrFun e)

end Basic

section FieldAut

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem isCyclic_aut : IsCyclic (K ≃+* K) := by
  obtain ⟨σ, -, -, hσ, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
    (by have := h.one_le; omega) h.card
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩

include h in
theorem finite_aut : Finite (K ≃+* K) :=
  Nat.finite_of_card_ne_zero (by rw [card_ringAut h]; have := h.one_le; omega)

include h in
theorem aut_comm (φ ψ : K ≃+* K) : φ * ψ = ψ * φ := by
  have := isCyclic_aut h
  exact (IsCyclic.commGroup (α := K ≃+* K)).mul_comm φ ψ

abbrev barE : K ≃+* K := miyamotoBarEquiv h

theorem barE_mul_self : barE h * barE h = 1 := by
  ext c
  change h.bar (h.bar c) = c
  exact h.bar_bar c

theorem barE_ne_one : barE h ≠ 1 := by
  intro e
  have hf : ∀ c : K, h.bar c = c := fun c => by
    have := congrArg (fun φ : K ≃+* K => φ c) e
    exact this
  have h1 := ncard_fixed h
  have h2 : {d : K | h.bar d = d} = Set.univ := by
    ext d
    simp [hf d]
  have h3 : (Set.univ : Set K).ncard = Nat.card K := by
    rw [Set.ncard_univ]
  rw [h2, h3, h.card] at h1
  have hf1 := h.one_le
  have : 2 ^ f < 2 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem eq_barE_of_mul_self {φ : K ≃+* K} (hφ : φ * φ = 1) (hne : φ ≠ 1) : φ = barE h := by
  rcases ringEquiv_eq_refl_or_bar h hφ with e | e
  · exact absurd e hne
  · exact RingEquiv.ext e

end FieldAut

section Stable

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem fStab_sg {M : Subgroup (GL (Fin 4) K)}
    (hM : ∀ (φ : K ≃+* K) (g : GL (Fin 4) K), glAut φ g ∈ M ↔ g ∈ M) : FStab h (sg h M) := by
  intro φ x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_miyamotoFieldAut_apply]
  exact hM φ _

theorem glAut_mem_unip (φ : K ≃+* K) {za zb : Bool} {g : GL (Fin 4) K}
    (hg : g ∈ miyamotoUnipotent h za zb) : glAut φ g ∈ miyamotoUnipotent h za zb := by
  obtain ⟨a, b, c, d, ha, hb, hb', hd, rfl⟩ := (mem_miyamotoUnipotent h).1 hg
  rw [glAut_miyamotoXGL]
  refine (mem_miyamotoUnipotent h).2 ⟨φ a, φ b, φ c, φ d, fun e => by rw [ha e, map_zero],
    fun e => by rw [hb e, map_zero], by rw [← map_bar_comm, hb'], ?_, rfl⟩
  have e := congrArg φ hd
  simp only [map_add, map_mul, map_zero, map_bar_comm] at e
  exact e

theorem glAut_mem_unip_iff (φ : K ≃+* K) {za zb : Bool} {g : GL (Fin 4) K} :
    glAut φ g ∈ miyamotoUnipotent h za zb ↔ g ∈ miyamotoUnipotent h za zb := by
  refine ⟨fun hg => ?_, glAut_mem_unip h φ⟩
  have := glAut_mem_unip h φ⁻¹ hg
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this

theorem glAut_mem_Z_iff (φ : K ≃+* K) {g : GL (Fin 4) K} :
    glAut φ g ∈ miyamotoZ h ↔ g ∈ miyamotoZ h := by
  have key : ∀ (ψ : K ≃+* K) {g : GL (Fin 4) K}, g ∈ miyamotoZ h → glAut ψ g ∈ miyamotoZ h := by
    rintro ψ g ⟨d, hd, rfl⟩
    rw [glAut_miyamotoXGL]
    exact ⟨ψ d, by rw [← map_bar_comm, hd], by simp⟩
  refine ⟨fun hg => ?_, key φ⟩
  have := key φ⁻¹ hg
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this

theorem fStab_Psy : FStab h (Psy h) := fStab_sg h fun φ _ => glAut_mem_unip_iff h φ

theorem fStab_A1X : FStab h (A1X h) := fStab_sg h fun φ _ => glAut_mem_unip_iff h φ

theorem fStab_A2X : FStab h (A2X h) := fStab_sg h fun φ _ => glAut_mem_unip_iff h φ

theorem fStab_ZX : FStab h (ZX h) := fStab_sg h fun φ _ => glAut_mem_Z_iff h φ

omit [CharP K 2] in
theorem fStab_normalizer {B : Subgroup (Xg h)} (hB : FStab h B) :
    FStab h (Subgroup.normalizer (B : Set (Xg h))) := by
  intro φ x
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    have := hx (fa h φ y)
    rwa [← map_inv, ← map_mul, ← map_mul, hB, hB] at this
  · intro hx y
    obtain ⟨y', rfl⟩ := (fa h φ).surjective y
    have := hx y'
    rw [← hB φ y', ← hB φ (x * y' * x⁻¹), map_mul, map_mul, map_inv] at this
    exact this

theorem fStab_Pt : FStab h (Pt h) := fStab_normalizer h (fStab_A2X h)

theorem fStab_Ln : FStab h (Ln h) := fStab_normalizer h (fStab_A1X h)

end Stable

section Elements

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

@[expose] def z1X : Xg h := ⟨miyamotoZ1 K, miyamotoZ1_mem_gramSU h⟩

@[expose] def z2X : Xg h := ⟨LocalAnalysis.miyamotoZ2 K, miyamotoZ2_mem_gramSU h⟩

theorem coe_z1X : ((z1X h : Xg h) : GL (Fin 4) K) = miyamotoXGL h 0 0 0 1 := miyamotoZ1_eq h

theorem coe_z2X : ((z2X h : Xg h) : GL (Fin 4) K) = miyamotoXGL h 0 0 1 0 := miyamotoZ2_eq h

theorem fa_z1X (φ : K ≃+* K) : fa h φ (z1X h) = z1X h := by
  apply Subtype.ext
  rw [coe_miyamotoFieldAut_apply, coe_z1X, glAut_miyamotoXGL]
  simp

theorem fa_z2X (φ : K ≃+* K) : fa h φ (z2X h) = z2X h := by
  apply Subtype.ext
  rw [coe_miyamotoFieldAut_apply, coe_z2X, glAut_miyamotoXGL]
  simp

theorem z1X_mem_ZX : z1X h ∈ ZX h := by
  rw [Subgroup.mem_subgroupOf, coe_z1X]
  exact (miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, rfl, by simp⟩

theorem z1X_mem_A1X : z1X h ∈ A1X h := by
  rw [Subgroup.mem_subgroupOf, coe_z1X]
  exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, by simp⟩

theorem z2X_mem_A1X : z2X h ∈ A1X h := by
  rw [Subgroup.mem_subgroupOf, coe_z2X]
  exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩

theorem z1X_mem_Psy : z1X h ∈ Psy h := miyamotoA1_le_P h (z1X_mem_A1X h)

theorem z2X_mem_Psy : z2X h ∈ Psy h := miyamotoA1_le_P h (z2X_mem_A1X h)

end Elements

end CFSG.Quasithin.H13.F431.Un.OL
