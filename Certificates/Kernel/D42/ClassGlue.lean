module

public import Certificates.Kernel.D42.ClassK
public import Certificates.Kernel.OmegaEight.Bridge3009
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses

public section

namespace CertificateChecks.KernelD42

open Equiv CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CertificateChecks.KernelO8
open CFSG.Sporadic.Schreier (conjClass conjClass_finite)

@[expose] def FixC (b : ℕ) (z : Perm (Fin 360)) : Prop := ∃ p : Fin 360, (p : ℕ) / 120 = b ∧ z p = p

theorem fixC_conj {h : Perm (Fin 360)} {b c : ℕ}
    (hh : ∀ p : Fin 360, ((h p : Fin 360) : ℕ) / 120 = c ↔ (p : ℕ) / 120 = b) (z : Perm (Fin 360)) :
    FixC c (h * z * h⁻¹) ↔ FixC b z := by
  constructor
  · rintro ⟨p, hp, hz⟩
    refine ⟨h⁻¹ p, (hh (h⁻¹ p)).1 (by simpa using hp), ?_⟩
    have e : h (z (h⁻¹ p)) = p := by simpa [Perm.mul_apply] using hz
    apply h.injective
    rw [e]
    simp
  · rintro ⟨p, hp, hz⟩
    exact ⟨h p, (hh p).2 hp, by simp [Perm.mul_apply, hz]⟩

theorem stab0_copy {g : Perm (Fin 360)} (hg : g ∈ stab0) (p : Fin 360) :
    ((g p : Fin 360) : ℕ) / 120 = 0 ↔ (p : ℕ) / 120 = 0 := by
  have := hg p
  omega

section Model


theorem rho_copy {b c : ℕ} (hb : b < 3) (hc : c = (b + 1) % 3) (p : Fin 360) :
    ((gen 8 p : Fin 360) : ℕ) / 120 = c ↔ (p : ℕ) / 120 = b := by
  rw [gen8_val]
  have := p.2
  omega

theorem fixC_omega {g : Perm (Fin 360)} (hg : g ∈ omegaT) (z : Perm (Fin 360)) :
    FixC 0 (g * z * g⁻¹) ↔ FixC 0 z :=
  fixC_conj (stab0_copy (omegaT_le_stab0 hg)) z

theorem x1_val (p : Fin 360) : ((mainPerm 1 p : Fin 360) : ℕ) = at9 (mainK 1) p := by
  rw [← (mainPerm_spec (i := 1) (by norm_num)).1 p, (main_ok (i := 1) (by norm_num)).1,
    at9_eq p.2]

theorem fixC_x1_zero : FixC 0 (mainPerm 1) :=
  ⟨8, rfl, Fin.ext (by rw [x1_val]; exact Nat.eq_of_beq_eq_true kC2Fix)⟩

theorem not_fixC_x1 {b : ℕ} (hb : 0 < b) : ¬ FixC b (mainPerm 1) := by
  rintro ⟨p, hp, hz⟩
  have h120 : 120 ≤ (p : ℕ) := by omega
  have hne := noFixUp_spec kC2NoFix ((p : ℕ) - 120) (by have := p.2; omega)
  rw [Nat.sub_add_cancel h120, ← x1_val, hz] at hne
  exact hne rfl

theorem rho_mem : gen 8 ∈ autT := gen_mem_autT (by norm_num)

theorem conj_rho_mem {g : Perm (Fin 360)} (hg : g ∈ omegaT) : gen 8 * g * (gen 8)⁻¹ ∈ omegaT :=
  (conj_mem_omegaT rho_mem).1 hg

theorem conj_rho_inv_mem {g : Perm (Fin 360)} (hg : g ∈ omegaT) :
    (gen 8)⁻¹ * g * gen 8 ∈ omegaT := by
  have := (conj_mem_omegaT (autT.inv_mem rho_mem)).1 hg
  rwa [inv_inv] at this

theorem ne_conj_one {g : Perm (Fin 360)} (hg : g ∈ omegaT) :
    g * mainPerm 1 * g⁻¹ ≠ gen 8 * mainPerm 1 * (gen 8)⁻¹ := by
  intro e
  have h1 := (fixC_omega hg _).2 fixC_x1_zero
  rw [e, fixC_conj (rho_copy (b := 2) (by norm_num) rfl)] at h1
  exact not_fixC_x1 (by norm_num) h1

theorem ne_conj_two {g : Perm (Fin 360)} (hg : g ∈ omegaT) :
    g * mainPerm 1 * g⁻¹ ≠ (gen 8)⁻¹ * mainPerm 1 * gen 8 := by
  intro e
  have h1 := (fixC_omega hg _).2 fixC_x1_zero
  rw [e, ← fixC_conj (rho_copy (b := 0) (by norm_num) rfl)] at h1
  have e2 : gen 8 * ((gen 8)⁻¹ * mainPerm 1 * gen 8) * (gen 8)⁻¹ = mainPerm 1 := by group
  rw [e2] at h1
  exact not_fixC_x1 (by norm_num) h1

theorem ne_conj_three {g : Perm (Fin 360)} (hg : g ∈ omegaT) :
    g * (gen 8 * mainPerm 1 * (gen 8)⁻¹) * g⁻¹ ≠ (gen 8)⁻¹ * mainPerm 1 * gen 8 := by
  intro e
  set r := gen 8
  have e2 : (r * g * r⁻¹) * (r * (r * mainPerm 1 * r⁻¹) * r⁻¹) * (r * g * r⁻¹)⁻¹ = mainPerm 1 :=
    calc (r * g * r⁻¹) * (r * (r * mainPerm 1 * r⁻¹) * r⁻¹) * (r * g * r⁻¹)⁻¹
        = r * (g * (r * mainPerm 1 * r⁻¹) * g⁻¹) * r⁻¹ := by group
      _ = r * (r⁻¹ * mainPerm 1 * r) * r⁻¹ := by rw [e]
      _ = mainPerm 1 := by group
  have h1 := fixC_x1_zero
  rw [← e2, fixC_omega (conj_rho_mem hg), fixC_conj (rho_copy (b := 2) (by norm_num) rfl),
    fixC_conj (rho_copy (b := 1) (by norm_num) rfl)] at h1
  exact not_fixC_x1 (by norm_num) h1

theorem disj_of_ne {u v : Perm (Fin 360)}
    (h : ∀ g ∈ omegaT, g * u * g⁻¹ ≠ v) : Disjoint (conjClass omegaT u) (conjClass omegaT v) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, e⟩
  apply h (b⁻¹ * a) (omegaT.mul_mem (omegaT.inv_mem hb) ha)
  rw [show b⁻¹ * a * u * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * u * a⁻¹) * b by group, e]
  group

theorem image_conj_sub {r : Perm (Fin 360)} (hr : ∀ g ∈ omegaT, r * g * r⁻¹ ∈ omegaT)
    (u : Perm (Fin 360)) :
    (fun z => r * z * r⁻¹) '' conjClass omegaT u ⊆ conjClass omegaT (r * u * r⁻¹) := by
  rintro _ ⟨z, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨r * a * r⁻¹, hr a ha, by group⟩

theorem ncard_le_conj {r : Perm (Fin 360)} (hr : ∀ g ∈ omegaT, r * g * r⁻¹ ∈ omegaT)
    (u : Perm (Fin 360)) :
    (conjClass omegaT u).ncard ≤ (conjClass omegaT (r * u * r⁻¹)).ncard := by
  have hinj : Function.Injective fun z : Perm (Fin 360) => r * z * r⁻¹ := fun a b h => by
    simpa using h
  rw [← Set.ncard_image_of_injective (conjClass omegaT u) hinj]
  exact Set.ncard_le_ncard (image_conj_sub hr u) (conjClass_finite _ _)

theorem conjClass_sub_auto {r : Perm (Fin 360)} (hr : r ∈ autT) (u : Perm (Fin 360)) :
    conjClass omegaT (r * u * r⁻¹) ⊆ conjClass autT u := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a * r, autT.mul_mem (omegaT_le_autT ha) hr, by group⟩

theorem three_mul_ncard_le :
    3 * (conjClass omegaT (mainPerm 1)).ncard ≤ (conjClass autT (mainPerm 1)).ncard := by
  set x := mainPerm 1
  set r := gen 8
  set S0 := conjClass omegaT x
  set S1 := conjClass omegaT (r * x * r⁻¹)
  set S2 := conjClass omegaT (r⁻¹ * x * r⁻¹⁻¹)
  have e2 : r⁻¹ * x * r⁻¹⁻¹ = r⁻¹ * x * r := by rw [inv_inv]
  have hf : ∀ u, (conjClass omegaT u).Finite := fun u => conjClass_finite _ _
  have h1 : S0.ncard ≤ S1.ncard := ncard_le_conj (fun g hg => conj_rho_mem hg) x
  have h2 : S0.ncard ≤ S2.ncard := by
    refine ncard_le_conj (fun g hg => ?_) x
    rw [inv_inv]
    exact conj_rho_inv_mem hg
  have d01 : Disjoint S0 S1 := disj_of_ne fun g hg => ne_conj_one hg
  have d02 : Disjoint S0 S2 := disj_of_ne fun g hg => by rw [e2]; exact ne_conj_two hg
  have d12 : Disjoint S1 S2 := disj_of_ne fun g hg => by rw [e2]; exact ne_conj_three hg
  have hsub : S0 ∪ S1 ∪ S2 ⊆ conjClass autT x := by
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, omegaT_le_autT ha, rfl⟩
    · exact conjClass_sub_auto rho_mem x
    · exact conjClass_sub_auto (autT.inv_mem rho_mem) x
  have hcard : (S0 ∪ S1 ∪ S2).ncard = S0.ncard + S1.ncard + S2.ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d02, d12⟩) ((hf _).union (hf _)) (hf _),
      Set.ncard_union_eq d01 (hf _) (hf _)]
  have hle := Set.ncard_le_ncard hsub (conjClass_finite _ _)
  omega

end Model

end CertificateChecks.KernelD42
